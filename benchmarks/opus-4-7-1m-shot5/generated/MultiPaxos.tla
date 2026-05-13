---- MODULE MultiPaxos ----
(*********************************************************************************)
(* MultiPaxos in state machine replication (SMR) style with write/read commands  *)
(* on a single key. Please refer to the detailed comments in PlusCal code to see *)
(* how this spec closely models a practical SMR log replication system.          *)
(*                                                                                *)
(* Network is modeled as a monotonic set of sent messages. This is a particularly*)
(* efficient model for a practical non-Byzantine asynchronous network: messages  *)
(* may be arbitrarily delayed, may be duplicatedly received, and may be lost     *)
(* (but in this case the sender would repeatedly retry and thus the message      *)
(* should eventually gets received).                                             *)
(*                                                                                *)
(* Linearizability is checked from global client's point of view on the sequence *)
(* of client observed request/acknowledgement events after termination.          *)
(*                                                                                *)
(* Liveness is checked by not having deadlocks till observation of all requests. *)
(*                                                                                *)
(* Possible further extensions include node failure injection, leader lease and  *)
(* local read mechanism, etc.                                                    *)
(*********************************************************************************)
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

(******************************)
(* Model inputs & assumptions. *)
(******************************)
CONSTANTS
  Replicas,    \* symmetric set of server nodes
  Writes,      \* symmetric set of write commands (each w/ unique value)
              \* a write command model value serves as both the
              \* ID of the command and the value to be written
  Reads,       \* symmetric set of read commands
  MaxBallot    \* maximum ballot pickable for leader preemption

ASSUME
  /\ IsFiniteSet(Replicas) /\ Replicas # {}
  /\ IsFiniteSet(Writes \cup Reads)
  /\ MaxBallot \in Nat /\ MaxBallot >= 1

(*******************************)
(* Useful constants & typedefs. *)
(*******************************)
Commands == Writes \cup Reads
NumCommands == Cardinality(Commands)
NumReplicas == Cardinality(Replicas)
MajorityNum == (NumReplicas \div 2) + 1
Slots == 1..NumCommands
Ballots == 1..MaxBallot

\* Client observable events.
ReqEvent(c) == [type |-> "Req", cmd |-> c]
\* val is the old value for a write command
AckEvent(c, v) == [type |-> "Ack", cmd |-> c, val |-> v]
ClientEvents == { ReqEvent(c) : c \in Commands }
              \cup { AckEvent(c, v) : c \in Commands, v \in Writes \cup {"nil"} }

\* W.L.O.G., choose any sequence concatenating writes
\* commands and read commands as the sequence of reqs;
\* all other cases are either symmetric or less useful
\* than this one
InitPending ==
  LET WS == CHOOSE s \in [1..Cardinality(Writes) -> Writes] :
              \A i, j \in 1..Cardinality(Writes) : (i # j) => (s[i] # s[j])
      RS == CHOOSE s \in [1..Cardinality(Reads) -> Reads] :
              \A i, j \in 1..Cardinality(Reads) : (i # j) => (s[i] # s[j])
  IN  [i \in 1..NumCommands |->
        IF i <= Cardinality(Writes) THEN WS[i] ELSE RS[i - Cardinality(Writes)]]

\* Server-side constants & states.
Statuses == {"Empty", "Preparing", "Accepting", "Committed"}
NullBal == 0
NullCmd == "nil"

InstanceState == [status : Statuses,
                  cmd    : Commands \cup {NullCmd},
                  voted  : [bal : Nat, cmd : Commands \cup {NullCmd}]]

NullInstance == [status |-> "Empty",
                 cmd |-> NullCmd,
                 voted |-> [bal |-> NullBal, cmd |-> NullCmd]]

NullNode == [leader      |-> NullCmd,
             balPrepared |-> NullBal,
             balMaxKnown |-> NullBal,
             commitUpTo  |-> 0,
             kvalue      |-> "nil",
             insts       |-> [s \in Slots |-> NullInstance]]

\* Service-internal messages.
PrepareMsg(r, b) == [type |-> "Prepare", src |-> r, bal |-> b]

PrepareReplyMsg(r, b, votes) ==
  [type |-> "PrepareReply", src |-> r, bal |-> b, votes |-> votes]

AcceptMsg(r, b, s, c) ==
  [type |-> "Accept", src |-> r, bal |-> b, slot |-> s, cmd |-> c]

AcceptReplyMsg(r, b, s) ==
  [type |-> "AcceptReply", src |-> r, bal |-> b, slot |-> s]

CommitNoticeMsg(s) ==
  [type |-> "CommitNotice", upto |-> s]

VotesByNode(n) == [s \in Slots |-> n.insts[s].voted]

\* For a set of PrepareReplies, find the peak voted command for slot s.
PeakVotedCmd(prs, s) ==
  LET candidates == { vr.votes[s] : vr \in prs }
      bestBal == LET ballots == { v.bal : v \in candidates }
                 IN  IF ballots = {} THEN NullBal
                     ELSE CHOOSE b \in ballots : \A b2 \in ballots : b >= b2
  IN  IF bestBal = NullBal THEN NullCmd
      ELSE (CHOOSE v \in candidates : v.bal = bestBal).cmd

FirstEmptySlot(insts) ==
  CHOOSE s \in Slots :
    /\ insts[s].status = "Empty"
    /\ \A s2 \in Slots : s2 < s => insts[s2].status # "Empty"

Range(seq) == { seq[i] : i \in DOMAIN seq }

(*****************************)
(* Main algorithm in PlusCal. *)
(*****************************)
(*--algorithm MultiPaxos
variable msgs = {},                             \* messages in the network
         node = [r \in Replicas |-> NullNode],  \* replica node state
         pending = InitPending,                 \* sequence of pending reqs
         observed = <<>>;                       \* client observed events
*)

\* BEGIN TRANSLATION (chksum(pcal) = "2be53042" /\ chksum(tla) = "bfbfd945")
VARIABLES msgs, node, pending, observed, pc

vars == << msgs, node, pending, observed, pc >>

ProcSet == Replicas

(* define statement *)
UnseenPending(insts) ==
  LET filter(c) == c \notin {insts[s].cmd: s \in Slots}
  IN  SelectSeq(pending, filter)

RemovePending(cmd) ==
  LET filter(c) == c # cmd
  IN  SelectSeq(pending, filter)

reqsMade == {e.cmd: e \in {e \in Range(observed): e.type = "Req"}}
acksRecv == {e.cmd: e \in {e \in Range(observed): e.type = "Ack"}}

terminated == /\ Len(pending) = 0
              /\ Cardinality(reqsMade) = NumCommands
              /\ Cardinality(acksRecv) = NumCommands

(* Global variables *)
Init ==
  /\ msgs = {}
  /\ node = [r \in Replicas |-> NullNode]
  /\ pending = InitPending
  /\ observed = <<>>
  /\ pc = [self \in ProcSet |-> "rloop"]

\* Send a set of messages helper.
Send(set, oldMsgs) == oldMsgs \cup set

\* Observe a client event helper.
ObserveSeq(e, oldObs) ==
  IF e \in Range(oldObs) THEN oldObs ELSE Append(oldObs, e)

\* Resolve a pending command helper.
Resolve(c, oldPending) ==
  LET filter(x) == x # c
  IN  SelectSeq(oldPending, filter)

\* Someone steps up as leader and sends Prepare message to followers.
BecomeLeader(r) ==
  \* if I'm not a leader
  /\ node[r].leader # r
  \* pick a greater ballot number
  /\ \E b \in Ballots :
       /\ b > node[r].balMaxKnown
       \* W.L.O.G., using this clause to model that ballot
       \* numbers from different proposers be unique
       /\ ~ \E m \in msgs : (m.type = "Prepare") /\ (m.bal = b)
       \* update states and restart Prepare phase for in-progress instances
       /\ node' = [node EXCEPT ![r] =
            [@ EXCEPT !.leader = r,
                      !.balPrepared = 0,
                      !.balMaxKnown = b,
                      !.insts = [s \in Slots |->
                        [@[s] EXCEPT !.status =
                            IF @ = "Accepting" THEN "Preparing" ELSE @]]]]
       \* broadcast Prepare and reply to myself instantly
       /\ msgs' = Send({PrepareMsg(r, b),
                        PrepareReplyMsg(r, b, VotesByNode(node[r]))}, msgs)
  /\ UNCHANGED <<pending, observed>>

\* Replica replies to a Prepare message.
HandlePrepare(r) ==
  \* if receiving a Prepare message with larger ballot than ever seen
  \E m \in msgs :
    /\ m.type = "Prepare"
    /\ m.bal > node[r].balMaxKnown
    \* update states and reset statuses
    /\ node' = [node EXCEPT ![r] =
         [@ EXCEPT !.leader = m.src,
                   !.balMaxKnown = m.bal,
                   !.insts = [s \in Slots |->
                     [@[s] EXCEPT !.status =
                         IF @ = "Accepting" THEN "Preparing" ELSE @]]]]
    \* send back PrepareReply with my voted list
    /\ msgs' = Send({PrepareReplyMsg(r, m.bal, VotesByNode(node[r]))}, msgs)
    /\ UNCHANGED <<pending, observed>>

\* Leader gathers PrepareReply messages until condition met.
HandlePrepareReplies(r) ==
  \* if I'm waiting for PrepareReplies
  /\ node[r].leader = r
  /\ node[r].balPrepared = 0
  \* when there are enough number of PrepareReplies of desired ballot
  /\ LET prs == { m \in msgs : /\ m.type = "PrepareReply"
                              /\ m.bal = node[r].balMaxKnown }
     IN
       /\ Cardinality(prs) >= MajorityNum
       \* marks this ballot as prepared and saves highest voted command
       /\ node' = [node EXCEPT ![r] =
            [@ EXCEPT !.balPrepared = node[r].balMaxKnown,
                      !.insts = [s \in Slots |->
                        [@[s] EXCEPT
                          !.status = IF \/ @ = "Preparing"
                                        \/ /\ @ = "Empty"
                                           /\ PeakVotedCmd(prs, s) # NullCmd
                                       THEN "Accepting"
                                       ELSE @,
                          !.cmd = IF PeakVotedCmd(prs, s) # NullCmd
                                    THEN PeakVotedCmd(prs, s)
                                    ELSE @]]]]
       \* send Accept messages for in-progress instances
       /\ msgs' = Send({ AcceptMsg(r, node[r].balPrepared, s, node[r].insts[s].cmd) :
                          s \in { s \in Slots : node[r].insts[s].status = "Accepting" } },
                       msgs)
  /\ UNCHANGED <<pending, observed>>

\* A prepared leader takes a new request to fill the next empty slot.
TakeNewRequest(r) ==
  \* if I'm a prepared leader and there's pending request
  /\ node[r].leader = r
  /\ node[r].balPrepared = node[r].balMaxKnown
  /\ \E s \in Slots : node[r].insts[s].status = "Empty"
  /\ Len(UnseenPending(node[r].insts)) > 0
  \* find the next empty slot and pick a pending request
  /\ LET s == FirstEmptySlot(node[r].insts)
         c == Head(UnseenPending(node[r].insts))
     IN
       \* W.L.O.G., only pick a command not seen in current
       \* prepared log to have smaller state space
       \* update slot status and voted
       /\ node' = [node EXCEPT ![r] =
            [@ EXCEPT !.insts =
              [@ EXCEPT ![s] =
                [@ EXCEPT !.status = "Accepting",
                          !.cmd = c,
                          !.voted = [bal |-> node[r].balPrepared, cmd |-> c]]]]]
       \* broadcast Accept and reply to myself instantly
       /\ msgs' = Send({ AcceptMsg(r, node[r].balPrepared, s, c),
                         AcceptReplyMsg(r, node[r].balPrepared, s) }, msgs)
       \* append to observed events sequence if haven't yet
       /\ observed' = ObserveSeq(ReqEvent(c), observed)
       /\ UNCHANGED pending

\* Replica replies to an Accept message.
HandleAccept(r) ==
  \* if receiving an unreplied Accept message with valid ballot
  \E m \in msgs :
    /\ m.type = "Accept"
    /\ m.bal >= node[r].balMaxKnown
    /\ m.bal > node[r].insts[m.slot].voted.bal
    \* update node states and corresponding instance's states
    /\ node' = [node EXCEPT ![r] =
         [@ EXCEPT !.leader = m.src,
                   !.balMaxKnown = m.bal,
                   !.insts = [@ EXCEPT ![m.slot] =
                     [@ EXCEPT !.status = "Accepting",
                               !.cmd = m.cmd,
                               !.voted = [bal |-> m.bal, cmd |-> m.cmd]]]]]
    \* send back AcceptReply
    /\ msgs' = Send({AcceptReplyMsg(r, m.bal, m.slot)}, msgs)
    /\ UNCHANGED <<pending, observed>>

\* Leader gathers AcceptReply messages for a slot.
HandleAcceptReplies(r) ==
  \* if I think I'm a current leader
  /\ node[r].leader = r
  /\ node[r].balPrepared = node[r].balMaxKnown
  /\ node[r].commitUpTo < NumCommands
  /\ node[r].insts[node[r].commitUpTo + 1].status = "Accepting"
  /\ LET s == node[r].commitUpTo + 1
         c == node[r].insts[s].cmd
         v == node[r].kvalue
         ars == { m \in msgs : /\ m.type = "AcceptReply"
                              /\ m.slot = s
                              /\ m.bal = node[r].balPrepared }
     IN
       /\ Cardinality(ars) >= MajorityNum
       \* marks this slot as committed and apply command
       /\ node' = [node EXCEPT ![r] =
            [@ EXCEPT !.insts = [@ EXCEPT ![s] = [@ EXCEPT !.status = "Committed"]],
                      !.commitUpTo = s,
                      !.kvalue = IF c \in Writes THEN c ELSE @]]
       \* append to observed events sequence if haven't yet, and remove
       \* the command from pending
       /\ observed' = ObserveSeq(AckEvent(c, v), observed)
       /\ pending' = Resolve(c, pending)
       \* broadcast CommitNotice to followers
       /\ msgs' = Send({CommitNoticeMsg(s)}, msgs)

\* Replica receives new commit notification.
HandleCommitNotice(r) ==
  \* if I'm a follower waiting on CommitNotice
  /\ node[r].leader # r
  /\ node[r].commitUpTo < NumCommands
  /\ node[r].insts[node[r].commitUpTo + 1].status = "Accepting"
  /\ LET s == node[r].commitUpTo + 1
         c == node[r].insts[s].cmd
     IN
       \E m \in msgs :
         /\ m.type = "CommitNotice"
         /\ m.upto = s
         \* marks this slot as committed and apply command
         /\ node' = [node EXCEPT ![r] =
              [@ EXCEPT !.insts = [@ EXCEPT ![s] = [@ EXCEPT !.status = "Committed"]],
                        !.commitUpTo = s,
                        !.kvalue = IF c \in Writes THEN c ELSE @]]
         /\ UNCHANGED <<msgs, pending, observed>>

\* Replica server node main loop.
rloop(self) ==
  /\ pc[self] = "rloop"
  /\ ~ terminated
  /\ \/ BecomeLeader(self)
     \/ HandlePrepare(self)
     \/ HandlePrepareReplies(self)
     \/ TakeNewRequest(self)
     \/ HandleAccept(self)
     \/ HandleAcceptReplies(self)
     \/ HandleCommitNotice(self)
  /\ pc' = [pc EXCEPT ![self] = "rloop"]

Replica(self) == rloop(self)

\* Allow infinite stuttering to prevent deadlock on termination.
Terminating ==
  /\ \A self \in ProcSet : pc[self] = "Done" \/ terminated
  /\ UNCHANGED vars

Next ==
  \/ (\E self \in Replicas : Replica(self))
  \/ Terminating

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

(* needed for MultiPaxos_MC linearizability checking *)
log == [r \in Replicas |-> [s \in Slots |->
          IF node[r].insts[s].status = "Committed" THEN node[r].insts[s].cmd
          ELSE NullCmd]]

====
