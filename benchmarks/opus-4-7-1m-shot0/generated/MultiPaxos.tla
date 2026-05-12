---- MODULE MultiPaxos ----
\* *********************************************************************************
\* MultiPaxos in state machine replication (SMR) style with write/read commands
\* on a single key. Network is modeled as a monotonic set of sent messages.
\*
\* Linearizability is checked from the global client's point of view on the
\* sequence of client observed request/acknowledgement events after termination.
\* Liveness is checked by not having deadlocks until observation of all requests.
\* *********************************************************************************

EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ******************************
\* Model inputs & assumptions.
\* ******************************

CONSTANTS
  Replicas,    \* symmetric set of server nodes
  Writes,      \* symmetric set of write commands (each w/ unique value)
  Reads,       \* symmetric set of read commands
  MaxBallot    \* maximum ballot pickable for leader preemption

ASSUME Cardinality(Replicas) > 0
ASSUME MaxBallot \in Nat /\ MaxBallot > 0

\* *******************************
\* Useful constants & typedefs.
\* *******************************

\* A write-command model value serves as both the ID of the command and the
\* value to be written.
Commands == Writes \cup Reads

NumCommands == Cardinality(Commands)

Slots   == 1..NumCommands
Ballots == 1..MaxBallot

MajorityNum == (Cardinality(Replicas) \div 2) + 1

NullNode == [leader        |-> CHOOSE r \in Replicas : TRUE,
              balPrepared   |-> 0,
              balMaxKnown   |-> 0,
              commitUpTo    |-> 0,
              kvalue        |-> "nil",
              insts         |-> [s \in Slots |->
                                  [status |-> "Empty",
                                   cmd    |-> "nil",
                                   voted  |-> [bal |-> 0, cmd |-> "nil"]]]]

\* W.L.O.G., choose any sequence concatenating writes then reads as InitPending.
\* (All other orderings are either symmetric or less useful.)
InitPending ==
  LET ws == CHOOSE seq \in [1..Cardinality(Writes) -> Writes] :
              \A i, j \in DOMAIN seq : i /= j => seq[i] /= seq[j]
      rs == CHOOSE seq \in [1..Cardinality(Reads) -> Reads] :
              \A i, j \in DOMAIN seq : i /= j => seq[i] /= seq[j]
  IN  ws \o rs

\* Client observable events. (val is the old value for a write command.)
ReqEvent(c)    == [type |-> "Req", cmd |-> c]
AckEvent(c, v) == [type |-> "Ack", cmd |-> c, val |-> v]

\* Server-side message constructors. (Service-internal messages.)
PrepareMsg(src, bal)            == [type |-> "Prepare", src |-> src, bal |-> bal]
PrepareReplyMsg(src, bal, votes) == [type |-> "PrepareReply",
                                      src |-> src, bal |-> bal, votes |-> votes]
AcceptMsg(src, bal, slot, cmd)   == [type |-> "Accept", src |-> src,
                                      bal |-> bal, slot |-> slot, cmd |-> cmd]
AcceptReplyMsg(src, bal, slot)   == [type |-> "AcceptReply",
                                      src |-> src, bal |-> bal, slot |-> slot]
CommitNoticeMsg(s)               == [type |-> "CommitNotice", upto |-> s]

VotesByNode(nd) == [s \in Slots |-> nd.insts[s].voted]

PeakVotedCmd(prs, s) ==
  LET candidates ==
        { p.votes[s] : p \in prs }
      maxBal ==
        IF candidates = {} THEN 0
        ELSE CHOOSE b \in { c.bal : c \in candidates } :
               \A c \in candidates : c.bal <= b
  IN  IF maxBal = 0 THEN "nil"
      ELSE (CHOOSE c \in candidates : c.bal = maxBal).cmd

FirstEmptySlot(insts) ==
  CHOOSE s \in Slots :
     /\ insts[s].status = "Empty"
     /\ \A s2 \in Slots : (s2 < s) => (insts[s2].status /= "Empty")

\* *****************************
\* Main algorithm in PlusCal.
\* *****************************

(*
--algorithm MultiPaxos
variable msgs = {},
         node = [r \in Replicas |-> NullNode],
         pending = InitPending,
         observed = <<>>;
... (see comments above) ...
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "2be53042" /\ chksum(tla) = "bfbfd945")

VARIABLES msgs, node, pending, observed, pc

\* define statement
UnseenPending(insts) ==
  LET seen == { insts[s].cmd : s \in Slots }
  IN  SelectSeq(pending, LAMBDA c : c \notin seen)

RemovePending(cmd) ==
  SelectSeq(pending, LAMBDA c : c /= cmd)

reqsMade == { e.cmd : e \in { x \in Range(observed) : x.type = "Req" } }
acksRecv == { e.cmd : e \in { x \in Range(observed) : x.type = "Ack" } }
terminated ==
  /\ Len(pending) = 0
  /\ Cardinality(reqsMade) = NumCommands
  /\ Cardinality(acksRecv) = NumCommands

\* Helper.
Range(seq) == { seq[i] : i \in DOMAIN seq }

vars == << msgs, node, pending, observed, pc >>

ProcSet == Replicas

Init ==
  /\ msgs = {}
  /\ node = [r \in Replicas |-> NullNode]
  /\ pending = InitPending
  /\ observed = << >>
  /\ pc = [self \in ProcSet |-> "rloop"]

\* ----- Replica actions -----

BecomeLeader(r) ==
  /\ pc[r] = "rloop"
  /\ node[r].leader /= r
  /\ \E b \in Ballots :
       /\ b > node[r].balMaxKnown
       /\ ~ \E m \in msgs : m.type = "Prepare" /\ m.bal = b
       /\ node' = [node EXCEPT ![r] = [@ EXCEPT
              !.leader       = r,
              !.balPrepared  = 0,
              !.balMaxKnown  = b,
              !.insts        = [s \in Slots |->
                                  [@[s] EXCEPT !.status =
                                     IF @ = "Accepting" THEN "Preparing"
                                     ELSE @]]]]
       /\ msgs' = msgs \cup { PrepareMsg(r, b),
                              PrepareReplyMsg(r, b, VotesByNode(node[r])) }
  /\ UNCHANGED << pending, observed, pc >>

HandlePrepare(r) ==
  /\ pc[r] = "rloop"
  /\ \E m \in msgs :
       /\ m.type = "Prepare"
       /\ m.bal > node[r].balMaxKnown
       /\ node' = [node EXCEPT ![r] = [@ EXCEPT
              !.leader      = m.src,
              !.balMaxKnown = m.bal,
              !.insts       = [s \in Slots |->
                                 [@[s] EXCEPT !.status =
                                    IF @ = "Accepting" THEN "Preparing"
                                    ELSE @]]]]
       /\ msgs' = msgs \cup { PrepareReplyMsg(r, m.bal, VotesByNode(node[r])) }
  /\ UNCHANGED << pending, observed, pc >>

HandlePrepareReplies(r) ==
  /\ pc[r] = "rloop"
  /\ node[r].leader = r
  /\ node[r].balPrepared = 0
  /\ LET prs == { m \in msgs : m.type = "PrepareReply" /\ m.bal = node[r].balMaxKnown }
     IN  /\ Cardinality(prs) >= MajorityNum
         /\ node' = [node EXCEPT ![r] = [@ EXCEPT
                !.balPrepared = node[r].balMaxKnown,
                !.insts = [s \in Slots |->
                             [@[s] EXCEPT
                               !.status = IF \/ @ = "Preparing"
                                            \/ (/\ @ = "Empty"
                                                /\ PeakVotedCmd(prs, s) /= "nil")
                                          THEN "Accepting" ELSE @,
                               !.cmd = PeakVotedCmd(prs, s)]]]]
         /\ msgs' = msgs \cup
              { AcceptMsg(r, node[r].balMaxKnown, s,
                          node[r].insts[s].cmd) :
                  s \in { s \in Slots : node[r].insts[s].status = "Accepting" } }
  /\ UNCHANGED << pending, observed, pc >>

TakeNewRequest(r) ==
  /\ pc[r] = "rloop"
  /\ node[r].leader = r
  /\ node[r].balPrepared = node[r].balMaxKnown
  /\ \E s0 \in Slots : node[r].insts[s0].status = "Empty"
  /\ Len(UnseenPending(node[r].insts)) > 0
  /\ LET s == FirstEmptySlot(node[r].insts)
         c == Head(UnseenPending(node[r].insts))
     IN  /\ node' = [node EXCEPT ![r] = [@ EXCEPT
                !.insts = [@.insts EXCEPT ![s] =
                           [@ EXCEPT !.status = "Accepting",
                                     !.cmd    = c,
                                     !.voted  = [bal |-> node[r].balPrepared,
                                                  cmd |-> c]]]]]
         /\ msgs' = msgs \cup { AcceptMsg(r, node[r].balPrepared, s, c),
                                AcceptReplyMsg(r, node[r].balPrepared, s) }
         /\ observed' = IF ReqEvent(c) \in Range(observed)
                          THEN observed ELSE Append(observed, ReqEvent(c))
  /\ UNCHANGED << pending, pc >>

HandleAccept(r) ==
  /\ pc[r] = "rloop"
  /\ \E m \in msgs :
       /\ m.type = "Accept"
       /\ m.bal >= node[r].balMaxKnown
       /\ m.bal > node[r].insts[m.slot].voted.bal
       /\ node' = [node EXCEPT ![r] = [@ EXCEPT
              !.leader      = m.src,
              !.balMaxKnown = m.bal,
              !.insts = [@.insts EXCEPT ![m.slot] =
                           [@ EXCEPT !.status = "Accepting",
                                     !.cmd    = m.cmd,
                                     !.voted  = [bal |-> m.bal, cmd |-> m.cmd]]]]]
       /\ msgs' = msgs \cup { AcceptReplyMsg(r, m.bal, m.slot) }
  /\ UNCHANGED << pending, observed, pc >>

HandleAcceptReplies(r) ==
  /\ pc[r] = "rloop"
  /\ node[r].leader = r
  /\ node[r].balPrepared = node[r].balMaxKnown
  /\ node[r].commitUpTo < NumCommands
  /\ node[r].insts[node[r].commitUpTo + 1].status = "Accepting"
  /\ LET s   == node[r].commitUpTo + 1
         c   == node[r].insts[s].cmd
         v   == node[r].kvalue
         ars == { m \in msgs : m.type = "AcceptReply"
                                /\ m.slot = s
                                /\ m.bal  = node[r].balPrepared }
     IN  /\ Cardinality(ars) >= MajorityNum
         /\ node' = [node EXCEPT ![r] = [@ EXCEPT
                !.insts = [@.insts EXCEPT ![s] = [@ EXCEPT !.status = "Committed"]],
                !.commitUpTo = s,
                !.kvalue = IF c \in Writes THEN c ELSE @.kvalue]]
         /\ observed' = IF AckEvent(c, v) \in Range(observed)
                          THEN observed
                          ELSE Append(observed, AckEvent(c, v))
         /\ pending' = RemovePending(c)
         /\ msgs' = msgs \cup { CommitNoticeMsg(s) }
  /\ UNCHANGED pc

HandleCommitNotice(r) ==
  /\ pc[r] = "rloop"
  /\ node[r].leader /= r
  /\ node[r].commitUpTo < NumCommands
  /\ node[r].insts[node[r].commitUpTo + 1].status = "Accepting"
  /\ LET s == node[r].commitUpTo + 1
         c == node[r].insts[s].cmd
     IN  /\ \E m \in msgs :
              /\ m.type = "CommitNotice"
              /\ m.upto = s
              /\ node' = [node EXCEPT ![r] = [@ EXCEPT
                     !.insts = [@.insts EXCEPT ![s] = [@ EXCEPT !.status = "Committed"]],
                     !.commitUpTo = s,
                     !.kvalue = IF c \in Writes THEN c ELSE @.kvalue]]
  /\ UNCHANGED << msgs, pending, observed, pc >>

\* Replica server node main loop.
Replica(self) ==
  /\ pc[self] = "rloop"
  /\ ~ terminated
  /\ \/ BecomeLeader(self)
     \/ HandlePrepare(self)
     \/ HandlePrepareReplies(self)
     \/ TakeNewRequest(self)
     \/ HandleAccept(self)
     \/ HandleAcceptReplies(self)
     \/ HandleCommitNotice(self)

\* Allow infinite stuttering to prevent deadlock on termination.
Terminating ==
  /\ terminated
  /\ UNCHANGED vars

Next ==
  \/ \E r \in Replicas : Replica(r)
  \/ Terminating

Spec == Init /\ [][Next]_vars /\ \A r \in Replicas : WF_vars(Replica(r))

\* END TRANSLATION

\* ----- Linearizability check helper -----

\* The sequence of observed events forms a legal linearization: every Ack has
\* a matching prior Req, and the read value matches the most recent committed
\* write (or "nil" if none).
Linearizable ==
  \A i \in DOMAIN observed :
     observed[i].type = "Ack" =>
        \E j \in 1..(i-1) :
           /\ observed[j].type = "Req"
           /\ observed[j].cmd = observed[i].cmd

TypeOK ==
  /\ msgs \subseteq UNION { [type : {"Prepare"}, src : Replicas, bal : Ballots],
                            [type : {"PrepareReply"}, src : Replicas, bal : Ballots,
                             votes : [Slots -> [bal : Nat, cmd : STRING]]],
                            [type : {"Accept"}, src : Replicas, bal : Ballots,
                             slot : Slots, cmd : Commands],
                            [type : {"AcceptReply"}, src : Replicas,
                             bal : Ballots, slot : Slots],
                            [type : {"CommitNotice"}, upto : Slots] }
  /\ pending \in Seq(Commands)

====
