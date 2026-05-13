---- MODULE MultiPaxos ----
(***************************************************************************)
(* MultiPaxos in state-machine-replication (SMR) style with write/read    *)
(* commands on a single key. Network is modeled as a monotonic set of     *)
(* sent messages: messages may be arbitrarily delayed, duplicated, or     *)
(* lost (in which case the sender retries). Linearizability is checked   *)
(* over the sequence of client-observed Req/Ack events.                   *)
(*                                                                         *)
(* This is a translation of the PlusCal algorithm to plain TLA+.          *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Replicas,    \* symmetric set of server nodes
    Writes,      \* symmetric set of write commands (each w/ unique value)
    Reads,       \* symmetric set of read commands
    MaxBallot    \* maximum ballot pickable for leader preemption

Commands == Writes \cup Reads
NumCommands == Cardinality(Commands)
MajorityNum == (Cardinality(Replicas) \div 2) + 1
Slots == 1..NumCommands
Ballots == 1..MaxBallot
Statuses == {"Empty", "Preparing", "Accepting", "Committed"}

NullNode ==
    [leader        |-> CHOOSE r : r \notin Replicas,
     balPrepared   |-> 0,
     balMaxKnown   |-> 0,
     commitUpTo    |-> 0,
     kvalue        |-> "nil",
     insts         |-> [s \in Slots |->
                          [status |-> "Empty",
                           cmd    |-> "nil",
                           voted  |-> [bal |-> 0, cmd |-> "nil"]]]]

\* W.L.O.G., choose any sequence concatenating writes then reads.
InitPending ==
    LET ws == CHOOSE seq \in [1..Cardinality(Writes) -> Writes] :
                \A i, j \in 1..Cardinality(Writes) : i /= j => seq[i] /= seq[j]
        rs == CHOOSE seq \in [1..Cardinality(Reads) -> Reads] :
                \A i, j \in 1..Cardinality(Reads) : i /= j => seq[i] /= seq[j]
    IN  ws \o rs

\* Client observable events.
ReqEvent(c) == [type |-> "Req", cmd |-> c]
AckEvent(c, val) == [type |-> "Ack", cmd |-> c, val |-> val]

\* Service-internal messages.
PrepareMsg(r, b)            == [type |-> "Prepare",      src |-> r, bal |-> b]
PrepareReplyMsg(r, b, votes) == [type |-> "PrepareReply", src |-> r, bal |-> b, votes |-> votes]
AcceptMsg(r, b, s, c)       == [type |-> "Accept",       src |-> r, bal |-> b, slot |-> s, cmd |-> c]
AcceptReplyMsg(r, b, s)     == [type |-> "AcceptReply",  src |-> r, bal |-> b, slot |-> s]
CommitNoticeMsg(s)          == [type |-> "CommitNotice", upto |-> s]

VARIABLES msgs,      \* messages in the network
          node,      \* replica node state
          pending,   \* sequence of pending reqs
          observed   \* client observed events

vars == <<msgs, node, pending, observed>>

\* The set of (slot, ballot, cmd) votes a node has cast.
VotesByNode(n) == [s \in Slots |-> n.insts[s].voted]

\* For a slot, the highest-ballot voted command across a set of PrepareReply msgs.
PeakVotedCmd(prs, s) ==
    LET cands == { m.votes[s] : m \in prs }
        nonNil == { v \in cands : v.cmd /= "nil" }
    IN  IF nonNil = {} THEN "nil"
        ELSE (CHOOSE v \in nonNil : \A w \in nonNil : v.bal >= w.bal).cmd

\* SelectSeq: filter a sequence keeping elements satisfying P.
RECURSIVE SelectSeq(_, _)
SelectSeq(s, P(_)) ==
    IF s = << >> THEN << >>
    ELSE IF P(Head(s)) THEN <<Head(s)>> \o SelectSeq(Tail(s), P)
         ELSE SelectSeq(Tail(s), P)

UnseenPending(insts) ==
    LET filter(c) == \A s \in Slots : insts[s].cmd /= c
    IN  SelectSeq(pending, filter)

RemovePending(cmd) ==
    LET filter(c) == c /= cmd
    IN  SelectSeq(pending, filter)

FirstEmptySlot(insts) ==
    CHOOSE s \in Slots : insts[s].status = "Empty"

Range(f) == { f[i] : i \in DOMAIN f }

reqsMade == { e.cmd : e \in { e \in Range(observed) : e.type = "Req" } }
acksRecv == { e.cmd : e \in { e \in Range(observed) : e.type = "Ack" } }

terminated ==
    /\ Len(pending) = 0
    /\ Cardinality(reqsMade) = NumCommands
    /\ Cardinality(acksRecv) = NumCommands

\* Send helper.
Send(set) == msgs' = msgs \cup set

\* Observe helper.
Observe(e) ==
    IF \E i \in DOMAIN observed : observed[i] = e
    THEN observed' = observed
    ELSE observed' = Append(observed, e)

\* Resolve helper.
Resolve(c) == pending' = RemovePending(c)

TypeOK ==
    /\ msgs \subseteq (
            [type : {"Prepare"}, src : Replicas, bal : Ballots]
          \cup [type : {"PrepareReply"}, src : Replicas, bal : Ballots,
                votes : [Slots -> [bal : 0..MaxBallot, cmd : Commands \cup {"nil"}]]]
          \cup [type : {"Accept"}, src : Replicas, bal : Ballots, slot : Slots, cmd : Commands]
          \cup [type : {"AcceptReply"}, src : Replicas, bal : Ballots, slot : Slots]
          \cup [type : {"CommitNotice"}, upto : Slots])
    /\ node \in [Replicas -> [
            leader        : Replicas \cup {NullNode.leader},
            balPrepared   : 0..MaxBallot,
            balMaxKnown   : 0..MaxBallot,
            commitUpTo    : 0..NumCommands,
            kvalue        : Writes \cup {"nil"},
            insts         : [Slots -> [
                                status : Statuses,
                                cmd    : Commands \cup {"nil"},
                                voted  : [bal : 0..MaxBallot, cmd : Commands \cup {"nil"}]]]]]
    /\ observed \in Seq([type : {"Req"}, cmd : Commands]
                          \cup [type : {"Ack"}, cmd : Commands, val : Writes \cup {"nil"}])

Init ==
    /\ msgs = {}
    /\ node = [r \in Replicas |-> NullNode]
    /\ pending = InitPending
    /\ observed = << >>

\* Someone steps up as leader and sends Prepare.
BecomeLeader(r) ==
    /\ node[r].leader /= r
    /\ \E b \in Ballots :
         /\ b > node[r].balMaxKnown
         /\ ~\E m \in msgs : m.type = "Prepare" /\ m.bal = b
         /\ LET nn == [node[r] EXCEPT
                          !.leader = r,
                          !.balPrepared = 0,
                          !.balMaxKnown = b,
                          !.insts = [s \in Slots |->
                                       [node[r].insts[s] EXCEPT
                                          !.status = IF @ = "Accepting" THEN "Preparing" ELSE @]]]
            IN  /\ node' = [node EXCEPT ![r] = nn]
                /\ Send({PrepareMsg(r, b), PrepareReplyMsg(r, b, VotesByNode(nn))})
    /\ UNCHANGED <<pending, observed>>

\* Replica replies to a Prepare message.
HandlePrepare(r) ==
    /\ \E m \in msgs :
         /\ m.type = "Prepare"
         /\ m.bal > node[r].balMaxKnown
         /\ LET nn == [node[r] EXCEPT
                          !.leader = m.src,
                          !.balMaxKnown = m.bal,
                          !.insts = [s \in Slots |->
                                       [node[r].insts[s] EXCEPT
                                          !.status = IF @ = "Accepting" THEN "Preparing" ELSE @]]]
            IN  /\ node' = [node EXCEPT ![r] = nn]
                /\ Send({PrepareReplyMsg(r, m.bal, VotesByNode(nn))})
    /\ UNCHANGED <<pending, observed>>

\* Leader gathers PrepareReply messages.
HandlePrepareReplies(r) ==
    /\ node[r].leader = r
    /\ node[r].balPrepared = 0
    /\ LET prs == { m \in msgs : m.type = "PrepareReply" /\ m.bal = node[r].balMaxKnown }
       IN  /\ Cardinality(prs) >= MajorityNum
           /\ LET nn == [node[r] EXCEPT
                          !.balPrepared = node[r].balMaxKnown,
                          !.insts = [s \in Slots |->
                                       [node[r].insts[s] EXCEPT
                                          !.status =
                                              IF @ = "Preparing"
                                                 \/ (@ = "Empty" /\ PeakVotedCmd(prs, s) /= "nil")
                                              THEN "Accepting" ELSE @,
                                          !.cmd = PeakVotedCmd(prs, s)]]]
              IN  /\ node' = [node EXCEPT ![r] = nn]
                  /\ Send({ AcceptMsg(r, node[r].balMaxKnown, s, nn.insts[s].cmd)
                              : s \in { s \in Slots : nn.insts[s].status = "Accepting" } })
    /\ UNCHANGED <<pending, observed>>

\* A prepared leader takes a new request.
TakeNewRequest(r) ==
    /\ node[r].leader = r
    /\ node[r].balPrepared = node[r].balMaxKnown
    /\ \E s \in Slots : node[r].insts[s].status = "Empty"
    /\ Len(UnseenPending(node[r].insts)) > 0
    /\ LET s == FirstEmptySlot(node[r].insts)
           c == Head(UnseenPending(node[r].insts))
           nn == [node[r] EXCEPT
                     !.insts[s] = [@ EXCEPT
                                      !.status = "Accepting",
                                      !.cmd = c,
                                      !.voted = [bal |-> node[r].balPrepared, cmd |-> c]]]
       IN  /\ node' = [node EXCEPT ![r] = nn]
           /\ Send({AcceptMsg(r, node[r].balPrepared, s, c),
                    AcceptReplyMsg(r, node[r].balPrepared, s)})
           /\ Observe(ReqEvent(c))
    /\ UNCHANGED pending

\* Replica replies to an Accept message.
HandleAccept(r) ==
    /\ \E m \in msgs :
         /\ m.type = "Accept"
         /\ m.bal >= node[r].balMaxKnown
         /\ m.bal > node[r].insts[m.slot].voted.bal
         /\ LET nn == [node[r] EXCEPT
                          !.leader = m.src,
                          !.balMaxKnown = m.bal,
                          !.insts[m.slot] = [@ EXCEPT
                                                !.status = "Accepting",
                                                !.cmd = m.cmd,
                                                !.voted = [bal |-> m.bal, cmd |-> m.cmd]]]
            IN  /\ node' = [node EXCEPT ![r] = nn]
                /\ Send({AcceptReplyMsg(r, m.bal, m.slot)})
    /\ UNCHANGED <<pending, observed>>

\* Leader gathers AcceptReply for a slot.
HandleAcceptReplies(r) ==
    /\ node[r].leader = r
    /\ node[r].balPrepared = node[r].balMaxKnown
    /\ node[r].commitUpTo < NumCommands
    /\ node[r].insts[node[r].commitUpTo + 1].status = "Accepting"
    /\ LET s == node[r].commitUpTo + 1
           c == node[r].insts[s].cmd
           v == node[r].kvalue
           ars == { m \in msgs : m.type = "AcceptReply" /\ m.slot = s /\ m.bal = node[r].balPrepared }
       IN  /\ Cardinality(ars) >= MajorityNum
           /\ node' = [node EXCEPT ![r] = [@ EXCEPT
                                              !.insts[s].status = "Committed",
                                              !.commitUpTo = s,
                                              !.kvalue = IF c \in Writes THEN c ELSE @]]
           /\ Observe(AckEvent(c, v))
           /\ Resolve(c)
           /\ Send({CommitNoticeMsg(s)})

\* Replica receives new commit notification.
HandleCommitNotice(r) ==
    /\ node[r].leader /= r
    /\ node[r].commitUpTo < NumCommands
    /\ node[r].insts[node[r].commitUpTo + 1].status = "Accepting"
    /\ LET s == node[r].commitUpTo + 1
           c == node[r].insts[s].cmd
       IN  /\ \E m \in msgs : m.type = "CommitNotice" /\ m.upto = s
           /\ node' = [node EXCEPT ![r] = [@ EXCEPT
                                              !.insts[s].status = "Committed",
                                              !.commitUpTo = s,
                                              !.kvalue = IF c \in Writes THEN c ELSE @]]
    /\ UNCHANGED <<msgs, pending, observed>>

Next ==
    \/ \E r \in Replicas :
        \/ BecomeLeader(r)
        \/ HandlePrepare(r)
        \/ HandlePrepareReplies(r)
        \/ TakeNewRequest(r)
        \/ HandleAccept(r)
        \/ HandleAcceptReplies(r)
        \/ HandleCommitNotice(r)
    \/ /\ terminated   \* Allow infinite stuttering to prevent deadlock on termination.
       /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ \A r \in Replicas : WF_vars(Next)

\* Linearizability: the sequence of Ack events for writes can be totally
\* ordered consistently with the original request order.
Linearizability ==
    \A i, j \in DOMAIN observed :
        (observed[i].type = "Ack" /\ observed[j].type = "Ack" /\ i < j)
        => (observed[i].cmd /= observed[j].cmd)

====
