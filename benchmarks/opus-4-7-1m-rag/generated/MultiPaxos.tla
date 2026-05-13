---- MODULE MultiPaxos ----
\* MultiPaxos in state-machine-replication style with write/read commands
\* on a single key. Network is modeled as a monotonic set of sent messages.
\* Linearizability is checked over the sequence of client-observed events.

EXTENDS Integers, Sequences, FiniteSets, TLC

\* Model inputs & assumptions.
CONSTANTS Replicas, Writes, Reads, MaxBallot

ASSUME IsFiniteSet(Replicas) /\ Replicas # {}
ASSUME IsFiniteSet(Writes)
ASSUME IsFiniteSet(Reads)
ASSUME MaxBallot \in Nat /\ MaxBallot >= 1

\* Useful constants & typedefs.
Commands == Writes \cup Reads
NumCommands == Cardinality(Commands)
Ballots == 1..MaxBallot
Slots == 1..NumCommands
MajorityNum == (Cardinality(Replicas) \div 2) + 1

NullNode == [leader |-> "none",
             balPrepared |-> 0,
             balMaxKnown |-> 0,
             commitUpTo |-> 0,
             kvalue |-> "nil",
             insts |-> [s \in Slots |-> [status |-> "Empty",
                                          cmd |-> "nil",
                                          voted |-> [bal |-> 0, cmd |-> "nil"]]]]

\* Client observable events. val is the old value for a write command.
ReqEvent(c) == [type |-> "Req", cmd |-> c]
AckEvent(c, v) == [type |-> "Ack", cmd |-> c, val |-> v]

\* W.l.o.g., a fixed concatenation of writes followed by reads.
\* Other orderings are symmetric or less informative.
InitPending ==
    LET wseq == CHOOSE s \in [1..Cardinality(Writes) -> Writes] :
                  \A i, j \in 1..Cardinality(Writes) : i # j => s[i] # s[j]
        rseq == CHOOSE s \in [1..Cardinality(Reads) -> Reads] :
                  \A i, j \in 1..Cardinality(Reads) : i # j => s[i] # s[j]
    IN  [i \in 1..NumCommands |->
           IF i <= Cardinality(Writes) THEN wseq[i]
                                       ELSE rseq[i - Cardinality(Writes)]]

\* Service-internal messages.
PrepareMsg(src, bal) == [type |-> "Prepare", src |-> src, bal |-> bal]
PrepareReplyMsg(src, bal, votes) ==
    [type |-> "PrepareReply", src |-> src, bal |-> bal, votes |-> votes]
AcceptMsg(src, bal, slot, cmd) ==
    [type |-> "Accept", src |-> src, bal |-> bal, slot |-> slot, cmd |-> cmd]
AcceptReplyMsg(src, bal, slot) ==
    [type |-> "AcceptReply", src |-> src, bal |-> bal, slot |-> slot]
CommitNoticeMsg(upto) == [type |-> "CommitNotice", upto |-> upto]

VotesByNode(n) == [s \in Slots |-> n.insts[s].voted]

PeakVotedCmd(prs, s) ==
    LET highest == CHOOSE pr \in prs :
                     \A other \in prs : other.votes[s].bal <= pr.votes[s].bal
    IN  highest.votes[s].cmd

FirstEmptySlot(insts) ==
    CHOOSE s \in Slots :
        /\ insts[s].status = "Empty"
        /\ \A t \in Slots : t < s => insts[t].status # "Empty"

VARIABLES
    msgs,     \* messages in the network
    node,     \* replica node state
    pending,  \* sequence of pending reqs
    observed  \* client observed events

vars == <<msgs, node, pending, observed>>

\* define statement
Range(seq) == {seq[i] : i \in DOMAIN seq}

UnseenPending(insts) ==
    LET filter(c) == c \notin {insts[s].cmd : s \in Slots}
    IN  SelectSeq(pending, LAMBDA c : filter(c))

RemovePending(cmd) ==
    LET filter(c) == c # cmd
    IN  SelectSeq(pending, LAMBDA c : filter(c))

reqsMade == {e.cmd : e \in {e \in Range(observed) : e.type = "Req"}}
acksRecv == {e.cmd : e \in {e \in Range(observed) : e.type = "Ack"}}

terminated ==
    /\ Len(pending) = 0
    /\ Cardinality(reqsMade) = NumCommands
    /\ Cardinality(acksRecv) = NumCommands

\* Global variables initial values
Init ==
    /\ msgs = {}
    /\ node = [r \in Replicas |-> NullNode]
    /\ pending = InitPending
    /\ observed = <<>>

Send(set) == msgs' = msgs \cup set

ObserveSeq(o, e) == IF e \in Range(o) THEN o ELSE Append(o, e)

\* Someone steps up as leader and sends Prepare message to followers.
BecomeLeader(r) ==
    /\ node[r].leader # r
    /\ \E b \in Ballots :
        /\ b > node[r].balMaxKnown
        /\ ~ \E m \in msgs : m.type = "Prepare" /\ m.bal = b
        /\ node' = [node EXCEPT
              ![r].leader = r,
              ![r].balPrepared = 0,
              ![r].balMaxKnown = b,
              ![r].insts = [s \in Slots |->
                              [@ [s] EXCEPT
                                 !.status = IF @ = "Accepting"
                                            THEN "Preparing" ELSE @]]]
        /\ Send({PrepareMsg(r, b),
                 PrepareReplyMsg(r, b, VotesByNode(node[r]))})
    /\ UNCHANGED <<pending, observed>>

\* Replica replies to a Prepare message.
HandlePrepare(r) ==
    /\ \E m \in msgs :
        /\ m.type = "Prepare"
        /\ m.bal > node[r].balMaxKnown
        /\ node' = [node EXCEPT
              ![r].leader = m.src,
              ![r].balMaxKnown = m.bal,
              ![r].insts = [s \in Slots |->
                              [@ [s] EXCEPT
                                 !.status = IF @ = "Accepting"
                                            THEN "Preparing" ELSE @]]]
        /\ Send({PrepareReplyMsg(r, m.bal, VotesByNode(node[r]))})
    /\ UNCHANGED <<pending, observed>>

\* Leader gathers PrepareReply messages, marks ballot prepared, recovers
\* highest voted command per slot.
HandlePrepareReplies(r) ==
    /\ node[r].leader = r
    /\ node[r].balPrepared = 0
    /\ LET prs == {m \in msgs : m.type = "PrepareReply"
                                /\ m.bal = node[r].balMaxKnown}
       IN  /\ Cardinality(prs) >= MajorityNum
           /\ node' = [node EXCEPT
                 ![r].balPrepared = node[r].balMaxKnown,
                 ![r].insts = [s \in Slots |->
                                 [@ [s] EXCEPT
                                    !.status =
                                      IF \/ @ = "Preparing"
                                         \/ (@ = "Empty"
                                             /\ PeakVotedCmd(prs, s) # "nil")
                                      THEN "Accepting" ELSE @,
                                    !.cmd = PeakVotedCmd(prs, s)]]]
           /\ Send({AcceptMsg(r, node[r].balPrepared, s, node[r].insts[s].cmd)
                    : s \in {s \in Slots : node[r].insts[s].status = "Accepting"}})
    /\ UNCHANGED <<pending, observed>>

\* A prepared leader takes a new request to fill the next empty slot.
TakeNewRequest(r) ==
    /\ node[r].leader = r
    /\ node[r].balPrepared = node[r].balMaxKnown
    /\ \E s \in Slots : node[r].insts[s].status = "Empty"
    /\ Len(UnseenPending(node[r].insts)) > 0
    /\ LET s == FirstEmptySlot(node[r].insts)
           c == Head(UnseenPending(node[r].insts))
       IN  /\ node' = [node EXCEPT
                 ![r].insts[s].status = "Accepting",
                 ![r].insts[s].cmd = c,
                 ![r].insts[s].voted.bal = node[r].balPrepared,
                 ![r].insts[s].voted.cmd = c]
           /\ Send({AcceptMsg(r, node[r].balPrepared, s, c),
                    AcceptReplyMsg(r, node[r].balPrepared, s)})
           /\ observed' = ObserveSeq(observed, ReqEvent(c))
    /\ UNCHANGED pending

\* Replica replies to an Accept message.
HandleAccept(r) ==
    /\ \E m \in msgs :
        /\ m.type = "Accept"
        /\ m.bal >= node[r].balMaxKnown
        /\ m.bal > node[r].insts[m.slot].voted.bal
        /\ node' = [node EXCEPT
              ![r].leader = m.src,
              ![r].balMaxKnown = m.bal,
              ![r].insts[m.slot].status = "Accepting",
              ![r].insts[m.slot].cmd = m.cmd,
              ![r].insts[m.slot].voted.bal = m.bal,
              ![r].insts[m.slot].voted.cmd = m.cmd]
        /\ Send({AcceptReplyMsg(r, m.bal, m.slot)})
    /\ UNCHANGED <<pending, observed>>

\* Leader collects AcceptReplies, commits slot, acknowledges client.
HandleAcceptReplies(r) ==
    /\ node[r].leader = r
    /\ node[r].balPrepared = node[r].balMaxKnown
    /\ node[r].commitUpTo < NumCommands
    /\ node[r].insts[node[r].commitUpTo + 1].status = "Accepting"
    /\ LET s == node[r].commitUpTo + 1
           c == node[r].insts[s].cmd
           v == node[r].kvalue
           ars == {m \in msgs : m.type = "AcceptReply"
                                /\ m.slot = s
                                /\ m.bal = node[r].balPrepared}
       IN  /\ Cardinality(ars) >= MajorityNum
           /\ node' = [node EXCEPT
                 ![r].insts[s].status = "Committed",
                 ![r].commitUpTo = s,
                 ![r].kvalue = IF c \in Writes THEN c ELSE @]
           /\ observed' = ObserveSeq(observed, AckEvent(c, v))
           /\ pending' = RemovePending(c)
           /\ Send({CommitNoticeMsg(s)})

\* Follower receives a new commit notification.
HandleCommitNotice(r) ==
    /\ node[r].leader # r
    /\ node[r].commitUpTo < NumCommands
    /\ node[r].insts[node[r].commitUpTo + 1].status = "Accepting"
    /\ \E m \in msgs :
        /\ m.type = "CommitNotice"
        /\ m.upto = node[r].commitUpTo + 1
        /\ LET s == node[r].commitUpTo + 1
               c == node[r].insts[s].cmd
           IN  node' = [node EXCEPT
                 ![r].insts[s].status = "Committed",
                 ![r].commitUpTo = s,
                 ![r].kvalue = IF c \in Writes THEN c ELSE @]
    /\ UNCHANGED <<msgs, pending, observed>>

\* Replica server node main loop.
ReplicaStep(r) ==
    \/ BecomeLeader(r)
    \/ HandlePrepare(r)
    \/ HandlePrepareReplies(r)
    \/ TakeNewRequest(r)
    \/ HandleAccept(r)
    \/ HandleAcceptReplies(r)
    \/ HandleCommitNotice(r)

Next == \/ \E r \in Replicas : ~ terminated /\ ReplicaStep(r)
        \* Allow infinite stuttering to prevent deadlock on termination.
        \/ (terminated /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

\* Type-correctness.
TypeOK ==
    /\ msgs \subseteq UNION {[type : {"Prepare"}, src : Replicas, bal : Ballots],
                              [type : {"Accept"}, src : Replicas,
                               bal : Ballots, slot : Slots, cmd : Commands],
                              [type : {"AcceptReply"}, src : Replicas,
                               bal : Ballots, slot : Slots],
                              [type : {"CommitNotice"}, upto : Slots]}
    /\ pending \in Seq(Commands)
    /\ observed \in Seq(UNION
         {[type : {"Req"}, cmd : Commands],
          [type : {"Ack"}, cmd : Commands, val : Writes \cup {"nil"}]})

\* Linearizability: the observed Ack sequence is a linearization of Req.
Linearizability ==
    \A i, j \in 1..Len(observed) :
        (observed[i].type = "Ack" /\ observed[j].type = "Ack" /\ i < j)
        => observed[i].cmd # observed[j].cmd

====
