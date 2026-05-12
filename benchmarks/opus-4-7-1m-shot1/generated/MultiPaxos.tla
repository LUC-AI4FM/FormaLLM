---- MODULE MultiPaxos ----
(***************************************************************************)
(* MultiPaxos in state machine replication (SMR) style with write/read     *)
(* commands on a single key.  Please refer to the detailed comments in     *)
(* PlusCal code to see how this spec closely models a practical SMR log    *)
(* replication system.                                                     *)
(*                                                                         *)
(* Network is modeled as a monotonic set of sent messages.                 *)
(* Linearizability is checked from global client's point of view.          *)
(* Liveness is checked by not having deadlocks till observation of all     *)
(* requests.                                                               *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* Model inputs & assumptions.                                             *)
(***************************************************************************)
CONSTANTS
  Replicas,    \* symmetric set of server nodes
  Writes,      \* symmetric set of write commands (each w/ unique value)
  Reads,       \* symmetric set of read commands
  MaxBallot    \* maximum ballot pickable for leader preemption

(***************************************************************************)
(* Useful constants & typedefs.                                            *)
(***************************************************************************)
Commands == Writes \cup Reads
NumCommands == Cardinality(Commands)
Slots == 1..NumCommands
Ballots == 1..MaxBallot
MajorityNum == (Cardinality(Replicas) \div 2) + 1
NullNode == [leader |-> "none",
             balPrepared |-> 0,
             balMaxKnown |-> 0,
             commitUpTo |-> 0,
             kvalue |-> "nil",
             insts |-> [s \in Slots |-> [status |-> "Empty",
                                         cmd    |-> "nil",
                                         voted  |-> [bal |-> 0, cmd |-> "nil"]]]]

InitPending ==
  LET ws == SetToSeq(Writes)
      rs == SetToSeq(Reads)
  IN ws \o rs

SetToSeq(S) == CHOOSE seq \in [1..Cardinality(S) -> S] :
                 \A i, j \in 1..Cardinality(S) : i # j => seq[i] # seq[j]

(***************************************************************************)
(* Client observable events.                                               *)
(***************************************************************************)
ReqEvent(c) == [type |-> "Req", cmd |-> c]
AckEvent(c, v) == [type |-> "Ack", cmd |-> c, val |-> v]

(***************************************************************************)
(* Service-internal messages.                                              *)
(***************************************************************************)
PrepareMsg(src, bal) == [type |-> "Prepare", src |-> src, bal |-> bal]
PrepareReplyMsg(src, bal, votes) ==
  [type |-> "PrepareReply", src |-> src, bal |-> bal, votes |-> votes]
AcceptMsg(src, bal, slot, cmd) ==
  [type |-> "Accept", src |-> src, bal |-> bal, slot |-> slot, cmd |-> cmd]
AcceptReplyMsg(src, bal, slot) ==
  [type |-> "AcceptReply", src |-> src, bal |-> bal, slot |-> slot]
CommitNoticeMsg(upto) == [type |-> "CommitNotice", upto |-> upto]

VotesByNode(nd) == [s \in Slots |-> nd.insts[s].voted]

PeakVotedCmd(prs, s) ==
  LET highestBal == CHOOSE b \in {pr.votes[s].bal : pr \in prs} :
                      \A pr \in prs : pr.votes[s].bal \leq b
      cands == { pr.votes[s].cmd : pr \in {p \in prs : p.votes[s].bal = highestBal} }
  IN IF highestBal = 0 THEN "nil" ELSE CHOOSE c \in cands : TRUE

FirstEmptySlot(insts) ==
  CHOOSE s \in Slots : insts[s].status = "Empty"
    /\ \A t \in Slots : t < s => insts[t].status # "Empty"

(***************************************************************************)
(* Global variables.                                                       *)
(***************************************************************************)
VARIABLES msgs, node, pending, observed, pc

vars == << msgs, node, pending, observed, pc >>

UnseenPending(insts) ==
  LET filter(c) == c \notin {insts[s].cmd : s \in Slots}
  IN SelectSeq(pending, filter)

RemovePending(cmd) ==
  LET filter(c) == c # cmd
  IN SelectSeq(pending, filter)

Range(seq) == { seq[i] : i \in 1..Len(seq) }

reqsMade == { e.cmd : e \in { e \in Range(observed) : e.type = "Req" } }
acksRecv == { e.cmd : e \in { e \in Range(observed) : e.type = "Ack" } }

terminated == /\ Len(pending) = 0
              /\ Cardinality(reqsMade) = NumCommands
              /\ Cardinality(acksRecv) = NumCommands

(***************************************************************************)
(* Initial state.                                                          *)
(***************************************************************************)
Init ==
  /\ msgs = {}
  /\ node = [r \in Replicas |-> NullNode]
  /\ pending = InitPending
  /\ observed = << >>
  /\ pc = [r \in Replicas |-> "rloop"]

BecomeLeader(r) ==
  /\ pc[r] = "rloop"
  /\ node[r].leader # r
  /\ \E b \in Ballots :
       /\ b > node[r].balMaxKnown
       /\ ~ \E m \in msgs : m.type = "Prepare" /\ m.bal = b
       /\ node' = [node EXCEPT ![r].leader = r,
                               ![r].balPrepared = 0,
                               ![r].balMaxKnown = b]
       /\ msgs' = msgs \cup { PrepareMsg(r, b),
                              PrepareReplyMsg(r, b, VotesByNode(node[r])) }
  /\ UNCHANGED <<pending, observed, pc>>

Next == \E r \in Replicas : BecomeLeader(r)

(***************************************************************************)
(* Allow infinite stuttering to prevent deadlock on termination.           *)
(***************************************************************************)
Spec == Init /\ [][Next \/ (terminated /\ UNCHANGED vars)]_vars

====
