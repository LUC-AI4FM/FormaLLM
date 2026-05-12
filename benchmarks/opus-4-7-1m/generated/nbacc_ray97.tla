---- MODULE nbacc_ray97 ----
(***************************************************************************)
(* TLA+ encoding of the Non-Blocking Atomic Commit (NBAC) algorithm with  *)
(* crashes, from:                                                          *)
(*   Raynal, Michel. "A case study of agreement problems in distributed   *)
(*   systems: non-blocking atomic commitment." High-Assurance Systems     *)
(*   Engineering Workshop, IEEE, 1997.                                    *)
(*                                                                         *)
(* Igor Konnov, Thanh Hai Tran, Josef Widder, 2016.                       *)
(*                                                                         *)
(* Modification History                                                    *)
(*   Last modified Mon Jul 09 13:26:03 CEST 2018 by tthai                  *)
(*   Created      Thu Mar 12 00:46:19 CET 2015 by igor                     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N

ASSUME N \in Nat /\ N > 0

\* All processes, including the crashed ones.
Proc == 1..N

VARIABLES
    pc,    \* program counters
    rcv,   \* messages which are received
    snt,   \* messages which are sent
    fd     \* failure detector reporting to each process whether some
           \* process has crashed

vars == <<pc, rcv, snt, fd>>

States == {"INIT", "YES", "NO", "COMMIT", "ABORT", "CRASH"}

TypeOK ==
    /\ pc \in [Proc -> States]
    /\ rcv \in [Proc -> SUBSET ([from : Proc, type : {"YES", "NO"}])]
    /\ snt \in [Proc -> SUBSET ([from : Proc, type : {"YES", "NO"}])]
    /\ fd \in [Proc -> BOOLEAN]

Init ==
    /\ pc = [i \in Proc |-> "INIT"]
    /\ rcv = [i \in Proc |-> {}]
    /\ snt = [i \in Proc |-> {}]
    /\ fd = [i \in Proc |-> FALSE]

\* Receive new messages.
Receive(self) ==
    /\ pc[self] /= "CRASH"
    /\ \E S \in SUBSET (UNION { snt[j] : j \in Proc }) :
         /\ S /= {}
         /\ rcv' = [rcv EXCEPT ![self] = @ \cup S]
    /\ UNCHANGED <<pc, snt, fd>>

\* The failure detector nondeterministically updates its prediction.
FDUpdate(self) ==
    /\ pc[self] /= "CRASH"
    /\ \E b \in BOOLEAN : fd' = [fd EXCEPT ![self] = b]
    /\ UNCHANGED <<pc, rcv, snt>>

\* Process self crashes.
Crash(self) ==
    /\ pc[self] /= "CRASH"
    /\ pc' = [pc EXCEPT ![self] = "CRASH"]
    /\ UNCHANGED <<rcv, snt, fd>>

\* Sends a YES message.
VoteYes(self) ==
    /\ pc[self] = "INIT"
    /\ pc' = [pc EXCEPT ![self] = "YES"]
    /\ snt' = [snt EXCEPT ![self] = @ \cup {[from |-> self, type |-> "YES"]}]
    /\ UNCHANGED <<rcv, fd>>

\* Sends a NO message.
VoteNo(self) ==
    /\ pc[self] = "INIT"
    /\ pc' = [pc EXCEPT ![self] = "NO"]
    /\ snt' = [snt EXCEPT ![self] = @ \cup {[from |-> self, type |-> "NO"]}]
    /\ UNCHANGED <<rcv, fd>>

\* If self voted and received a NO, it aborts.
\* If self voted and thinks some process has crashed, it aborts.
\* If self voted, received only YES from all, and FD reports no crash, it commits.
Decide(self) ==
    /\ pc[self] \in {"YES", "NO"}
    /\ \/ /\ \E m \in rcv[self] : m.type = "NO"
          /\ pc' = [pc EXCEPT ![self] = "ABORT"]
       \/ /\ fd[self]
          /\ pc' = [pc EXCEPT ![self] = "ABORT"]
       \/ /\ \A j \in Proc : \E m \in rcv[self] : m.from = j /\ m.type = "YES"
          /\ ~fd[self]
          /\ pc' = [pc EXCEPT ![self] = "COMMIT"]
    /\ UNCHANGED <<rcv, snt, fd>>

\* Do nothing (to avoid deadlock).
Stutter(self) ==
    /\ pc[self] \in {"COMMIT", "ABORT", "CRASH"}
    /\ UNCHANGED vars

Step(self) ==
    \/ Receive(self)
    \/ FDUpdate(self)
    \/ Crash(self)
    \/ VoteYes(self)
    \/ VoteNo(self)
    \/ Decide(self)
    \/ Stutter(self)

Next == \E self \in Proc : Step(self)

\* Add weak fairness conditions.
Spec == Init /\ [][Next]_vars
            /\ \A self \in Proc :
                WF_vars(VoteYes(self) \/ VoteNo(self) \/ Decide(self) \/ Receive(self))

\*****************************************************************************
\* Liveness / non-triviality property:
\* If all processes vote YES, none crash, and the failure detector eventually
\* always reports FALSE for all processes, then all eventually COMMIT.
\*****************************************************************************
NonTriv ==
    (   /\ \A i \in Proc : pc[i] = "YES"
        /\ [](\A i \in Proc : pc[i] /= "CRASH")
        /\ <>[](\A self \in Proc : (fd[self] = FALSE)))
    => <>(\A self \in Proc : pc[self] = "COMMIT")
====
