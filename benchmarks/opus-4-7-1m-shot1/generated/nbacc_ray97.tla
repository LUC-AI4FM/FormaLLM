---- MODULE nbacc_ray97 ----
(***************************************************************************)
(* TLA+ encoding of the algorithm NBAC with crashes in:                    *)
(* [1] Raynal, Michel. "A case study of agreement problems in distributed *)
(* systems: non-blocking atomic commitment."                               *)
(* High-Assurance Systems Engineering Workshop, 1997, Proceedings. IEEE.   *)
(*                                                                         *)
(* Igor Konnov, Thanh Hai Tran, Josef Widder, 2016                         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

Proc == 1..N

PCs == {"PROPOSE", "YES", "NO", "COMMIT", "ABORT", "CRASH"}

VARIABLES
  pc,    \* program counters
  rcvd,  \* messages which are received
  sent,  \* messages which are sent
  fd     \* a failure detector reporting to every process whether some process has crashed

vars == <<pc, rcvd, sent, fd>>

Messages == [type: {"YES", "NO"}, src: Proc]

(***************************************************************************)
(* Type correctness.                                                       *)
(***************************************************************************)
TypeOK ==
  /\ pc \in [Proc -> PCs]
  /\ rcvd \in [Proc -> SUBSET Messages]
  /\ sent \in SUBSET Messages
  /\ fd \in [Proc -> BOOLEAN]

Init ==
  /\ pc = [i \in Proc |-> "PROPOSE"]
  /\ rcvd = [i \in Proc |-> {}]
  /\ sent = {}
  /\ fd \in [Proc -> BOOLEAN]

(***************************************************************************)
(* Receive new messages.                                                   *)
(***************************************************************************)
Receive(self) ==
  /\ \E newMsgs \in SUBSET (sent \ rcvd[self]) :
       rcvd' = [rcvd EXCEPT ![self] = @ \cup newMsgs]
  /\ UNCHANGED <<pc, sent, fd>>

(***************************************************************************)
(* The failure detector sends a nondeterministically new prediction to     *)
(* process self.                                                           *)
(***************************************************************************)
UpdateFD(self) ==
  /\ \E v \in BOOLEAN : fd' = [fd EXCEPT ![self] = v]
  /\ UNCHANGED <<pc, rcvd, sent>>

(***************************************************************************)
(* Process self becomes crashed.                                           *)
(***************************************************************************)
Crash(self) ==
  /\ pc[self] # "CRASH"
  /\ pc' = [pc EXCEPT ![self] = "CRASH"]
  /\ UNCHANGED <<rcvd, sent, fd>>

(***************************************************************************)
(* Sends a YES message.                                                    *)
(***************************************************************************)
SendYes(self) ==
  /\ pc[self] = "PROPOSE"
  /\ pc' = [pc EXCEPT ![self] = "YES"]
  /\ sent' = sent \cup {[type |-> "YES", src |-> self]}
  /\ UNCHANGED <<rcvd, fd>>

(***************************************************************************)
(* Sends a NO message.                                                     *)
(***************************************************************************)
SendNo(self) ==
  /\ pc[self] = "PROPOSE"
  /\ pc' = [pc EXCEPT ![self] = "NO"]
  /\ sent' = sent \cup {[type |-> "NO", src |-> self]}
  /\ UNCHANGED <<rcvd, fd>>

(***************************************************************************)
(* - If process self voted and received a NO message, it aborts.           *)
(* - If process self voted and thinks that some process has crashed,       *)
(*   it aborts.                                                            *)
(* - If process self voted, received only YES from all processes, and      *)
(*   thinks all processes are still correct, it commits.                   *)
(***************************************************************************)
Decide(self) ==
  /\ pc[self] \in {"YES", "NO"}
  /\ \/ /\ \E m \in rcvd[self] : m.type = "NO"
        /\ pc' = [pc EXCEPT ![self] = "ABORT"]
     \/ /\ fd[self] = TRUE
        /\ pc' = [pc EXCEPT ![self] = "ABORT"]
     \/ /\ Cardinality({m \in rcvd[self] : m.type = "YES"}) = N
        /\ fd[self] = FALSE
        /\ pc' = [pc EXCEPT ![self] = "COMMIT"]
  /\ UNCHANGED <<rcvd, sent, fd>>

(***************************************************************************)
(* Do nothing but we need this to avoid deadlock.                          *)
(***************************************************************************)
Stutter(self) ==
  /\ UNCHANGED vars

Step(self) ==
  \/ Receive(self)
  \/ UpdateFD(self)
  \/ Crash(self)
  \/ SendYes(self) \/ SendNo(self)
  \/ Decide(self)

Next == \E self \in Proc : Step(self)

Spec == Init /\ [][Next]_vars /\ \A self \in Proc : WF_vars(Step(self))

(***************************************************************************)
(* Some processes vote YES.  Others vote NO.                               *)
(***************************************************************************)

(***************************************************************************)
(* All processes vote YES.                                                 *)
(***************************************************************************)
NonTriv ==
  /\ \A i \in Proc : pc[i] = "YES"
  /\ [](\A i \in Proc : pc[i] # "CRASH")
  /\ (<>[](\A self \in Proc : fd[self] = FALSE))
  => <>(\A self \in Proc : pc[self] = "COMMIT")

====
