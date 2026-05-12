---- MODULE nbacc_ray97 ----
(***************************************************************************)
(* TLA+ encoding of the algorithm NBAC with crashes in:                    *)
(* [1] Raynal, Michel. "A case study of agreement problems in distributed *)
(* systems: non-blocking atomic commitment." High-Assurance Systems        *)
(* Engineering Workshop, 1997., Proceedings. IEEE, 1997.                  *)
(*                                                                          *)
(* Igor Konnov, Thanh Hai Tran, Josef Widder, 2016                         *)
(* This file is a subject to the license that is bundled together with    *)
(* this package and can be found in the file LICENSE.                     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Proc == 1..N   \* all processes, including the crashed ones
Status == {"NO_VOTE", "YES", "NO", "COMMIT", "ABORT", "CRASH"}

VARIABLES
  pc,        \* program counters
  rcvd,      \* messages which are received
  sent,      \* messages which are sent by
  fd         \* a failure detector reporting to every process
            \* whether some process has crashed

vars == <<pc, rcvd, sent, fd>>

Messages ==
  [type : {"YES", "NO"}, src : Proc]

TypeOK ==
  /\ pc \in [Proc -> Status]
  /\ rcvd \in [Proc -> SUBSET Messages]
  /\ sent \subseteq Messages
  /\ fd \in [Proc -> BOOLEAN]

Init ==
  /\ pc \in [Proc -> {"NO_VOTE"}]
  /\ rcvd = [i \in Proc |-> {}]
  /\ sent = {}
  /\ fd = [i \in Proc |-> FALSE]

(* Receive new messages *)
Receive(self) ==
  /\ pc[self] # "CRASH"
  /\ \E msgs \in SUBSET sent :
       /\ msgs # {}
       /\ rcvd' = [rcvd EXCEPT ![self] = @ \cup msgs]
  /\ UNCHANGED <<pc, sent, fd>>

(* The failure detector sends a nondeterministically new prediction to
   process self. *)
UpdateFD(self) ==
  /\ pc[self] # "CRASH"
  /\ \E b \in BOOLEAN :
       fd' = [fd EXCEPT ![self] = b]
  /\ UNCHANGED <<pc, rcvd, sent>>

(* Process self becomes crash. *)
Crash(self) ==
  /\ pc[self] # "CRASH"
  /\ pc' = [pc EXCEPT ![self] = "CRASH"]
  /\ UNCHANGED <<rcvd, sent, fd>>

(* Sends a YES message *)
VoteYes(self) ==
  /\ pc[self] = "NO_VOTE"
  /\ pc' = [pc EXCEPT ![self] = "YES"]
  /\ sent' = sent \cup {[type |-> "YES", src |-> self]}
  /\ UNCHANGED <<rcvd, fd>>

(* Sends a NO message *)
VoteNo(self) ==
  /\ pc[self] = "NO_VOTE"
  /\ pc' = [pc EXCEPT ![self] = "NO"]
  /\ sent' = sent \cup {[type |-> "NO", src |-> self]}
  /\ UNCHANGED <<rcvd, fd>>

(***************************************************************************)
(* - If process self voted and received a NO message, it aborts.           *)
(* - If process self voted and thinks that some process has crashed, it    *)
(*   aborts.                                                               *)
(* - If process self voted, received only YES messages from all processes, *)
(*   and thinks that all processes are still correct, it commits.          *)
(***************************************************************************)
Decide(self) ==
  /\ pc[self] \in {"YES", "NO"}
  /\ \/ /\ \E m \in rcvd[self] : m.type = "NO"
        /\ pc' = [pc EXCEPT ![self] = "ABORT"]
     \/ /\ fd[self] = TRUE
        /\ pc' = [pc EXCEPT ![self] = "ABORT"]
     \/ /\ \A p \in Proc : \E m \in rcvd[self] : m.type = "YES" /\ m.src = p
        /\ fd[self] = FALSE
        /\ pc' = [pc EXCEPT ![self] = "COMMIT"]
  /\ UNCHANGED <<rcvd, sent, fd>>

(* Do nothing but we need this to avoid deadlock *)
Idle(self) ==
  /\ pc[self] # "CRASH"
  /\ UNCHANGED vars

Next ==
  \E self \in Proc :
    \/ Receive(self) \/ UpdateFD(self) \/ Crash(self)
    \/ VoteYes(self) \/ VoteNo(self) \/ Decide(self) \/ Idle(self)

Spec ==
  /\ Init
  /\ [][Next]_vars
  (* Add the weak fainress condition *)
  /\ \A self \in Proc : WF_vars(Receive(self) \/ Decide(self))

(* Some processes vote YES. Others vote NO. *)
SomeYesSomeNo ==
  /\ \E i \in Proc : pc[i] = "YES"
  /\ \E i \in Proc : pc[i] = "NO"

(* All processes vote YES. *)
AllYes == \A i \in Proc : pc[i] = "YES"

(*
NonTriv ==
  (   /\ \A i \in Proc : pc[i] = "YES"
      /\ [](\A i \in Proc : pc[i] # "CRASH")
      /\ (<>[](\A self \in Proc : (fd[self] = FALSE)))
   => <>(\A self \in Proc : (pc[self] = "COMMIT"))
*)
NonTriv ==
  (   /\ AllYes
      /\ []( \A i \in Proc : pc[i] # "CRASH" )
      /\ <>[]( \A self \in Proc : fd[self] = FALSE ))
  => <>( \A self \in Proc : pc[self] = "COMMIT" )
====
