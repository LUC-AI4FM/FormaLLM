---- MODULE HDiskSynod ----
(***************************************************************************)
(* Modification History                                                    *)
(* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai                     *)
(* Created Sat Jan 26 15:23:57 CET 2019 by tthai                           *)
(*                                                                         *)
(* /\ (bk.bal = 0) <=> (bk.inp = NotAnInput)                               *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, Inputs, Ballot, Disk

IsMajority(S) == 2 * Cardinality(S) > Cardinality(Disk)

NotAnInput == CHOOSE x : x \notin Inputs

DiskBlock == [mbal: Ballot \cup {0}, bal: Ballot \cup {0}, inp: Inputs \cup {NotAnInput}]

InitDB == [mbal |-> 0, bal |-> 0, inp |-> NotAnInput]

VARIABLES disk, dblock, phase, output

vars == <<disk, dblock, phase, output>>

TypeOK ==
  /\ disk \in [Disk -> [1..N -> DiskBlock]]
  /\ dblock \in [1..N -> DiskBlock]
  /\ phase \in [1..N -> {0, 1, 2, 3}]
  /\ output \in [1..N -> Inputs \cup {NotAnInput}]

Init ==
  /\ disk = [d \in Disk |-> [p \in 1..N |-> InitDB]]
  /\ dblock = [p \in 1..N |-> InitDB]
  /\ phase = [p \in 1..N |-> 0]
  /\ output = [p \in 1..N |-> NotAnInput]

StartBallot(p) ==
  /\ phase[p] = 0
  /\ phase' = [phase EXCEPT ![p] = 1]
  /\ UNCHANGED <<disk, dblock, output>>

Next == \E p \in 1..N : StartBallot(p)

Spec == Init /\ [][Next]_vars

Consistency ==
  \A p, q \in 1..N :
    (output[p] # NotAnInput /\ output[q] # NotAnInput) => output[p] = output[q]

====
