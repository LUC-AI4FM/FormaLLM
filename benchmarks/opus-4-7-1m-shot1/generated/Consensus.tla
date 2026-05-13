---- MODULE Consensus ----
(***************************************************************************)
(* The consensus problem requires a set of processes to choose a single    *)
(* value.  This module specifies the problem by specifying exactly what    *)
(* the requirements are for choosing a value.                              *)
(*                                                                         *)
(* We let the constant parameter Value be the set of all values that can   *)
(* be chosen.                                                              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLAPS

CONSTANT Value

(***************************************************************************)
(* We now specify the safety property of consensus as a trivial algorithm  *)
(* that describes the allowed behaviors of a consensus algorithm.  It uses *)
(* the variable `chosen' to represent the set of all chosen values.       *)
(*                                                                         *)
(* --algorithm Consensus {                                                 *)
(* variable chosen = {};                                                   *)
(* macro Choose() { when chosen = {};                                      *)
(*                  with (v \in Value) { chosen := {v} } }                 *)
(* { lbl: while (TRUE) { Choose() } }                                      *)
(* }                                                                       *)
(***************************************************************************)

(***** BEGIN TRANSLATION ******)
VARIABLES chosen, pc

vars == << chosen, pc >>

Init == /\ chosen = {}
        /\ pc = "lbl"

lbl == /\ pc = "lbl"
       /\ chosen = {}
       /\ \E v \in Value : chosen' = {v}
       /\ pc' = "lbl"

Next == lbl

Spec == Init /\ [][Next]_vars

(***** END TRANSLATION ******)

(***************************************************************************)
(* The type-correctness invariant.                                         *)
(***************************************************************************)
TypeOK == /\ chosen \subseteq Value
          /\ pc = "lbl"

(***************************************************************************)
(* Safety: At most one value is chosen.                                    *)
(***************************************************************************)
Inv == /\ TypeOK
       /\ Cardinality(chosen) \leq 1

(***************************************************************************)
(* The following lemma asserts that Inv is an inductive invariant of the   *)
(* next-state action Next.                                                 *)
(***************************************************************************)
LEMMA InvInv == Inv /\ [Next]_vars => Inv'

THEOREM Invariance == Spec => []Inv

(***************************************************************************)
(* Liveness: A value is eventually chosen.                                 *)
(***************************************************************************)
LiveSpec == Spec /\ WF_vars(Next)

(***************************************************************************)
(* For liveness, we need to assume that there exists at least one value.   *)
(***************************************************************************)
ASSUME ValueNonempty == Value # {}

Success == <>(chosen # {})

THEOREM LiveSpec => Success

(***************************************************************************)
(* The following theorem is used in the refinement proof in module         *)
(* VoteProof.                                                              *)
(***************************************************************************)
THEOREM ChosenStable == Spec => [](chosen # {} => [](chosen = chosen))

====
