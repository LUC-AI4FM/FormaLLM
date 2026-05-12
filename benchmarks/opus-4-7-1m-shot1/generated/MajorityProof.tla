---- MODULE MajorityProof ----
(***************************************************************************)
(* TLAPS proofs for the Majority module.                                   *)
(***************************************************************************)
EXTENDS Majority, TLAPS, NaturalsInduction, SequenceTheorems, FiniteSetTheorems

(***************************************************************************)
(* Proving type correctness is easy.                                       *)
(***************************************************************************)
LEMMA TypeCorrect == Spec => []TypeOK
  <1>1. Init => TypeOK BY DEF Init, TypeOK
  <1>2. TypeOK /\ [Next]_vars => TypeOK' BY DEF TypeOK, Next, vars
  <1>3. QED BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************)
(* Auxiliary lemmas about positions and occurrences.                       *)
(***************************************************************************)
LEMMA OccurrencesBound ==
  ASSUME NEW v \in Value, NEW s \in Seq(Value)
  PROVE  Cardinality({ i \in 1..Len(s) : s[i] = v }) \leq Len(s)
  OBVIOUS

LEMMA OccurrencesBeforePositive ==
  ASSUME TypeOK
  PROVE  OccurrencesBefore(cand) \geq 0
  BY DEF OccurrencesBefore, PositionsBefore

(***************************************************************************)
(* We prove correctness based on the inductive invariant.                  *)
(***************************************************************************)
THEOREM Correctness_Proof == Spec => []Correctness
  <1>1. Init => Inv
    BY DEF Init, Inv, TypeOK, PositionsBefore, OccurrencesBefore
  <1>2. Inv /\ [Next]_vars => Inv'
    BY DEF Inv, Next, vars, TypeOK, PositionsBefore, OccurrencesBefore
  <1>3. Inv => Correctness
    BY DEF Inv, Correctness, PositionsBefore, OccurrencesBefore, Occurrences
  <1>4. QED BY <1>1, <1>2, <1>3, PTL DEF Spec

====
