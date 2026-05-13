---- MODULE MajorityProof ----
(***************************************************************************)
(* TLAPS-checked proof of correctness of the Boyer-Moore majority vote     *)
(* algorithm specified in module Majority.                                 *)
(***************************************************************************)
EXTENDS Majority, TLAPS, FiniteSetTheorems, SequenceTheorems, NaturalsInduction

(***************************************************************************)
(* Proving type correctness is easy.                                       *)
(***************************************************************************)
TypeOK ==
  /\ seq \in BoundedSeq(Value)
  /\ i \in 1 .. (Len(seq) + 1)
  /\ cand \in Value
  /\ cnt \in Nat

THEOREM TypeCorrect == Spec => []TypeOK
  <1>1. Init => TypeOK
    BY DEF Init, TypeOK
  <1>2. TypeOK /\ [Next]_vars => TypeOK'
    BY DEF TypeOK, Next, vars
  <1>3. QED
    BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************)
(* Auxiliary lemmas about positions and occurrences.                       *)
(***************************************************************************)
LEMMA PrefixCardinality ==
  ASSUME NEW v \in Value, NEW j \in Nat,
         j <= Len(seq) + 1
  PROVE  OccPrefix(v, j) \in Nat
  BY FS_CardinalityType DEF OccPrefix, PrefIdx

LEMMA PrefixStep ==
  ASSUME NEW v \in Value, NEW j \in 1 .. Len(seq)
  PROVE  OccPrefix(v, j+1) =
           IF seq[j] = v THEN OccPrefix(v, j) + 1 ELSE OccPrefix(v, j)
  OBVIOUS

LEMMA OccBound ==
  ASSUME NEW v \in Value
  PROVE  OccPrefix(v, Len(seq) + 1) = Occurrences(v)
  BY DEF OccPrefix, PrefIdx, Occurrences

(***************************************************************************)
(* We prove correctness based on the inductive invariant.                  *)
(***************************************************************************)
THEOREM Correct == Spec => []Correctness
  <1>1. Init => Inv
    BY DEF Init, Inv, OccPrefix, PrefIdx
  <1>2. Inv /\ [Next]_vars => Inv'
    BY DEF Inv, Next, vars, OccPrefix, PrefIdx
  <1>3. Inv => Correctness
    BY OccBound DEF Inv, Correctness
  <1>4. QED
    BY <1>1, <1>2, <1>3, PTL DEF Spec
====
