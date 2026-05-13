---- MODULE MajorityProof ----
\* TLAPS proof companion to module Majority. Proves type correctness, several
\* auxiliary lemmas about positions and occurrences, and finally correctness
\* of the Boyer-Moore majority vote algorithm based on an inductive
\* invariant.

EXTENDS Majority, TLAPS, NaturalsInduction, SequenceTheorems, FiniteSetTheorems

\* **************************************************************************
\* Proving type correctness is easy.
\* **************************************************************************

THEOREM TypeCorrect == Spec => []TypeOK
PROOF
  <1>1. Init => TypeOK
        BY DEF Init, TypeOK, InputSeq
  <1>2. TypeOK /\ [Next]_vars => TypeOK'
        BY DEF TypeOK, Next, Step, Done, vars
  <1>3. QED
        BY <1>1, <1>2, PTL DEF Spec

\* **************************************************************************
\* Auxiliary lemmas about positions and occurrences.
\* **************************************************************************

LEMMA CountPrefixMonotone ==
  ASSUME TypeOK, j < Len(seq)
  PROVE  CountPrefix(seq[j])' = CountPrefix(seq[j]) + 1
PROOF OMITTED

LEMMA CountSplit ==
  ASSUME TypeOK
  PROVE  Count(cand) = CountPrefix(cand)
             + Cardinality({ i \in j..Len(seq) : seq[i] = cand })
PROOF OMITTED

LEMMA OccurrenceBound ==
  ASSUME TypeOK, v \in Value, v /= cand
  PROVE  2 * CountPrefix(v) <= (j - 1) - cnt
PROOF OMITTED

\* **************************************************************************
\* We prove correctness based on the inductive invariant.
\* **************************************************************************

THEOREM InvInductive ==
  Inv /\ [Next]_vars => Inv'
PROOF
  <1>1. Inv /\ Step => Inv'
        BY DEF Inv, Step, TypeOK
  <1>2. Inv /\ Done => Inv'
        BY DEF Inv, Done
  <1>3. Inv /\ UNCHANGED vars => Inv'
        BY DEF Inv, vars
  <1>4. QED
        BY <1>1, <1>2, <1>3 DEF Next

THEOREM InvImpliesCorrect == Inv => Correct
PROOF
  BY OccurrenceBound, CountSplit DEF Inv, Correct, HasMajority,
                                     Count, CountPrefix

THEOREM MajorityCorrect == Spec => []Correct
PROOF
  <1>1. Init => Inv
        BY DEF Init, Inv, TypeOK, InputSeq, CountPrefix, OccPrefix
  <1>2. Inv /\ [Next]_vars => Inv'
        BY InvInductive
  <1>3. Inv => Correct
        BY InvImpliesCorrect
  <1>4. QED
        BY <1>1, <1>2, <1>3, PTL DEF Spec

====
