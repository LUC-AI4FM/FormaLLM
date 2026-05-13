---- MODULE MajorityProof ----
\* TLAPS proof harness for the Majority spec. Proves type-correctness,
\* auxiliary lemmas about positions and occurrences, and the inductive
\* invariant that implies Correctness.

EXTENDS Majority, TLAPS, FiniteSetTheorems, SequenceTheorems

(***************************************************************************
 Proving type correctness is easy.
 ***************************************************************************)

THEOREM TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
    BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
    <2>1. ASSUME TypeOK, Next
          PROVE  TypeOK'
        BY <2>1 DEF TypeOK, Next, vars
    <2>2. ASSUME TypeOK, UNCHANGED vars
          PROVE  TypeOK'
        BY <2>2 DEF TypeOK, vars
    <2>3. QED BY <2>1, <2>2
<1>3. QED BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************
 Auxiliary lemmas about positions and occurrences.
 ***************************************************************************)

LEMMA OccurrencesBeforeFinite ==
    ASSUME TypeOK, NEW v \in Value
    PROVE  IsFiniteSet(OccurrencesBefore(v))
<1>1. OccurrencesBefore(v) \subseteq 1..(j - 1)
    BY DEF OccurrencesBefore
<1>2. IsFiniteSet(1..(j - 1))
    BY DEF TypeOK
<1>3. QED BY <1>1, <1>2, FS_Subset

LEMMA CountBeforeBound ==
    ASSUME TypeOK, NEW v \in Value
    PROVE  CountBefore(v) <= j - 1
<1>1. OccurrencesBefore(v) \subseteq 1..(j - 1)
    BY DEF OccurrencesBefore
<1>2. Cardinality(1..(j - 1)) = j - 1
    BY DEF TypeOK
<1>3. QED BY <1>1, <1>2, FS_Subset, FS_CardinalityType
       DEF CountBefore, TypeOK

LEMMA SumOfCounts ==
    ASSUME TypeOK
    PROVE  (\A v \in Value : CountBefore(v) >= 0) /\
           Cardinality({k \in 1..(j - 1) : TRUE}) = j - 1
OMITTED

(***************************************************************************
 We prove correctness based on the inductive invariant.
 ***************************************************************************)

THEOREM InductiveInvariantHolds == Spec => []InductiveInvariant
<1>1. Init => InductiveInvariant
    BY DEF Init, InductiveInvariant, TypeOK,
       OccurrencesBefore, CountBefore
<1>2. InductiveInvariant /\ [Next]_vars => InductiveInvariant'
    <2>1. ASSUME InductiveInvariant, Next
          PROVE  InductiveInvariant'
        BY <2>1 DEF InductiveInvariant, Next, TypeOK,
                    OccurrencesBefore, CountBefore
    <2>2. ASSUME InductiveInvariant, UNCHANGED vars
          PROVE  InductiveInvariant'
        BY <2>2 DEF InductiveInvariant, TypeOK, vars,
                    OccurrencesBefore, CountBefore
    <2>3. QED BY <2>1, <2>2
<1>3. QED BY <1>1, <1>2, PTL DEF Spec

THEOREM Correct == Spec => []Correctness
<1>1. InductiveInvariant => Correctness
    BY DEF InductiveInvariant, Correctness, TypeOK,
       Count, CountBefore, OccurrencesBefore
<1>2. QED BY <1>1, InductiveInvariantHolds, PTL DEF Spec

====
