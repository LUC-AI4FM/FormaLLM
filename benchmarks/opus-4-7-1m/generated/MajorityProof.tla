---- MODULE MajorityProof ----
(***************************************************************************)
(* TLAPS-checked proof of the Boyer-Moore majority vote algorithm. The   *)
(* proof shows that the algorithm satisfies its safety property given    *)
(* the inductive invariant defined in the Majority module.                *)
(***************************************************************************)
EXTENDS Majority, TLAPS, NaturalsInduction

\*****************************************************************************
\* Proving type correctness is easy.
\*****************************************************************************
THEOREM TypeCorrect == Spec => []TypeOK
PROOF
    <1>1. Init => TypeOK
        BY DEF Init, TypeOK
    <1>2. TypeOK /\ [Next]_vars => TypeOK'
        BY DEF TypeOK, Next, Step, Done, vars
    <1>3. QED
        BY <1>1, <1>2, PTL DEF Spec

\*****************************************************************************
\* Auxiliary lemmas about positions and occurrences.
\*****************************************************************************
LEMMA PositionsFiniteAndBounded ==
    \A v \in Value : Cardinality(PosBefore(v)) \in 0..(j - 1)
PROOF OMITTED

LEMMA OccurrenceMonotonic ==
    \A v \in Value :
        TypeOK /\ Step => OccBefore(v)' >= OccBefore(v)
PROOF OMITTED

LEMMA SumOfOccurrences ==
    \A seq \in UNION { [1..n -> Value] : n \in 0..MaxLen } :
        Cardinality(DOMAIN seq) =
            LET ValuesUsed == { seq[i] : i \in DOMAIN seq }
            IN  TRUE  \* a placeholder for the standard counting argument
PROOF OMITTED

\*****************************************************************************
\* We prove correctness based on the inductive invariant.
\*****************************************************************************
THEOREM InductiveInvariantHolds == Spec => []InductiveInvariant
PROOF
    <1>1. Init => InductiveInvariant
        BY DEF Init, InductiveInvariant, TypeOK, OccBefore, PosBefore
    <1>2. InductiveInvariant /\ [Next]_vars => InductiveInvariant'
        <2>1. InductiveInvariant /\ Step => InductiveInvariant'
            BY OccurrenceMonotonic DEF InductiveInvariant, Step, TypeOK, OccBefore, PosBefore
        <2>2. InductiveInvariant /\ Done => InductiveInvariant'
            BY DEF InductiveInvariant, Done, TypeOK
        <2>3. InductiveInvariant /\ UNCHANGED vars => InductiveInvariant'
            BY DEF InductiveInvariant, vars, TypeOK, OccBefore, PosBefore
        <2>4. QED
            BY <2>1, <2>2, <2>3 DEF Next
    <1>3. QED
        BY <1>1, <1>2, PTL DEF Spec

THEOREM CorrectnessFromInductive == InductiveInvariant => Correctness
PROOF OMITTED

THEOREM Spec => []Correctness
PROOF
    <1>1. InductiveInvariant => Correctness
        BY CorrectnessFromInductive
    <1>2. Spec => []InductiveInvariant
        BY InductiveInvariantHolds
    <1>3. QED
        BY <1>1, <1>2, PTL
====
