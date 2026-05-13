----------------------------- MODULE Consensus ------------------------------
\* Abstract specification of consensus: a set of processes must choose a
\* single value. We specify the safety requirement by describing the set
\* `chosen' of all chosen values: it is initially empty, may be set to a
\* singleton, and never changes thereafter.

EXTENDS Naturals, FiniteSets, TLAPS, FiniteSetTheorems

CONSTANT Value

(***************************************************************************
PlusCal source:

--algorithm Consensus {
    variable chosen = {};
    macro Choose() {
        when chosen = {};
        with (v \in Value) { chosen := {v} }
    }
    { lbl: while (TRUE) { Choose() } }
}

The PlusCal translation appears below.
 ***************************************************************************)

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

LiveSpec == Spec /\ WF_vars(Next)

-----------------------------------------------------------------------------

TypeOK == /\ chosen \subseteq Value
          /\ IsFiniteSet(chosen)
          /\ pc = "lbl"

Inv == /\ TypeOK
       /\ Cardinality(chosen) \leq 1

THEOREM Invariance == Spec => []Inv
<1>1. Init => Inv
    BY FS_EmptySet DEF Init, Inv, TypeOK
<1>2. Inv /\ [Next]_vars => Inv'
    <2>1. Inv /\ Next => Inv'
        BY FS_Singleton DEF Next, lbl, Inv, TypeOK
    <2>2. Inv /\ UNCHANGED vars => Inv'
        BY DEF Inv, TypeOK, vars
    <2>. QED BY <2>1, <2>2
<1>3. QED BY <1>1, <1>2, PTL DEF Spec

-----------------------------------------------------------------------------

\* Liveness: some value is eventually chosen.
Success == <>(chosen # {})

\* Liveness requires the set of values to be non-empty.
ASSUME ValueNonempty == Value # {}

\* Characterize states where the next-state action is enabled.
LEMMA EnabledLbl == TypeOK /\ chosen = {} => ENABLED <<Next>>_vars
    OBVIOUS

THEOREM Liveness == LiveSpec => Success
<1>1. Inv /\ chosen = {} ~> chosen # {}
    OBVIOUS
<1>2. QED BY <1>1, Invariance, PTL DEF LiveSpec, Success, Inv

\* Used in the refinement proof in module VoteProof.
THEOREM Spec => [](Cardinality(chosen) \leq 1)
    BY Invariance DEF Inv

=============================================================================
