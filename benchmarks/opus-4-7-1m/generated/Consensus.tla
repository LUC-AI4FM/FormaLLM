---- MODULE Consensus ----
(***************************************************************************)
(* A very abstract specification of the consensus problem: a set of       *)
(* processes must choose a single value. We abstract away even the        *)
(* processes; we describe the set of all chosen values. The set is        *)
(* initially empty, it can be set to a single value, and then it can      *)
(* never change.                                                           *)
(*                                                                         *)
(* We are ignoring liveness, so we do not require that a value is         *)
(* eventually chosen.                                                      *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT Value

\* The set of all values that have been chosen.
VARIABLE chosen

vars == <<chosen>>

\* The type-correctness invariant asserting the "type" of chosen.
TypeOK == chosen \subseteq Value /\ IsFiniteSet(chosen)

\* The initial predicate.
Init == chosen = {}

\* The next-state relation. Enabled iff chosen equals the empty set.
Next ==
    /\ chosen = {}
    /\ \E v \in Value : chosen' = {v}

\* The TLA+ temporal formula that is the spec.
Spec == Init /\ [][Next]_chosen

\* Liveness-augmented spec.
LiveSpec == Spec /\ WF_chosen(Next)

\* The safety property: chosen contains at most one value in any reachable state.
Inv == Cardinality(chosen) \in {0, 1}

\* Liveness: some value is eventually chosen.
Success == <>(chosen /= {})

THEOREM Spec => []Inv
====
