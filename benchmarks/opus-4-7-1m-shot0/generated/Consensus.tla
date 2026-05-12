---- MODULE Consensus ----
\* The consensus problem requires a set of processes to choose a single
\* value. This module specifies the problem by specifying exactly what the
\* requirements are for choosing a value.
\*
\* The constant Value is the set of all values that can be chosen.
\* The variable `chosen' is the set of all values chosen so far. The trivial
\* algorithm allows only behaviors that contain a single state-change in
\* which `chosen' goes from {} to {v} for some v in Value.

EXTENDS Naturals, FiniteSets

CONSTANT Value

(* --algorithm Consensus {
   variable chosen = {};
   macro Choose() { when chosen = {};
                    with (v \in Value) { chosen := {v} } }
   { lbl: while (TRUE) { Choose() }
   }
}  *)

\**** BEGIN TRANSLATION
VARIABLES chosen, pc

vars == << chosen, pc >>

Init ==
  /\ chosen = {}
  /\ pc = "lbl"

lbl ==
  /\ pc = "lbl"
  /\ chosen = {}
  /\ \E v \in Value : chosen' = {v}
  /\ pc' = "lbl"

Next == lbl

Spec == Init /\ [][Next]_vars

LiveSpec == Spec /\ WF_vars(Next)

\**** END TRANSLATION

\* Type-correctness invariant.
TypeOK ==
  /\ chosen \subseteq Value
  /\ pc \in {"lbl"}

\* Inductive invariant: at most one value is chosen.
Inv ==
  /\ TypeOK
  /\ Cardinality(chosen) <= 1

\* Eventually some value is chosen (requires Value /= {}).
Success == <> (chosen /= {})

\* LEMMA: Inv is inductive.
LEMMA InvInductive == Inv /\ [Next]_vars => Inv'

\* THEOREM: Spec implies Inv always holds.
THEOREM SafetyTheorem == Spec => []Inv

\* For liveness, we need at least one value to exist.
ASSUME LiveAssumption == Value /= {}

\* THEOREM: LiveSpec eventually achieves Success.
THEOREM LivenessTheorem == LiveSpec => Success

\* The following theorem is used in the refinement proof in VoteProof.
THEOREM ConsensusRefinement == Spec => Spec

====
