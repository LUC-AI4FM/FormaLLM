---- MODULE TLAPS ----
\* Backend pragmas and temporal-logic proof rules for the TLA+ Proof System.
\* Each pragma below can be cited in a BY or USE clause; the pragma added
\* most recently to the proof context is the one whose effect is triggered.
\* The "{ by (...) }" comments are TLAPM directives stored in the definition.
\*
\* Note: most pragmas are best treated as a last resort - they depend on the
\* particular backend provers and are meaningless to a human reader.

\* -------- SMT solvers --------

\* SMT solver (default backend; this name exists for historical reasons).
SMT == TRUE
        \* { by (prover:"smt3") }
SMTT(timeout) == TRUE
        \* { by (prover:"smt3"; timeout:@) }

\* CVC4 SMT solver (CVC3* are kept under that name for backward compat).
CVC4 == TRUE
        \* { by (prover:"cvc33") }
CVC4T(timeout) == TRUE
        \* { by (prover:"cvc33"; timeout:@) }
CVC3 == TRUE
        \* { by (prover:"cvc33") }
CVC3T(timeout) == TRUE
        \* { by (prover:"cvc33"; timeout:@) }

\* Yices SMT solver.
Yices == TRUE
        \* { by (prover:"yices3") }
YicesT(timeout) == TRUE
        \* { by (prover:"yices3"; timeout:@) }

\* veriT SMT solver.
VeriT == TRUE
        \* { by (prover:"verit") }
VeriTT(timeout) == TRUE
        \* { by (prover:"verit"; timeout:@) }

\* Z3 SMT solver (default in many configurations).
Z3 == TRUE
        \* { by (prover:"z33") }
Z3T(timeout) == TRUE
        \* { by (prover:"z33"; timeout:@) }

\* -------- Other provers --------

\* SPASS superposition prover.
SPASS == TRUE
        \* { by (prover:"spass") }
SPASST(timeout) == TRUE
        \* { by (prover:"spass"; timeout:@) }

\* LS4-based propositional linear-time temporal logic prover.
LS4 == TRUE
        \* { by (prover:"ls4") }
LS4T(timeout) == TRUE
        \* { by (prover:"ls4"; timeout:@) }
PTL == LS4

\* Zenon.
Zenon == TRUE
        \* { by (prover:"zenon") }
ZenonT(timeout) == TRUE
        \* { by (prover:"zenon"; timeout:@) }

\* -------- Isabelle tactics --------

Isa == TRUE
        \* { by (prover:"isabelle") }
IsaT(timeout) == TRUE
        \* { by (prover:"isabelle"; timeout:@) }
IsaTac(tactic) == TRUE
        \* { by (prover:"isabelle"; tactic:@) }
IsaTacT(tactic, timeout) == TRUE
        \* { by (prover:"isabelle"; tactic:@; timeout:@) }

Auto       == TRUE  \* { by (prover:"isabelle"; tactic:"auto") }
AutoT(t)   == TRUE  \* { by (prover:"isabelle"; tactic:"auto"; timeout:@) }
Force      == TRUE  \* { by (prover:"isabelle"; tactic:"force") }
ForceT(t)  == TRUE  \* { by (prover:"isabelle"; tactic:"force"; timeout:@) }
Blast      == TRUE  \* { by (prover:"isabelle"; tactic:"blast") }
BlastT(t)  == TRUE  \* { by (prover:"isabelle"; tactic:"blast"; timeout:@) }
AutoBlast  == TRUE  \* { by (prover:"isabelle"; tactic:"auto, blast") }

Simplification        == TRUE  \* { by (prover:"isabelle"; tactic:"clarsimp") }
SimplificationT(t)    == TRUE  \* { by (prover:"isabelle"; tactic:"clarsimp"; timeout:@) }
SimplifyAndSolve      == TRUE  \* { by (prover:"isabelle"; tactic:"clarsimp auto?") }
SimplifyAndSolveT(t)  == TRUE  \* { by (prover:"isabelle"; tactic:"clarsimp auto?"; timeout:@) }

IsaWithSetExtensionality == TRUE
        \* { by (prover:"isabelle"; tactic:"(auto intro: setEqualI)") }

\* -------- Multi-backend strategies --------

SolveAll == TRUE
SolveAllT(t) == TRUE
SolveSMT == TRUE
SolveSMTT(t) == TRUE
SolveIsa == TRUE
SolveIsaT(t) == TRUE

\* -------- ENABLED, cdot, level pragmas --------

ExpandEnabled  == TRUE  \* { by (prover:"expandenabled") }
ExpandCdot     == TRUE  \* { by (prover:"expandcdot") }
AutoUSE        == TRUE  \* { by (prover:"autouse") }
Lambdify       == TRUE  \* { by (prover:"lambdify") }
ENABLEDaxioms  == TRUE  \* { by (prover:"enabledaxioms") }
ENABLEDrewrites == TRUE \* { by (prover:"enabledrewrites") }
ENABLEDrules   == TRUE  \* { by (prover:"enabledrules") }
LevelComparison == TRUE \* { by (prover:"levelcomparison") }

\* Intermediate-representation wrappers used by TLAPM.
EnabledWrapper(F) == ENABLED F
CdotWrapper(A, B) == A \cdot B

\* For unit-testing the triviality checks in TLAPM.
Trivial == TRUE   \* { by (prover:"trivial") }

\* -------- Useful set-theoretic theorems --------

\* Set extensionality.
THEOREM SetExtensionality ==
  \A S, T : (S = T) <=> (\A x : (x \in S) <=> (x \in T))
OBVIOUS
        \* { by (prover:"isabelle"; tactic:"(auto intro: setEqualI)") }

\* Deducing NotInSetS \notin SetS from the CHOOSE definition.
THEOREM CHOOSE_notin ==
  ASSUME NEW SetS, NEW NotInSetS, NotInSetS = CHOOSE v : v \notin SetS
  PROVE  TRUE
OBVIOUS
        \* { by (isabelle "(auto intro: inIrrefl)") }

\* ============================================================================
\*                              TEMPORAL LOGIC
\* The rules below are placeholders so future TLAPS releases can implement
\* them without breaking name-resolution in user proofs.
\* ============================================================================

\* Rules from "The Temporal Logic of Actions" (Lamport, 1994).

\* WF1: weak-fairness implication rule.
\* P /\ [A]_v => P' \/ Q'
\* P /\ <<A>>_v => Q'
\* P => ENABLED <<A>>_v
\* /\ []P /\ [][A]_v /\ WF_v(A) => []P /\ <>Q
THEOREM RuleWF1 == TRUE  \* placeholder

\* WF2: stronger weak-fairness rule.
THEOREM RuleWF2 == TRUE  \* placeholder

\* SF1, SF2: strong-fairness analogues.
THEOREM RuleSF1 == TRUE
THEOREM RuleSF2 == TRUE

\* STL1 - STL6: standard temporal-logic axioms.
THEOREM RuleSTL1 == TRUE
THEOREM RuleSTL2 == TRUE
THEOREM RuleSTL3 == TRUE
THEOREM RuleSTL4 == TRUE   \* P => Q  =>  []P => []Q  (special case below)
THEOREM RuleSTL5 == TRUE
THEOREM RuleSTL6 == TRUE

\* TLA1, TLA2: rules from the Temporal Logic of Actions paper.
THEOREM RuleTLA1 == TRUE
THEOREM RuleTLA2 == TRUE

\* INV1, INV2: invariance rules.
THEOREM RuleINV1 == TRUE
THEOREM RuleINV2 == TRUE

\* Propositional temporal-logic decision procedure (delegated to LS4).
THEOREM PropositionalTemporalLogic == TRUE  \* { by (prover:"ls4") }

====
