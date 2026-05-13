---- MODULE TLAPS ----
\* TLAPS standard library: backend-pragma declarations and basic
\* temporal-logic proof rules used by the TLA+ proof manager.

EXTENDS Naturals

\* Backend pragmas. Each can be cited with BY or USE. The most recently
\* added pragma to an obligation's context is the one whose effects fire.
\* The pragmas below are intended only as a last resource, since they
\* depend on the particular backend prover set.

\* Backend pragma: use the SMT solver for arithmetic.
\* This name persists for historical reasons.
SMT == TRUE (*{ by (prover:"smt3") }*)
SMTT(n) == TRUE (*{ by (prover:"smt3"; timeout:@) }*)

\* Backend pragma: SMT solver. Translates obligation to SMTLIB2; the
\* supported fragment includes first-order logic, set theory, functions,
\* and records. SMT calls the solver with a default 5s timeout; SMTT(n)
\* uses a custom timeout n.
SMT2 == TRUE (*{ by (prover:"smt3") }*)
SMT2T(n) == TRUE (*{ by (prover:"smt3"; timeout:@) }*)

\* Backend pragma: CVC4 SMT solver.
CVC4 == TRUE (*{ by (prover: "cvc33") }*)
CVC4T(n) == TRUE (*{ by (prover:"cvc33"; timeout:@) }*)
CVC3 == TRUE (*{ by (prover: "cvc33") }*)
CVC3T(n) == TRUE (*{ by (prover:"cvc33"; timeout:@) }*)

\* Backend pragma: Yices SMT solver.
Yices == TRUE (*{ by (prover: "yices3") }*)
YicesT(n) == TRUE (*{ by (prover:"yices3"; timeout:@) }*)

\* Backend pragma: veriT SMT solver.
VeriT == TRUE (*{ by (prover: "verit") }*)
VeriTT(n) == TRUE (*{ by (prover:"verit"; timeout:@) }*)

\* Backend pragma: Z3 SMT solver. Z3 is used by default; this name lets
\* one call it explicitly.
Z3 == TRUE (*{ by (prover: "z33") }*)
Z3T(n) == TRUE (*{ by (prover:"z33"; timeout:@) }*)

\* Backend pragma: SPASS superposition prover.
SPASS == TRUE (*{ by (prover: "spass") }*)
SPASST(n) == TRUE (*{ by (prover:"spass"; timeout:@) }*)

\* Backend pragma: LS4-based PTL propositional linear-time temporal
\* logic prover.
LS4 == TRUE (*{ by (prover: "ls4") }*)
LS4T(n) == TRUE (*{ by (prover: "ls4"; timeout:@) }*)
PTL == TRUE (*{ by (prover: "ls4") }*)

\* Backend pragma: Zenon with optional timeouts (default 10s).
Zenon == TRUE (*{ by (prover:"zenon") }*)
ZenonT(n) == TRUE (*{ by (prover:"zenon"; timeout:@) }*)

\* Backend pragma: Isabelle with optional timeouts and tactics
\* (default 30s, "auto").
Isa == TRUE (*{ by (prover:"isabelle") }*)
IsaT(n) == TRUE (*{ by (prover:"isabelle"; timeout:@) }*)
IsaM(tac) == TRUE (*{ by (prover:"isabelle"; tactic:@) }*)
IsaMT(tac, n) == TRUE (*{ by (prover:"isabelle"; tactic:@; timeout:@) }*)

\* Theorem of set extensionality (the useful implication direction).
\* Sometimes required by the SMT backend; counter-productive in BY for
\* Zenon or Isabelle backends - use IsaWithSetExtensionality instead.
THEOREM SetExtensionality ==
    \A S, T : (S = T) <=> (\A x : (x \in S) <=> (x \in T))
OBVIOUS

IsaWithSetExtensionality == TRUE
    (*{ by (prover:"isabelle"; tactic:"(auto intro: setEqualI)")}*)

\* For: NotInSetS == CHOOSE v : v \notin SetS  (lets one deduce
\* NotInSetS \notin SetS).
THEOREM NotInSet ==
    \A S : (CHOOSE v : v \notin S) \notin S
OMITTED

IsaWithInIrrefl == TRUE (*{by (isabelle "(auto intro: inIrrefl)")}*)

\* Old versions of Zenon and Isabelle pragmas (kept for compatibility).
Zenon20 == TRUE (*{ by (prover:"zenon"; timeout:20) }*)
Zenon40 == TRUE (*{ by (prover:"zenon"; timeout:40) }*)
Zenon80 == TRUE (*{ by (prover:"zenon"; timeout:80) }*)
Zenon160 == TRUE (*{ by (prover:"zenon"; timeout:160) }*)

\* Isabelle "auto" tactic. Bypasses Zenon; useful for simplification and
\* equational reasoning.
Auto == TRUE (*{ by (prover:"isabelle"; tactic:"auto") }*)
AutoT(n) == TRUE (*{ by (prover:"isabelle"; tactic:"auto"; timeout:@) }*)
Auto2 == TRUE (*{ by (prover:"isabelle"; tactic:"auto"; timeout:120) }*)
Auto3 == TRUE (*{ by (prover:"isabelle"; tactic:"auto"; timeout:480) }*)
Auto4 == TRUE (*{ by (prover:"isabelle"; tactic:"auto"; timeout:960) }*)

\* Isabelle "force" tactic. Useful for quantifier reasoning.
Force == TRUE (*{ by (prover:"isabelle"; tactic:"force") }*)
ForceT(n) == TRUE (*{ by (prover:"isabelle"; tactic:"force"; timeout:@) }*)

\* Isabelle simplification tactics. Often needed for record/tuple
\* projections; use SimplifyAndSolve unless plain Simplification works.
Simplification == TRUE
    (*{ by (prover:"isabelle"; tactic:"clarsimp") }*)
SimplifyAndSolve == TRUE
    (*{ by (prover:"isabelle"; tactic:"clarsimp auto?") }*)

\* Isabelle "blast" tactic. Rarely better than Zenon alone but useful
\* combined with Auto (the AutoBlast pragma below).
Blast == TRUE (*{ by (prover:"isabelle"; tactic:"blast") }*)
BlastT(n) == TRUE (*{ by (prover:"isabelle"; tactic:"blast"; timeout:@) }*)
AutoBlast == TRUE (*{ by (prover:"isabelle"; tactic:"auto, blast") }*)

\* Multi-backend pragmas: try a sequence of backends in turn.
\* CVC3 first (bundled with TLAPS), then Zenon and Isabelle before the
\* other SMT solvers.
SMTOrZ3OrCooper == TRUE
    (*{ by (prover:"cvc33") by (prover:"smt3")
         by (prover:"yices3") by (prover:"verit") by (prover:"z33") }*)

\* Pragmas controlling expansion of the operators ENABLED and \cdot.
ExpandENABLED == TRUE (*{ by (prover:"expandenabled") }*)
ExpandCdot == TRUE (*{ by (prover:"expandcdot") }*)
AutoUSE == TRUE (*{ by (prover:"autouse") }*)
Lambdify == TRUE (*{ by (prover:"lambdify") }*)
ENABLEDaxioms == TRUE (*{ by (prover:"enabledaxioms") }*)
ENABLEDrules == TRUE (*{ by (prover:"enabledrules") }*)
ENABLEDrewrites == TRUE (*{ by (prover:"enabledrewrites") }*)
LevelComparison == TRUE (*{ by (prover:"levelcomparison") }*)

\* Internal wrappers occurring in TLAPM's intermediate representation.
EnabledWrapper(A) == ENABLED A
CdotWrapper(A, B) == A \cdot B

\* BY ONLY Trivial unit-tests TLAPM's triviality checks.
Trivial == TRUE (*{ by (prover:"trivial") }*)

\*****************************************************************************
\* TEMPORAL LOGIC
\*
\* The rules below are placeholders for when TLAPS gains full temporal
\* reasoning. They will not work today; they are reserved here so their
\* names do not clash with future versions.
\*****************************************************************************

\* Rules from "The Temporal Logic of Actions" (Lamport).

\* WF1: weak-fairness leads-to rule.
THEOREM RuleWF1 ==
    ASSUME NEW P, NEW Q, NEW Next, NEW A, NEW v,
           P /\ [Next]_v => (P' \/ Q'),
           P /\ <<Next /\ A>>_v => Q',
           P => ENABLED <<A>>_v
    PROVE  [][Next]_v /\ WF_v(A) => (P ~> Q)
OMITTED

\* SF1: strong-fairness leads-to rule.
THEOREM RuleSF1 ==
    ASSUME NEW P, NEW Q, NEW Next, NEW A, NEW v,
           P /\ [Next]_v => (P' \/ Q'),
           P /\ <<Next /\ A>>_v => Q',
           []P => <>(ENABLED <<A>>_v)
    PROVE  [][Next]_v /\ SF_v(A) => (P ~> Q)
OMITTED

\* WF2/SF2 are obtained from WF1/SF1 with EM <- ENABLED <<M>>_g; the
\* general versions cannot yet be handled by TLAPS.

\* Special case of STL4 (general STL4 over arbitrary temporal formulas
\* is not yet supported).
THEOREM RuleSTL4 ==
    ASSUME NEW F, NEW G,
           F => G
    PROVE  []F => []G
OMITTED

\* Special case of TLA2.
THEOREM RuleTLA2 ==
    ASSUME NEW Step, NEW Step2, NEW v, NEW w,
           Step /\ (v' = v) => Step2 /\ (w' = w)
    PROVE  [Step]_v => [Step2]_w
OMITTED

\* Invokes a decision procedure for propositional temporal logic.
PTLPropDecision == TRUE (*{ by (prover:"ls4") }*)

====
