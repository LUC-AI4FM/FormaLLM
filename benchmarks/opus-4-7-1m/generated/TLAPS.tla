---- MODULE TLAPS ----
(***************************************************************************)
(* The TLAPS standard module. Backend pragmas and temporal-logic rules    *)
(* for the TLA+ Proof System.                                              *)
(*                                                                         *)
(* Each pragma can be cited with a BY or a USE. The pragma added to the   *)
(* context of an obligation most recently is the one whose effects are    *)
(* triggered.                                                              *)
(***************************************************************************)
EXTENDS Naturals

\* Backend pragmas. The annotations are not required for parsing but are
\* documented for completeness.

\* SMT solver via the historical name.
SMT == TRUE          (* { by (prover:"smt3") } *)

\* SMT solver with explicit name and timeout.
SMTT(n) == TRUE      (* { by (prover:"smt3"; timeout:@) } *)

\* CVC3 SMT solver (bundled with TLAPS).
CVC3 == TRUE         (* { by (prover:"cvc33") } *)
CVC3T(n) == TRUE     (* { by (prover:"cvc33"; timeout:@) } *)

\* Yices SMT solver.
Yices == TRUE        (* { by (prover:"yices3") } *)
YicesT(n) == TRUE    (* { by (prover:"yices3"; timeout:@) } *)

\* veriT SMT solver.
VeriT == TRUE        (* { by (prover:"verit") } *)
VeriTT(n) == TRUE    (* { by (prover:"verit"; timeout:@) } *)

\* Z3 SMT solver.
Z3 == TRUE           (* { by (prover:"z33") } *)
Z3T(n) == TRUE       (* { by (prover:"z33"; timeout:@) } *)

\* SPASS superposition prover.
SPASS == TRUE        (* { by (prover:"spass") } *)
SPASST(n) == TRUE    (* { by (prover:"spass"; timeout:@) } *)

\* LS4 PTL prover.
LS4 == TRUE          (* { by (prover:"ls4") } *)
PTL == TRUE          (* { by (prover:"ls4") } *)

\* Zenon with default and explicit timeouts.
Zenon == TRUE        (* { by (prover:"zenon") } *)
ZenonT(n) == TRUE    (* { by (prover:"zenon"; timeout:@) } *)

\* Isabelle with default timeout and tactic.
Isa == TRUE
IsaT(n) == TRUE
IsaWithTactic(t) == TRUE
IsaWithTacticAndTimeout(t, n) == TRUE

\* Set extensionality theorem.
THEOREM SetExtensionality ==
    \A S, T : (S = T) <=> (\A x : (x \in S) <=> (x \in T))

\* Isabelle pragma that turns on the set-extensionality intro rule.
IsaWithSetExtensionality == TRUE
    (* { by (prover:"isabelle"; tactic:"(auto intro: setEqualI)") } *)

\* Theorem needed to deduce NotInSetS \notin SetS from
\*   NotInSetS == CHOOSE v : v \notin SetS
THEOREM NotInChoose ==
    \A S : (CHOOSE v : v \notin S) \notin S
        \/ \A x : x \in S

(*****************************************************************************
 * Old-style Zenon / Isabelle pragmas (kept for compatibility).
 *****************************************************************************)

Zenon20  == TRUE   (* { by (prover:"zenon"; timeout:20) } *)
Zenon40  == TRUE
Zenon80  == TRUE
Zenon160 == TRUE

\* Isabelle's auto search.
Auto          == TRUE  (* { by (prover:"isabelle"; tactic:"auto") } *)
AutoT(n)      == TRUE

\* Isabelle "force".
Force         == TRUE
ForceT(n)     == TRUE

\* Isabelle simplification tactics.
Simplification     == TRUE
SimplificationT(n) == TRUE
SimplifyAndSolve   == TRUE

\* Isabelle "blast".
Blast      == TRUE
BlastT(n)  == TRUE
AutoBlast  == TRUE

\* Multi-back-end pragmas.
AllProvers     == TRUE
AllProversT(n) == TRUE
AllSMT         == TRUE
AllSMT_T(n)    == TRUE
AllIsa         == TRUE
AllIsaT(n)     == TRUE

(*****************************************************************************
 * TEMPORAL LOGIC
 *
 * The following rules are intended to be used when TLAPS handles temporal
 * logic. They will not work now. Moreover, when temporal reasoning is
 * implemented, these rules may be changed or omitted. They are included
 * mainly to reserve their names against name clashes.
 *
 * Most of the rules below are from "The Temporal Logic of Actions".
 *****************************************************************************)

\* WF1: weak-fairness rule.
THEOREM WF1 == TRUE

\* WF2 / SF2: weak/strong fairness, obtained from WF1' / SF1' by substituting
\*   M <- M, g <- g, EM <- ENABLED <<M>>_g.
THEOREM WF2 == TRUE
THEOREM SF1 == TRUE
THEOREM SF2 == TRUE

\* STL4 — special case from "The Temporal Logic of Actions"; general case
\* with arbitrary F and G is not yet handled by TLAPS.
THEOREM STL4 == TRUE

\* TLA2 — special case of rule TLA2.
THEOREM TLA2 == TRUE

\* Propositional-temporal-logic decision procedure.
THEOREM TemporalDecision == TRUE
====
