---- MODULE TLAPS ----
(***************************************************************************)
(* Backend pragmas.                                                        *)
(*                                                                          *)
(* Each of these pragmas can be cited with a BY or a USE.  The pragma that *)
(* is added to the context of an obligation most recently is the one whose *)
(* effects are triggered.                                                  *)
(*                                                                          *)
(* The following pragmas should be used only as a last resource.  They are *)
(* dependent upon the particular backend provers, and are unlikely to have *)
(* any effect if the set of backend provers changes.  Moreover, they are   *)
(* meaningless to a reader of the proof.                                   *)
(***************************************************************************)

(*************************************************************************)
(* Backend pragma: use the SMT solver for arithmetic.                    *)
(*                                                                        *)
(* This method exists under this name for historical reasons.            *)
(*************************************************************************)
SimpleArithmetic == TRUE (*{ by (prover:"smt3") }*)

(*************************************************************************)
(* Backend pragma: SMT solver                                            *)
(*                                                                        *)
(* This method translates the proof obligation to SMTLIB2. The supported *)
(* fragment includes first-order logic, set theory, functions and        *)
(* records.                                                              *)
(* SMT calls the smt-solver with the default timeout of 5 seconds        *)
(* while SMTT(n) calls the smt-solver with a timeout of n seconds.       *)
(*************************************************************************)
SMT == TRUE   (*{ by (prover:"smt3") }*)
SMTT(n) == TRUE (*{ by (prover:"smt3"; timeout:@) }*)

(*************************************************************************)
(* Backend pragma: CVC3 SMT solver                                       *)
(*                                                                        *)
(* CVC3 is used by default but you can also explicitly call it.          *)
(*************************************************************************)
CVC3 == TRUE  (*{ by (prover: "cvc33") }*)
CVC3T(n) == TRUE (*{ by (prover:"cvc33"; timeout:@) }*)

(*************************************************************************)
(* Backend pragma: Yices SMT solver                                      *)
(*                                                                        *)
(* This method translates the proof obligation to Yices native language. *)
(*************************************************************************)
Yices == TRUE (*{ by (prover: "yices3") }*)
YicesT(n) == TRUE (*{ by (prover:"yices3"; timeout:@) }*)

(*************************************************************************)
(* Backend pragma: veriT SMT solver                                      *)
(*                                                                        *)
(* This method translates the proof obligation to SMTLIB2 and calls veriT*)
(*************************************************************************)
VeriT == TRUE (*{ by (prover: "verit") }*)
VeriTT(n) == TRUE (*{ by (prover:"verit"; timeout:@) }*)

(*************************************************************************)
(* Backend pragma: Z3 SMT solver                                         *)
(*                                                                        *)
(* This method translates the proof obligation to SMTLIB2 and calls Z3.  *)
(*************************************************************************)
Z3 == TRUE   (*{ by (prover: "z33") }*)
Z3T(n) == TRUE (*{ by (prover:"z33"; timeout:@) }*)

(*************************************************************************)
(* Backend pragma: SPASS superposition prover                            *)
(*                                                                        *)
(* This method translates the proof obligation to the DFG format        *)
(* language supported by the ATP SPASS. The translation is based on the *)
(* SMT one.                                                             *)
(*************************************************************************)
Spass == TRUE (*{ by (prover: "spass") }*)
SpassT(n) == TRUE (*{ by (prover:"spass"; timeout:@) }*)

(*************************************************************************)
(* Backend pragma: The PTL propositional linear time temporal logic     *)
(* prover.  It currently is the LS4 backend.                            *)
(*                                                                        *)
(* This method translates the negetation of the proof obligation to     *)
(* Seperated Normal Form (TRP++ format) and checks for unsatisfiability *)
(*************************************************************************)
LS4 == TRUE (*{ by (prover: "ls4") }*)
PTL == TRUE (*{ by (prover: "ls4") }*)

(*************************************************************************)
(* Backend pragma: Zenon with different timeouts (default is 10 seconds) *)
(*************************************************************************)
Zenon == TRUE (*{ by (prover:"zenon") }*)
ZenonT(n) == TRUE (*{ by (prover:"zenon"; timeout:@) }*)

(*******************************************************************)
(* Backend pragma: Isabelle with different timeouts and tactics    *)
(* (default is 30 seconds/auto)                                    *)
(*******************************************************************)
Isa == TRUE (*{ by (prover:"isabelle") }*)
IsaT(n) == TRUE (*{ by (prover:"isabelle"; timeout:@) }*)
IsaM(t) == TRUE (*{ by (prover:"isabelle"; tactic:@) }*)
IsaMT(t, n) == TRUE (*{ by (prover:"isabelle"; tactic:@; timeout:@) }*)

(***************************************************************************)
(* The following theorem expresses the (useful implication of the) law of  *)
(* set extensionality, which can be written as                             *)
(*                                                                          *)
(*    THEOREM  \A S, T : (S = T) <=> (\A x : (x \in S) <=> (x \in T))      *)
(*                                                                          *)
(* Theorem SetExtensionality is sometimes required by the SMT backend for  *)
(* reasoning about sets. It is usually counterproductive to include        *)
(* theorem SetExtensionality in a BY clause for the Zenon or Isabelle      *)
(* backends. Instead, use the pragma IsaWithSetExtensionality to instruct  *)
(* the Isabelle backend to use the rule of set extensionality.             *)
(***************************************************************************)
THEOREM SetExtensionality ==
  \A S, T : (\A x : (x \in S) <=> (x \in T)) => (S = T)

IsaWithSetExtensionality == TRUE
  (*{ by (prover:"isabelle"; tactic:"(auto intro: setEqualI)")}*)

(***************************************************************************)
(* The following theorem is needed to deduce NotInSetS \notin SetS from    *)
(* the definition                                                          *)
(*                                                                          *)
(*    NotInSetS == CHOOSE v : v \notin SetS                                *)
(***************************************************************************)
THEOREM NotInSetSAxiom == \A S : (CHOOSE v : v \notin S) \notin S

IsaWithChooseNotIn == TRUE
  (*{by (isabelle "(auto intro: inIrrefl)")}*)

(*******************************************************************)
(*******************************************************************)
(*******************************************************************)
(*******************************************************************)
(* Old versions of Zenon and Isabelle pragmas below                *)
(* (kept for compatibility)                                        *)
(*******************************************************************)

(*************************************************************************)
(* Backend pragma: Zenon with different timeouts (default is 10 seconds) *)
(*************************************************************************)
Zenon20  == TRUE (*{ by (prover:"zenon"; timeout:20) }*)
Zenon40  == TRUE (*{ by (prover:"zenon"; timeout:40) }*)
Zenon80  == TRUE (*{ by (prover:"zenon"; timeout:80) }*)
Zenon160 == TRUE (*{ by (prover:"zenon"; timeout:160) }*)

(*******************************************************************)
(* Backend pragma: Isabelle's automatic search ("auto")            *)
(*                                                                  *)
(* This pragma bypasses Zenon. It is useful in situations involving*)
(* essentially simplification and equational reasoning.            *)
(* Default imeout for all isabelle tactics is 30 seconds.          *)
(*******************************************************************)
Auto      == TRUE (*{ by (prover:"isabelle"; tactic:"auto") }*)
Auto120   == TRUE (*{ by (prover:"isabelle"; tactic:"auto"; timeout:120) }*)
Auto480   == TRUE (*{ by (prover:"isabelle"; tactic:"auto"; timeout:480) }*)
Auto960   == TRUE (*{ by (prover:"isabelle"; tactic:"auto"; timeout:960) }*)

(*******************************************************************)
(* Backend pragma: Isabelle's "force" tactic                       *)
(*                                                                  *)
(* This pragma bypasses Zenon. It is useful in situations involving*)
(* quantifier reasoning.                                           *)
(*******************************************************************)
Force      == TRUE (*{ by (prover:"isabelle"; tactic:"force") }*)
Force120   == TRUE (*{ by (prover:"isabelle"; tactic:"force"; timeout:120) }*)
Force480   == TRUE (*{ by (prover:"isabelle"; tactic:"force"; timeout:480) }*)
Force960   == TRUE (*{ by (prover:"isabelle"; tactic:"force"; timeout:960) }*)

(**********************************************************************)
(* Backend pragma: Isabelle's "simplification" tactics                *)
(*                                                                     *)
(* These tactics simplify the goal before running one of the automated*)
(* tactics. They are often necessary for obligations involving record *)
(* or tuple projections. Use the SimplfyAndSolve tactic unless you're *)
(* sure you can get away with just Simplification                     *)
(**********************************************************************)
SimplifyAndSolve     == TRUE (*{ by (prover:"isabelle"; tactic:"clarsimp auto?") }*)
SimplifyAndSolve120  == TRUE (*{ by (prover:"isabelle"; tactic:"clarsimp auto?"; timeout:120) }*)
SimplifyAndSolve480  == TRUE (*{ by (prover:"isabelle"; tactic:"clarsimp auto?"; timeout:480) }*)
SimplifyAndSolve960  == TRUE (*{ by (prover:"isabelle"; tactic:"clarsimp auto?"; timeout:960) }*)
Simplification       == TRUE (*{ by (prover:"isabelle"; tactic:"clarsimp") }*)
Simplification120    == TRUE (*{ by (prover:"isabelle"; tactic:"clarsimp"; timeout:120) }*)
Simplification480    == TRUE (*{ by (prover:"isabelle"; tactic:"clarsimp"; timeout:480) }*)
Simplification960    == TRUE (*{ by (prover:"isabelle"; tactic:"clarsimp"; timeout:960) }*)

(*************************************************************************)
(* Backend pragma: Isabelle's tableau prover ("blast")                   *)
(*                                                                        *)
(* This pragma bypasses Zenon and uses Isabelle's built-in theorem       *)
(* prover, Blast.                                                       *)
(*************************************************************************)
Blast        == TRUE (*{ by (prover:"isabelle"; tactic:"blast") }*)
Blast120     == TRUE (*{ by (prover:"isabelle"; tactic:"blast"; timeout:120) }*)
Blast480     == TRUE (*{ by (prover:"isabelle"; tactic:"blast"; timeout:480) }*)
Blast960     == TRUE (*{ by (prover:"isabelle"; tactic:"blast"; timeout:960) }*)
AutoBlast    == TRUE (*{ by (prover:"isabelle"; tactic:"auto, blast") }*)

(*************************************************************************)
(* Backend pragmas: multi-back-ends                                      *)
(*                                                                        *)
(* These pragmas just run a bunch of back-ends one after the other in    *)
(* the hope that one will succeed. This saves time and effort for the    *)
(* user at the expense of computation time.                              *)
(*************************************************************************)
\* CVC3 goes first because it's bundled with TLAPS, then the other SMT
\* solvers are unlikely to succeed if CVC3 fails, so we run zenon and
\* Isabelle before them.
SlowSolver == TRUE
  (*{
    by (prover:"cvc33")
    by (prover:"zenon")
    by (prover:"isabelle"; tactic:"auto")
    by (prover:"spass")
    by (prover:"smt3")
    by (prover:"yices3")
    by (prover:"verit")
    by (prover:"z33")
    by (prover:"isabelle"; tactic:"force")
    by (prover:"isabelle"; tactic:"(auto intro: setEqualI)")
    by (prover:"isabelle"; tactic:"clarsimp auto?")
    by (prover:"isabelle"; tactic:"clarsimp")
    by (prover:"isabelle"; tactic:"auto, blast")
   }*)

SlowSolverT(n) == TRUE
  (*{
    by (prover:"cvc33"; timeout:@)
    by (prover:"zenon"; timeout:@)
    by (prover:"isabelle"; tactic:"auto"; timeout:@)
    by (prover:"spass"; timeout:@)
    by (prover:"smt3"; timeout:@)
    by (prover:"yices3"; timeout:@)
    by (prover:"verit"; timeout:@)
    by (prover:"z33"; timeout:@)
    by (prover:"isabelle"; tactic:"force"; timeout:@)
    by (prover:"isabelle"; tactic:"(auto intro: setEqualI)"; timeout:@)
    by (prover:"isabelle"; tactic:"clarsimp auto?"; timeout:@)
    by (prover:"isabelle"; tactic:"clarsimp"; timeout:@)
    by (prover:"isabelle"; tactic:"auto, blast"; timeout:@)
   }*)

SMTSolver == TRUE
  (*{
    by (prover:"cvc33")
    by (prover:"smt3")
    by (prover:"yices3")
    by (prover:"verit")
    by (prover:"z33")
   }*)

SMTSolverT(n) == TRUE
  (*{
    by (prover:"cvc33"; timeout:@)
    by (prover:"smt3"; timeout:@)
    by (prover:"yices3"; timeout:@)
    by (prover:"verit"; timeout:@)
    by (prover:"z33"; timeout:@)
   }*)

IsaSolver == TRUE
  (*{
    by (prover:"isabelle"; tactic:"auto")
    by (prover:"isabelle"; tactic:"force")
    by (prover:"isabelle"; tactic:"(auto intro: setEqualI)")
    by (prover:"isabelle"; tactic:"clarsimp auto?")
    by (prover:"isabelle"; tactic:"clarsimp")
    by (prover:"isabelle"; tactic:"auto, blast")
   }*)

IsaSolverT(n) == TRUE
  (*{
    by (prover:"isabelle"; tactic:"auto"; timeout:@)
    by (prover:"isabelle"; tactic:"force"; timeout:@)
    by (prover:"isabelle"; tactic:"(auto intro: setEqualI)"; timeout:@)
    by (prover:"isabelle"; tactic:"clarsimp auto?"; timeout:@)
    by (prover:"isabelle"; tactic:"clarsimp"; timeout:@)
    by (prover:"isabelle"; tactic:"auto, blast"; timeout:@)
   }*)

(***************************************************************************)
(*                            TEMPORAL LOGIC                                *)
(*                                                                          *)
(* The following rules are intended to be used when TLAPS handles temporal *)
(* logic.  They will not work now.  Moreover when temporal reasoning is    *)
(* implemented, these rules may be changed or omitted, and additional      *)
(* rules will probably be added.  However, they are included mainly so     *)
(* their names will be defined, preventing the use of identifiers that are *)
(* likely to produce name clashes with future versions of this module.     *)
(***************************************************************************)

(***************************************************************************)
(* The following proof rules (and their names) are from the paper "The     *)
(* Temporal Logic of Actions".                                             *)
(***************************************************************************)
RuleINV1 ==
  ASSUME NEW TEMPORAL I, NEW ACTION N, NEW STATE v,
         I /\ [N]_v => I'
  PROVE  I /\ [][N]_v => []I

RuleINV2 ==
  ASSUME NEW STATE I, NEW ACTION N, NEW STATE v
  PROVE  []I => ([][N]_v <=> [][N /\ I /\ I']_v)

RuleTLA1 ==
  ASSUME NEW STATE P, NEW ACTION A, NEW STATE f,
         P /\ (f' = f) => P',
         P /\ <<A>>_f => P'
  PROVE  []P <=> P /\ [][P => P']_f

RuleTLA2 ==
  ASSUME NEW ACTION A, NEW ACTION B,
         NEW STATE f, NEW STATE g,
         NEW STATE P, NEW STATE Q,
         P /\ [A]_f => Q /\ [B]_g
  PROVE  []P /\ [][A]_f => []Q /\ [][B]_g

(***************************************************************************)
(* The rules WF2 and SF2 in "The Temporal Logic of Actions" are obtained   *)
(* from the following two rules by the following substitutions: `.         *)
(*                                                                          *)
(*    ___        ___         _______________                                *)
(*    M <- M ,   g <- g ,  EM <- ENABLED <<M>>_g       .'                  *)
(***************************************************************************)
RuleWF1 ==
  ASSUME NEW STATE P, NEW STATE Q,
         NEW ACTION N, NEW ACTION A, NEW STATE v,
         P /\ [N]_v => P' \/ Q',
         P /\ <<N /\ A>>_v => Q',
         P => ENABLED <<A>>_v
  PROVE  [][N]_v /\ WF_v(A) => (P ~> Q)

RuleSF1 ==
  ASSUME NEW STATE P, NEW STATE Q,
         NEW ACTION N, NEW ACTION A, NEW STATE v,
         NEW TEMPORAL F,
         P /\ [N]_v => P' \/ Q',
         P /\ <<N /\ A>>_v => Q',
         []P /\ []F => <>ENABLED <<A>>_v
  PROVE  [][N]_v /\ SF_v(A) /\ []F => (P ~> Q)

(***************************************************************************)
(* The following rule is a special case of the general temporal logic     *)
(* proof rule STL4 from the paper "The Temporal Logic of Actions".  The    *)
(* general rule is for arbitrary temporal formulas F and G, but it cannot  *)
(* yet be handled by TLAPS.                                                *)
(***************************************************************************)
RuleSTL4 ==
  ASSUME NEW STATE F, NEW STATE G, F => G
  PROVE  []F => []G

(***************************************************************************)
(* The following rule is a special case of rule TLA2 from the paper "The   *)
(* Temporal Logic of Actions".                                             *)
(***************************************************************************)
RuleTLA2Simple ==
  ASSUME NEW ACTION A, NEW STATE f, NEW STATE P,
         P /\ [A]_f => P'
  PROVE  []P /\ [][A]_f => [][A /\ P /\ P']_f

(***************************************************************************)
(* The following may be used to invoke a decision procedure for            *)
(* propositional temporal logic.                                           *)
(***************************************************************************)
PTLDecisionProcedure == PTL
====
