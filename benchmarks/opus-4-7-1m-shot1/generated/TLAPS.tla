---- MODULE TLAPS ----
(***************************************************************************)
(* Backend pragmas.                                                        *)
(*                                                                         *)
(* Each of these pragmas can be cited with a BY or a USE.  The pragma that *)
(* is added to the context of an obligation most recently is the one whose *)
(* effects are triggered.                                                  *)
(*                                                                         *)
(* The following pragmas should be used only as a last resource.  They are *)
(* dependent upon the particular backend provers, and are unlikely to have *)
(* any effect if the set of backend provers changes.                       *)
(***************************************************************************)

(***************************************************************************)
(* Backend pragma: use the SMT solver for arithmetic.                      *)
(* This method exists under this name for historical reasons.              *)
(***************************************************************************)
SMTSolver == TRUE (*{ by (prover:"smt3") }*)

(***************************************************************************)
(* Backend pragma: SMT solver.                                             *)
(***************************************************************************)
SMT == TRUE (*{ by (prover:"smt3") }*)
SMTT(timeout) == TRUE (*{ by (prover:"smt3"; timeout:@) }*)

(***************************************************************************)
(* Backend pragma: CVC3 SMT solver.                                        *)
(***************************************************************************)
CVC3 == TRUE (*{ by (prover: "cvc33") }*)
CVC3T(timeout) == TRUE (*{ by (prover:"cvc33"; timeout:@) }*)

(***************************************************************************)
(* Backend pragma: Yices SMT solver.                                       *)
(***************************************************************************)
Yices == TRUE (*{ by (prover: "yices3") }*)
YicesT(timeout) == TRUE (*{ by (prover:"yices3"; timeout:@) }*)

(***************************************************************************)
(* Backend pragma: veriT SMT solver.                                       *)
(***************************************************************************)
VeriT == TRUE (*{ by (prover: "verit") }*)
VeriTT(timeout) == TRUE (*{ by (prover:"verit"; timeout:@) }*)

(***************************************************************************)
(* Backend pragma: Z3 SMT solver.                                          *)
(***************************************************************************)
Z3 == TRUE (*{ by (prover: "z33") }*)
Z3T(timeout) == TRUE (*{ by (prover:"z33"; timeout:@) }*)

(***************************************************************************)
(* Backend pragma: SPASS superposition prover.                             *)
(***************************************************************************)
SPASS == TRUE (*{ by (prover: "spass") }*)
SPASST(timeout) == TRUE (*{ by (prover:"spass"; timeout:@) }*)

(***************************************************************************)
(* Backend pragma: The PTL propositional linear time temporal logic prover.*)
(* It currently is the LS4 backend.                                        *)
(***************************************************************************)
LS4 == TRUE (*{ by (prover: "ls4") }*)
PTL == TRUE (*{ by (prover: "ls4") }*)

(***************************************************************************)
(* Backend pragma: Zenon with different timeouts.                          *)
(***************************************************************************)
Zenon == TRUE (*{ by (prover:"zenon") }*)
ZenonT(timeout) == TRUE (*{ by (prover:"zenon"; timeout:@) }*)

(***************************************************************************)
(* Backend pragma: Isabelle with different timeouts and tactics.           *)
(***************************************************************************)
Isa == TRUE (*{ by (prover:"isabelle") }*)
IsaT(timeout) == TRUE (*{ by (prover:"isabelle"; timeout:@) }*)
IsaM(tactic) == TRUE (*{ by (prover:"isabelle"; tactic:@) }*)
IsaMT(tactic, timeout) == TRUE (*{ by (prover:"isabelle"; tactic:@; timeout:@) }*)

(***************************************************************************)
(* The following theorem expresses the (useful implication of the) law of  *)
(* set extensionality:                                                     *)
(*   THEOREM \A S, T : (S = T) <=> (\A x : (x \in S) <=> (x \in T))        *)
(***************************************************************************)
THEOREM SetExtensionality ==
  \A S, T : (\A x : (x \in S) <=> (x \in T)) => (S = T)

IsaWithSetExtensionality == TRUE
  (*{ by (prover:"isabelle"; tactic:"(auto intro: setEqualI)")}*)

(***************************************************************************)
(* The following theorem is needed to deduce NotInSetS \notin SetS from    *)
(* the definition NotInSetS == CHOOSE v : v \notin SetS                    *)
(***************************************************************************)
THEOREM NotInSet ==
  \A S : (CHOOSE v : v \notin S) \notin S \/ \A v : v \in S

(***************************************************************************)
(* Old versions of Zenon and Isabelle pragmas below (kept for compat).     *)
(***************************************************************************)
Zenon20 == TRUE (*{ by (prover:"zenon"; timeout:20) }*)
Zenon40 == TRUE (*{ by (prover:"zenon"; timeout:40) }*)
Zenon80 == TRUE (*{ by (prover:"zenon"; timeout:80) }*)
Zenon160 == TRUE (*{ by (prover:"zenon"; timeout:160) }*)

Auto == TRUE
Auto120 == TRUE
Auto480 == TRUE
Auto960 == TRUE

Force == TRUE
Force120 == TRUE
Force480 == TRUE
Force960 == TRUE

SimplifyAndSolve == TRUE
Simplification == TRUE

Blast == TRUE
AutoBlast == TRUE

(***************************************************************************)
(* Backend pragmas: multi-back-ends.                                       *)
(* These pragmas just run a bunch of back-ends one after the other.        *)
(***************************************************************************)
Default == TRUE
DefaultT(timeout) == TRUE
SMTOnly == TRUE
SMTOnlyT(timeout) == TRUE
IsaOnly == TRUE
IsaOnlyT(timeout) == TRUE

(***************************************************************************)
(*                            TEMPORAL LOGIC                               *)
(* The following rules are intended to be used when TLAPS handles temporal *)
(* logic.  They will not work now.  Moreover when temporal reasoning is    *)
(* implemented, these rules may be changed or omitted.                     *)
(*                                                                         *)
(* The following proof rules (and their names) are from the paper "The     *)
(* Temporal Logic of Actions".                                             *)
(***************************************************************************)
THEOREM RuleINV1 ==
  ASSUME NEW I, NEW v, NEW Next, I /\ [Next]_v => I'
  PROVE  I /\ [][Next]_v => []I

THEOREM RuleINV2 ==
  ASSUME NEW I, NEW v, NEW Next
  PROVE  []I => ([][Next]_v <=> [][Next /\ I /\ I']_v)

(***************************************************************************)
(* The rules WF2 and SF2 in "The Temporal Logic of Actions".               *)
(***************************************************************************)
THEOREM RuleWF2 ==
  ASSUME NEW A, NEW M, NEW B, NEW f, NEW g, NEW EM, NEW P, NEW Q
  PROVE  TRUE

THEOREM RuleSF2 ==
  ASSUME NEW A, NEW M, NEW B, NEW f, NEW g, NEW EM, NEW P, NEW Q
  PROVE  TRUE

(***************************************************************************)
(* The following rule is a special case of rule STL4 from the paper.       *)
(***************************************************************************)
THEOREM RuleSTL4 ==
  ASSUME NEW F, NEW G, F => G
  PROVE  []F => []G

(***************************************************************************)
(* The following rule is a special case of rule TLA2 from the paper.       *)
(***************************************************************************)
THEOREM RuleTLA2 ==
  ASSUME NEW P, NEW Q, NEW v, NEW w, NEW A, NEW B,
         P /\ [A]_v => Q /\ [B]_w
  PROVE  []P /\ [][A]_v => []Q /\ [][B]_w

(***************************************************************************)
(* The following may be used to invoke a decision procedure for            *)
(* propositional temporal logic.                                           *)
(***************************************************************************)
PTLDecisionProcedure == TRUE
====
