---- MODULE TwoPhase ----
(***************************************************************************)
(* Generated at Sat Oct 31 03:15:55 PDT 2009                              *)
(*                                                                         *)
(* This module specifies the two-phase handshake, which is a simple but    *)
(* very important hardware protocol by which a Producer process and a      *)
(* Consumer process alternately perform actions, with the Producer going   *)
(* first.  The system is pictured as follows:                              *)
(*                                                                         *)
(*  `.                                                                     *)
(*       ------------           p          ------------                    *)
(*       |            | -----------------> |            |                  *)
(*       |  Producer  |                    |  Consumer  |                  *)
(*       |            | <----------------- |            |                  *)
(*       ------------           c          ------------    .'              *)
(*                                                                         *)
(* In the spec, we represent the Producer and Consumer actions the way we  *)
(* represented the actions A_0 and A_1 of the Alternate specification.  We *)
(* then show that this specification implements the Alternate              *)
(* specification under a suitable refinement mapping (substitution for the *)
(* variable v).                                                            *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS XInit(_), XAct(_, _, _)

VARIABLES p, c, x

vars == <<p, c, x>>

Init ==
  /\ XInit(x)
  /\ p = 0
  /\ c = 0

PAction ==
  /\ p = c
  /\ p' = 1 - p
  /\ XAct(0, x, x')
  /\ UNCHANGED c

CAction ==
  /\ c # p
  /\ c' = 1 - c
  /\ XAct(1, x, x')
  /\ UNCHANGED p

Next == PAction \/ CAction

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Inv is the invariant that is needed for the proof.                      *)
(***************************************************************************)
Inv ==
  /\ p \in {0,1}
  /\ c \in {0,1}

(***************************************************************************)
(* We prove that specification Spec implement (implies) the specification  *)
(* obtained by substiting a state function vBar for the variable v, where  *)
(* vBar is defined as follows.                                             *)
(***************************************************************************)
vBar == IF p = c THEN 0 ELSE 1

(***************************************************************************)
(* The following statement imports, for every defined operator D of module *)
(* Alternate, a definition of A!D to equal the definition of D with vBar   *)
(* substituted for v and with the parameters x, XInit, and XAct of this    *)
(* module substituted for the parameters of the same name of module        *)
(* Alternate.  Thus, A!Spec is defined to be the formula Spec of module    *)
(* Alternate with vBar substituted for v.                                  *)
(***************************************************************************)
A == INSTANCE Alternate WITH v <- vBar

(***************************************************************************)
(* The following theorem is a standard proof that one specification        *)
(* implements (the safety part of) another specification under a           *)
(* refinement mapping.  In fact, the temporal leaf proofs will be exactly  *)
(* the same one-liners for every such proof.  In realistic example, the    *)
(* non-temporal leaf proofs will be replaced by fairly long structured     *)
(* proofs--especially the two substeps numbered <2>2.                      *)
(***************************************************************************)
THEOREM Spec => A!Spec
  <1>1. Init => A!Init
    BY DEF Init, A!Init, vBar
  <1>2. Inv /\ [Next]_vars => [A!Next]_<<x, vBar>>
    BY DEF Next, A!Next, PAction, CAction, A!A, vBar, vars
  <1>3. Spec => []Inv
    <2>1. Init => Inv
      BY DEF Init, Inv
    <2>2. Inv /\ [Next]_vars => Inv'
      BY DEF Inv, Next, PAction, CAction, vars
    <2>3. QED
      BY <2>1, <2>2, PTL DEF Spec
  <1>4. QED
    BY <1>1, <1>2, <1>3, PTL DEF Spec, A!Spec

====
