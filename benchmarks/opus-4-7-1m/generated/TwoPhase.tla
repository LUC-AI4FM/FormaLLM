---- MODULE TwoPhase ----
(***************************************************************************)
(* Generated at Sat Oct 31 03:15:55 PDT 2009                               *)
(*                                                                         *)
(* This module specifies the two-phase handshake, a simple but important  *)
(* hardware protocol in which a Producer process and a Consumer process   *)
(* alternately perform actions, the Producer going first.                 *)
(*                                                                         *)
(*    ------------           p          ------------                      *)
(*    |          | -----------------> |          |                        *)
(*    | Producer |                    | Consumer |                        *)
(*    |          | <----------------- |          |                        *)
(*    ------------           c          ------------                      *)
(*                                                                         *)
(* Producer and Consumer actions are represented analogously to A_0 and  *)
(* A_1 of the Alternate specification. We show that Spec implements      *)
(* Alternate under a suitable refinement mapping.                         *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS XInit(_), XAct(_, _, _)

VARIABLES x, p, c

vars == <<x, p, c>>

Init ==
    /\ XInit(x)
    /\ p = 0
    /\ c = 0

\* Producer action: bumps p when p = c, performing A_0 on x.
Produce ==
    /\ p = c
    /\ p' = 1 - p
    /\ XAct(0, x, x')
    /\ UNCHANGED c

\* Consumer action: bumps c when p /= c, performing A_1 on x.
Consume ==
    /\ p /= c
    /\ c' = 1 - c
    /\ XAct(1, x, x')
    /\ UNCHANGED p

Next == Produce \/ Consume

Spec == Init /\ [][Next]_vars

\* Inv is the invariant needed for the proof of refinement.
Inv == p \in {0, 1} /\ c \in {0, 1}

TPTypeOK == Inv

\* Define vBar as a function of p and c so we can refine Alternate.
\* When p = c, the next producer action is pending => Alternate's v = 0.
\* When p /= c, the next consumer action is pending => Alternate's v = 1.
vBar == IF p = c THEN 0 ELSE 1

\* Instantiate Alternate with vBar substituted for v.
A == INSTANCE Alternate WITH v <- vBar, x <- x, XInit <- XInit, XAct <- XAct

\* The refinement theorem.
THEOREM Spec => A!Spec

TPSpec == Spec
====
