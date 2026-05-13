---- MODULE TwoPhase ----
\* Two-phase handshake protocol. A Producer and a Consumer alternate
\* actions, the Producer going first. We model the two channels p and c.
\* This spec refines the Alternate specification under a refinement
\* mapping that substitutes vBar for v.

EXTENDS Naturals

CONSTANTS XInit(_), XAct(_, _, _)

VARIABLES x, p, c

vars == <<x, p, c>>

Init == /\ XInit(x)
        /\ p = 0
        /\ c = 0

\* Producer action: p and c are equal, producer toggles p to differ from c.
Produce == /\ p = c
           /\ p' = 1 - p
           /\ XAct(0, x, x')
           /\ UNCHANGED c

\* Consumer action: p differs from c, consumer toggles c to match p.
Consume == /\ p # c
           /\ c' = 1 - c
           /\ XAct(1, x, x')
           /\ UNCHANGED p

Next == Produce \/ Consume

Spec == Init /\ [][Next]_vars

\* The invariant Inv is needed for the proof of the refinement.
Inv == /\ p \in {0, 1}
       /\ c \in {0, 1}

\* The state function vBar is the value of v in the Alternate spec under
\* the refinement mapping.
vBar == IF p = c THEN 0 ELSE 1

\* Import the operators of Alternate under the refinement mapping.
A == INSTANCE Alternate WITH v <- vBar

\* The refinement theorem: Spec implements A!Spec.
THEOREM Spec => A!Spec
====
