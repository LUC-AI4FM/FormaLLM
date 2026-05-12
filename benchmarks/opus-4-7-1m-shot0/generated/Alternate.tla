---- MODULE Alternate ----
\* This specifies a system that alternately performs two actions, A_0 and A_1.
\* It uses a variable v whose value alternates between 0 and 1, performing an
\* A_0 action when v changes from 0 to 1, and an A_1 action when v changes
\* from 1 to 0.
\*
\* The variable x represents the part of the state that is changed by the A_0
\* and A_1 actions. The constant operators XInit and XAct are user-supplied:
\*   XInit(x)                : x has a correct initial value
\*   XAct(i, xInit, xNext)   : changing x from xInit to xNext is an A_i action.
\*
\* A philosophically correct spec would hide v with \EE v : Spec; we don't
\* bother here.

EXTENDS Naturals

CONSTANTS XInit(_), XAct(_, _, _)

VARIABLES v, x

vars == << v, x >>

Init ==
  /\ v = 0
  /\ XInit(x)

A0 ==
  /\ v = 0
  /\ v' = 1
  /\ XAct(0, x, x')

A1 ==
  /\ v = 1
  /\ v' = 0
  /\ XAct(1, x, x')

Next == A0 \/ A1

Spec == Init /\ [][Next]_vars

\* Type invariant on v.
TypeOK == v \in {0, 1}

\* Alternation: consecutive states never share the same v value when an
\* action occurs.
Alternation == [][v' /= v]_vars

====
