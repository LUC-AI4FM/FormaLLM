---- MODULE Alternate ----
\* This specifies a system that alternately performs two actions, which
\* for now I will call A_0 and A_1.  It uses a variable v whose value
\* alternates between 0 and 1, performing an A_0 action when v changes
\* from 0 to 1, and an A_1 action when v changes from 1 to 0.
\*
\* We let the variable x represent the part of the state that is changed
\* by the A_0 and A_1 actions.  We introduce two constant operators XInit
\* and XAct, where XInit(x) is assumed to assert that x has a correct
\* initial value, and XAct(i, xInit, xNext) is assumed to assert that
\* changing the value of x from xInit to xNext represents an A_i action,
\* for i = 0, 1.
\*
\* A philosophically correct spec would actually be
\*     \EE v : Spec
\* which is the specification Spec with v hidden.  However, engineers are
\* interested in what works, not what is philosophically correct, so we
\* don't worry about this.

EXTENDS Naturals

CONSTANTS XInit(_), XAct(_, _, _)

VARIABLES x, v

vars == <<x, v>>

Init == /\ XInit(x)
        /\ v = 0

A0 == /\ v = 0
      /\ v' = 1
      /\ XAct(0, x, x')

A1 == /\ v = 1
      /\ v' = 0
      /\ XAct(1, x, x')

Next == A0 \/ A1

Spec == Init /\ [][Next]_vars

====
