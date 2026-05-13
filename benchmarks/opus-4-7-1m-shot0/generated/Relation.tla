---- MODULE Relation ----
\* This module provides some basic operations on relations, represented as
\* binary Boolean functions over some set S.  A relation R is treated as a
\* function S \X S -> BOOLEAN, i.e. R[x,y] is TRUE iff x is related to y.
\*
\* Last modified Sun Jun 14 15:32:47 CEST 2020 by merz
\* Created Tue Apr 26 10:24:07 CEST 2016 by merz

EXTENDS Naturals, FiniteSets

\* Is R a binary relation over S?
IsRelation(R, S) == R \in [S \X S -> BOOLEAN]

\* Is the relation R reflexive over S?
IsReflexive(R, S) == \A x \in S : R[x,x]

\* Is the relation R irreflexive over S?
IsIrreflexive(R, S) == \A x \in S : ~ R[x,x]

\* Is the relation R symmetric over S?
IsSymmetric(R, S) ==
  \A x, y \in S : R[x,y] => R[y,x]

\* Is the relation R asymmetric over S?
IsAsymmetric(R, S) ==
  \A x, y \in S : R[x,y] => ~ R[y,x]

\* Is the relation R antisymmetric over S?
IsAntisymmetric(R, S) ==
  \A x, y \in S : (R[x,y] /\ R[y,x]) => (x = y)

\* Is the relation R transitive over S?
IsTransitive(R, S) ==
  \A x, y, z \in S : (R[x,y] /\ R[y,z]) => R[x,z]

\* Compute the transitive closure of R over S as the least fixed point.
\* The transitive closure connects x to y if there is a non-empty sequence
\* x = a_0, a_1, ..., a_n = y with all (a_i, a_{i+1}) in R.
TransitiveClosure(R, S) ==
  LET TCstep[k \in Nat] ==
        IF k = 0 THEN R
        ELSE [<<x,y>> \in S \X S |->
                \/ TCstep[k-1][x,y]
                \/ \E z \in S : TCstep[k-1][x,z] /\ R[z,y]]
  IN TCstep[Cardinality(S)]

\* Compute the reflexive transitive closure of R over S.
ReflexiveTransitiveClosure(R, S) ==
  [<<x,y>> \in S \X S |-> (x = y) \/ TransitiveClosure(R, S)[x,y]]

\* Is R connected over S? I.e. there is a path between any two elements.
IsConnected(R, S) ==
  LET RTC == ReflexiveTransitiveClosure(R, S)
  IN  \A x, y \in S : RTC[x,y]

\* Is R an equivalence relation over S?
IsEquivalence(R, S) ==
  /\ IsReflexive(R, S)
  /\ IsSymmetric(R, S)
  /\ IsTransitive(R, S)

\* Is R a partial order over S?
IsPartialOrder(R, S) ==
  /\ IsReflexive(R, S)
  /\ IsAntisymmetric(R, S)
  /\ IsTransitive(R, S)

====
