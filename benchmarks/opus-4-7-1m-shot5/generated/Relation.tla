---- MODULE Relation ----
(***************************************************************************)
(* This module provides some basic operations on relations, represented    *)
(* as binary Boolean functions over some set S.                            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

(***************************************************************************)
(* Is the relation R reflexive over S?                                     *)
(***************************************************************************)
IsReflexive(R, S) == \A x \in S : R[x, x]

(***************************************************************************)
(* Is the relation R irreflexive over set S?                               *)
(***************************************************************************)
IsIrreflexive(R, S) == \A x \in S : ~ R[x, x]

(***************************************************************************)
(* Is the relation R symmetric over set S?                                 *)
(***************************************************************************)
IsSymmetric(R, S) == \A x, y \in S : R[x, y] <=> R[y, x]

(***************************************************************************)
(* Is the relation R asymmetric over set S?                                *)
(***************************************************************************)
IsAsymmetric(R, S) == \A x, y \in S : ~ (R[x, y] /\ R[y, x])

(***************************************************************************)
(* Is the relation R transitive over set S?                                *)
(***************************************************************************)
IsTransitive(R, S) ==
  \A x, y, z \in S : R[x, y] /\ R[y, z] => R[x, z]

(***************************************************************************)
(* Compute the transitive closure of relation R over set S.                *)
(***************************************************************************)
TransitiveClosure(R, S) ==
  LET tc[n \in Nat] ==
        IF n = 0
        THEN R
        ELSE [x, y \in S |->
                \/ tc[n-1][x, y]
                \/ \E z \in S : tc[n-1][x, z] /\ tc[n-1][z, y]]
  IN  tc[Cardinality(S)]

(***************************************************************************)
(* Compute the reflexive transitive closure of relation R over set S.      *)
(***************************************************************************)
ReflexiveTransitiveClosure(R, S) ==
  LET TC == TransitiveClosure(R, S)
  IN  [x, y \in S |-> (x = y) \/ TC[x, y]]

(***************************************************************************)
(* Is the relation R connected over set S, i.e. does there exist a path    *)
(* between two arbitrary elements of S?                                    *)
(***************************************************************************)
IsConnected(R, S) ==
  LET RTC == ReflexiveTransitiveClosure(R, S)
  IN  \A x, y \in S : RTC[x, y]

(***************************************************************************)
(* Modification History                                                   *)
(* Last modified Sun Jun 14 15:32:47 CEST 2020 by merz                    *)
(* Created Tue Apr 26 10:24:07 CEST 2016 by merz                          *)
(***************************************************************************)
====
