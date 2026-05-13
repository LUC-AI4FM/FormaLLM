---- MODULE MCDieHarder ----
(***************************************************************************)
(* Model-checking wrapper for DieHarder. Defines concrete values for the   *)
(* constant parameters Jug and Capacity that the DieHarder module needs.   *)
(* The .cfg file substitutes MCJug for Jug and MCCapacity for Capacity.    *)
(***************************************************************************)
EXTENDS DieHarder

MCJug == {"a", "b", "c"}

MCCapacity == [j \in MCJug |-> CASE j = "a" -> 5
                                 [] j = "b" -> 8
                                 [] j = "c" -> 3]
====
