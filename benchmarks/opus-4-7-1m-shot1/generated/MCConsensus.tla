---- MODULE MCConsensus ----
(***************************************************************************)
(* Checking                                                                *)
(*                                                                         *)
(*    Inv /\ [Next]_chosen => Inv'                                         *)
(*                                                                         *)
(* which is equivalent to checking                                         *)
(*                                                                         *)
(*    Inv /\ [][Next]_chosen => []Inv                                      *)
(*                                                                         *)
(* which asserts that Inv is an invariant of the spec                      *)
(*                                                                         *)
(*    Inv /\ [][Next]_chosen                                               *)
(***************************************************************************)
EXTENDS Consensus

Inv ==
  /\ TypeOK
  /\ Cardinality(chosen) \leq 1

ISpec == Inv /\ [][Next]_chosen
====
