---- MODULE MCConsensus ----
(***************************************************************************)
(* Model-checking wrapper for Consensus. Provides concrete values for the *)
(* CONSTANT Value used by Consensus.                                      *)
(*                                                                         *)
(* Modification History                                                    *)
(*   Created Mon Jun 10 07:38:26 PDT 2019 by lamport                       *)
(***************************************************************************)
EXTENDS Consensus

CONSTANTS a, b, c

const_Value == {a, b, c}
====
