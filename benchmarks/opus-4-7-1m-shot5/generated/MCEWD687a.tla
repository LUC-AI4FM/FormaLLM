---- MODULE MCEWD687a ----
(***************************************************************************)
(* TLA+ model for model-checking the EWD687a termination detection         *)
(* algorithm.                                                              *)
(*                                                                         *)
(* MV CONSTANT declarations@modelParameterConstants                        *)
(* MV CONSTANT definitions Procs                                           *)
(* CONSTANT definitions @modelParameterConstants:1Edges                    *)
(* CONSTANT definitions @modelParameterConstants:2Leader                   *)
(* CONSTRAINT definition @modelParameterContraint:0                        *)
(*                                                                         *)
(* Modification History                                                    *)
(* Created Fri Oct 01 12:28:54 PDT 2021 by lamport                        *)
(***************************************************************************)
EXTENDS EWD687a

CONSTANTS L, P1, P2, P3

const_1633116534008310000 == {L, P1, P2, P3}
const_1633116534008311000 == {<<L,P1>>, <<L,P2>>, <<P1,P3>>, <<P2,P3>>,
                              <<P1,L>>, <<P2,L>>, <<P3,P1>>, <<P3,P2>>}
const_1633116534008312000 == L

constr_1633116534008313000 ==
  \A p \in Procs : counter[p] \in -3..3

====
