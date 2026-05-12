---- MODULE MCEWD687a ----
(***************************************************************************)
(* MV CONSTANT declarations@modelParameterConstants                        *)
(* MV CONSTANT definitions Procs                                           *)
(* CONSTANT definitions @modelParameterConstants:1 Edges                   *)
(* CONSTANT definitions @modelParameterConstants:2 Leader                  *)
(* CONSTRAINT definition @modelParameterContraint:0                        *)
(* Modification History                                                    *)
(* Created Fri Oct 01 12:28:54 PDT 2021 by lamport                         *)
(***************************************************************************)
EXTENDS EWD687a, TLC

CONSTANTS L, P1, P2, P3

const_1633116534008310000 == {L, P1, P2, P3}

const_1633116534008311000 ==
  { <<L, P1>>, <<P1, L>>,
    <<L, P2>>, <<P2, L>>,
    <<P1, P3>>, <<P3, P1>>,
    <<P2, P3>>, <<P3, P2>> }

const_1633116534008312000 == L

constr_1633116534008313000 ==
  TRUE

====
