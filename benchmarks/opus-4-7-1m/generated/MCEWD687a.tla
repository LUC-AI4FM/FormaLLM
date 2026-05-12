---- MODULE MCEWD687a ----
(***************************************************************************)
(* Model-checking wrapper for EWD687a (detection of termination in        *)
(* distributed computations). This module fixes concrete values for the   *)
(* CONSTANTS Procs, Edges, and Leader, and supplies a state constraint    *)
(* for bounded model checking.                                            *)
(*                                                                         *)
(* Modification History                                                    *)
(*   Created Fri Oct 01 12:28:54 PDT 2021 by lamport                       *)
(***************************************************************************)
EXTENDS EWD687a

CONSTANTS L, P1, P2, P3

const_Procs == {L, P1, P2, P3}

const_Edges == { <<L, P1>>, <<L, P2>>, <<P1, P3>>, <<P2, P3>> }

const_Leader == L

\* A simple state-space-bounding constraint.
const_Constraint == TRUE
====
