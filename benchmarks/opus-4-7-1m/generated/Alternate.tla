---- MODULE Alternate ----
(***************************************************************************)
(* Generated at Sat Oct 31 02:58:46 PDT 2009                               *)
(*                                                                         *)
(* This specifies a system that alternately performs two actions, which   *)
(* we call A_0 and A_1. It uses a variable v whose value alternates       *)
(* between 0 and 1: performs A_0 when v changes from 0 to 1, and A_1 when *)
(* v changes from 1 to 0.                                                 *)
(*                                                                         *)
(* The variable x represents the part of the state changed by A_0 and    *)
(* A_1. XInit(x) asserts x has a correct initial value, and              *)
(* XAct(i, xInit, xNext) asserts changing x from xInit to xNext is an    *)
(* A_i action, for i = 0, 1.                                              *)
(*                                                                         *)
(* A philosophically correct spec would actually be                       *)
(*    \EE v : Spec                                                        *)
(* the specification Spec with v hidden. We don't bother hiding here.     *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS XInit(_), XAct(_, _, _)

VARIABLES x, v

vars == <<x, v>>

Init ==
    /\ XInit(x)
    /\ v = 0

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

TypeOK == v \in {0, 1}

\* The alternation invariant: A_0 happens exactly when v transitions 0 -> 1
\* and A_1 exactly when v transitions 1 -> 0. This is captured by Next.

====
