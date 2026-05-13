---- MODULE SimpleRegular ----
(***************************************************************************)
(* This is a minor modification of the algorithm in module Simple.  That   *)
(* algorithm is an N-process algorithm shared-memory algorithm, in which   *)
(* each process i has a shared register x[i] that it writes and is read by *)
(* process x[(i-1) % N].  Each process i also has a local register y[i]    *)
(* that only it can access.                                                *)
(*                                                                         *)
(* The shared registers x[i] in the algorithm of module Simple are assumed *)
(* to be atomic, effectively meaning that each read or write by any        *)
(* process is an atomic action.  In the algorithm in this module, the     *)
(* x[i] are assumed to be a weaker class of registers called regular      *)
(* registers.                                                              *)
(*                                                                         *)
(* A regular register r can be modeled in a TLA+ spec modeled as a         *)
(* variable rv that equals a set of values.                                *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLAPS

CONSTANTS N

ASSUME N \in Nat /\ N > 0

(***************************************************************************
--algorithm SimpleRegular {
  variables x = [i \in 0..(N-1) |-> {0}], y = [i \in 0..(N-1) |-> 0] ;
  process (proc \in 0..N-1) {
    a1: x[self] := {0,1} ;
    a2: x[self] := {1} ;
    b:  with (v \in x[(self-1) % N]) {y[self] := v }
  }
}
 ***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == 0..N-1

Init == /\ x = [i \in 0..(N-1) |-> {0}]
        /\ y = [i \in 0..(N-1) |-> 0]
        /\ pc = [self \in ProcSet |-> "a1"]

a1(self) == /\ pc[self] = "a1"
            /\ x' = [x EXCEPT ![self] = {0, 1}]
            /\ pc' = [pc EXCEPT ![self] = "a2"]
            /\ UNCHANGED y

a2(self) == /\ pc[self] = "a2"
            /\ x' = [x EXCEPT ![self] = {1}]
            /\ pc' = [pc EXCEPT ![self] = "b"]
            /\ UNCHANGED y

b(self) == /\ pc[self] = "b"
           /\ \E v \in x[(self - 1) % N] :
                y' = [y EXCEPT ![self] = v]
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED x

proc(self) == a1(self) \/ a2(self) \/ b(self)

Next == (\E self \in ProcSet : proc(self))
        \/ (\A self \in ProcSet : pc[self] = "Done") /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars
\* END TRANSLATION

(***************************************************************************)
(* The definition of PCorrect is the same as in module Simple.             *)
(***************************************************************************)
PCorrect ==
  (\A self \in ProcSet : pc[self] = "Done") =>
    \E i \in ProcSet : y[i] = 1

(***************************************************************************)
(* The type invariant TypeOK is the obvious modification of the type       *)
(* invariant TypeOK of module Simple.                                      *)
(***************************************************************************)
TypeOK ==
  /\ x \in [0..(N-1) -> SUBSET {0, 1}]
  /\ y \in [0..(N-1) -> {0, 1}]
  /\ pc \in [ProcSet -> {"a1", "a2", "b", "Done"}]
  /\ \A i \in 0..(N-1) : x[i] # {}

(***************************************************************************)
(* Inductive invariant Inv.                                                *)
(***************************************************************************)
Inv ==
  /\ TypeOK
  /\ \A i \in ProcSet :
       /\ (pc[i] = "a1") => (x[i] = {0})
       /\ (pc[i] \in {"b", "Done"}) => (1 \in x[i])
  /\ PCorrect

====
