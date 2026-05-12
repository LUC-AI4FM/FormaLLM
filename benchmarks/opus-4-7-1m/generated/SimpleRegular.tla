---- MODULE SimpleRegular ----
(***************************************************************************)
(* Minor modification of the algorithm in module Simple. An N-process     *)
(* shared-memory algorithm: each process i has a shared register x[i] it  *)
(* writes, read by process (i-1) % N. Each process has a local y[i].      *)
(*                                                                         *)
(* The x[i] here are regular (not atomic) registers: a read overlapping a *)
(* set of writes obtains either the prior value or one of the in-flight   *)
(* values. Modeled by letting x[i] be a SET of values; writing v after w  *)
(* transitions x[i] from {w} to {w, v} to {v}. A read picks any element.  *)
(*                                                                         *)
(* From Yuri Abraham, "On Lamport's Teaching Concurrency", EATCS No. 127  *)
(* February 2019.                                                          *)
(*                                                                         *)
(* PlusCal source:                                                         *)
(*   --algorithm SimpleRegular {                                          *)
(*     variables x = [i \in 0..(N-1) |-> {0}], y = [i \in 0..(N-1) |-> 0]; *)
(*     process (proc \in 0..N-1) {                                        *)
(*       a1: x[self] := {0,1} ;                                           *)
(*       a2: x[self] := {1} ;                                             *)
(*       b:  with (v \in x[(self-1) % N]) { y[self] := v }                *)
(*     }                                                                  *)
(*   }                                                                    *)
(***************************************************************************)
EXTENDS Integers

CONSTANT N

ASSUME N \in Nat /\ N > 0

VARIABLES x, y, pc

vars == <<x, y, pc>>

Procs == 0..(N - 1)

TypeOK ==
    /\ x \in [Procs -> SUBSET {0, 1}]
    /\ \A i \in Procs : x[i] /= {}
    /\ y \in [Procs -> {0, 1}]
    /\ pc \in [Procs -> {"a1", "a2", "b", "Done"}]

Init ==
    /\ x = [i \in Procs |-> {0}]
    /\ y = [i \in Procs |-> 0]
    /\ pc = [i \in Procs |-> "a1"]

a1(self) ==
    /\ pc[self] = "a1"
    /\ x' = [x EXCEPT ![self] = {0, 1}]
    /\ pc' = [pc EXCEPT ![self] = "a2"]
    /\ UNCHANGED y

a2(self) ==
    /\ pc[self] = "a2"
    /\ x' = [x EXCEPT ![self] = {1}]
    /\ pc' = [pc EXCEPT ![self] = "b"]
    /\ UNCHANGED y

b(self) ==
    /\ pc[self] = "b"
    /\ \E v \in x[(self - 1) % N] :
         y' = [y EXCEPT ![self] = v]
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED x

proc(self) == a1(self) \/ a2(self) \/ b(self)

\* Allow infinite stuttering to prevent deadlock on termination.
Terminating == (\A i \in Procs : pc[i] = "Done") /\ UNCHANGED vars

Next == (\E self \in Procs : proc(self)) \/ Terminating

Spec == Init /\ [][Next]_vars
            /\ \A self \in Procs : WF_vars(proc(self))

\* Partial-correctness invariant (same as in module Simple).
PCorrect ==
    (\A i \in Procs : pc[i] = "Done")
        => \E i \in Procs : y[i] = 1

\* Inductive invariant (same as in module Simple, with the type adjusted).
Inv ==
    /\ TypeOK
    /\ \A i \in Procs :
        /\ (pc[i] = "a1") => x[i] = {0}
        /\ (pc[i] = "a2") => x[i] = {0, 1}
        /\ (pc[i] \in {"b", "Done"}) => x[i] = {1}
    /\ \A i \in Procs :
        (pc[i] = "Done") => y[i] \in x[(i - 1) % N] \cup {0, 1}

THEOREM Spec => []PCorrect
====
