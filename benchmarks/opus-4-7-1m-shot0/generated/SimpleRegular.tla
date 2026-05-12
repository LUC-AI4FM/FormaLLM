---- MODULE SimpleRegular ----
\* A minor modification of the algorithm in module Simple. The original is
\* an N-process shared-memory algorithm, in which each process i has a
\* shared register x[i] that it writes and is read by process (i-1) % N.
\* Each process i also has a local register y[i].
\*
\* In Simple, each x[i] is atomic. Here, each x[i] is a regular register
\* (Lamport, "On Interprocess Communication", 1986). A regular register r is
\* modeled in TLA+ as a variable rv that equals a SET of values: rv = {v}
\* when the register has value v; while a write of w is in progress over an
\* established value v, rv = {v, w}; once the write completes, rv = {w}.
\* A read obtains any v \in rv.
\*
\* The variable x[i] = {v} initially. To write v -> w, we first set x[i] to
\* {v, w} (a1), then to {w} (a2). A read of x[(self-1) % N] (b) atomically
\* picks any v in that set.

EXTENDS Naturals, TLAPS

CONSTANT N

ASSUME N \in Nat /\ N >= 1

(* --algorithm SimpleRegular {
   variables x = [i \in 0..(N-1) |-> {0}],
             y = [i \in 0..(N-1) |-> 0];
   process (proc \in 0..N-1) {
     a1: x[self] := {0,1};
     a2: x[self] := {1};
     b:  with (v \in x[(self-1) % N]) { y[self] := v }
   }
} *)

\* BEGIN TRANSLATION

VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == 0..(N-1)

Init ==
  /\ x = [i \in 0..(N-1) |-> {0}]
  /\ y = [i \in 0..(N-1) |-> 0]
  /\ pc = [self \in ProcSet |-> "a1"]

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
       /\ y' = [y EXCEPT ![self] = v]
  /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED x

\* Allow infinite stuttering to prevent deadlock on termination.
Terminating ==
  /\ \A self \in ProcSet : pc[self] = "Done"
  /\ UNCHANGED vars

Next ==
  \/ \E self \in ProcSet : a1(self) \/ a2(self) \/ b(self)
  \/ Terminating

Spec == Init /\ [][Next]_vars

\* END TRANSLATION

\* Partial correctness: same as in module Simple.
PCorrect ==
  \A i \in ProcSet :
     (pc[i] = "Done") =>
        \E j \in ProcSet : y[i] \in {0, 1}

\* Type invariant.
TypeOK ==
  /\ x \in [0..(N-1) -> SUBSET {0, 1}]
  /\ \A i \in 0..(N-1) : x[i] /= {}
  /\ y \in [0..(N-1) -> {0, 1}]
  /\ pc \in [ProcSet -> {"a1", "a2", "b", "Done"}]

\* Inductive invariant.
Inv ==
  /\ TypeOK
  /\ \A i \in ProcSet :
        /\ (pc[i] = "a1") => x[i] = {0}
        /\ (pc[i] = "a2") => x[i] = {0, 1}
        /\ (pc[i] \in {"b", "Done"}) => x[i] = {1}

THEOREM Spec => []PCorrect

====
