------------------------------ MODULE SimpleRegular ------------------------------
\* Variant of the Simple algorithm where each shared register x[i] is a
\* "regular" register (Lamport 1986): a read overlapping a set of writes
\* returns either the prior value or one of the values being written.
\* Modeled by making x[i] a set of values; writes pass through a transient
\* {old, new} state.

EXTENDS Integers, TLAPS

CONSTANT N
ASSUME NAssump == (N \in Nat) /\ (N > 0)

(***************************************************************************
--algorithm SimpleRegular {
    variables x = [i \in 0..(N-1) |-> {0}], y = [i \in 0..(N-1) |-> 0] ;
    process (proc \in 0..N-1) {
        a1: x[self] := {0,1} ;
        a2: x[self] := {1} ;
        b:  with (v \in x[(self-1) % N]) { y[self] := v }
    }
}
 ***************************************************************************)

VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == (0..N-1)

Init ==
    /\ x = [i \in 0..(N-1) |-> {0}]
    /\ y = [i \in 0..(N-1) |-> 0]
    /\ pc = [self \in ProcSet |-> "a1"]

a1(self) ==
    /\ pc[self] = "a1"
    /\ x' = [x EXCEPT ![self] = {0, 1}]
    /\ pc' = [pc EXCEPT ![self] = "a2"]
    /\ y' = y

a2(self) ==
    /\ pc[self] = "a2"
    /\ x' = [x EXCEPT ![self] = {1}]
    /\ pc' = [pc EXCEPT ![self] = "b"]
    /\ y' = y

b(self) ==
    /\ pc[self] = "b"
    /\ \E v \in x[(self - 1) % N] :
         y' = [y EXCEPT ![self] = v]
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ x' = x

proc(self) == a1(self) \/ a2(self) \/ b(self)

Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in 0..(N-1) : proc(self))
        \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

----------------------------------------------------------------------------

\* PCorrect is unchanged from Simple.
PCorrect == (\A i \in 0..(N-1) : pc[i] = "Done") =>
            (\E i \in 0..(N-1) : y[i] = 1)

\* TypeOK is the obvious modification: x[i] is now a non-empty subset
\* of {0, 1}.
TypeOK ==
    /\ x \in [0..(N-1) -> (SUBSET {0, 1}) \ {{}}]
    /\ y \in [0..(N-1) -> {0, 1}]
    /\ pc \in [0..(N-1) -> {"a1", "a2", "b", "Done"}]

\* Inductive invariant matches Simple, adjusted for the regular-register
\* representation.
Inv ==
    /\ TypeOK
    /\ \A i \in 0..(N-1) :
         (pc[i] = "a2") => (x[i] = {0, 1})
    /\ \A i \in 0..(N-1) :
         (pc[i] \in {"b", "Done"}) => (x[i] = {1})
    /\ \/ \E i \in 0..(N-1) : pc[i] # "Done"
       \/ \E i \in 0..(N-1) : y[i] = 1

THEOREM Spec => []PCorrect
<1> USE NAssump
<1>1. Init => Inv
    BY DEF Init, Inv, TypeOK, ProcSet
<1>2. Inv /\ [Next]_vars => Inv'
    <2> SUFFICES ASSUME Inv, [Next]_vars
                 PROVE  Inv'
        OBVIOUS
    <2>1. ASSUME NEW self \in 0..(N-1), a1(self)
          PROVE  Inv'
        BY <2>1 DEF a1, Inv, TypeOK
    <2>2. ASSUME NEW self \in 0..(N-1), a2(self)
          PROVE  Inv'
        BY <2>2 DEF a2, Inv, TypeOK
    <2>3. ASSUME NEW self \in 0..(N-1), b(self)
          PROVE  Inv'
        BY <2>3, Z3 DEF b, Inv, TypeOK
    <2>4. CASE UNCHANGED vars
        BY <2>4 DEF TypeOK, Inv, vars
    <2>5. QED BY <2>1, <2>2, <2>3, <2>4 DEF Next, Terminating, proc
<1>3. Inv => PCorrect
    BY DEF Inv, TypeOK, PCorrect
<1>4. QED BY <1>1, <1>2, <1>3, PTL DEF Spec

=============================================================================
