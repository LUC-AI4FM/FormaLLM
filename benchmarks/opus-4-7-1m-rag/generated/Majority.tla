---- MODULE Majority ----
\* Boyer-Moore majority vote algorithm: one pass over a sequence to find
\* a candidate that is the only possible absolute-majority element.

EXTENDS Integers, Sequences, FiniteSets

CONSTANT Value

\* seq: the input sequence, never changes once initialized.
\* j: next position of the sequence to be checked.
\* cand: current candidate for having a majority.
\* cnt: lower bound for the number of occurrences of cand so far.
VARIABLES seq, j, cand, cnt

vars == <<seq, j, cand, cnt>>

Init == /\ seq \in Seq(Value)
        /\ j = 1
        /\ cand \in Value
        /\ cnt = 0

\* Indexes in the prefix strictly before j that hold value v.
OccurrencesBefore(v) == { k \in 1..(j-1) : seq[k] = v }

\* Number of times v occurs in the prefix [1, j).
CountBefore(v) == Cardinality(OccurrencesBefore(v))

\* Total number of times v occurs in the whole sequence.
Count(v) == Cardinality({ k \in 1..Len(seq) : seq[k] = v })

Next == /\ j <= Len(seq)
        /\ j' = j + 1
        /\ seq' = seq
        /\ \/ /\ cnt = 0
              /\ cand' = seq[j]
              /\ cnt' = 1
           \/ /\ cnt # 0
              /\ seq[j] = cand
              /\ cand' = cand
              /\ cnt' = cnt + 1
           \/ /\ cnt # 0
              /\ seq[j] # cand
              /\ cand' = cand
              /\ cnt' = cnt - 1

Spec == Init /\ [][Next]_vars

\* Main correctness property: only cand could be a majority element.
Correctness ==
    (j = Len(seq) + 1) =>
        \A v \in Value : (v # cand) => (2 * Count(v) <= Len(seq))

\* Type-correct invariant.
TypeOK ==
    /\ seq \in Seq(Value)
    /\ j \in 1..(Len(seq) + 1)
    /\ cand \in Value
    /\ cnt \in Nat

\* Inductive invariant for proving correctness.
InductiveInvariant ==
    /\ TypeOK
    /\ cnt <= CountBefore(cand)
    /\ \A v \in Value :
         (v # cand) => 2 * CountBefore(v) <= (j - 1) - cnt

THEOREM Spec => []Correctness
====
