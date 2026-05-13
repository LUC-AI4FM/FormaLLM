---- MODULE Majority ----
\* TLA+ specification and proof of the majority vote algorithm due to Boyer
\* and Moore.
\*
\*   R.S. Boyer, J.S. Moore: MJRTY - A Fast Majority Vote Algorithm.
\*   In R.S. Boyer (ed.): Automated Reasoning: Essays in Honor of Woody
\*   Bledsoe, pp. 105-117. Dordrecht, The Netherlands, 1991.
\*   Originally published in a technical report from 1981.
\*
\* The algorithm takes as input a sequence of values, makes one pass over
\* the sequence, and reports an element cand such that no element other
\* than cand may have an absolute majority in the sequence.

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Value, N
ASSUME N \in Nat /\ N > 0

VARIABLES
  seq,      \* input sequence of values, never changes
  j,        \* next position of the sequence to be checked
  cand,     \* current candidate for having a majority
  cnt       \* lower bound for the number of occurrences of cand so far

vars == << seq, j, cand, cnt >>

\* Although seq is an input to the algorithm, we make it a variable so that
\* we can use TLC to verify it for all sequences up to a bounded size.

\* The set of inputs we model-check over: sequences of length up to N.
InputSeq == UNION { [1..n -> Value] : n \in 1..N }

TypeOK ==
  /\ seq  \in InputSeq
  /\ j    \in 1..(Len(seq) + 1)
  /\ cand \in Value
  /\ cnt  \in Nat

\* ----- Definitions used for stating correctness -----

\* Set of indexes in the prefix of seq strictly before j holding value v.
OccPrefix(v) == { i \in 1..(j-1) : seq[i] = v }

\* Number of times v occurs in that prefix.
CountPrefix(v) == Cardinality(OccPrefix(v))

\* Number of times v occurs in all of seq.
Count(v) == Cardinality({ i \in 1..Len(seq) : seq[i] = v })

\* v has an absolute majority in seq.
HasMajority(v) == 2 * Count(v) > Len(seq)

\* ----- Initial state -----

Init ==
  /\ seq  \in InputSeq
  /\ j    = 1
  /\ cand \in Value
  /\ cnt  = 0

\* ----- Step -----

Step ==
  /\ j <= Len(seq)
  /\ j' = j + 1
  /\ IF cnt = 0
       THEN /\ cand' = seq[j]
            /\ cnt'  = 1
       ELSE IF cand = seq[j]
              THEN /\ cnt' = cnt + 1
                   /\ UNCHANGED cand
              ELSE /\ cnt' = cnt - 1
                   /\ UNCHANGED cand
  /\ UNCHANGED seq

Done == j > Len(seq) /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars

\* ----- Correctness -----

\* Main correctness property: cand can be the only value with a majority.
Correct ==
  (j > Len(seq)) =>
    \A v \in Value : v /= cand => ~ HasMajority(v)

\* Inductive invariant used to prove Correct.
\* For any v /= cand: 2 * CountPrefix(v) <= (j - 1) - cnt,
\* i.e. v's count so far plus a remaining "credit" cnt does not exceed half
\* the elements processed so far.
Inv ==
  /\ TypeOK
  /\ cnt <= CountPrefix(cand) + Cardinality({ i \in j..Len(seq) : seq[i] = cand })
  /\ \A v \in Value : v /= cand =>
        2 * CountPrefix(v) <= (j - 1) - cnt

====
