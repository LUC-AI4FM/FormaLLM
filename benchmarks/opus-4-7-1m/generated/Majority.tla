---- MODULE Majority ----
(***************************************************************************)
(* TLA+ specification of the Boyer-Moore majority vote algorithm.         *)
(*                                                                         *)
(* R.S. Boyer, J.S. Moore: MJRTY - A Fast Majority Vote Algorithm.        *)
(* In: R.S. Boyer (ed.), Automated Reasoning: Essays in Honor of Woody    *)
(* Bledsoe, pp. 105-117. Dordrecht, 1991. Originally tech report 1981.    *)
(*                                                                         *)
(* The algorithm takes a sequence of values, makes one pass, and reports  *)
(* an element cand such that no element other than cand may have an       *)
(* absolute majority in the sequence.                                      *)
(*                                                                         *)
(* Although seq is an input, we make it a variable so the model checker   *)
(* can verify the algorithm for all sequences up to some bounded size.    *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Value, MaxLen

ASSUME MaxLen \in Nat

VARIABLES seq,    \* input sequence, never changes
          j,      \* next position to be checked
          cand,   \* current candidate for having a majority
          cnt     \* lower bound on occurrences of cand so far

vars == <<seq, j, cand, cnt>>

\* Set of indexes in the prefix of seq strictly before j holding v.
PosBefore(v) == { i \in 1..(j - 1) : seq[i] = v }

\* Number of times v occurs in that prefix.
OccBefore(v) == Cardinality(PosBefore(v))

\* Number of times v occurs in the whole sequence.
Occ(v) == Cardinality({ i \in DOMAIN seq : seq[i] = v })

TypeOK ==
    /\ seq \in UNION { [1..n -> Value] : n \in 0..MaxLen }
    /\ j \in 1..(Len(seq) + 1)
    /\ cand \in Value
    /\ cnt \in Nat

Init ==
    /\ seq \in UNION { [1..n -> Value] : n \in 0..MaxLen }
    /\ j = 1
    /\ cand \in Value
    /\ cnt = 0

\* Process the next element of seq.
Step ==
    /\ j <= Len(seq)
    /\ \/ /\ cnt = 0
          /\ cand' = seq[j]
          /\ cnt' = 1
       \/ /\ cnt > 0
          /\ seq[j] = cand
          /\ cand' = cand
          /\ cnt' = cnt + 1
       \/ /\ cnt > 0
          /\ seq[j] /= cand
          /\ cand' = cand
          /\ cnt' = cnt - 1
    /\ j' = j + 1
    /\ UNCHANGED seq

Done ==
    /\ j > Len(seq)
    /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars

\* Main correctness property: cand can be the only value that has a majority.
Correctness ==
    (j > Len(seq)) =>
        \A v \in Value : v /= cand => 2 * Occ(v) <= Len(seq)

\* Inductive invariant for proving correctness.
InductiveInvariant ==
    /\ TypeOK
    /\ j \in 1..(Len(seq) + 1)
    /\ \A v \in Value :
        v /= cand =>
            2 * OccBefore(v) <= (j - 1) - cnt
    /\ 2 * OccBefore(cand) >= cnt + ((j - 1) - cnt) \div 2
====
