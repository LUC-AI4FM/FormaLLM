---- MODULE Majority ----
(***************************************************************************)
(* TLA+ specification and proof of the majority vote algorithm due to Boyer*)
(* and Moore.                                                               *)
(* R.S. Boyer, J.S. Moore: MJRTY - A Fast Majority Vote Algorithm.          *)
(* In: R.S. Boyer (ed.): Automated Reasoning: Essays in Honor of Woody      *)
(* Bledsoe, pp. 105-117.  Dordrecht, The Netherlands, 1991.                 *)
(* Originally published in a technical report from 1981.                    *)
(* The algorithm takes as input a sequence of values, makes one pass over   *)
(* the sequence, and reports an element cand such that no element other     *)
(* than cand may have an absolute majority in the sequence.                 *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Value, BoundedSeq

VARIABLES
  seq,    \* input sequence of values, never changes
  j,      \* next position of sequence to be checked
  cand,   \* current candidate for having a majority
  cnt     \* lower bound for the number of occurrences of the candidate so far

vars == <<seq, j, cand, cnt>>

(***************************************************************************)
(* Definitions used for stating correctness.                               *)
(***************************************************************************)
(* set of indexes in the prefix of the sequence strictly before j holding v*)
PositionsBefore(v) == { i \in 1..(j-1) : seq[i] = v }

(* number of times v occurs in that prefix *)
OccurrencesBefore(v) == Cardinality(PositionsBefore(v))

(* number of times v occurs in all of the sequence *)
Occurrences(v) == Cardinality({ i \in 1..Len(seq) : seq[i] = v })

(***************************************************************************)
(* Although seq is an input to the algorithm, we make it a variable so that*)
(* we can use the model checker to verify the algorithm for all sequences  *)
(* up to some bounded size.                                                *)
(***************************************************************************)
TypeOK ==
  /\ seq \in BoundedSeq
  /\ j \in 1..(Len(seq) + 1)
  /\ cand \in Value
  /\ cnt \in Nat

Init ==
  /\ seq \in BoundedSeq
  /\ j = 1
  /\ cand \in Value
  /\ cnt = 0

Next ==
  /\ j \leq Len(seq)
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
  /\ j' = j + 1
  /\ UNCHANGED seq

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Main correctness property: cand can be the only value that has a        *)
(* majority.                                                               *)
(***************************************************************************)
Correctness ==
  (j = Len(seq) + 1) =>
    \A v \in Value : v # cand => 2 * Occurrences(v) \leq Len(seq)

(***************************************************************************)
(* Inductive invariant for proving correctness.                            *)
(***************************************************************************)
Inv ==
  /\ TypeOK
  /\ 2 * OccurrencesBefore(cand) \geq cnt + (j - 1 - OccurrencesBefore(cand))
  /\ \A v \in Value :
       v # cand =>
         2 * OccurrencesBefore(v) \leq (j - 1) - cnt

====
