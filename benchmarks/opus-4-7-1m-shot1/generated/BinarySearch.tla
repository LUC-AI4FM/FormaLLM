---- MODULE BinarySearch ----
(***************************************************************************)
(* This module defines a binary search algorithm for finding an item in a  *)
(* sorted sequence, and contains a TLAPS-checked proof of its safety       *)
(* property.  We assume a sorted sequence seq with elements in some set    *)
(* Values of integers and a number val in Values, it sets the value        *)
(* `result' to either a number i with seq[i] = val, or to 0 if there is    *)
(* no such i.                                                              *)
(*                                                                         *)
(* This algorithm is one of the examples in Section 7.3 of "Proving Safety *)
(* Properties", which is at                                                *)
(*                                                                         *)
(*    http://lamport.azurewebsites.net/tla/proving-safety.pdf              *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLAPS

CONSTANTS Values

SortedSeqs == { s \in Seq(Values) :
                  \A i, j \in 1..Len(s) : i \leq j => s[i] \leq s[j] }

(***************************************************************************
--fair algorithm BinarySearch {
variables seq \in SortedSeqs, val \in Values,
          low = 1, high = Len(seq), result = 0 ;
{ a: while (low =< high /\ result = 0) {
        with (mid = (low + high) \div 2, mval = seq[mid]) {
          if (mval = val) { result := mid }
          else if (val < mval) { high := mid - 1 }
          else { low := mid + 1 } } } } }
 ***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES seq, val, low, high, result, pc

vars == << seq, val, low, high, result, pc >>

Init == /\ seq \in SortedSeqs
        /\ val \in Values
        /\ low = 1
        /\ high = Len(seq)
        /\ result = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF low \leq high /\ result = 0
           THEN /\ LET mid == (low + high) \div 2 IN
                  LET mval == seq[mid] IN
                    IF mval = val
                      THEN /\ result' = mid
                           /\ UNCHANGED <<low, high>>
                      ELSE /\ IF val < mval
                                 THEN /\ high' = mid - 1
                                      /\ UNCHANGED low
                                 ELSE /\ low' = mid + 1
                                      /\ UNCHANGED high
                           /\ UNCHANGED result
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << low, high, result >>
     /\ UNCHANGED << seq, val >>

Next == a \/ (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars /\ WF_vars(a)

Termination == <>(pc = "Done")
\* END TRANSLATION

resultCorrect ==
  (pc = "Done") =>
    \/ (result = 0 /\ \A i \in 1..Len(seq) : seq[i] # val)
    \/ (result \in 1..Len(seq) /\ seq[result] = val)

(***************************************************************************)
(* A suitable inductive invariant Inv.                                     *)
(***************************************************************************)
Inv ==
  /\ seq \in SortedSeqs
  /\ val \in Values
  /\ low \in 1..(Len(seq) + 1)
  /\ high \in 0..Len(seq)
  /\ result \in 0..Len(seq)
  /\ \A i \in 1..Len(seq) : (i < low \/ i > high) /\ result = 0 => seq[i] # val
  /\ (result # 0) => (result \in 1..Len(seq) /\ seq[result] = val)

THEOREM Spec => []resultCorrect

====
