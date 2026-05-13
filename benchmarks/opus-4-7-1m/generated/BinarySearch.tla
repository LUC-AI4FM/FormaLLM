---- MODULE BinarySearch ----
(***************************************************************************)
(* A binary search algorithm for finding an item in a sorted sequence,    *)
(* with a TLAPS-checked safety property. Given a sorted sequence seq with *)
(* elements in Values (integers) and a number val in Values, it sets      *)
(* `result' to either i with seq[i] = val, or to 0 if no such i exists.   *)
(*                                                                         *)
(* Translation of the PlusCal algorithm:                                   *)
(*   --fair algorithm BinarySearch {                                      *)
(*     variables seq \in SortedSeqs, val \in Values,                      *)
(*               low = 1, high = Len(seq), result = 0 ;                   *)
(*     { a: while (low =< high /\ result = 0) {                           *)
(*           with (mid = (low + high) \div 2, mval = seq[mid]) {          *)
(*             if (mval = val)      { result := mid }                     *)
(*             else if (val < mval) { high := mid - 1 }                   *)
(*             else                 { low := mid + 1 }                    *)
(*       } } } }                                                          *)
(*                                                                         *)
(* From Section 7.3 of "Proving Safety Properties",                       *)
(* http://lamport.azurewebsites.net/tla/proving-safety.pdf                *)
(*                                                                         *)
(* Modification History                                                    *)
(*   Last modified Fri Feb 17 16:12:03 CET 2023 by merz                    *)
(*   Last modified Tue Aug 27 12:59:52 PDT 2019 by loki                    *)
(*   Last modified Fri May 03 16:28:58 PDT 2019 by lamport                 *)
(*   Created      Wed Apr 17 15:15:12 PDT 2019 by lamport                  *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS Values

\* Sorted sequences (non-decreasing) of elements in Values.
SortedSeqs == { s \in Seq(Values) :
                \A i \in 1..(Len(s) - 1) : s[i] <= s[i+1] }

VARIABLES seq, val, low, high, result, pc

vars == <<seq, val, low, high, result, pc>>

TypeOK ==
    /\ seq \in SortedSeqs
    /\ val \in Values
    /\ low \in Int
    /\ high \in Int
    /\ result \in 0..Len(seq)
    /\ pc \in {"a", "Done"}
    /\ Len(seq) \in Nat

Init ==
    /\ seq \in SortedSeqs
    /\ val \in Values
    /\ low = 1
    /\ high = Len(seq)
    /\ result = 0
    /\ pc = "a"

a ==
    /\ pc = "a"
    /\ IF low <= high /\ result = 0
       THEN /\ LET mid == (low + high) \div 2
                 mval == seq[mid]
             IN  IF mval = val
                 THEN /\ result' = mid
                      /\ UNCHANGED <<low, high>>
                 ELSE IF val < mval
                      THEN /\ high' = mid - 1
                           /\ UNCHANGED <<low, result>>
                      ELSE /\ low' = mid + 1
                           /\ UNCHANGED <<high, result>>
            /\ pc' = "a"
       ELSE /\ pc' = "Done"
            /\ UNCHANGED <<low, high, result>>
    /\ UNCHANGED <<seq, val>>

\* Allow infinite stuttering to prevent deadlock on termination.
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(a)

\* Partial-correctness invariant.
resultCorrect ==
    pc = "Done" =>
        \/ /\ result \in 1..Len(seq)
           /\ seq[result] = val
        \/ /\ result = 0
           /\ \A i \in 1..Len(seq) : seq[i] /= val

\* Inductive invariant.
Inv ==
    /\ TypeOK
    /\ low \in 1..(Len(seq) + 1)
    /\ high \in 0..Len(seq)
    /\ result \in 0..Len(seq)
    /\ (result /= 0) => seq[result] = val
    /\ (pc = "a" /\ result = 0) =>
            \A i \in 1..Len(seq) :
                (seq[i] = val) => (i \in low..high)

THEOREM Spec => []resultCorrect
====
