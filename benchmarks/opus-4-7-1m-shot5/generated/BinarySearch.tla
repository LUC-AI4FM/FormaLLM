---- MODULE BinarySearch ----
(***************************************************************************)
(* This module defines a binary search algorithm for finding an item in a  *)
(* sorted sequence, and contains a TLAPS-checked proof of its safety       *)
(* property.  We assume a sorted sequence seq with elements in some set    *)
(* Values of integers and a number val in Values, it sets the value        *)
(* `result' to either a number i with seq[i] = val, or to 0 if there is no *)
(* such i.                                                                 *)
(*                                                                          *)
(* It is surprisingly difficult to get such a binary search algorithm      *)
(* correct without making errors that have to be caught by debugging.  I   *)
(* suggest trying to write a correct PlusCal binary search algorithm       *)
(* yourself before looking at this one.                                    *)
(*                                                                          *)
(* This algorithm is one of the examples in Section 7.3 of "Proving Safety *)
(* Properties", which is at                                                *)
(*                                                                          *)
(*    http://lamport.azurewebsites.net/tla/proving-safety.pdf              *)
(***************************************************************************)
EXTENDS Integers, Sequences, TLAPS, SequenceTheorems

CONSTANT Values

ASSUME ValuesAssump == Values \subseteq Int

SortedSeqs ==
  { s \in Seq(Values) :
      \A i, j \in 1..Len(s) : (i <= j) => (s[i] <= s[j]) }

(*--fair algorithm BinarySearch {
    variables seq \in SortedSeqs, val \in Values,
              low = 1, high = Len(seq), result = 0 ;
    { a: while (low =< high /\ result = 0) {
           with (mid = (low + high) \div 2, mval = seq[mid]) {
              if (mval = val) { result := mid}
              else if (val < mval) { high := mid - 1}
                   else {low := mid + 1}                    } } } }
*)

\* BEGIN TRANSLATION
VARIABLES seq, val, low, high, result, pc

vars == << seq, val, low, high, result, pc >>

Init == (* Global variables *)
        /\ seq \in SortedSeqs
        /\ val \in Values
        /\ low = 1
        /\ high = Len(seq)
        /\ result = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF low =< high /\ result = 0
           THEN /\ LET mid == (low + high) \div 2 IN
                  LET mval == seq[mid] IN
                    IF mval = val
                       THEN /\ result' = mid
                            /\ UNCHANGED << low, high >>
                       ELSE /\ IF val < mval
                                  THEN /\ high' = mid - 1
                                       /\ low' = low
                                  ELSE /\ low' = mid + 1
                                       /\ high' = high
                            /\ UNCHANGED result
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << low, high, result >>
     /\ UNCHANGED << seq, val >>

\* Allow infinite stuttering to prevent deadlock on termination.
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

(***************************************************************************)
(* Partial correctness of the algorithm is expressed by invariance of      *)
(* formula resultCorrect.  To get TLC to check this property, we use a     *)
(* model that overrides the definition of Seq so Seq(S) is the set of      *)
(* sequences of elements of S having at most some small length.  For       *)
(* example,                                                                *)
(*                                                                          *)
(*    Seq(S) == UNION {[1..i -> S] : i \in 0..3}                           *)
(*                                                                          *)
(* is the set of such sequences with length at most 3.                     *)
(***************************************************************************)
resultCorrect ==
  pc = "Done" =>
    \/ /\ result \in 1..Len(seq)
       /\ seq[result] = val
    \/ /\ result = 0
       /\ \A i \in 1..Len(seq) : seq[i] # val

(***************************************************************************)
(* Proving the invariance of resultCorrect requires finding an inductive   *)
(* invariant that implies it.  A suitable inductive invariant Inv is       *)
(* defined here.                                                           *)
(***************************************************************************)
Inv ==
  /\ seq \in SortedSeqs
  /\ val \in Values
  /\ Len(seq) \in Nat
  /\ low \in 1..(Len(seq) + 1)
  /\ high \in 0..Len(seq)
  /\ result \in 0..Len(seq)
  /\ pc \in {"a", "Done"}
  /\ (result # 0) => (seq[result] = val)
  /\ (pc = "Done") =>
       \/ result # 0
       \/ /\ result = 0
          /\ \A i \in 1..Len(seq) : seq[i] # val
  /\ (pc = "a" /\ result = 0) =>
       /\ \A i \in 1..Len(seq) : (i < low \/ i > high) => seq[i] # val

(***************************************************************************)
(* Here is the invariance proof.                                           *)
(***************************************************************************)
THEOREM Spec => []resultCorrect
  <1>1. Init => Inv
    BY DEF Init, Inv, SortedSeqs
  <1>2. Inv /\ [Next]_vars => Inv'
    <2> SUFFICES ASSUME Inv, [Next]_vars
                 PROVE  Inv'
      OBVIOUS
    <2>1. CASE a
      BY <2>1 DEF a, Inv, vars, SortedSeqs
    <2>2. CASE Terminating
      BY <2>2 DEF Terminating, Inv, vars
    <2>3. CASE UNCHANGED vars
      BY <2>3 DEF Inv, vars
    <2>4. QED
      BY <2>1, <2>2, <2>3 DEF Next
  <1>3. Inv => resultCorrect
    BY DEF Inv, resultCorrect
  <1>4. QED
    BY <1>1, <1>2, <1>3, PTL DEF Spec

====
