---- MODULE BinarySearch ----
\* This module defines a binary search algorithm for finding an item in a
\* sorted sequence, and contains a TLAPS-checked proof of its safety
\* property. We assume a sorted sequence seq with elements in some set
\* Values of integers and a number val in Values; the algorithm sets the
\* variable `result' to either a number i with seq[i] = val, or to 0 if
\* there is no such i.
\*
\* This algorithm is one of the examples in Section 7.3 of "Proving Safety
\* Properties", http://lamport.azurewebsites.net/tla/proving-safety.pdf

EXTENDS Integers, Sequences, TLAPS

CONSTANT Values

\* Set of sequences over Values that are sorted in non-decreasing order.
SortedSeqs ==
  { s \in Seq(Values) :
       \A i, j \in DOMAIN s : (i < j) => s[i] <= s[j] }

(* --fair algorithm BinarySearch {
    variables seq \in SortedSeqs, val \in Values,
              low = 1, high = Len(seq), result = 0;
    { a: while (low =< high /\ result = 0) {
            with (mid = (low + high) \div 2, mval = seq[mid]) {
                if (mval = val) { result := mid }
                else if (val < mval) { high := mid - 1 }
                else { low := mid + 1 } } } } } *)

\* BEGIN TRANSLATION
VARIABLES seq, val, low, high, result, pc

vars == << seq, val, low, high, result, pc >>

Init ==
  /\ seq    \in SortedSeqs
  /\ val    \in Values
  /\ low    = 1
  /\ high   = Len(seq)
  /\ result = 0
  /\ pc     = "a"

a ==
  /\ pc = "a"
  /\ IF low =< high /\ result = 0
       THEN /\ LET mid  == (low + high) \div 2
                    mval == seq[mid]
                IN  IF mval = val
                      THEN /\ result' = mid
                           /\ UNCHANGED << low, high >>
                      ELSE IF val < mval
                             THEN /\ high'   = mid - 1
                                  /\ UNCHANGED << low, result >>
                             ELSE /\ low'    = mid + 1
                                  /\ UNCHANGED << high, result >>
            /\ pc' = "a"
       ELSE /\ pc' = "Done"
            /\ UNCHANGED << low, high, result >>
  /\ UNCHANGED << seq, val >>

\* Allow infinite stuttering to prevent deadlock on termination.
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* END TRANSLATION

\* ----- Partial correctness -----

\* Partial correctness: when the algorithm terminates, `result' is correct.
resultCorrect ==
  (pc = "Done") =>
     \/ (result = 0 /\ \A i \in DOMAIN seq : seq[i] /= val)
     \/ (result \in DOMAIN seq /\ seq[result] = val)

\* TypeOK.
TypeOK ==
  /\ seq    \in SortedSeqs
  /\ val    \in Values
  /\ low    \in Int
  /\ high   \in Int
  /\ result \in Nat
  /\ result \in 0..Len(seq)
  /\ pc     \in {"a", "Done"}
  /\ Len(seq) \in Nat

\* Inductive invariant.
Inv ==
  /\ TypeOK
  /\ low >= 1
  /\ high <= Len(seq)
  /\ result \in 0..Len(seq)
  /\ (result /= 0) => seq[result] = val
  /\ (result = 0 /\ pc = "a") =>
        \A i \in DOMAIN seq :
           seq[i] = val => (i \in low..high)
  /\ (pc = "Done") => resultCorrect

\* Invariance proof.
THEOREM Spec => []resultCorrect

====
