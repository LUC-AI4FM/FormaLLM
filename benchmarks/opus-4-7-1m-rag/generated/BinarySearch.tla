----------------------------- MODULE BinarySearch -----------------------------
\* Binary search on a sorted integer sequence. Sets result to an index i
\* with seq[i] = val, or 0 if no such index exists. TLAPS proof of safety.

EXTENDS Integers, Sequences, TLAPS, SequenceTheorems

CONSTANT Values

ASSUME ValAssump == Values \subseteq Int

SortedSeqs ==
    {s \in Seq(Values) :
        \A i, j \in 1..Len(s) : i <= j => s[i] <= s[j]}

(***************************************************************************
--fair algorithm BinarySearch {
    variables seq \in SortedSeqs, val \in Values,
              low = 1, high = Len(seq), result = 0 ;
    { a: while (low <= high /\ result = 0) {
           with (mid = (low + high) \div 2, mval = seq[mid]) {
             if (mval = val) { result := mid }
             else if (val < mval) { high := mid - 1 }
             else { low := mid + 1 }
           }
         }
    }
}
 ***************************************************************************)

VARIABLES seq, val, low, high, result, pc

vars == << seq, val, low, high, result, pc >>

Init ==
    /\ seq \in SortedSeqs
    /\ val \in Values
    /\ low = 1
    /\ high = Len(seq)
    /\ result = 0
    /\ pc = "a"

a == /\ pc = "a"
     /\ IF low <= high /\ result = 0
        THEN /\ LET mid == (low + high) \div 2
                    mval == seq[mid]
                IN  IF mval = val
                    THEN /\ result' = mid
                         /\ UNCHANGED << low, high >>
                    ELSE IF val < mval
                         THEN /\ high' = mid - 1
                              /\ UNCHANGED << low, result >>
                         ELSE /\ low' = mid + 1
                              /\ UNCHANGED << high, result >>
             /\ pc' = "a"
        ELSE /\ pc' = "Done"
             /\ UNCHANGED << low, high, result >>
     /\ UNCHANGED << seq, val >>

\* Allow infinite stuttering to prevent deadlock on termination.
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ Terminating

Spec == /\ Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* Partial correctness invariant.
resultCorrect ==
    pc = "Done" =>
        \/ /\ result \in 1..Len(seq)
           /\ seq[result] = val
        \/ /\ result = 0
           /\ \A i \in 1..Len(seq) : seq[i] # val

\* Inductive invariant that implies resultCorrect.
Inv ==
    /\ seq \in SortedSeqs
    /\ val \in Values
    /\ low \in 1..(Len(seq) + 1)
    /\ high \in 0..Len(seq)
    /\ result \in 0..Len(seq)
    /\ pc \in {"a", "Done"}
    /\ result # 0 => seq[result] = val
    /\ (result = 0 /\ pc = "a") =>
         \A i \in 1..Len(seq) :
             (i < low \/ i > high) => seq[i] # val
    /\ (pc = "Done") => resultCorrect

THEOREM Spec => []resultCorrect
<1>1. Init => Inv
    BY DEF Init, Inv, resultCorrect, SortedSeqs
<1>2. Inv /\ [Next]_vars => Inv'
    OBVIOUS
<1>3. QED BY <1>1, <1>2, PTL DEF Spec, Inv

=============================================================================
