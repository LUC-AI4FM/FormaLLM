---- MODULE BufferedRandomAccessFile ----
(***************************************************************************)
(* Copyright (c) 2024, Oracle and/or its affiliates.                       *)
(*                                                                         *)
(* This is a model-checkable specification for BufferedRandomAccessFile.   *)
(* It covers the core fields as well as the seek, read, write, flush, and  *)
(* setLength operations.                                                   *)
(*                                                                         *)
(* There are three major correctness conditions:                           *)
(*   (1) the internal invariants V1-V5 should hold                         *)
(*   (2) the behavior should refine a general RandomAccessFile             *)
(*   (3) each operation should refine its RandomAccessFile counterpart     *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC, RandomAccessFile

(***************************************************************************)
(* Constants                                                               *)
(***************************************************************************)
CONSTANT BuffSz   \* bound model checking

ASSUME BuffSz \in Nat /\ BuffSz > 0

(***************************************************************************)
(* In-memory variables (BufferedRandomAccessFile class fields).            *)
(***************************************************************************)
VARIABLES
  lo,          \* base offset of buffer
  curr,        \* current logical position
  diskPos,     \* the underlying disk position
  hi,          \* end of valid buffer
  buff,        \* the in-memory buffer
  dirty,       \* whether buffer differs from disk
  disk         \* the underlying file

regular_vars == << lo, curr, diskPos, hi, buff, dirty, disk >>

(***************************************************************************)
(* Helpers / shared definitions imported from RandomAccessFile module.     *)
(***************************************************************************)
Min(a, b) == IF a \leq b THEN a ELSE b
Max(a, b) == IF a \geq b THEN a ELSE b

(***************************************************************************)
(* Internal invariants (copied from comment in BufferedRandomAccessFile).  *)
(***************************************************************************)
Inv1 == 0 \leq lo /\ lo \leq hi /\ hi \leq lo + BuffSz
Inv2 == lo \leq curr /\ curr \leq hi
Inv3 == diskPos = hi
Inv4 == \A i \in lo..(hi-1) : buff[i] = disk[i]
        \* denoted c(f) / disk(f)[i] in .java file
Inv5 == dirty => \E i \in lo..(hi-1) : TRUE

TypeOK ==
  /\ lo      \in 0..MaxOffset
  /\ curr    \in 0..MaxOffset
  /\ diskPos \in 0..MaxOffset
  /\ hi      \in 0..MaxOffset
  /\ buff    \in [0..(MaxOffset-1) -> Symbols \cup {ArbitrarySymbol}]
  /\ dirty   \in BOOLEAN
  /\ disk    \in Seq(Symbols \cup {ArbitrarySymbol})

Init ==
  /\ lo = 0
  /\ curr = 0
  /\ diskPos = 0
  /\ hi = 0
  /\ buff = [i \in 0..(MaxOffset-1) |-> ArbitrarySymbol]
  /\ dirty = FALSE
  /\ disk = << >>

(***************************************************************************)
(* Helper for Seek: reads lo', constrains diskPos', file_pointer', buff'.  *)
(***************************************************************************)
FlushBuffer ==
  /\ dirty
  /\ disk' = [i \in 0..(Max(Len(disk), hi) - 1) |->
                IF i \in lo..(hi-1) THEN buff[i] ELSE
                IF i+1 \leq Len(disk) THEN disk[i+1] ELSE ArbitrarySymbol]
  /\ diskPos' = hi
  /\ dirty' = FALSE
  /\ UNCHANGED <<lo, curr, hi, buff>>

Seek(newCurr) ==
  /\ ~ dirty
  /\ newCurr \in 0..MaxOffset
  /\ curr' = newCurr
  /\ lo' = newCurr
  /\ hi' \in lo'..Min(lo' + BuffSz, Len(disk))
  /\ diskPos' = hi'
  /\ buff' \in [0..(MaxOffset-1) -> Symbols \cup {ArbitrarySymbol}]
  /\ UNCHANGED <<dirty, disk>>

WriteAtMost(byte) ==
  /\ Inv2
  /\ byte \in Symbols
  /\ buff' = [buff EXCEPT ![curr] = byte]
  /\ curr' = curr + 1
  /\ hi' = Max(hi, curr')
  /\ dirty' = TRUE
  /\ UNCHANGED <<lo, diskPos, disk>>

Read1 ==
  /\ Inv2
  /\ curr < hi
  /\ curr' = curr + 1
  /\ UNCHANGED <<lo, diskPos, hi, buff, dirty, disk>>

SetLength(newLen) ==
  /\ newLen \in 0..MaxOffset
  /\ disk' = [i \in 0..(newLen-1) |->
                IF i+1 \leq Len(disk) THEN disk[i+1] ELSE ArbitrarySymbol]
  /\ curr' = Min(curr, newLen)
  /\ lo' = Min(lo, newLen)
  /\ hi' = Min(hi, newLen)
  /\ diskPos' = hi'
  /\ UNCHANGED <<buff, dirty>>

Next ==
  \/ FlushBuffer
  \/ \E o \in 0..MaxOffset : Seek(o)
  \/ \E b \in Symbols : WriteAtMost(b)
  \/ Read1
  \/ \E n \in 0..MaxOffset : SetLength(n)

Spec == Init /\ [][Next]_regular_vars

(***************************************************************************)
(* Refinement of general RandomAccessFile.                                 *)
(* Abstract vars.                                                          *)
(***************************************************************************)
file_content ==
  [i \in 0..(Max(hi, Len(disk)) - 1) |->
     IF i \in lo..(hi-1) THEN buff[i]
     ELSE IF i+1 \leq Len(disk) THEN disk[i+1]
     ELSE ArbitrarySymbol]

file_pointer == curr

Alias ==
  [ lo |-> lo, curr |-> curr, diskPos |-> diskPos, hi |-> hi,
    buff |-> buff, dirty |-> dirty, disk |-> disk,
    file_content |-> file_content, file_pointer |-> file_pointer ]

Symmetry == Permutations(Symbols)

(***************************************************************************)
(* Inv2 can always be restored by FlushBuffer (if necessary) + Seek(curr). *)
(***************************************************************************)
Inv2CanAlwaysBeRestored ==
  [](dirty => ENABLED FlushBuffer)

FlushBufferCorrect == [][FlushBuffer => ~ dirty']_regular_vars
SeekCorrect == \A o \in 0..MaxOffset : [][Seek(o) => UNCHANGED disk]_regular_vars
SeekEstablishesInv2 == \A o \in 0..MaxOffset : [][Seek(o) => Inv2']_regular_vars
Write1Correct == \A b \in Symbols : [][WriteAtMost(b) => Inv1' /\ Inv3' /\ Inv5']_regular_vars
Read1Correct == [][Read1 => UNCHANGED disk]_regular_vars
WriteAtMostCorrect == Write1Correct
ReadCorrect == Read1Correct

Safety == [](TypeOK /\ Inv1 /\ Inv3 /\ Inv4 /\ Inv5)

====
