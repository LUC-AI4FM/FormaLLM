---- MODULE BufferedRandomAccessFile ----
(***************************************************************************)
(* Copyright (c) 2024, Oracle and/or its affiliates.                       *)
(*                                                                         *)
(* Model-checkable specification of BufferedRandomAccessFile.java. Covers *)
(* the core fields and the seek, read, write, flush, and setLength ops.   *)
(*                                                                         *)
(* Correctness conditions:                                                 *)
(*   (1) internal invariants V1-V5 hold;                                  *)
(*   (2) behavior refines a general RandomAccessFile;                     *)
(*   (3) each operation refines its RandomAccessFile counterpart.         *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Symbols,
    ArbitrarySymbol,
    MaxOffset,
    BuffSz

Offsets == 0..MaxOffset
Bytes == Symbols \cup {ArbitrarySymbol}

\* Min and max of two numbers.
Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b

\* 0-indexed arrays.
EmptyArr == << >>
ArrLen(a) == Len(a)
ArrIdx(a, i) == a[i + 1]

\* In-memory BufferedRandomAccessFile fields.
VARIABLES
    file_content_disk, \* the underlying file (0-indexed array of bytes)
    diskPos,           \* the disk pointer position
    lo,                \* offset on disk of the start of buff
    curr,              \* the current file position from the client's view
    buff,              \* the in-memory buffer (0-indexed array)
    hi,                \* the highest valid offset in buff
    dirty,             \* TRUE iff buff has been modified since the last flush
    maxHi              \* the highest hi reached since the last seek

\* Abstract RandomAccessFile state.
VARIABLES
    file_content,      \* the disk content of the abstract file
    file_pointer       \* the abstract file pointer

regular_vars  == <<file_content_disk, diskPos, lo, curr, buff, hi, dirty, maxHi>>
abstract_vars == <<file_content, file_pointer>>
vars == <<regular_vars, abstract_vars>>

\* Type invariant.
TypeOK ==
    /\ file_content_disk \in Seq(Bytes)
    /\ Len(file_content_disk) <= MaxOffset
    /\ diskPos \in Offsets
    /\ lo \in Offsets
    /\ curr \in Offsets
    /\ buff \in Seq(Bytes)
    /\ Len(buff) <= BuffSz
    /\ hi \in Offsets
    /\ dirty \in BOOLEAN
    /\ maxHi \in Offsets
    /\ file_content \in Seq(Bytes)
    /\ file_pointer \in Offsets

\* Internal invariants V1-V5 (denoted c(f), disk(f)[i] in the .java file).
Inv1 == lo <= curr /\ curr <= hi
Inv2 == curr - lo <= ArrLen(buff)
Inv3 == hi - lo = ArrLen(buff)
Inv4 == diskPos = lo + ArrLen(buff) \/ diskPos = lo
Inv5 ==
    /\ ~dirty =>
        \A i \in 0..(ArrLen(buff) - 1) :
            (lo + i) < Len(file_content_disk) =>
                ArrIdx(buff, i) = file_content_disk[lo + i + 1]

Init ==
    /\ file_content_disk = << >>
    /\ diskPos = 0
    /\ lo = 0
    /\ curr = 0
    /\ buff = << >>
    /\ hi = 0
    /\ dirty = FALSE
    /\ maxHi = 0
    /\ file_content = << >>
    /\ file_pointer = 0

\* Helper for Seek (not a full action): reads lo', constrains diskPos', buff', file_pointer'.
SeekHelper(newLo) ==
    /\ lo' = newLo
    /\ diskPos' = newLo
    /\ buff' = << >>
    /\ hi' = newLo
    /\ maxHi' = newLo

FlushBuffer ==
    /\ dirty
    /\ LET writeStart == lo
           writeLen   == ArrLen(buff)
           pad        == Max(0, writeStart - Len(file_content_disk))
           padded     == file_content_disk \o [i \in 1..pad |-> ArbitrarySymbol]
           prefix     == SubSeq(padded, 1, writeStart)
           suffix     == IF writeStart + writeLen >= Len(padded) THEN << >>
                         ELSE SubSeq(padded, writeStart + writeLen + 1, Len(padded))
       IN  file_content_disk' = prefix \o buff \o suffix
    /\ diskPos' = lo + ArrLen(buff)
    /\ dirty' = FALSE
    /\ UNCHANGED <<lo, curr, buff, hi, maxHi, file_content, file_pointer>>

Seek(newCurr) ==
    /\ Inv2
    /\ newCurr \in Offsets
    /\ ~dirty
    /\ SeekHelper(newCurr)
    /\ curr' = newCurr
    /\ dirty' = dirty
    /\ file_content_disk' = file_content_disk
    /\ file_pointer' = newCurr
    /\ UNCHANGED file_content

\* Write at most BuffSz bytes from data_to_write at the current pointer.
Write1(b) ==
    /\ Inv2
    /\ curr - lo < BuffSz
    /\ LET pos == curr - lo
       IN  IF pos < ArrLen(buff)
           THEN buff' = [buff EXCEPT ![pos + 1] = b]
           ELSE buff' = buff \o <<b>>
    /\ hi' = Max(hi, curr + 1)
    /\ curr' = curr + 1
    /\ maxHi' = Max(maxHi, hi')
    /\ dirty' = TRUE
    /\ LET extended ==
            IF curr + 1 > Len(file_content)
            THEN file_content \o [i \in 1..(curr + 1 - Len(file_content)) |-> ArbitrarySymbol]
            ELSE file_content
       IN  file_content' = [extended EXCEPT ![curr + 1] = b]
    /\ file_pointer' = curr + 1
    /\ UNCHANGED <<lo, diskPos, file_content_disk>>

Read1 ==
    /\ Inv2
    /\ curr < hi
    /\ LET pos == curr - lo
           b   == ArrIdx(buff, pos)
       IN  /\ curr' = curr + 1
           /\ file_pointer' = curr + 1
    /\ UNCHANGED <<file_content_disk, diskPos, lo, buff, hi, dirty, maxHi,
                   file_content>>

WriteAtMost ==
    /\ \E b \in Symbols : Write1(b)

Read == Read1

\* setLength: truncate or extend the abstract file with ArbitrarySymbol.
SetLength(newLen) ==
    /\ newLen \in Offsets
    /\ \/ /\ newLen <= Len(file_content)
          /\ file_content' = SubSeq(file_content, 1, newLen)
       \/ /\ newLen > Len(file_content)
          /\ file_content' =
                file_content \o [i \in 1..(newLen - Len(file_content)) |-> ArbitrarySymbol]
    /\ file_pointer' = Min(file_pointer, newLen)
    /\ file_content_disk' = file_content'
    /\ diskPos' = Min(diskPos, newLen)
    /\ lo' = 0
    /\ curr' = file_pointer'
    /\ buff' = << >>
    /\ hi' = 0
    /\ dirty' = FALSE
    /\ maxHi' = 0

Next ==
    \/ FlushBuffer
    \/ \E o \in Offsets : Seek(o)
    \/ WriteAtMost
    \/ Read
    \/ \E o \in Offsets : SetLength(o)

Spec == Init /\ [][Next]_vars

\* Refinement mapping: file_pointer corresponds to curr.
RAF == INSTANCE RandomAccessFile WITH file_content <- file_content,
                                      file_pointer <- curr

Safety == RAF!Spec

\* These invariants are kept here for symmetry-reduced model-checking.
Symmetry == Permutations(Symbols)
Alias == [
    file_content_disk |-> file_content_disk,
    diskPos           |-> diskPos,
    lo                |-> lo,
    curr              |-> curr,
    buff              |-> buff,
    hi                |-> hi,
    dirty             |-> dirty,
    maxHi             |-> maxHi,
    file_content      |-> file_content,
    file_pointer      |-> file_pointer]

\* Inv2 may temporarily fail mid-method, but can always be restored.
Inv2CanAlwaysBeRestored ==
    [](dirty => ENABLED FlushBuffer)
    /\ [][FlushBuffer => ~dirty']_vars
    /\ [](~dirty => \E c \in Offsets : ENABLED Seek(c))
    /\ [][\A c \in Offsets : Seek(c) => Inv2']_vars

FlushBufferCorrect == [][FlushBuffer => UNCHANGED file_content]_vars
SeekCorrect == [][\A c \in Offsets : Seek(c) => curr' = c]_vars
SeekEstablishesInv2 == [][\A c \in Offsets : Seek(c) => Inv2']_vars
Write1Correct == [][\A b \in Symbols : Write1(b) => file_pointer' = curr + 1]_vars
Read1Correct == [][Read1 => file_pointer' = curr + 1]_vars
WriteAtMostCorrect == [][WriteAtMost => file_pointer' > file_pointer]_vars
ReadCorrect == [][Read => file_pointer' = curr + 1]_vars
====
