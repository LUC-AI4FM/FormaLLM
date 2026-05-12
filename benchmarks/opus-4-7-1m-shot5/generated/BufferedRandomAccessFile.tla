---- MODULE BufferedRandomAccessFile ----
(***************************************************************************)
(* Copyright (c) 2024, Oracle and/or its affiliates.                       *)
(*                                                                          *)
(* This is a model-checkable specification for BufferedRandomAccessFile.java*)
(* It covers the core fields as well as the seek, read, write, flush, and  *)
(* setLength operations.                                                   *)
(*                                                                          *)
(* There are three major correctess conditions:                            *)
(*  (1) the internal invariants V1-V5 should hold                          *)
(*  (2) the behavior should refine a general RandomAccessFile              *)
(*  (3) each operation should refine its RandomAccessFile counterpart      *)
(*                                                                          *)
(* Readers will probably want to start with the general RandomAccessFile   *)
(* spec before reading this one.                                           *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

(* constants *)
CONSTANTS
  Symbols,           \* data stored in the file
  ArbitrarySymbol,   \* special token for an arbitrary symbol
  MaxOffset,         \* the highest possible offset
  BuffSz             \* bound model checking: maximum buffer size

ASSUME
  /\ ArbitrarySymbol \notin Symbols
  /\ MaxOffset \in Nat
  /\ BuffSz \in Nat \ {0}

(* The set of legal offsets *)
Offsets == 0 .. MaxOffset

(* The set of things that can appear at an offset in a file *)
Bytes == Symbols \cup {ArbitrarySymbol}

(* Minimum and maximum of two numbers *)
Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b

(***************************************************************************)
(* Definitions for 0-indexed arrays (as opposed to TLA+ 1-indexed          *)
(* sequences). A major goal of the BufferedRandomAccessFile spec is to     *)
(* prevent off-by-one errors in the implementation.                        *)
(***************************************************************************)
EmptyArr == [i \in {} |-> ArbitrarySymbol]
ArrLen(a) == Cardinality(DOMAIN a)
ArrOfLen(S, n) == IF n = 0 THEN EmptyArr ELSE [i \in 0..(n-1) -> S]
ArrConcat(a, b) ==
  LET la == ArrLen(a)
      lb == ArrLen(b)
  IN  [i \in 0..(la + lb - 1) |->
         IF i < la THEN a[i] ELSE b[i - la]]
ArrSub(a, lo, hi) ==
  IF hi <= lo THEN EmptyArr
  ELSE [i \in 0..(hi - lo - 1) |-> a[lo + i]]

(* General contract of the file `write()` call: extend the file with      *)
(* ArbitrarySymbols if necessary, then overlay some `data_to_write` at    *)
(* the given offset.                                                     *)
FileWrite(file, off, data_to_write) ==
  LET dlen == ArrLen(data_to_write)
      newLen == Max(ArrLen(file), off + dlen)
      extended == [i \in 0..(newLen - 1) |->
                    IF i \in DOMAIN file THEN file[i] ELSE ArbitrarySymbol]
  IN  [i \in 0..(newLen - 1) |->
        IF i >= off /\ i < off + dlen
          THEN data_to_write[i - off]
          ELSE extended[i]]

(* General contract of the file `setLength()` call: truncate the file or  *)
(* fill it with ArbitrarySymbol to reach the desired length.              *)
FileSetLength(file, newLen) ==
  IF newLen = 0 THEN EmptyArr
  ELSE [i \in 0..(newLen - 1) |->
         IF i \in DOMAIN file THEN file[i] ELSE ArbitrarySymbol]

(* in-memory variables (BufferedRandomAccessFile class fields) *)
VARIABLES
  lo,        \* logical offset of the buffer in the file
  curr,      \* current file pointer (logical)
  hi,        \* upper bound of the valid bytes in the buffer
  diskPos,   \* disk seek position
  dirty,     \* whether buff contains data not yet flushed
  buff,      \* the in-memory buffer
  disk       \* the underlying file

(* regular vars *)
vars == <<lo, curr, hi, diskPos, dirty, buff, disk>>

(* abstract vars *)
file_content == disk
file_pointer == curr

(***************************************************************************)
(* Internal invariants (copied from comment in                             *)
(* BufferedRandomAccessFile.java).                                         *)
(***************************************************************************)
TypeOK ==
  /\ lo \in Offsets
  /\ curr \in Offsets
  /\ hi \in Offsets
  /\ diskPos \in Offsets
  /\ dirty \in BOOLEAN
  /\ buff \in [0..(BuffSz - 1) -> Bytes]
  /\ disk \in UNION { [0..(n-1) -> Bytes] : n \in 0 .. MaxOffset } \cup {EmptyArr}

(* V1: hi - lo <= BuffSz *)
Inv1 == hi - lo <= BuffSz
(* V2: lo <= curr <= hi    (denoted c(f) in .java file) *)
Inv2 == lo <= curr /\ curr <= hi
(* V3: disk content matches buff[i - lo] for i in [lo, hi) when not dirty,
       denoted disk(f)[i] in .java file *)
Inv3 ==
  ~ dirty =>
    \A i \in lo .. (hi - 1) :
      (i \in DOMAIN disk) => disk[i] = buff[i - lo]
(* V4: hi is within the file or at end *)
Inv4 == hi <= ArrLen(disk) \/ dirty
(* V5: diskPos and curr alignment *)
Inv5 == ~ dirty => diskPos \in {lo, hi}

(* f.closed == closed(f) \* close() not described in this spec *)
(* f.curr == curr(f)     \* by definition; see `file_pointer <- curr` in
                            refinement mapping below *)

(***************************************************************************)
(* Inv2 is a bit special.  Most methods restore it just before they return.*)
(* It is generally restored by calling                                     *)
(* `restoreInvariantsAfterIncreasingCurr()`. But, that behavior is         *)
(* difficult to model in straight TLA+ because each method may modify      *)
(* variables multiple times.  So instead, this spec treats Inv2 as a       *)
(* precondition for the methods and verifies that it is always restored by *)
(* calling `restoreInvariantsAfterIncreasingCurr()`.                       *)
(* See `Inv2CanAlwaysBeRestored` below.                                    *)
(***************************************************************************)

----------------------------------------------------------------------------
(* Behavior *)
Init ==
  /\ lo = 0
  /\ curr = 0
  /\ hi = 0
  /\ diskPos = 0
  /\ dirty = FALSE
  /\ buff = [i \in 0..(BuffSz - 1) |-> ArbitrarySymbol]
  /\ disk = EmptyArr

(* call to FlushBuffer *)
FlushBuffer ==
  /\ dirty
  /\ disk' =
       LET fileLen == Max(ArrLen(disk), hi)
           padded  == [i \in 0..(fileLen - 1) |->
                       IF i \in DOMAIN disk THEN disk[i] ELSE ArbitrarySymbol]
       IN  [i \in 0..(fileLen - 1) |->
            IF i >= lo /\ i < hi THEN buff[i - lo] ELSE padded[i]]
  /\ diskPos' = hi
  /\ dirty' = FALSE
  /\ UNCHANGED <<lo, curr, hi, buff>>

(* Helper for Seek (not a full action):
     - reads lo'
     - constrains diskPos', file_pointer', and buff' *)
SeekHelper(newLo) ==
  /\ newLo \in Offsets
  /\ ~ dirty
  /\ lo' = newLo
  /\ hi' = Min(newLo + BuffSz, ArrLen(disk))
  /\ diskPos' = lo'
  /\ UNCHANGED <<dirty, disk>>
  (* super.seek(this.lo) *)
  (* In reality the buffer doesn't change---but some of its bytes might no
     longer be relevant and have to be marked as arbitrary. *)
  /\ buff' \in [0..(BuffSz - 1) -> Bytes]
  /\ \A i \in lo' .. (hi' - 1) :
        (i \in DOMAIN disk) => buff'[i - lo'] = disk[i]

Seek(newCurr) ==
  /\ newCurr \in Offsets
  /\ \/ /\ newCurr >= lo /\ newCurr <= hi
        /\ curr' = newCurr
        /\ UNCHANGED <<lo, hi, diskPos, dirty, buff, disk>>
     \/ /\ \/ newCurr < lo \/ newCurr > hi
        /\ SeekHelper(newCurr)
        /\ curr' = newCurr

Write1(b) ==
  /\ b \in Symbols
  /\ Inv2
  /\ curr >= lo /\ curr < lo + BuffSz
  /\ buff' = [buff EXCEPT ![curr - lo] = b]
  /\ hi' = Max(hi, curr + 1)
  /\ curr' = curr + 1
  /\ dirty' = TRUE
  /\ UNCHANGED <<lo, diskPos, disk>>

Read1 ==
  /\ Inv2
  /\ curr < hi
  /\ UNCHANGED <<lo, hi, diskPos, dirty, buff, disk>>
  /\ curr' = curr + 1

(***************************************************************************)
(* The `write()` method is composed of repeated calls to `writeAtMost()`,  *)
(* so verifying that the latter maintains all our invariants should be    *)
(* sufficient.                                                            *)
(***************************************************************************)
WriteAtMost(data) ==
  \E i \in 0 .. (BuffSz - 1) :
    /\ ArrLen(data) > 0
    /\ Write1(data[0])

ReadAction == Read1

SetLength(newLen) ==
  /\ newLen \in Offsets
  /\ disk' = FileSetLength(disk, newLen)
  /\ curr' = IF curr > newLen THEN newLen ELSE curr
  /\ lo' = Min(lo, newLen)
  /\ hi' = Min(hi, newLen)
  /\ dirty' = FALSE
  /\ diskPos' = Min(diskPos, newLen)
  /\ UNCHANGED buff

Next ==
  \/ FlushBuffer
  \/ \E off \in Offsets : Seek(off)
  \/ \E b \in Symbols : Write1(b)
  \/ Read1
  \/ \E n \in Offsets : SetLength(n)

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement of general RandomAccessFile                                  *)
(* Ensure that the various actions behave according to their abstract     *)
(* specifications.                                                        *)
(***************************************************************************)
RAF == INSTANCE RandomAccessFile WITH
  Symbols <- Symbols,
  ArbitrarySymbol <- ArbitrarySymbol,
  MaxOffset <- MaxOffset,
  file_content <- file_content,
  file_pointer <- file_pointer

Safety == RAF!Spec

FlushBufferCorrect == [][FlushBuffer => UNCHANGED <<file_content, file_pointer>>]_vars
SeekCorrect == [][\A o \in Offsets : Seek(o) => RAF!Seek(o)]_vars
SeekEstablishesInv2 == [][\A o \in Offsets : Seek(o) => Inv2']_vars
Write1Correct == [][\A b \in Symbols : Write1(b) => RAF!Write(b)]_vars
Read1Correct == [][Read1 => RAF!Read]_vars
WriteAtMostCorrect == [][\A d \in [0..(BuffSz - 1) -> Symbols] : WriteAtMost(d) => RAF!Spec]_vars
ReadCorrect == [][ReadAction => RAF!Read]_vars

(***************************************************************************)
(* Inv2 is a precondition for many actions; it should always be possible  *)
(* to restore Inv2 by execuing `restoreInvariantsAfterIncreasingCurr()`.   *)
(* That method calls `seek(curr)`, which is composed of a FlushBuffer      *)
(* followed by a Seek, or just a Seek.                                    *)
(*                                                                         *)
(* To ensure that `restoreInvariantsAfterIncreasingCurr()` works as       *)
(* expected, we'll verify a few things:                                   *)
(*  - dirty => ENABLED FlushBuffer                                        *)
(*  - FlushBuffer => ~dirty'                                              *)
(*  - ~dirty => ENABLED Seek(curr)                                        *)
(*  - Seek(curr) => Inv2'                                                 *)
(***************************************************************************)
Inv2CanAlwaysBeRestored ==
  /\ [](dirty => ENABLED FlushBuffer)
  /\ [][FlushBuffer => ~ dirty']_vars
  /\ [](~ dirty => ENABLED Seek(curr))
  /\ [][Seek(curr) => Inv2']_vars

----------------------------------------------------------------------------
(* Model checking helper definitions *)
Symmetry == Permutations(Symbols)

Alias == [
  lo |-> lo, curr |-> curr, hi |-> hi,
  diskPos |-> diskPos, dirty |-> dirty,
  buff |-> buff, disk |-> disk,
  file_content |-> file_content,
  file_pointer |-> file_pointer
]
====
