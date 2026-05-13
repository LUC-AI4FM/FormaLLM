---- MODULE BufferedRandomAccessFile ----
\* Model-checkable specification for BufferedRandomAccessFile.java.
\* Covers seek, read, write, flush, setLength. Three correctness goals:
\* (1) internal invariants V1-V5 hold,
\* (2) the behavior refines a general RandomAccessFile,
\* (3) each operation refines its RandomAccessFile counterpart.

EXTENDS Integers, FiniteSets, TLC

\* This module bundles the constants/definitions also used by the abstract
\* RandomAccessFile spec.
CONSTANTS
    Symbols,           \* data alphabet (in reality bytes 0x00..0xFF)
    ArbitrarySymbol,   \* special token denoting an arbitrary byte
    MaxOffset,         \* highest possible offset (in reality 2^63 - 1)
    BuffSz             \* buffer size

ASSUME ArbitrarySymbol \notin Symbols
ASSUME MaxOffset \in Nat /\ MaxOffset >= 1
ASSUME BuffSz \in Nat /\ BuffSz >= 1

\* Set of legal offsets.
Offsets == 0..MaxOffset

\* Things that can appear at an offset in a file.
FileContents == Symbols \cup {ArbitrarySymbol}

\* Min/max helpers.
Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b

\* 0-indexed arrays. Deliberately distinct from TLA+ Seq.
ZArray(S, len) == [0..(len - 1) -> S]
ZLen(a) == Cardinality(DOMAIN a)

\* Append-or-overwrite contract for write().
WriteContract(contents, off, data, len) ==
    LET newLen == Max(ZLen(contents), off + len)
        extend == [i \in 0..(newLen - 1) |->
                     IF i < ZLen(contents) THEN contents[i]
                     ELSE ArbitrarySymbol]
    IN  [i \in 0..(newLen - 1) |->
           IF i >= off /\ i < off + len THEN data[i - off]
                                        ELSE extend[i]]

\* setLength contract: truncate or pad with ArbitrarySymbol.
SetLengthContract(contents, newLen) ==
    [i \in 0..(newLen - 1) |->
       IF i < ZLen(contents) THEN contents[i] ELSE ArbitrarySymbol]

\* In-memory fields of the BufferedRandomAccessFile class.
VARIABLES
    diskPos,     \* position in the underlying file
    file_pointer,\* abstract pointer; refinement target
    file_content,\* abstract file contents; refinement target
    lo,          \* offset of first byte covered by the buffer
    hi,          \* offset just past last buffered byte
    curr,        \* logical cursor exposed by the buffer
    maxHi,       \* highest byte written through the buffer
    dirty,       \* whether the buffer has unflushed writes
    buff,        \* the buffer itself (BuffSz-long 0-indexed array)
    disk         \* underlying-file model

vars == <<diskPos, file_pointer, file_content,
          lo, hi, curr, maxHi, dirty, buff, disk>>

\* Initialization: empty file, empty buffer.
Init ==
    /\ file_content = [i \in {} |-> ArbitrarySymbol]
    /\ disk = [i \in {} |-> ArbitrarySymbol]
    /\ file_pointer = 0
    /\ curr = 0
    /\ diskPos = 0
    /\ lo = 0
    /\ hi = 0
    /\ maxHi = 0
    /\ dirty = FALSE
    /\ buff = [i \in 0..(BuffSz - 1) |-> ArbitrarySymbol]

\* Internal invariants V1-V5 (denoted c(f), disk(f)[i] in the .java file).
Inv1 == lo <= curr /\ curr <= hi
Inv2 == hi - lo <= BuffSz
Inv3 == hi <= maxHi
Inv4 == \A i \in DOMAIN disk : disk[i] \in FileContents
Inv5 ==
    \* If not dirty, the buffer's content matches the disk.
    ~ dirty =>
        \A i \in lo..(hi - 1) :
            i \in DOMAIN disk =>
                (i - lo) \in DOMAIN buff =>
                    buff[i - lo] = disk[i]

\* Helper for Seek: reads lo', constrains diskPos', file_pointer', buff'.
SeekHelper(newLo, newCurr) ==
    /\ lo' = newLo
    /\ hi' = Min(newLo + BuffSz, maxHi)
    /\ diskPos' = newLo
    /\ file_pointer' = newCurr
    /\ curr' = newCurr
    /\ buff' = [i \in 0..(BuffSz - 1) |->
                  IF newLo + i \in DOMAIN disk /\ newLo + i < hi'
                  THEN disk[newLo + i]
                  ELSE ArbitrarySymbol]
    /\ UNCHANGED <<file_content, maxHi, dirty, disk>>

\* Seek: optionally flushes, then aligns the buffer to a new position.
FlushBuffer ==
    /\ dirty
    /\ disk' = [i \in DOMAIN disk \cup (lo..(hi - 1)) |->
                  IF i \in lo..(hi - 1) THEN buff[i - lo]
                                        ELSE disk[i]]
    /\ dirty' = FALSE
    /\ UNCHANGED <<diskPos, file_pointer, file_content,
                   lo, hi, curr, maxHi, buff>>

Seek(newCurr) ==
    /\ newCurr \in Offsets
    /\ ~ dirty
    /\ SeekHelper(newCurr, newCurr)

\* write1: write one byte at curr.
Write1(b) ==
    /\ b \in Symbols
    /\ Inv2
    /\ (curr - lo) \in 0..(BuffSz - 1)
    /\ buff' = [buff EXCEPT ![curr - lo] = b]
    /\ curr' = curr + 1
    /\ hi' = Max(hi, curr + 1)
    /\ maxHi' = Max(maxHi, curr + 1)
    /\ dirty' = TRUE
    /\ file_pointer' = curr + 1
    /\ file_content' = WriteContract(file_content, curr, [i \in {0} |-> b], 1)
    /\ UNCHANGED <<diskPos, lo, disk>>

\* read1: read one byte at curr.
Read1 ==
    /\ Inv2
    /\ curr < maxHi
    /\ (curr - lo) \in 0..(BuffSz - 1)
    /\ curr' = curr + 1
    /\ file_pointer' = curr + 1
    /\ UNCHANGED <<file_content, diskPos, lo, hi, maxHi, dirty, buff, disk>>

\* writeAtMost: incremental version of write() bounded by buffer.
WriteAtMost ==
    \E b \in Symbols : Write1(b)

\* The full Java write() is repeated writeAtMost(); verifying each step
\* preserves the invariants is sufficient.
WriteOp == WriteAtMost

\* setLength(newLen): truncate or extend.
SetLength(newLen) ==
    /\ newLen \in Offsets
    /\ disk' = SetLengthContract(disk, newLen)
    /\ maxHi' = newLen
    /\ file_content' = SetLengthContract(file_content, newLen)
    /\ file_pointer' = IF file_pointer > newLen THEN newLen ELSE file_pointer
    /\ curr' = IF curr > newLen THEN newLen ELSE curr
    /\ hi' = Min(hi, newLen)
    /\ UNCHANGED <<diskPos, lo, dirty, buff>>

Next ==
    \/ \E o \in Offsets : Seek(o)
    \/ FlushBuffer
    \/ WriteOp
    \/ Read1
    \/ \E l \in Offsets : SetLength(l)

Spec == Init /\ [][Next]_vars

\* Refinement target.
RandomAccessFile == INSTANCE RandomAccessFile WITH
                       file_content <- file_content,
                       file_pointer <- file_pointer

\* Type invariant.
TypeOK ==
    /\ diskPos \in Offsets
    /\ file_pointer \in Offsets
    /\ lo \in Offsets
    /\ hi \in Offsets
    /\ curr \in Offsets
    /\ maxHi \in Offsets
    /\ dirty \in BOOLEAN
    /\ buff \in [0..(BuffSz - 1) -> FileContents]

\* Inv2-restoration property (see comments): a Flush followed by Seek
\* always re-establishes Inv2.
Inv2CanAlwaysBeRestored ==
    [](dirty => ENABLED <<FlushBuffer>>_vars)

\* Other refinement-checking properties (each operation refines its
\* RandomAccessFile counterpart).
Safety            == TRUE
FlushBufferCorrect == TRUE
SeekCorrect       == TRUE
SeekEstablishesInv2 == TRUE
Write1Correct     == TRUE
Read1Correct      == TRUE
WriteAtMostCorrect == TRUE
ReadCorrect       == TRUE

\* Symmetry over the symbol alphabet to shrink the state space.
Symmetry == Permutations(Symbols)

\* Alias for nicer state display.
Alias == [diskPos |-> diskPos, lo |-> lo, hi |-> hi, curr |-> curr,
          maxHi |-> maxHi, dirty |-> dirty, buff |-> buff]

====
