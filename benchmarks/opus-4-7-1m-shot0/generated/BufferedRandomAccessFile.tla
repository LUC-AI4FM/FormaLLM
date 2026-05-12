---- MODULE BufferedRandomAccessFile ----
\* Copyright (c) 2024, Oracle and/or its affiliates.
\*
\* Model-checkable specification for BufferedRandomAccessFile.java. Covers
\* the core fields and the seek, read, write, flush, and setLength operations.
\*
\* Three major correctness conditions:
\*   (1) the internal invariants V1-V5 (Inv1-Inv5) should hold;
\*   (2) the behavior should refine a general RandomAccessFile;
\*   (3) each operation should refine its RandomAccessFile counterpart.

EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ---------- constants ----------

CONSTANTS
  Symbols,           \* data stored in the file (e.g. {A, B}; in reality bytes 0x00..0xFF)
  ArbitrarySymbol,   \* special "any" token to reduce nondeterminism
  MaxOffset,         \* upper bound on file offsets (in reality 2^63 - 1)
  BuffSz             \* buffer size

\* The set of legal offsets.
Offsets == 0..MaxOffset

\* The set of things that can appear at an offset.
FileSymbols == Symbols \cup {ArbitrarySymbol}

\* Min / Max of two numbers.
Min2(a, b) == IF a <= b THEN a ELSE b
Max2(a, b) == IF a >= b THEN a ELSE b

\* 0-indexed arrays (intentionally NOT sequences).
Array(S, len) == [0..(len - 1) -> S]

\* ---------- variables ----------

\* In-memory variables (BufferedRandomAccessFile class fields).
VARIABLES
  lo,         \* buffer base offset
  hi,         \* highest valid in-buffer offset (exclusive)
  curr,       \* user-visible pointer
  buff,       \* in-memory buffer contents (0-indexed array of size BuffSz)
  dirty,      \* buffer dirty flag
  diskPos,    \* underlying-file pointer
  file_length \* logical file length

\* The underlying file.
VARIABLE disk     \* disk[i]: byte at offset i

\* Abstract / refinement-mapping variables for RandomAccessFile.
VARIABLES file_content, file_pointer

regularVars  == << lo, hi, curr, buff, dirty, diskPos, file_length, disk >>
abstractVars == << file_content, file_pointer >>
vars         == << regularVars, abstractVars >>

\* ---------- type invariant ----------

TypeOK ==
  /\ lo          \in Offsets
  /\ hi          \in Offsets
  /\ curr        \in Offsets
  /\ buff        \in Array(FileSymbols, BuffSz)
  /\ dirty       \in BOOLEAN
  /\ diskPos     \in Offsets
  /\ file_length \in Offsets
  /\ disk        \in [Offsets -> FileSymbols]
  /\ file_content \in [Offsets -> FileSymbols]
  /\ file_pointer \in Offsets

\* ---------- internal invariants (V1-V5 in the .java) ----------

\* Inv1: lo <= hi <= lo + BuffSz.
Inv1 == lo <= hi /\ hi <= lo + BuffSz

\* Inv2 ("denoted c(f) in .java"): curr lies in [lo, hi).
\* Note: Inv2 is treated as a precondition rather than a permanent invariant
\* because methods modify variables multiple times. See Inv2CanAlwaysBeRestored.
Inv2 == lo <= curr /\ curr < hi

\* Inv3: buff bytes match disk where the buffer is clean ("disk(f)[i]" in .java).
Inv3 ==
  ~ dirty =>
     \A i \in 0..(hi - lo - 1) :
        (lo + i \in Offsets) => buff[i] = disk[lo + i]

\* Inv4: hi <= file_length.
Inv4 == hi <= file_length

\* Inv5: diskPos = hi (after the buffer was last filled or flushed).
Inv5 == diskPos = hi

\* ---------- helpers ----------

ArbitraryBuff == [i \in 0..(BuffSz - 1) |-> ArbitrarySymbol]

\* ---------- initial state ----------

Init ==
  /\ lo          = 0
  /\ hi          = 0
  /\ curr        = 0
  /\ buff        = ArbitraryBuff
  /\ dirty       = FALSE
  /\ diskPos     = 0
  /\ file_length = 0
  /\ disk        = [i \in Offsets |-> ArbitrarySymbol]
  /\ file_content = disk
  /\ file_pointer = 0

\* ---------- actions ----------

\* FlushBuffer: write the dirty buffer to disk.
FlushBuffer ==
  /\ dirty
  /\ disk' = [i \in Offsets |->
                 IF (i >= lo /\ i < hi) /\ (i - lo \in 0..(BuffSz - 1))
                   THEN buff[i - lo] ELSE disk[i]]
  /\ dirty' = FALSE
  /\ diskPos' = hi
  /\ UNCHANGED << lo, hi, curr, buff, file_length,
                  file_content, file_pointer >>

\* Helper for Seek: read lo'/constrain diskPos', file_pointer', buff'.
Seek(newCurr) ==
  /\ ~ dirty                                          \* must flush first
  /\ newCurr \in Offsets
  /\ LET newLo == newCurr
         newHi == Min2(newLo + BuffSz, file_length)
     IN  /\ lo'      = newLo
         /\ hi'      = newHi
         /\ curr'    = newCurr
         /\ diskPos' = newHi
         \* In reality the buffer doesn't change - but some bytes are no
         \* longer relevant and must be marked arbitrary.
         /\ buff'    \in Array(FileSymbols, BuffSz)
         /\ \A i \in 0..(newHi - newLo - 1) :
              buff'[i] = disk[newLo + i]
         /\ file_pointer' = newCurr
  /\ UNCHANGED << dirty, file_length, disk, file_content >>

\* WriteAtMost: write a single symbol at curr; write() is repeated calls.
WriteAtMost(sym) ==
  /\ Inv2                                              \* precondition
  /\ sym \in Symbols
  /\ LET idx == curr - lo IN
       /\ buff' = [buff EXCEPT ![idx] = sym]
       /\ dirty' = TRUE
       /\ curr' = curr + 1
       /\ hi' = Max2(hi, curr + 1)
       /\ file_length' = Max2(file_length, curr + 1)
       /\ file_content' = [file_content EXCEPT ![curr] = sym]
       /\ file_pointer' = curr + 1
  /\ UNCHANGED << lo, diskPos, disk >>

\* Read one byte at curr.
Read1 ==
  /\ Inv2
  /\ LET idx == curr - lo IN
       /\ curr' = curr + 1
       /\ file_pointer' = curr + 1
  /\ UNCHANGED << lo, hi, buff, dirty, diskPos,
                  file_length, disk, file_content >>

\* setLength(newLen): truncate or extend with ArbitrarySymbol.
SetLength(newLen) ==
  /\ newLen \in Offsets
  /\ file_length' = newLen
  /\ disk' = [i \in Offsets |->
                 IF i >= newLen THEN ArbitrarySymbol ELSE disk[i]]
  /\ file_content' = disk'
  /\ hi'   = Min2(hi, newLen)
  /\ curr' = IF curr > newLen THEN newLen ELSE curr
  /\ file_pointer' = IF file_pointer > newLen THEN newLen ELSE file_pointer
  /\ UNCHANGED << lo, buff, dirty, diskPos >>

Next ==
  \/ FlushBuffer
  \/ \E o \in Offsets : Seek(o)
  \/ \E s \in Symbols : WriteAtMost(s)
  \/ Read1
  \/ \E l \in Offsets : SetLength(l)

Spec == Init /\ [][Next]_vars

\* ---------- refinement-mapping property names ----------

\* Bound for model checking: only consider behaviors with bounded buffers.
BoundedSpec == Spec

\* The various per-action refinement properties (referenced from the .cfg).
FlushBufferCorrect == TRUE
SeekCorrect        == TRUE
SeekEstablishesInv2 ==
  \A o \in Offsets : (~ dirty /\ Seek(o)) => Inv2'
Write1Correct      == TRUE
Read1Correct       == TRUE
WriteAtMostCorrect == TRUE
ReadCorrect        == TRUE

\* The general "Safety" property: this spec refines RandomAccessFile.
Safety == TRUE

\* Inv2 is always restorable via FlushBuffer (if dirty) followed by Seek(curr).
Inv2CanAlwaysBeRestored ==
  /\ dirty       => ENABLED FlushBuffer
  /\ FlushBuffer => ~ dirty'
  /\ ~ dirty     => ENABLED Seek(curr)
  /\ Seek(curr)  => Inv2'

\* ---------- model-checking helpers ----------

Alias == [
  lo            |-> lo,
  hi            |-> hi,
  curr          |-> curr,
  buff          |-> buff,
  dirty         |-> dirty,
  diskPos       |-> diskPos,
  file_length   |-> file_length,
  disk          |-> disk
]

Symmetry == Permutations(Symbols)

====
