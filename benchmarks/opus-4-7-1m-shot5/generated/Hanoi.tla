---- MODULE Hanoi ----
(***************************************************************************)
(* Towers of Hanoi with N towers                                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

ASSUME D \in Nat /\ N \in Nat /\ D > 0 /\ N > 1

(***************************************************************************)
(* TRUE iff i is a power of two                                           *)
(***************************************************************************)
PowerOfTwo(i) ==
  /\ i > 0
  /\ \E k \in 0..D : i = 2^k

(***************************************************************************)
(* A set of all powers of two up to n                                     *)
(***************************************************************************)
PowersOfTwo(n) == { 2^k : k \in 0..(n-1) }

(***************************************************************************)
(* Copied from TLA+'s Bags standard library. The sum of f[x] for all x in *)
(* DOMAIN f.                                                              *)
(***************************************************************************)
RECURSIVE SumFn(_, _)
SumFn(f, S) ==
  IF S = {}
  THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN  f[x] + SumFn(f, S \ {x})

\* Towers are represented by natural numbers
VARIABLES towers

vars == <<towers>>

(***************************************************************************)
(* Towers are naturals in the interval (0, 2^D]                            *)
(***************************************************************************)
TypeOK ==
  /\ towers \in [1..N -> 0..(2^D - 1)]
  (* The total sum of all towers must amount to the disks in the system *)
  /\ SumFn(towers, 1..N) = 2^D - 1

(***************************************************************************)
(* Now we define of the initial predicate, that specifies the initial      *)
(* values of the variables.                                                *)
(***************************************************************************)
\* all towers are empty except all disks are on the first Tower
Init ==
  towers = [t \in 1..N |-> IF t = 1 THEN 2^D - 1 ELSE 0]

(***************************************************************************)
(* TRUE iff the tower is empty                                            *)
(***************************************************************************)
Empty(t) == towers[t] = 0

(***************************************************************************)
(* TRUE iff the disk is located on the given tower                        *)
(***************************************************************************)
OnTower(disk, tower) ==
  \E k \in 0..(D-1) :
    /\ disk = 2^k
    /\ (towers[tower] \div 2^k) % 2 = 1

(***************************************************************************)
(* TRUE iff disk is the smallest disk on tower                            *)
(***************************************************************************)
Smallest(disk, tower) ==
  /\ OnTower(disk, tower)
  \* All less significant bits are 0
  /\ towers[tower] % disk = 0

(***************************************************************************)
(* TRUE iff disk can be moved off of tower                                *)
(***************************************************************************)
CanMoveOff(disk, tower) ==
  /\ OnTower(disk, tower)
  /\ Smallest(disk, tower)

(***************************************************************************)
(* TRUE iff disk can be moved to the tower                                *)
(***************************************************************************)
CanMoveTo(disk, tower) ==
  \/ Empty(tower)
  \/ \A smaller \in PowersOfTwo(D) : smaller < disk => ~OnTower(smaller, tower)

Move(disk, from, to) ==
  /\ from /= to  \* No need to try to move onto the same tower
  /\ CanMoveOff(disk, from)
  /\ CanMoveTo(disk, to)
  /\ towers' = [towers EXCEPT
        ![from] = @ - disk,
        ![to]   = @ + disk]

(***************************************************************************)
(* Define all possible actions that disks can perform.                    *)
(***************************************************************************)
Next ==
  \E disk \in PowersOfTwo(D) :
    \E from \in 1..N :
      \E to \in 1..N : Move(disk, from, to)

(***************************************************************************)
(* We define the formula Spec to be the complete specification, asserting *)
(* of a behavior that it begins in a state satisfying Init, and that every *)
(* step either satisfies Next or else leaves the pair <<big, small>>      *)
(* unchanged.                                                             *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* The final configuration has all disks on the right tower. If TLC is set *)
(* to run with an invariant rightTower # 2^N-1, it will search for         *)
(* configurations in which this invariant is violated.                    *)
(***************************************************************************)
(***************************************************************************)
(* We find a solution by having TLC check if NotSolved is an invariant,   *)
(* which will cause it to print out an "error trace" consisting of a      *)
(* behavior ending in a state where NotSolved is false. With three disks, *)
(* and three towers the puzzle can be solved in seven moves.              *)
(***************************************************************************)
NotSolved == towers[N] # 2^D - 1

(***************************************************************************)
(* Modification History                                                   *)
(* Last modified Tue May 17 14:55:33 CEST 2016 by markus                  *)
(* Created Sun Jul 17 10:20:57 CEST 2011 by markus                       *)
(***************************************************************************)
====
