---- MODULE Hanoi ----
(***************************************************************************)
(* Towers of Hanoi with N towers                                           *)
(* D is number of disks and N number of towers                             *)
(* Towers are represented by natural numbers; all towers are empty except  *)
(* all disks are on the first Tower.                                       *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

ASSUME D \in Nat /\ N \in Nat /\ D > 0 /\ N > 0

(***************************************************************************)
(* TRUE iff i is a power of two.  All less significant bits are 0.         *)
(***************************************************************************)
RECURSIVE IsPowerOfTwo(_)
IsPowerOfTwo(i) ==
  IF i = 1 THEN TRUE
  ELSE IF i < 2 \/ (i % 2 # 0) THEN FALSE
  ELSE IsPowerOfTwo(i \div 2)

(***************************************************************************)
(* A set of all powers of two up to n.                                     *)
(***************************************************************************)
PowersOfTwo(n) == { i \in 1..n : IsPowerOfTwo(i) }

(***************************************************************************)
(* Copied from TLA+'s Bags standard library.  The sum of f[x] for all x in *)
(* DOMAIN f.                                                               *)
(***************************************************************************)
RECURSIVE SumFn(_, _)
SumFn(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN f[x] + SumFn(f, S \ {x})

Sum(f) == SumFn(f, DOMAIN f)

(***************************************************************************)
(* Towers are naturals in the interval (0, 2^D].                           *)
(***************************************************************************)
RECURSIVE Pow(_, _)
Pow(b, e) == IF e = 0 THEN 1 ELSE b * Pow(b, e-1)

MaxTowerVal == Pow(2, D)

VARIABLE towers

vars == <<towers>>

(***************************************************************************)
(* The total sum of all towers must amount to the disks in the system.    *)
(***************************************************************************)
TypeOK ==
  /\ towers \in [1..N -> 0..(MaxTowerVal - 1)]
  /\ Sum(towers) = MaxTowerVal - 1

(***************************************************************************)
(* Now we define of the initial predicate, that specifies the initial      *)
(* values of the variables.                                                *)
(***************************************************************************)
Init == towers = [t \in 1..N |-> IF t = 1 THEN MaxTowerVal - 1 ELSE 0]

(***************************************************************************)
(* TRUE iff the tower is empty.                                            *)
(***************************************************************************)
IsEmpty(tower) == towers[tower] = 0

(***************************************************************************)
(* TRUE iff the disk is located on the given tower.                        *)
(***************************************************************************)
OnTower(disk, tower) == (towers[tower] \div disk) % 2 = 1

(***************************************************************************)
(* TRUE iff disk is the smallest disk on tower.                            *)
(***************************************************************************)
Smallest(disk, tower) ==
  /\ OnTower(disk, tower)
  /\ \A d \in PowersOfTwo(MaxTowerVal - 1) :
       d < disk => ~OnTower(d, tower)

(***************************************************************************)
(* TRUE iff disk can be moved off of tower.                                *)
(***************************************************************************)
CanMoveOff(disk, tower) == Smallest(disk, tower)

(***************************************************************************)
(* TRUE iff disk can be moved to the tower.                                *)
(***************************************************************************)
CanMoveTo(disk, tower) ==
  IsEmpty(tower) \/
  \A d \in PowersOfTwo(MaxTowerVal - 1) :
    (d < disk /\ OnTower(d, tower)) = FALSE

(***************************************************************************)
(* Move disk from one tower to another.                                    *)
(* Remaining tower does not change.                                        *)
(* No need to try to move onto the same tower (Move(...) prevents it too)  *)
(***************************************************************************)
Move(disk, from, to) ==
  /\ from # to
  /\ CanMoveOff(disk, from)
  /\ CanMoveTo(disk, to)
  /\ towers' = [towers EXCEPT ![from] = @ - disk,
                              ![to]   = @ + disk]

(***************************************************************************)
(* Define all possible actions that disks can perform.                     *)
(***************************************************************************)
Next ==
  \E disk \in PowersOfTwo(MaxTowerVal - 1) :
    \E from \in 1..N, to \in 1..N :
      Move(disk, from, to)

(***************************************************************************)
(* Spec to be the complete specification, asserting of a behavior that it  *)
(* begins in a state satisfying Init, and that every step either satisfies *)
(* Next or else leaves the pair unchanged.                                 *)
(***************************************************************************)
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* The final configuration has all disks on the right tower.  If TLC is    *)
(* set to run with an invariant rightTower # 2^N-1, it will search for     *)
(* configurations in which this invariant is violated.                     *)
(*                                                                         *)
(* We find a solution by having TLC check if NotSolved is an invariant,    *)
(* which will cause it to print out an "error trace" consisting of a       *)
(* behavior ending in a state where NotSolved is false.                    *)
(***************************************************************************)
NotSolved == towers[N] # MaxTowerVal - 1

====
