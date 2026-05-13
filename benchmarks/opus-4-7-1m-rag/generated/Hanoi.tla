---- MODULE Hanoi ----
\* Towers of Hanoi with N towers.
\*
\* Towers are represented by natural numbers: bit i of the value held by
\* a tower is 1 iff disk i is on that tower.  All less significant bits
\* of the smallest disk on a tower are 0.  The remaining tower does not
\* change.  No need to try to move onto the same tower (Move(...)
\* prevents it too).

EXTENDS Naturals, FiniteSets

CONSTANT D,  \* number of disks
         N   \* number of towers

ASSUME /\ D \in Nat /\ D > 0
       /\ N \in Nat /\ N > 1

\* TRUE iff i is a power of two.
IsPowerOfTwo(i) == \E k \in 0 .. D : 2^k = i

\* A set of all powers of two up to n.
PowersOfTwo(n) == { 2^k : k \in 0 .. n }

\* Copied from TLA+'s Bags standard library.  The sum of f[x] for all x
\* in DOMAIN f.
Sum(f) ==
  LET DSum[S \in SUBSET DOMAIN f] ==
        LET elt == IF S = {} THEN CHOOSE x \in DOMAIN f : TRUE
                             ELSE CHOOSE x \in S : TRUE
        IN  IF S = {} THEN 0
                      ELSE f[elt] + DSum[S \ {elt}]
  IN  DSum[DOMAIN f]

\* The state is a function from tower index to a natural in [0, 2^D),
\* whose bit pattern encodes the disks on that tower.
VARIABLE towers

vars == towers

\* Towers are naturals in the interval [0, 2^D).
TypeOK == towers \in [1..N -> 0 .. 2^D - 1]

\* The total sum of all towers must amount to the disks in the system.
\* The bits across all towers must partition {0, ..., D-1} -- equivalently,
\* the sum of the values equals 2^D - 1 (all bits set somewhere).
Inv == Sum(towers) = 2^D - 1

\* Initially all towers are empty except all disks are on the first
\* tower.
Init == towers = [t \in 1..N |-> IF t = 1 THEN 2^D - 1 ELSE 0]

\* TRUE iff the tower is empty.
IsEmpty(tower) == towers[tower] = 0

\* TRUE iff the disk is located on the given tower.  disk is encoded as
\* a power of two (= 2^i for disk i).
OnTower(disk, tower) ==
  \E k \in 0 .. D-1 : /\ disk = 2^k
                      /\ (towers[tower] \div 2^k) % 2 = 1

\* TRUE iff disk is the smallest disk on tower.  Equivalently, all bits
\* less significant than disk are 0 in tower's value.
SmallestOn(disk, tower) ==
  /\ OnTower(disk, tower)
  /\ towers[tower] % disk = 0

\* TRUE iff disk can be moved off of tower.
CanMoveFrom(disk, tower) == SmallestOn(disk, tower)

\* TRUE iff disk can be moved to the tower.
CanMoveTo(disk, tower) ==
  \/ IsEmpty(tower)
  \/ \E k \in 0 .. D-1 :
        /\ disk < 2^k
        /\ SmallestOn(2^k, tower)

\* Move the disk from tower a to tower b.
Move(disk, a, b) ==
  /\ a # b
  /\ CanMoveFrom(disk, a)
  /\ CanMoveTo(disk, b)
  /\ towers' = [towers EXCEPT
                  ![a] = @ - disk,
                  ![b] = @ + disk]

\* Define all possible actions that disks can perform.
Next == \E disk \in PowersOfTwo(D-1) :
          \E a, b \in 1..N : Move(disk, a, b)

\* We define the formula Spec to be the complete specification, asserting
\* of a behavior that it begins in a state satisfying Init, and that
\* every step either satisfies Next or else leaves towers unchanged.
Spec == Init /\ [][Next]_vars

\* The final configuration has all disks on the right tower.  If TLC is
\* set to run with an invariant rightTower # 2^D - 1, it will search for
\* configurations in which this invariant is violated.  If a violation
\* can be found, the stack trace shows the steps to solve the Hanoi
\* problem.
rightTower == towers[N]

\* We find a solution by having TLC check if NotSolved is an invariant,
\* which will cause it to print out an "error trace" consisting of a
\* behavior ending in a state where NotSolved is false.  With three
\* disks and three towers the puzzle can be solved in seven moves.  The
\* minimum number of moves required to solve a Tower of Hanoi puzzle
\* generally is 2^n - 1 where n is the number of disks, so the
\* counter-examples shown by TLC will be of length 2^n - 1.
NotSolved == rightTower # 2^D - 1

====
