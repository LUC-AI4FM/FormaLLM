---- MODULE Hanoi ----
\* Towers of Hanoi with N towers and D disks.
\*
\* Each tower is represented as a natural number in (0, 2^D].
\* Bit i (i = 0..D-1) is 1 iff disk i sits on the tower (disk 0 is the
\* smallest).  An action moves the smallest disk from one tower to another;
\* this is the lowest set bit of the source tower.
\*
\* We solve the puzzle by asking TLC to check the invariant NotSolved
\* ("not all disks are on tower N"); the counterexample TLC produces is a
\* valid solution.

EXTENDS Naturals, FiniteSets

CONSTANTS D, N    \* D disks, N towers

ASSUME D \in Nat /\ D > 0
ASSUME N \in Nat /\ N > 1

\* ---------- arithmetic helpers ----------

\* RECURSIVE definitions
RECURSIVE Pow2(_)
Pow2(n) == IF n = 0 THEN 1 ELSE 2 * Pow2(n-1)

\* TRUE iff i is a power of two.
IsPow2(i) == \E k \in 0..D : Pow2(k) = i

\* The set of all powers of two up to (but not exceeding) n.
PowersOfTwo(n) == { Pow2(k) : k \in 0..D } \cap 1..n

\* Sum of f[x] for all x in DOMAIN f. Copied from the Bags library.
RECURSIVE Sum(_, _)
Sum(f, S) == IF S = {} THEN 0
             ELSE LET x == CHOOSE y \in S : TRUE
                  IN  f[x] + Sum(f, S \ {x})

\* ---------- state ----------

VARIABLE towers   \* function 1..N -> Nat, the contents of each tower

vars == << towers >>

\* Type-invariant: each tower's value is in [0, 2^D].
TypeOK == towers \in [1..N -> 0..Pow2(D)]

\* The total over all towers must always equal 2^D - 1 (all D disks present).
SumOK == Sum(towers, DOMAIN towers) = Pow2(D) - 1

\* ---------- predicates ----------

\* TRUE iff tower t is empty.
EmptyTower(t) == towers[t] = 0

\* TRUE iff disk d (value 2^d as a one-hot) is on tower t.
OnTower(disk, t) ==
  \* disk is a one-hot value 2^k
  /\ towers[t] >= disk
  /\ (towers[t] \div disk) % 2 = 1

\* TRUE iff disk is the smallest (lowest-bit) disk on tower t.
SmallestOn(disk, t) ==
  /\ OnTower(disk, t)
  /\ \A d2 \in PowersOfTwo(disk - 1) : ~ OnTower(d2, t)

\* TRUE iff disk can be moved off tower t (disk must be smallest on t).
CanMoveOff(disk, t) == SmallestOn(disk, t)

\* TRUE iff disk can be moved onto tower t (no smaller disk already there).
CanMoveOnto(disk, t) ==
  \A d2 \in PowersOfTwo(disk - 1) : ~ OnTower(d2, t)

\* ---------- initial state ----------

\* All disks on tower 1, all others empty.
Init ==
  towers = [t \in 1..N |-> IF t = 1 THEN Pow2(D) - 1 ELSE 0]

\* ---------- move action ----------

\* Move disk from tower src to tower dst.
Move(disk, src, dst) ==
  /\ src \in 1..N /\ dst \in 1..N
  /\ src /= dst
  /\ CanMoveOff(disk, src)
  /\ CanMoveOnto(disk, dst)
  /\ towers' = [towers EXCEPT ![src] = @ - disk, ![dst] = @ + disk]

Next ==
  \E disk \in PowersOfTwo(Pow2(D)), src, dst \in 1..N :
     Move(disk, src, dst)

Spec == Init /\ [][Next]_vars

\* ---------- solving invariants ----------

\* All disks on tower N (the rightmost).
Solved == towers[N] = Pow2(D) - 1

\* If TLC is told NotSolved is an invariant, it will produce a trace ending
\* in a solved state - i.e., a solution to the puzzle.
NotSolved == ~ Solved

====
