---- MODULE Hanoi ----
(***************************************************************************)
(* Towers of Hanoi with N towers and D disks.                              *)
(* Towers are represented by natural numbers; each tower's value encodes   *)
(* the set of disks on it as a bitmap (bit k set iff disk k is on tower).  *)
(* All disks start on the first tower; the goal is to move all to another. *)
(*                                                                         *)
(* TLC finds a solution by checking that NotSolved is an invariant. The   *)
(* counter-example trace shows the steps to solve the puzzle. The minimum *)
(* number of moves is 2^D - 1.                                             *)
(*                                                                         *)
(* Modification History                                                    *)
(*   Last modified Tue May 17 14:55:33 CEST 2016 by markus                 *)
(*   Created      Sun Jul 17 10:20:57 CEST 2011 by markus                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS D, N

ASSUME /\ D \in Nat \ {0}
       /\ N \in Nat \ {0}

\* TRUE iff i is a power of two (only one bit set, and i > 0).
RECURSIVE IsPowerOfTwo(_)
IsPowerOfTwo(i) ==
    IF i <= 0 THEN FALSE
    ELSE IF i = 1 THEN TRUE
    ELSE IF i % 2 = 1 THEN FALSE
    ELSE IsPowerOfTwo(i \div 2)

\* The set of all powers of two up to n.
PowersOfTwo(n) == { i \in 1..n : IsPowerOfTwo(i) }

\* Sum of f[x] for all x in DOMAIN f (from TLA+ Bags standard library).
RECURSIVE SetSum(_, _)
SetSum(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN  f[x] + SetSum(f, S \ {x})

Sum(f) == SetSum(f, DOMAIN f)

VARIABLE towers

vars == towers

Towers == 1..N

\* Each tower is a natural in [0, 2^D].
MaxTowerValue == 2^D

TypeOK ==
    /\ towers \in [Towers -> 0..(MaxTowerValue - 1)]
    /\ Sum(towers) = MaxTowerValue - 1  \* total disks = sum of bits = 2^D - 1

\* Initial state: all disks on the first tower, others empty.
Init ==
    towers = [t \in Towers |-> IF t = 1 THEN MaxTowerValue - 1 ELSE 0]

\* TRUE iff the tower is empty.
Empty(t) == towers[t] = 0

\* TRUE iff disk d (a power of two) is located on tower t.
OnTower(d, t) == (towers[t] \div d) % 2 = 1

\* TRUE iff disk is the smallest disk on tower (all less significant bits 0).
SmallestOnTower(d, t) ==
    /\ OnTower(d, t)
    /\ \A e \in PowersOfTwo(d - 1) : ~OnTower(e, t)

\* TRUE iff disk d can be moved off of tower from.
CanMoveOff(d, from) ==
    /\ ~Empty(from)
    /\ OnTower(d, from)
    /\ SmallestOnTower(d, from)

\* TRUE iff disk d can be moved onto tower to.
CanMoveTo(d, to) ==
    \/ Empty(to)
    \/ \E e \in PowersOfTwo(MaxTowerValue - 1) :
           /\ e > d
           /\ SmallestOnTower(e, to)

\* Move disk d from tower from to tower to.
Move(d, from, to) ==
    /\ from /= to                 \* no moving to same tower
    /\ CanMoveOff(d, from)
    /\ CanMoveTo(d, to)
    /\ towers' = [towers EXCEPT
            ![from] = @ - d,
            ![to]   = @ + d]

Next ==
    \E from, to \in Towers :
        \E d \in PowersOfTwo(MaxTowerValue - 1) :
            Move(d, from, to)

Spec == Init /\ [][Next]_vars

\* Goal: all disks on the last tower.
Solved == towers[N] = MaxTowerValue - 1

\* NotSolved as an invariant: TLC's counter-example shows the solution.
NotSolved == ~Solved
====
