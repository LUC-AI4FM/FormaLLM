---- MODULE MultiPaxos_MC ----
(***************************************************************************)
(* Model-checking instance of MultiPaxos. Provides concrete values for    *)
(* TLC configuration, the type-check invariant, and the linearizability   *)
(* invariant.                                                              *)
(***************************************************************************)
EXTENDS MultiPaxos, TLC

\* TLC config-related defs.
ConstMaxBallot == 2

\* Symmetry on replicas to reduce the state space.
SymmetricPerms == Permutations(Replicas)

\* Type check invariant (inherited and re-exported here).
TypeOK == MultiPaxos!TypeOK

\* Linearizability constraint: the order of completed reads/writes is
\* consistent with a sequential history that respects real-time order.
Linearizability == MultiPaxos!Linearizability
====
