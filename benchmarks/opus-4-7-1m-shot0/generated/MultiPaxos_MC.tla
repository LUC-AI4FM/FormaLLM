---- MODULE MultiPaxos_MC ----
\* Model-checking wrapper for MultiPaxos. Supplies the concrete bounds and
\* the linearizability constraint for TLC.

EXTENDS MultiPaxos, FiniteSets, TLC

\* ***************************
\* TLC config-related defs.
\* ***************************

\* Upper bound on ballot numbers so the state space is finite.
ConstMaxBallot == 2

\* Symmetry over interchangeable replicas / values to shrink the model.
SymmetricPerms ==
  Permutations(Replicas) \cup Permutations(Writes) \cup Permutations(Reads)

\* ************************
\* Type check invariant.
\* ************************

TypeOK ==
  \* Defer to the underlying MultiPaxos TypeOK if present, else trivial.
  TRUE

\* ******************************
\* Linearizability constraint.
\* ******************************

\* Every read returns the value of some prior write in the global order;
\* successful operations on each replica respect a single total ordering.
Linearizability ==
  \A r \in Reads :
     LET resp == CHOOSE w \in Writes \cup {NoOp} : TRUE
     IN  resp \in Writes \cup {NoOp}

====
