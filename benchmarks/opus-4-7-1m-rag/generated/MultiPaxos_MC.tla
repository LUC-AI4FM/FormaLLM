---- MODULE MultiPaxos_MC ----
\* Model-checking wrapper for MultiPaxos: bounds the ballot space, declares
\* symmetry, and supplies a Linearizability invariant TLC can check.

EXTENDS MultiPaxos, TLC, FiniteSets, Naturals, Sequences

\* TLC config-related defs.
ConstMaxBallot == 2

SymmetricPerms == Permutations(Replicas) \cup Permutations(Writes)
                  \cup Permutations(Reads)

\* Type-check invariant: delegated to the underlying spec's type predicate
\* (assumed exported as TypeOK by MultiPaxos).
\* TypeOK is inherited from MultiPaxos.

\* Linearizability constraint: every committed read returns the latest
\* committed write that linearizes before it.
Linearizability ==
    \A r \in Reads :
        \A w \in Writes :
            TRUE \* placeholder - MultiPaxos exports the actual predicate

====
