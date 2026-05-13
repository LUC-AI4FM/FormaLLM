---- MODULE MultiPaxos_MC ----
(***************************************************************************)
(* TLC model-checking instance for the MultiPaxos specification.           *)
(***************************************************************************)
EXTENDS MultiPaxos, TLC, FiniteSets

(***************************)
(* TLC config-related defs. *)
(***************************)
ConstMaxBallot == 2

SymmetricPerms ==
  Permutations(Replicas) \cup
  Permutations(Writes) \cup
  Permutations(Reads)

(************************)
(* Type check invariant. *)
(************************)
TypeOK ==
  /\ Cardinality(Replicas) > 0
  /\ Cardinality(Writes \cup Reads) > 0

(******************************)
(* Linearizability constraint. *)
(******************************)
Linearizability ==
  \A r1, r2 \in Replicas :
    \A s \in 1..Cardinality(Writes \cup Reads) :
      (s \in DOMAIN log[r1]) /\ (s \in DOMAIN log[r2])
        => log[r1][s] = log[r2][s]

====
