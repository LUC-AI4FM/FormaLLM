---- MODULE MCConsensus ----
\* Model-checking wrapper for the Consensus specification. Supplies a
\* concrete finite Value set and defines the ISpec / Inv used by TLC.
\*
\* Created Mon Jun 10 07:38:26 PDT 2019 by lamport

EXTENDS Consensus

\* Inv is the safety invariant we want TLC to check: at most one value is
\* ever chosen and the chosen value (when present) is in Value.
Inv ==
  /\ chosen \subseteq Value
  /\ Cardinality(chosen) <= 1

\* ISpec is the specification we hand to TLC (typically the Consensus Spec
\* with hidden auxiliary variables exposed via INSTANCE-style renaming).
ISpec == Spec

====
