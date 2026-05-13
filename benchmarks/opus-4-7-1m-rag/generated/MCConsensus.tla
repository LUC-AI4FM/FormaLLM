---- MODULE MCConsensus ----
\* Model-checking wrapper for Consensus. Supplies a finite set of model
\* values for the Value constant so TLC can enumerate the state space.

EXTENDS Integers

CONSTANTS a, b, c, Value

INSTANCE Consensus
====
