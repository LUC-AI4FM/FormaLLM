---- MODULE MCDieHarder ----
\* Model-check wrapper for the DieHarder generalization of the Die Hard puzzle.
\* The original problem asks how to measure exactly 4 gallons using a 3-gallon
\* jug and a 5-gallon jug. DieHarder generalizes the problem to an arbitrary
\* set of jugs Jug with a Capacity function and a target Goal. Because TLC
\* cannot directly hold a function-valued constant, we define MCJug and
\* MCCapacity here and let the .cfg file substitute them for Jug and Capacity.

EXTENDS DieHarder

MCJug == {"a", "b"}

MCCapacity == [j \in MCJug |-> CASE j = "a" -> 3
                                 [] j = "b" -> 5]

====
