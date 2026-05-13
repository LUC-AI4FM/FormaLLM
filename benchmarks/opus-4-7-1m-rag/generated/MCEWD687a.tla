---- MODULE MCEWD687a ----
\* Model-checking harness for EWD687a (the Dijkstra-Scholten tree
\* algorithm).  Binds the operator constants Procs/Edges/Leader to a
\* finite four-process instance and adds a state constraint to keep
\* state space bounded.

EXTENDS EWD687a

CONSTANTS L, P1, P2, P3

const_1633116534008310000 == {L, P1, P2, P3}

const_1633116534008311000 ==
    { <<L, P1>>, <<L, P2>>, <<P1, P3>>, <<P2, P3>>,
      <<P1, P2>>, <<P3, P1>> }

const_1633116534008312000 == L

\* Keep counters bounded so TLC terminates.
const_1633116534008313000 ==
    /\ \A e \in Edges : sentUnacked[e] <= 3
    /\ \A e \in Edges : msgs[e] <= 3
    /\ \A e \in Edges : acks[e] <= 3
    /\ \A e \in Edges : rcvdUnacked[e] <= 3

====
