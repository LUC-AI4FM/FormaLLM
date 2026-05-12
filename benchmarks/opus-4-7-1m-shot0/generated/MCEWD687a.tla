---- MODULE MCEWD687a ----
\* Model-checking wrapper for EWD687a (Dijkstra-Scholten / "echo" termination
\* detection on an arbitrary graph). Defines the constants needed by TLC.
\*
\* Created Fri Oct 01 12:28:54 PDT 2021 by lamport

EXTENDS EWD687a, TLC, FiniteSets

\* Three processes plus a leader L.
const_1633116534008310000 == { "L", "P1", "P2", "P3" }

\* A connected undirected graph (here a star rooted at L).
const_1633116534008311000 ==
  { <<"L","P1">>, <<"P1","L">>,
    <<"L","P2">>, <<"P2","L">>,
    <<"L","P3">>, <<"P3","L">>,
    <<"P1","P2">>, <<"P2","P1">> }

\* The leader.
const_1633116534008312000 == "L"

\* State-space bound: limit the size of the inbox/message bag.
constr_1633116534008313000 ==
  \A p \in Procs : Cardinality(DOMAIN inbox[p]) <= 4

====
