---- MODULE YoYoNoPruning ----
\* TLA+ specification of the Yo-Yo leader-election algorithm in arbitrary
\* undirected graphs without self-loops, introduced by Nicola Santoro,
\* cf. "Design and Analysis of Distributed Algorithms", section 3.8.3.
\* https://en.wikipedia.org/wiki/Yo-yo_(algorithm)
\*
\* Nodes are identified by integers; the node with the smallest identity
\* will be elected leader.
\*
\* The algorithm orients the edges of the graph: initially each edge points
\* from the smaller to the larger identity, so sources are local minima and
\* sinks are local maxima. Each round consists of two phases:
\*  - "down" (yo-): sources broadcast their identity; non-source nodes wait
\*    until they have received values from all incoming neighbors, then
\*    broadcast the minimum to all outgoing neighbors. Sinks do not send.
\*  - "up" (-yo): sinks reply "yes" to neighbors that sent the minimum value
\*    and "no" to all others. Other nodes wait until "up" messages have been
\*    received from all outgoing neighbors. If any is "no", they send "no" to
\*    all incoming neighbors; otherwise they send "yes" to the incoming
\*    neighbors that sent the minimum value and "no" to others. Sources do
\*    not send during the up phase.
\* Edges along which "no" is sent during the up phase change orientation,
\* which may change a node's status.
\*
\* This variant does NOT include the pruning that detects termination.
\* Authors: Ludovic Yvoz and Stephan Merz, 2024.

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
  Node,    \* the set of nodes (integer identities)
  Edge     \* the set of undirected edges (unordered pairs {n, m})

\* the nodes and edges of the graph
ASSUME /\ Node \subseteq Int
       /\ \A e \in Edge : Cardinality(e) = 2 /\ e \subseteq Node

\* Neighbors of node n in the graph.
Neigh(n) == { m \in Node : {n, m} \in Edge }

VARIABLES
  phase,    \* phase[n]: "down" or "up" - the phase n is currently executing
  inN,      \* inN[n]: current set of incoming neighbors of n
  outN,     \* outN[n]: current set of outgoing neighbors of n
  mbox      \* mbox[n]: mailbox of n (set of messages with sender info)

vars == << phase, inN, outN, mbox >>

\* Kind of a node: source, sink or internal.
Kind(n) ==
  IF inN[n] = {}  THEN "source"
  ELSE IF outN[n] = {} THEN "sink"
       ELSE "internal"

\* Messages.
DownMsg(v, src)   == [type |-> "down", val |-> v, from |-> src]
YesMsg(src)       == [type |-> "up", ans |-> "yes", from |-> src]
NoMsg(src)        == [type |-> "up", ans |-> "no",  from |-> src]

Message ==
       [type : {"down"}, val : Node, from : Node]
  \cup [type : {"up"},   ans : {"yes", "no"}, from : Node]

\* Type-correctness predicate.
TypeOK ==
  /\ phase \in [Node -> {"down", "up"}]
  /\ inN   \in [Node -> SUBSET Node]
  /\ outN  \in [Node -> SUBSET Node]
  /\ mbox  \in [Node -> SUBSET Message]
  /\ \A n \in Node : inN[n] \cap outN[n] = {}
  /\ \A n \in Node : (inN[n] \cup outN[n]) = Neigh(n)
  \* at most one message per neighbor (always true for sinks)
  /\ \A n \in Node : Cardinality(mbox[n]) <= Cardinality(Neigh(n))

\* Initial state: edges oriented from smaller to larger identity, phase = "down",
\* and source nodes have already deposited their down messages.
Init ==
  /\ phase = [n \in Node |-> "down"]
  /\ inN   = [n \in Node |-> { m \in Neigh(n) : m < n }]
  /\ outN  = [n \in Node |-> { m \in Neigh(n) : m > n }]
  /\ mbox  = [n \in Node |-> {}]

\* ---------- Down phase ----------

\* Source's down step: broadcast own identity to outgoing neighbors.
DownSource(n) ==
  /\ phase[n] = "down"
  /\ Kind(n) = "source"
  /\ mbox' = [m \in Node |->
               IF m \in outN[n] THEN mbox[m] \cup {DownMsg(n, n)}
               ELSE mbox[m]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED << inN, outN >>

\* Non-source's down step: wait for all incoming values, broadcast minimum.
DownOther(n) ==
  /\ phase[n] = "down"
  /\ Kind(n) /= "source"
  /\ LET received == { msg \in mbox[n] :
                         msg.type = "down" /\ msg.from \in inN[n] }
     IN  /\ { msg.from : msg \in received } = inN[n]
         /\ LET minVal == CHOOSE v \in { msg.val : msg \in received } :
                            \A v2 \in { msg.val : msg \in received } : v <= v2
            IN  IF Kind(n) = "sink"
                  THEN /\ phase' = [phase EXCEPT ![n] = "up"]
                       /\ UNCHANGED << inN, outN, mbox >>
                  ELSE /\ mbox' = [m \in Node |->
                                    IF m \in outN[n]
                                      THEN mbox[m] \cup {DownMsg(minVal, n)}
                                      ELSE mbox[m]]
                       /\ phase' = [phase EXCEPT ![n] = "up"]
                       /\ UNCHANGED << inN, outN >>

\* ---------- Up phase ----------

\* Sink's up step: reply "yes" to neighbors that sent the minimum value.
UpSink(n) ==
  /\ phase[n] = "up"
  /\ Kind(n) = "sink"
  /\ LET downs  == { msg \in mbox[n] : msg.type = "down" }
         minVal == CHOOSE v \in { msg.val : msg \in downs } :
                      \A v2 \in { msg.val : msg \in downs } : v <= v2
         yesNbrs == { msg.from : msg \in { d \in downs : d.val = minVal } }
         noNbrs  == inN[n] \ yesNbrs
     IN  /\ mbox' = [m \in Node |->
                       IF m \in yesNbrs THEN mbox[m] \cup {YesMsg(n)}
                       ELSE IF m \in noNbrs THEN mbox[m] \cup {NoMsg(n)}
                       ELSE mbox[m]]
         \* Edges with "no" reverse orientation.
         /\ inN'  = [inN  EXCEPT ![n] = inN[n] \ noNbrs]
         /\ outN' = [outN EXCEPT ![n] = outN[n] \cup noNbrs]
         /\ phase' = [phase EXCEPT ![n] = "down"]

\* Source / internal up step.
UpOther(n) ==
  /\ phase[n] = "up"
  /\ Kind(n) /= "sink"
  /\ LET upmsgs == { msg \in mbox[n] :
                       msg.type = "up" /\ msg.from \in outN[n] }
     IN  /\ { msg.from : msg \in upmsgs } = outN[n]
         /\ LET allYes == \A msg \in upmsgs : msg.ans = "yes"
            IN
              IF Kind(n) = "source"
                THEN \* Sources don't send during the up phase.
                     /\ phase' = [phase EXCEPT ![n] = "down"]
                     /\ UNCHANGED << inN, outN, mbox >>
                ELSE LET downs  == { msg \in mbox[n] :
                                       msg.type = "down" /\ msg.from \in inN[n] }
                         minVal == CHOOSE v \in { msg.val : msg \in downs } :
                                       \A v2 \in { msg.val : msg \in downs } : v <= v2
                         yesNbrs == IF allYes
                                       THEN { msg.from : msg \in
                                              { d \in downs : d.val = minVal } }
                                       ELSE {}
                         noNbrs  == inN[n] \ yesNbrs
                     IN  /\ mbox' = [m \in Node |->
                                       IF m \in yesNbrs
                                          THEN mbox[m] \cup {YesMsg(n)}
                                       ELSE IF m \in noNbrs
                                          THEN mbox[m] \cup {NoMsg(n)}
                                       ELSE mbox[m]]
                         /\ inN'  = [inN  EXCEPT ![n] = inN[n] \ noNbrs]
                         /\ outN' = [outN EXCEPT ![n] = outN[n] \cup noNbrs]
                         /\ phase' = [phase EXCEPT ![n] = "down"]

Next ==
  \E n \in Node :
     DownSource(n) \/ DownOther(n) \/ UpSink(n) \/ UpOther(n)

Spec == Init /\ [][Next]_vars

\* ---------- Verification formulas ----------

\* Always at least two source nodes (checked as an invariant to obtain a
\* counterexample showing elimination of all sources except the leader).
AlwaysTwoSources ==
  Cardinality({ n \in Node : Kind(n) = "source" }) >= 2

\* Edge consistency: m is outgoing for n iff n is incoming for m, except
\* when the edge is currently being reversed (a "no" message is in flight).
EdgeConsistency ==
  \A n, m \in Node :
     m \in outN[n] =>
        \/ n \in inN[m]
        \/ \E msg \in mbox[n] \cup mbox[m] :
              msg.type = "up" /\ msg.ans = "no"

\* No new sources are generated during execution.
NoNewSources ==
  \A n \in Node :
     (Kind(n) = "source") =>
        [] (Kind(n) = "source" \/ \A m \in Node : Kind(m) /= "source")

\* Stabilization condition: only one source remains, every "down" message
\* carries that source's identity, and every "up" message is "yes".
Stable ==
  LET sources == { n \in Node : Kind(n) = "source" }
  IN  /\ Cardinality(sources) = 1
      /\ LET leader == CHOOSE n \in sources : TRUE
         IN  /\ \A n \in Node, m \in mbox[n] :
                  m.type = "down" => m.val = leader
             /\ \A n \in Node, m \in mbox[n] :
                  m.type = "up" => m.ans = "yes"

\* Eventually only one source remains (the leader).
Termination == <> Stable

====
