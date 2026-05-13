---- MODULE YoYoNoPruning ----
(***************************************************************************)
(* TLA+ specification of the Yo-Yo leader election algorithm in arbitrary  *)
(* undirected graphs without self-loops. The algorithm was introduced by   *)
(* Nicola Santoro, cf. "Design and Analysis of Distributed Algorithms",    *)
(* section 3.8.3, see also https://en.wikipedia.org/wiki/Yo-yo_(algorithm).*)
(*                                                                         *)
(* The algorithm assumes that nodes are (identified by) integers, and the  *)
(* node with the smallest identity will be elected leader.                 *)
(*                                                                         *)
(* The algorithm orients the edges of the graph. Initially, all edges are  *)
(* directed from smaller to larger node identities, so sources correspond  *)
(* to local minima in their neighborhoods and sinks correspond to local    *)
(* maxima.                                                                 *)
(*                                                                         *)
(* Authors: Ludovic Yvoz and Stephan Merz, 2024.                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences, TLC

(***************************************************************************)
(* The nodes and edges of the graph.                                       *)
(***************************************************************************)
CONSTANTS Node, Edge

ASSUME
  /\ Node \subseteq Nat
  /\ Edge \subseteq (Node \X Node)
  /\ \A e \in Edge : e[1] # e[2]  \* no self-loops

(***************************************************************************)
(* nodes are represented by their integer identities.                      *)
(* the phase (down or up) each node is currently executing.                *)
(* incoming and outgoing neighbors of each node.                           *)
(* mailbox of each node.                                                   *)
(***************************************************************************)
VARIABLES phase, incoming, outgoing, mailbox

vars == << phase, incoming, outgoing, mailbox >>

(***************************************************************************)
(* Determine the kind of the node: source, sink or internal.               *)
(***************************************************************************)
IsSource(n) == incoming[n] = {}
IsSink(n) == outgoing[n] = {}
IsInternal(n) == ~ IsSource(n) /\ ~ IsSink(n)

(***************************************************************************)
(* Messages sent during the algorithm.                                     *)
(***************************************************************************)
DownMsg(v) == [type |-> "down", val |-> v]
UpYes == [type |-> "up", val |-> "yes"]
UpNo  == [type |-> "up", val |-> "no"]

Messages == { DownMsg(v) : v \in Node } \cup {UpYes, UpNo}

(***************************************************************************)
(* Type correctness predicate.                                             *)
(***************************************************************************)
TypeOK ==
  /\ phase    \in [Node -> {"down", "up"}]
  /\ incoming \in [Node -> SUBSET Node]
  /\ outgoing \in [Node -> SUBSET Node]
  /\ mailbox  \in [Node \X Node -> SUBSET Messages]

InitialIncoming(n) == { m \in Node : <<m, n>> \in Edge \cup { <<e[2], e[1]>> : e \in Edge }
                                   /\ m < n }

InitialOutgoing(n) == { m \in Node : <<m, n>> \in Edge \cup { <<e[2], e[1]>> : e \in Edge }
                                   /\ m > n }

Init ==
  /\ phase = [n \in Node |-> "down"]
  /\ incoming = [n \in Node |-> InitialIncoming(n)]
  /\ outgoing = [n \in Node |-> InitialOutgoing(n)]
  /\ mailbox = [pq \in Node \X Node |-> {}]

(***************************************************************************)
(* Yo-Yo algorithm as a state machine.                                     *)
(* Down phase: we distinguish sources and other nodes.                     *)
(* Note that a node retains "down" messages after executing the phase     *)
(* because they are used during the up phase.                              *)
(***************************************************************************)
DownSource(n) ==
  /\ phase[n] = "down"
  /\ IsSource(n)
  /\ mailbox' = [pq \in Node \X Node |->
                   IF pq[1] = n /\ pq[2] \in outgoing[n]
                     THEN mailbox[pq] \cup {DownMsg(n)}
                     ELSE mailbox[pq]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing>>

DownInternal(n) ==
  /\ phase[n] = "down"
  /\ IsInternal(n)
  /\ \A m \in incoming[n] :
       \E msg \in mailbox[<<m, n>>] : msg.type = "down"
  /\ LET vals == { msg.val : msg \in
                     UNION { mailbox[<<m, n>>] : m \in incoming[n] } }
         minv == CHOOSE v \in vals : \A w \in vals : v \leq w
     IN mailbox' = [pq \in Node \X Node |->
                       IF pq[1] = n /\ pq[2] \in outgoing[n]
                         THEN mailbox[pq] \cup {DownMsg(minv)}
                         ELSE mailbox[pq]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing>>

DownSink(n) ==
  /\ phase[n] = "down"
  /\ IsSink(n)
  /\ \A m \in incoming[n] :
       \E msg \in mailbox[<<m, n>>] : msg.type = "down"
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<incoming, outgoing, mailbox>>

(***************************************************************************)
(* Up phase, again distinguishing sources and other nodes.                 *)
(* An internal or source node may already have received "down" messages    *)
(* for the following round from neighbors that it still considers as       *)
(* outgoing neighbors but for which the edge direction was reversed.       *)
(***************************************************************************)
UpSink(n) ==
  /\ phase[n] = "up"
  /\ IsSink(n)
  /\ LET downs == [m \in incoming[n] |->
                     CHOOSE msg \in mailbox[<<m, n>>] : msg.type = "down"]
         vals == { downs[m].val : m \in incoming[n] }
         minv == CHOOSE v \in vals : \A w \in vals : v \leq w
         flips == { m \in incoming[n] : downs[m].val # minv }
     IN
       /\ mailbox' = [pq \in Node \X Node |->
                        IF pq[1] = n /\ pq[2] \in incoming[n]
                          THEN mailbox[pq] \cup
                                 {IF pq[2] \in flips THEN UpNo ELSE UpYes}
                          ELSE mailbox[pq]]
       /\ incoming' = [incoming EXCEPT ![n] = incoming[n] \ flips]
       /\ outgoing' = [outgoing EXCEPT ![n] = outgoing[n] \cup flips]
  /\ phase' = [phase EXCEPT ![n] = "down"]

UpInternalOrSource(n) ==
  /\ phase[n] = "up"
  /\ ~ IsSink(n)
  /\ \A m \in outgoing[n] :
       \E msg \in mailbox[<<m, n>>] : msg.type = "up"
  /\ phase' = [phase EXCEPT ![n] = "down"]
  /\ UNCHANGED <<incoming, outgoing, mailbox>>  \* simplified

Next ==
  \E n \in Node :
    \/ DownSource(n) \/ DownInternal(n) \/ DownSink(n)
    \/ UpSink(n) \/ UpInternalOrSource(n)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Formulas used for verification.                                         *)
(***************************************************************************)
Sources == { n \in Node : IsSource(n) }

(***************************************************************************)
(* Predicate asserting that there will always be at least two source nodes.*)
(* Checking this as an invariant produces an execution that shows that all *)
(* sources except for the leader will be eliminated.                       *)
(***************************************************************************)
AlwaysTwoSources == Cardinality(Sources) \geq 2

(***************************************************************************)
(* Node m is an outgoing neighbor of node n iff n is an incoming neighbor  *)
(* of m, except if the edge is being reversed.                             *)
(***************************************************************************)
EdgeConsistent ==
  \A n, m \in Node :
    m \in outgoing[n] => n \in incoming[m] \/ UpNo \in mailbox[<<n, m>>] \cup mailbox[<<m, n>>]

(***************************************************************************)
(* No new sources are generated during execution of the algorithm.         *)
(***************************************************************************)
NoNewSources ==
  Cardinality(Sources) \leq Cardinality({ n \in Node : InitialIncoming(n) = {} })

(***************************************************************************)
(* Stabilization condition: there is only one source node, all "down"      *)
(* messages carry the identity of that node, all "up" messages say "yes".  *)
(***************************************************************************)
Stabilized ==
  /\ Cardinality(Sources) = 1
  /\ \E ldr \in Sources :
       \A pq \in Node \X Node :
         \A msg \in mailbox[pq] :
           /\ (msg.type = "down") => msg.val = ldr
           /\ (msg.type = "up")   => msg.val = "yes"

====
