---- MODULE YoYoNoPruning ----
(***************************************************************************)
(* TLA+ specification of the Yo-Yo leader election algorithm in arbitrary  *)
(* undirected graphs without self-loops. The algorithm was introduced by    *)
(* Nicola Santoro, cf. "Design and Analysis of Distributed Algorithms",     *)
(* section 3.8.3, see also https://en.wikipedia.org/wiki/Yo-yo_(algorithm).*)
(* The algorithm assumes that nodes are (identified by) integers, and the   *)
(* node with the smallest identity will be elected leader.                  *)
(*                                                                          *)
(* The algorithm orients the edges of the graph. Initially, all edges are   *)
(* directed from smaller to larger node identities, so sources correspond   *)
(* to local minima in their neighborhoods and sinks correspond to local     *)
(* maxima. Sources are considered candidates for being leader, and as long  *)
(* as their are at least two sources, each round will eliminate at least    *)
(* one of them.                                                             *)
(*                                                                          *)
(* Each round consists of two phases, traditionally called the "Yo-" and    *)
(* "-Yo" phases, that will be called "down" and "up" phases below.          *)
(*                                                                          *)
(* The down phase is initiated by the sources, which broadcast their        *)
(* identity to all neighbors. Non-source nodes wait for values to have been *)
(* received from all incoming neighbors, then broadcast the minimum value   *)
(* that has been received to all outgoing neighbors. (Sink nodes do not     *)
(* send messages in the down phase.)                                        *)
(*                                                                          *)
(* The up phase is initiated by sink nodes when they have received values   *)
(* from all neighbors in the down phase. They reply "yes" to all neighbors  *)
(* that sent the minimum value and "no" to all other neighbors. The other   *)
(* nodes wait until messages for the up phase have been received from all   *)
(* outgoing neighbors. If one message is "no", they send "no" to all        *)
(* incoming neighbors, otherwise they send "yes" to those incoming          *)
(* neighbors who sent the smallest value during the down phase and "no" to  *)
(* all other incoming neighbors. (Source nodes do not send messages in the  *)
(* up phase.)                                                               *)
(*                                                                          *)
(* Moreover, edges along which a "no" message is sent during the up phase   *)
(* change orientation. This may change the status of a node (source,        *)
(* sink or internal).                                                       *)
(*                                                                          *)
(* The algorithm stabilizes in a state where there is at most one source,   *)
(* after which point only the identity of that source will be sent during   *)
(* the down phase and only "yes" messages will be sent during the up phase. *)
(* However, no node detects termination. Ensuring termination of the        *)
(* algorithm is achieved by pruning the graph, modeled in a variant of the  *)
(* present specification.                                                   *)
(*                                                                          *)
(* Authors: Ludovic Yvoz and Stephan Merz, 2024.                            *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, TLC

(* the nodes and edges of the graph *)
CONSTANTS Node, Edge

ASSUME
  /\ Node \subseteq Int
  /\ Edge \subseteq { e \in SUBSET Node : Cardinality(e) = 2 }

VARIABLES
  phase,    \* the phase (down or up) each node is currently executing
  inN,      \* incoming neighbors of each node
  outN,     \* outgoing neighbors of each node
  mbox      \* mailbox of each node

vars == <<phase, inN, outN, mbox>>

\* Initial orientation: from smaller to larger.
InitInN(n) == { m \in Node : {n, m} \in Edge /\ m < n }
InitOutN(n) == { m \in Node : {n, m} \in Edge /\ m > n }

(***************************************************************************)
(* Determine the kind of the node: source, sink or internal.               *)
(***************************************************************************)
Sources == { n \in Node : inN[n] = {} /\ outN[n] # {} }
Sinks == { n \in Node : outN[n] = {} /\ inN[n] # {} }
Internal == Node \ (Sources \cup Sinks)

(***************************************************************************)
(* Messages sent during the algorithm.                                     *)
(***************************************************************************)
DownMsg(v) == [type |-> "down", val |-> v]
UpMsg(ans) == [type |-> "up", ans |-> ans]

Messages == { DownMsg(v) : v \in Node }
            \cup { UpMsg(a) : a \in {"yes", "no"} }

(***************************************************************************)
(* Type correctness predicate.                                             *)
(***************************************************************************)
TypeOK ==
  /\ phase \in [Node -> {"down", "up"}]
  /\ inN \in [Node -> SUBSET Node]
  /\ outN \in [Node -> SUBSET Node]
  \* at most one message per neighbor
  /\ mbox \in [Node -> [Node -> SUBSET Messages]]
  /\ \A n \in Node : \A m \in Node : Cardinality(mbox[n][m]) <= 2

(***************************************************************************)
(* Yo-Yo algorithm as a state machine.                                     *)
(***************************************************************************)
Init ==
  /\ phase = [n \in Node |-> "down"]
  /\ inN = [n \in Node |-> InitInN(n)]
  /\ outN = [n \in Node |-> InitOutN(n)]
  /\ mbox = [n \in Node |-> [m \in Node |-> {}]]

(***************************************************************************)
(* Down phase: we distinguish sources and other nodes.                     *)
(* Note that a node retains "down" messages after executing the phase      *)
(* because they are used during the up phase.                              *)
(***************************************************************************)
DownSource(n) ==
  /\ phase[n] = "down"
  /\ n \in Sources
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ mbox' = [mbox EXCEPT ![n] = [m \in Node |->
        IF m \in outN[n] THEN @[m] \cup {DownMsg(n)} ELSE @[m]]]
  /\ UNCHANGED <<inN, outN>>

DownOther(n) ==
  /\ phase[n] = "down"
  /\ n \notin Sources
  /\ \A m \in inN[n] : \E msg \in mbox[m][n] : msg.type = "down"
  /\ LET vals == { msg.val : msg \in UNION { mbox[m][n] : m \in inN[n] } }
         minV == CHOOSE v \in vals : \A v2 \in vals : v <= v2
     IN
       /\ phase' = [phase EXCEPT ![n] = "up"]
       /\ IF n \in Sinks
            THEN UNCHANGED mbox  \* sinks do not send messages in the down phase
            ELSE mbox' = [mbox EXCEPT ![n] = [m \in Node |->
                   IF m \in outN[n] THEN @[m] \cup {DownMsg(minV)} ELSE @[m]]]
       /\ UNCHANGED <<inN, outN>>

(***************************************************************************)
(* Up phase, again distinguishing sources and other nodes.                 *)
(*                                                                          *)
(* An internal or source node may already have received "down" messages    *)
(* for the following round from neighbors that it still considers as       *)
(* outgoing neighbors but for which the edge direction was reversed.       *)
(* We therefore have to be careful to only consider "down" messages from   *)
(* neighbors that the node considers as incoming, and also to preserve     *)
(* "down" messages for the following round when cleaning the mailbox.      *)
(***************************************************************************)
UpSink(n) ==
  /\ phase[n] = "up"
  /\ n \in Sinks
  /\ \A m \in inN[n] : \E msg \in mbox[m][n] : msg.type = "down"
  /\ LET vals == { msg.val : msg \in UNION { mbox[m][n] : m \in inN[n] } }
         minV == CHOOSE v \in vals : \A v2 \in vals : v <= v2
         minSenders == { m \in inN[n] :
                          \E msg \in mbox[m][n] :
                            msg.type = "down" /\ msg.val = minV }
         reversed == inN[n] \ minSenders
     IN
       /\ mbox' = [mbox EXCEPT ![n] = [m \in Node |->
             IF m \in minSenders THEN @[m] \cup {UpMsg("yes")}
             ELSE IF m \in reversed THEN @[m] \cup {UpMsg("no")}
             ELSE @[m]]]
       \* Reverse edges with "no"
       /\ inN' = [inN EXCEPT ![n] = minSenders]
       /\ outN' = [outN EXCEPT ![n] = outN[n] \cup reversed]
       /\ phase' = [phase EXCEPT ![n] = "down"]

UpOther(n) ==
  /\ phase[n] = "up"
  /\ n \notin Sinks
  /\ n \notin Sources \/ outN[n] # {}
  /\ \A m \in outN[n] : \E msg \in mbox[m][n] : msg.type = "up"
  /\ LET ups == UNION { { msg \in mbox[m][n] : msg.type = "up" } : m \in outN[n] }
         hasNo == \E msg \in ups : msg.ans = "no"
         vals == { msg.val : msg \in UNION { mbox[m][n] : m \in inN[n] } }
         minV == IF vals = {} THEN 0
                 ELSE CHOOSE v \in vals : \A v2 \in vals : v <= v2
         minSenders == { m \in inN[n] :
                          \E msg \in mbox[m][n] :
                            msg.type = "down" /\ msg.val = minV }
         reversed == IF hasNo THEN inN[n] ELSE inN[n] \ minSenders
         noOut == { m \in outN[n] :
                     \E msg \in mbox[m][n] : msg.type = "up" /\ msg.ans = "no" }
     IN
       /\ IF n \in Sources
            THEN UNCHANGED mbox  \* sources do not send messages in the up phase
            ELSE mbox' = [mbox EXCEPT ![n] = [m \in Node |->
                   IF hasNo /\ m \in inN[n] THEN @[m] \cup {UpMsg("no")}
                   ELSE IF m \in inN[n] /\ m \in minSenders THEN @[m] \cup {UpMsg("yes")}
                   ELSE IF m \in inN[n] THEN @[m] \cup {UpMsg("no")}
                   ELSE @[m]]]
       /\ inN' = [inN EXCEPT ![n] = inN[n] \ reversed]
       /\ outN' = [outN EXCEPT ![n] = (outN[n] \ noOut) \cup reversed]
       /\ phase' = [phase EXCEPT ![n] = "down"]

Next ==
  \E n \in Node :
    \/ DownSource(n) \/ DownOther(n)
    \/ UpSink(n)     \/ UpOther(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Formulas used for verification.                                         *)
(***************************************************************************)

(***************************************************************************)
(* Predicate asserting that there will always be at least two source       *)
(* nodes. Checking this as an invariant produces an execution that shows   *)
(* that all sources except for the leader will be eliminated.              *)
(***************************************************************************)
AlwaysTwoSources == Cardinality(Sources) >= 2

(***************************************************************************)
(* Node m is an outgoing neighbor of node n iff n is an incoming neighbor  *)
(* of m, except if the edge is being reversed, in which case there is a    *)
(* "no" message in one of the mailboxes.                                   *)
(***************************************************************************)
EdgeOrientationConsistent ==
  \A n \in Node, m \in Node :
    (m \in outN[n]) <=> ((n \in inN[m]) \/ \E msg \in mbox[n][m] \cup mbox[m][n] :
                                              msg.type = "up" /\ msg.ans = "no")

(***************************************************************************)
(* No new sources are generated during execution of the algorithm.         *)
(***************************************************************************)
NoNewSources == \A n \in Sources : inN[n] = {}

(***************************************************************************)
(* Stabilization condition: there is only one source node, all "down"      *)
(* messages carry the identity of that node, all "up" messages say "yes".  *)
(***************************************************************************)
Stabilized ==
  /\ Cardinality(Sources) = 1
  /\ LET ldr == CHOOSE n \in Sources : TRUE
     IN  /\ \A n, m \in Node :
              \A msg \in mbox[n][m] :
                msg.type = "down" => msg.val = ldr
         /\ \A n, m \in Node :
              \A msg \in mbox[n][m] :
                msg.type = "up" => msg.ans = "yes"

====
