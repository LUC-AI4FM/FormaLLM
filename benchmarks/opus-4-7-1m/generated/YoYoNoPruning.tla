---- MODULE YoYoNoPruning ----
(***************************************************************************)
(* TLA+ specification of the Yo-Yo leader election algorithm in arbitrary *)
(* undirected graphs without self-loops. Introduced by Nicola Santoro,    *)
(* "Design and Analysis of Distributed Algorithms" sec. 3.8.3.            *)
(* https://en.wikipedia.org/wiki/Yo-yo_(algorithm)                         *)
(*                                                                         *)
(* Nodes are identified by integers; the node with the smallest identity  *)
(* will be elected leader.                                                 *)
(*                                                                         *)
(* The algorithm orients edges (initially smaller -> larger). Sources    *)
(* (local minima) are leader candidates. Each round has a down phase     *)
(* (sources broadcast identity, intermediate nodes forward the min) and  *)
(* an up phase (sinks reply yes/no, edges reverse where "no" sent). The  *)
(* algorithm stabilizes when only one source remains.                     *)
(*                                                                         *)
(* This variant does NOT prune the graph; termination is not detected.   *)
(*                                                                         *)
(* Authors: Ludovic Yvoz and Stephan Merz, 2024.                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes,    \* the nodes (integer identities)
          Edges     \* the edges (undirected; given as unordered pairs)

ASSUME
    /\ Nodes \subseteq Nat
    /\ Edges \subseteq SUBSET Nodes
    /\ \A e \in Edges : Cardinality(e) = 2

\* Initial orientation: smaller to larger.
InitOutgoing(n) == { m \in Nodes : {n, m} \in Edges /\ n < m }
InitIncoming(n) == { m \in Nodes : {n, m} \in Edges /\ n > m }

VARIABLES
    phase,    \* phase[n] \in {"down", "up"} : phase node n is executing
    incoming, \* incoming[n] : set of incoming neighbors of n
    outgoing, \* outgoing[n] : set of outgoing neighbors of n
    mailbox   \* mailbox[n] : multiset (modeled as set with at-most-one-per-neighbor) of msgs for n

vars == <<phase, incoming, outgoing, mailbox>>

\* Messages.
DownMsg(src, val) == [type |-> "down", src |-> src, val |-> val]
UpMsg(src, ans)   == [type |-> "up",   src |-> src, ans |-> ans]
Msgs == [type : {"down"}, src : Nodes, val : Nodes]
          \cup [type : {"up"}, src : Nodes, ans : {"yes", "no"}]

\* Kind of a node.
IsSource(n) == incoming[n] = {}
IsSink(n)   == outgoing[n] = {}
IsInternal(n) == ~IsSource(n) /\ ~IsSink(n)

\* Type correctness.
TypeOK ==
    /\ phase \in [Nodes -> {"down", "up"}]
    /\ incoming \in [Nodes -> SUBSET Nodes]
    /\ outgoing \in [Nodes -> SUBSET Nodes]
    /\ mailbox \in [Nodes -> SUBSET Msgs]

Init ==
    /\ phase = [n \in Nodes |-> "down"]
    /\ outgoing = [n \in Nodes |-> InitOutgoing(n)]
    /\ incoming = [n \in Nodes |-> InitIncoming(n)]
    /\ mailbox = [n \in Nodes |-> {}]

\*****************************************************************************
\* Down phase: distinguish sources from other nodes. Down messages are kept
\* in the mailbox because the up phase uses them.
\*****************************************************************************
DownSource(n) ==
    /\ IsSource(n)
    /\ phase[n] = "down"
    /\ mailbox' = [m \in Nodes |->
                    IF m \in outgoing[n] THEN mailbox[m] \cup {DownMsg(n, n)}
                    ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<incoming, outgoing>>

DownOther(n) ==
    /\ ~IsSource(n)
    /\ phase[n] = "down"
    /\ \A m \in incoming[n] : \E d \in mailbox[n] :
            d.type = "down" /\ d.src = m
    /\ LET downs == { d \in mailbox[n] : d.type = "down" /\ d.src \in incoming[n] }
           vals  == { d.val : d \in downs }
           minV  == CHOOSE v \in vals : \A w \in vals : v <= w
       IN IF IsSink(n)
          THEN mailbox' = mailbox
          ELSE mailbox' = [m \in Nodes |->
                            IF m \in outgoing[n] THEN mailbox[m] \cup {DownMsg(n, minV)}
                            ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<incoming, outgoing>>

\*****************************************************************************
\* Up phase, distinguishing sinks, sources, and internal nodes.
\* An internal or source node may already have received "down" messages for
\* the following round; we must preserve them when cleaning the mailbox.
\*****************************************************************************
UpSink(n) ==
    /\ IsSink(n)
    /\ phase[n] = "up"
    /\ LET downs == { d \in mailbox[n] : d.type = "down" /\ d.src \in incoming[n] }
           vals  == { d.val : d \in downs }
           minV  == CHOOSE v \in vals : \A w \in vals : v <= w
           winners == { d.src : d \in { d \in downs : d.val = minV } }
           toNeighbor(m) ==
               IF m \in winners THEN UpMsg(n, "yes") ELSE UpMsg(n, "no")
       IN  mailbox' = [m \in Nodes |->
                            IF m \in incoming[n] THEN mailbox[m] \cup {toNeighbor(m)}
                            ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "down"]
    /\ UNCHANGED <<incoming, outgoing>>

UpOther(n) ==
    /\ ~IsSink(n)
    /\ phase[n] = "up"
    /\ \A m \in outgoing[n] : \E u \in mailbox[n] :
            u.type = "up" /\ u.src = m
    /\ LET ups   == { u \in mailbox[n] : u.type = "up" /\ u.src \in outgoing[n] }
           anyNo == \E u \in ups : u.ans = "no"
           downs == { d \in mailbox[n] : d.type = "down" /\ d.src \in incoming[n] }
           vals  == { d.val : d \in downs }
           minV  == IF vals = {} THEN 0 ELSE CHOOSE v \in vals : \A w \in vals : v <= w
           winners == { d.src : d \in { d \in downs : d.val = minV } }
           toIncoming(m) ==
               IF anyNo THEN UpMsg(n, "no")
               ELSE IF m \in winners THEN UpMsg(n, "yes") ELSE UpMsg(n, "no")
           reversed == { m \in outgoing[n] :
                            \E u \in ups : u.src = m /\ u.ans = "no" }
       IN
          /\ IF IsSource(n)
             THEN mailbox' = [m \in Nodes |->
                                IF m \in incoming[n]
                                THEN mailbox[m]  \* source sends nothing
                                ELSE mailbox[m]]
             ELSE mailbox' = [m \in Nodes |->
                                IF m \in incoming[n] THEN mailbox[m] \cup {toIncoming(m)}
                                ELSE mailbox[m]]
          /\ outgoing' = [outgoing EXCEPT ![n] = @ \ reversed]
          /\ incoming' = [incoming EXCEPT ![n] = @ \cup reversed]
    /\ phase' = [phase EXCEPT ![n] = "down"]

Next ==
    \E n \in Nodes :
        \/ DownSource(n) \/ DownOther(n) \/ UpSink(n) \/ UpOther(n)

Spec == Init /\ [][Next]_vars

\*****************************************************************************
\* Formulas used for verification.
\*****************************************************************************

\* Always at least two source nodes (checking as invariant produces a
\* counter-example showing sources except the leader being eliminated).
AlwaysTwoSources == Cardinality({ n \in Nodes : IsSource(n) }) >= 2

\* m is an outgoing neighbor of n iff n is an incoming neighbor of m, unless
\* the edge is being reversed (a "no" message exists in some mailbox).
ConsistentOrientation ==
    \A n, m \in Nodes :
        (m \in outgoing[n]) <=>
            \/ n \in incoming[m]
            \/ \E mb \in mailbox[m] : mb.type = "up" /\ mb.ans = "no" /\ mb.src = n

\* No new sources are generated.
NoNewSources ==
    \A n \in Nodes : IsSource(n) => InitIncoming(n) = {}

\* Stabilization condition.
Stabilization ==
    /\ Cardinality({ n \in Nodes : IsSource(n) }) = 1
    /\ LET leader == CHOOSE n \in Nodes : IsSource(n)
       IN  \A n \in Nodes :
            /\ \A d \in mailbox[n] : d.type = "down" => d.val = leader
            /\ \A u \in mailbox[n] : u.type = "up"  => u.ans = "yes"
====
