----------------------------- MODULE YoYoNoPruning ---------------------------
\* TLA+ specification of the Yo-Yo leader-election algorithm (Santoro)
\* on arbitrary undirected graphs without self-loops. Variant without
\* graph pruning: termination is not detected; only stabilization holds.

EXTENDS TLC, Integers, FiniteSets, UndirectedGraphs

CONSTANT N
ASSUME N \in Nat \ {0}

\* The nodes and edges of the graph. Nodes are integer identities; the
\* smallest identity is elected leader.
Nodes == 1 .. N

Edges == {{e[1], e[2]} : e \in {e \in Nodes \X Nodes : e[1] # e[2]}}

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

VARIABLES
    phase,     \* the phase ("down" or "up") each node is executing
    incoming,  \* incoming neighbors of each node
    outgoing,  \* outgoing neighbors of each node
    mailbox    \* mailbox of each node

vars == <<phase, incoming, outgoing, mailbox>>

\* Determine the kind of the node.
kind(n) ==
    IF incoming[n] = {} /\ outgoing[n] = {} THEN "leader"
    ELSE IF incoming[n] = {} THEN "source"
    ELSE IF outgoing[n] = {} THEN "sink"
    ELSE "internal"

\* Messages sent during the algorithm. No prune field (unlike YoYoPruning).
Messages ==
    [phase : {"down"}, sndr : Nodes, val : Nodes] \cup
    [phase : {"up"},   sndr : Nodes, reply : {"yes", "no"}]

downMsg(s, v) == [phase |-> "down", sndr |-> s, val |-> v]
upMsg(s, r)   == [phase |-> "up",   sndr |-> s, reply |-> r]

\* Type-correctness predicate.
TypeOK ==
    /\ phase \in [Nodes -> {"down", "up"}]
    /\ incoming \in [Nodes -> SUBSET Nodes]
    /\ outgoing \in [Nodes -> SUBSET Nodes]
    /\ mailbox \in [Nodes -> SUBSET Messages]
    /\ \A n \in Nodes : \A msg \in mailbox[n] :
         /\ msg.phase = "down" =>
            \* at most one "down" message per neighbor
            /\ n \in outgoing[msg.sndr]
            /\ \A mm \in mailbox[n] :
                 mm.phase = "down" /\ mm.sndr = msg.sndr => mm = msg
         /\ msg.phase = "up" =>
            \* at most one "up" message per neighbor
            /\ msg.sndr \in outgoing[n]
            /\ \A mm \in mailbox[n] :
                 mm.phase = "up" /\ mm.sndr = msg.sndr => mm = msg

-------------------------------------------------------------------------------

\* Initial state: edges are directed from smaller to larger identities.
Init ==
    /\ phase = [n \in Nodes |-> "down"]
    /\ mailbox = [n \in Nodes |-> {}]
    /\ \E Nbrs \in SUBSET Edges :
         /\ IsStronglyConnected([node |-> Nodes, edge |-> Nbrs])
         /\ incoming = [n \in Nodes |-> {m \in Nodes : {m,n} \in Nbrs /\ m < n}]
         /\ outgoing = [n \in Nodes |-> {m \in Nodes : {m,n} \in Nbrs /\ m > n}]

-------------------------------------------------------------------------------

\* Down phase. Distinguish sources and other nodes.
DownSource(n) ==
    /\ kind(n) = "source"
    /\ phase[n] = "down"
    /\ mailbox' = [m \in Nodes |->
                     IF m \in outgoing[n] THEN mailbox[m] \cup {downMsg(n, n)}
                     ELSE mailbox[m]]
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<incoming, outgoing>>

DownOther(n) ==
    /\ kind(n) \in {"internal", "sink"}
    /\ phase[n] = "down"
    /\ LET downMsgs == {msg \in mailbox[n] : msg.phase = "down"}
       IN  /\ {msg.sndr : msg \in downMsgs} = incoming[n]
           /\ LET mn == Min({msg.val : msg \in downMsgs})
              IN  mailbox' = [m \in Nodes |->
                                IF m \in outgoing[n]
                                THEN mailbox[m] \cup {downMsg(n, mn)}
                                ELSE mailbox[m]]
    \* Note: "down" messages are retained for use in the up phase.
    /\ phase' = [phase EXCEPT ![n] = "up"]
    /\ UNCHANGED <<incoming, outgoing>>

Down(n) == DownSource(n) \/ DownOther(n)

-------------------------------------------------------------------------------

\* Up phase. Distinguish sources and other nodes.
\* An internal or source node may already have received "down" messages for
\* the following round from neighbors that it still considers outgoing but
\* whose edge direction was reversed in the previous up phase. We therefore
\* filter "down" messages by incoming-neighbor status and preserve any
\* "down" messages for the following round when cleaning the mailbox.

UpSource(n) ==
    /\ kind(n) = "source"
    /\ phase[n] = "up"
    /\ LET upMsgs == {msg \in mailbox[n] : msg.phase = "up"}
           noSndrs == {msg.sndr : msg \in {mm \in upMsgs : mm.reply = "no"}}
       IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]
           /\ mailbox' = [mailbox EXCEPT ![n] = mailbox[n] \ upMsgs]
           \* Edges with a "no" reply reverse orientation.
           /\ incoming' = [incoming EXCEPT ![n] = noSndrs]
           /\ outgoing' = [outgoing EXCEPT ![n] = @ \ noSndrs]
    /\ phase' = [phase EXCEPT ![n] = "down"]

UpOther(n) ==
    /\ kind(n) \in {"internal", "sink"}
    /\ phase[n] = "up"
    /\ LET upMsgs == {msg \in mailbox[n] : msg.phase = "up"}
           noSndrs == {msg.sndr : msg \in {mm \in upMsgs : mm.reply = "no"}}
           downMsgs == {msg \in mailbox[n] :
                          msg.phase = "down" /\ msg.sndr \in incoming[n]}
           mn == Min({msg.val : msg \in downMsgs})
           minSndrs == {msg.sndr :
                          msg \in {mm \in downMsgs : mm.val = mn}}
       IN  /\ {msg.sndr : msg \in upMsgs} = outgoing[n]
           /\ IF noSndrs = {}
              THEN \* "yes" to senders of the minimum, "no" to others
                /\ mailbox' = [m \in Nodes |->
                                 IF m \in incoming[n]
                                 THEN mailbox[m] \cup
                                      {upMsg(n,
                                             IF m \in minSndrs
                                             THEN "yes" ELSE "no")}
                                 ELSE IF m = n
                                      THEN mailbox[m] \ (upMsgs \cup downMsgs)
                                      ELSE mailbox[m]]
              ELSE \* "no" to all incoming neighbors
                /\ mailbox' = [m \in Nodes |->
                                 IF m \in incoming[n]
                                 THEN mailbox[m] \cup {upMsg(n, "no")}
                                 ELSE IF m = n
                                      THEN mailbox[m] \ (upMsgs \cup downMsgs)
                                      ELSE mailbox[m]]
           \* Edges where a "no" reply was sent reverse orientation.
           /\ incoming' = [incoming EXCEPT ![n] = noSndrs]
           /\ outgoing' = [outgoing EXCEPT ![n] = @ \ noSndrs]
    /\ phase' = [phase EXCEPT ![n] = "down"]

Up(n) == UpSource(n) \/ UpOther(n)

-------------------------------------------------------------------------------

Next == \E n \in Nodes : Down(n) \/ Up(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-------------------------------------------------------------------------------

\* Formulas used for verification.

\* Predicate asserting at least two source nodes; refuting it produces an
\* execution that shows all sources except the leader being eliminated.
MoreThanOneSource ==
    \E s1, s2 \in Nodes :
        s1 # s2 /\ kind(s1) = "source" /\ kind(s2) = "source"

\* Node m is an outgoing neighbor of n iff n is an incoming neighbor of m,
\* except for in-flight reversal.
NeighborInv ==
    \A m, n \in Nodes :
        m \in outgoing[n] <=>
            \/ n \in incoming[m]
            \/ /\ n \in outgoing[m]
               /\ \/ upMsg(n, "no") \in mailbox[m]
                  \/ upMsg(m, "no") \in mailbox[n]

\* No new sources are generated during execution.
NoNewSource ==
    \A n \in Nodes :
        (kind(n) # "source") => [](kind(n) # "source")

\* Stabilization: only one source, all "down" messages carry that node's
\* identity, all "up" messages say "yes".
Stabilization ==
    /\ \E n \in Nodes :
         /\ kind(n) = "source"
         /\ \A m \in Nodes \ {n} : kind(m) # "source"
    /\ \A n \in Nodes : \A msg \in mailbox[n] :
         /\ msg.phase = "down" => (\E s \in Nodes : kind(s) = "source"
                                                /\ msg.val = s)
         /\ msg.phase = "up"   => msg.reply = "yes"

==============================================================================
