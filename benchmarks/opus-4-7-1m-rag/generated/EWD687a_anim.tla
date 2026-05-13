---- MODULE EWD687a_anim ----
\* SVG-based animation harness for EWD687a.  Each TLC state is rendered
\* as a numbered SVG frame so that a counter-example trace can be turned
\* into an animated GIF.  This module
\*   - declares a concrete (or randomly generated) network of processes,
\*   - exposes an Alias that exports the relevant variables,
\*   - exports an SVG visualization of the current state via Frame,
\*   - and adds an action constraint that suppresses spurious idle steps
\*     while simulating.
\*
\* Render the resulting frames as an animated gif with:
\*     $ convert -delay 100 -density 200 *.svg EWD687a.gif
\*
\* An animated gif is portable across browsers, but cannot be
\* advanced/reversed manually unless a user installs a browser plugin
\* such as https://github.com/0ui/gif-scrubber.  Alternatively use
\* https://animator.tlapl.us (interactively explore the animation).

EXTENDS EWD687a, SVG, TLC, TLCExt, Sequences, Integers, IOUtils

\* Processes.
CONSTANTS L, P1, P2, P3, P4, P5

\* A randomly generated network of processes.
NodesOfNetwork == {L, P1, P2, P3, P4, P5}

Network ==
  LET Edgs == SUBSET { n \in (NodesOfNetwork \X NodesOfNetwork) :
                          \* No self-loops.
                          /\ n[1] # n[2]
                          \* L is a source and never a sink.
                          /\ n[2] # L }
  IN  TLCEval(RandomElement(Edgs))

\* Print the randomly chosen set of edges.
ASSUME PrintT(<<"Edges", Edges>>)

\* A specific network of processes.
\*   ASSUME Edges = {<<L, P1>>, <<L, P2>>, <<P1, P3>>, <<P2, P3>>,
\*                   <<P3, P4>>, <<P4, P5>>, <<P5, P3>>}

----------------------------------------------------------------------------
\* Alias to export the variables of EWD687a.

Alias ==
    [ active      |-> active,
      sentUnacked |-> sentUnacked,
      rcvdUnacked |-> rcvdUnacked,
      msgs        |-> msgs,
      acks        |-> acks ]

----------------------------------------------------------------------------
\* Disable Idle steps that leave the variables unchanged (an idle
\* process becoming idle) to prevent finite stuttering when simulating.
NoSuperfluousIdleSteps ==
    \A p \in Procs : ~(Idle(p) /\ active[p] = FALSE)

----------------------------------------------------------------------------
\* A counter-example that is a violation of this property is a prefix of
\* a behavior of at least 30 states with the Leader neutral in the final
\* state.
InterestingBehavior ==
    ~ (neutral(Leader) /\ TLCGet("level") >= 30)

----------------------------------------------------------------------------
\* Concatenates the given string str n times.  The empty string is
\* returned if n is less than 1.
\*   "m", 0 -> ""
\*   "m", 1 -> "m"
\*   "m", 2 -> "mm"
\*   "m", 3 -> "mmm"
\*   ...
RECURSIVE Concat(_, _)
Concat(str, n) == IF n < 1 THEN "" ELSE str \o Concat(str, n - 1)

----------------------------------------------------------------------------
\* SVG dimensions.

\* NodeDimension ought to be divisible by 2 for proper alignment of
\* nodes and edges.
NodeDimension == 30

\* Defines an arrow with plain SVG that is referenced in the def of E
\* below.
\* Increasing refX moves the arrowhead to the middle of the line away
\* from the tip.
Defs ==
    "<defs><marker id='arrow' markerWidth='15' markerHeight='15' refX='9' refY='3' orient='auto' markerUnits='strokeWidth' viewBox='0 0 20 20'><path d='M0,0 L0,6 L9,3 z' fill='black' /></marker></defs>"

\* A function from processes to x,y coordinates: [Procs -> [x: Nat, y: Nat]]
\* The coordinates are chosen according to the given layout algorithm
\* parameterized by the given "options" record.
Layout ==
    LET nodes == SetToSeq(Procs)
        cols  == Cardinality(Procs)
    IN  [ p \in Procs |->
            LET i == CHOOSE k \in 1..Len(nodes) : nodes[k] = p
            IN  [x |-> 100 + 100 * i, y |-> 100 + 50 * (i % 2)] ]

----------------------------------------------------------------------------
\* Legend with four rows of labels (text) whose top-left point is
\* located at BasePos:
\* 1: The current state ordinal.
\* 2: The action from the predecessor state to the current state.
\* 3: The action from the current state to the next/successor state.
\* 4: "~neutral procs red, round when also active".
\*
\* The name of the action concatenated with the action's context.
LegendBasePos == [x |-> 10, y |-> 20]

Arial == [font |-> "Arial"]

Legend ==
    Group(<<Text(LegendBasePos.x, LegendBasePos.y,
                 "State: " \o ToString(TLCGet("level")), Arial),
            Text(LegendBasePos.x, LegendBasePos.y + 15,
                 "Last action", Arial),
            Text(LegendBasePos.x, LegendBasePos.y + 30,
                 "Next action", Arial),
            Text(LegendBasePos.x, LegendBasePos.y + 45,
                 "~neutral procs red, round when also active", Arial)>>,
          <<>>)

----------------------------------------------------------------------------
\* An SVG group containing rectangles denoting the graph of processes.
\* Approximately at the center of each node, a text indicates the
\* processes name (Procs).  A black square denotes an idle process, a
\* red circle an active one.  Round (rx=15) if node is active.
Nodes ==
    LET nf == [ p \in Procs |->
                  LET pos == Layout[p]
                      shape == Rect(pos.x, pos.y, NodeDimension, NodeDimension,
                                    [rx     |-> IF active[p] THEN "15" ELSE "0",
                                     stroke |-> "black",
                                     fill   |-> IF neutral(p) THEN "white" ELSE "red"])
                      label == Text(pos.x + NodeDimension \div 2,
                                    pos.y + NodeDimension + 12,
                                    ToString(p), Arial)
                  IN  Group(<<shape, label>>, <<>>) ]
    IN  Group([ p \in Procs |-> nf[p] ], <<>>)

----------------------------------------------------------------------------
\* An SVG group containing lines denoting the (graph) edges.  A line,
\* connecting a from and to node, is annotated with three labels:
\*
\* 1: At the mid-point of the line, a string indicates the in-flight
\*    messages and ACKs, or the empty string if there are no messages
\*    in flight.  An in-flight message is denoted by an "m" and an ACK
\*    by an "a", respectively.
\* 2: At the quad-point towards the source of the edge, a negative
\*    integer denotes the number of unacknowledged messages.  If there
\*    are zero unacknowledged messages, the integer is made invisible
\*    to reduce visual clutter.
\* 3: At the quad-point towards the sink of the edge, a natural denotes
\*    the number of ACKs that the sink still has to send.  Again, if
\*    there are zero ACKs to be sent the natural is invisible.
\*
\* A solid, black line with an arrow at its tip denotes an edge.
EdgesSVG ==
    LET ef[e \in Edges] ==
            LET from == Layout[e[1]]
                to   == Layout[e[2]]
                fx == from.x + NodeDimension \div 2
                fy == from.y + NodeDimension \div 2
                tx == to.x   + NodeDimension \div 2
                ty == to.y   + NodeDimension \div 2
                mx == (fx + tx) \div 2
                my == (fy + ty) \div 2
                qx1 == (fx + mx) \div 2
                qy1 == (fy + my) \div 2
                qx2 == (mx + tx) \div 2
                qy2 == (my + ty) \div 2
                line == Line(fx, fy, tx, ty,
                             [stroke |-> "black",
                              marker_end |-> "url(#arrow)"])
                lbl1 == Text(mx, my,
                             Concat("m", msgs[e]) \o Concat("a", acks[e]),
                             Arial)
                lbl2 == Text(qx1, qy1,
                             IF sentUnacked[e] = 0 THEN ""
                                                   ELSE ToString(-sentUnacked[e]),
                             Arial)
                lbl3 == Text(qx2, qy2,
                             IF rcvdUnacked[e] = 0 THEN ""
                                                   ELSE ToString(rcvdUnacked[e]),
                             Arial)
            IN  Group(<<line, lbl1, lbl2, lbl3>>, <<>>)
    IN  Group([ e \in Edges |-> ef[e] ], <<>>)

----------------------------------------------------------------------------
\* An SVG group containing the lines visualizing the upEdges of the
\* overlay tree.  An upEdge is denoted by a dashed, orange line.
UpEdgesSVG ==
    LET up == { upEdge[p] : p \in (Procs \ {Leader}) } \ {NotAnEdge}
        uf[e \in up] ==
            LET from == Layout[e[1]]
                to   == Layout[e[2]]
                fx == from.x + NodeDimension \div 2
                fy == from.y + NodeDimension \div 2
                tx == to.x   + NodeDimension \div 2
                ty == to.y   + NodeDimension \div 2
            IN  Line(fx, fy, tx, ty,
                     [stroke |-> "orange",
                      stroke_dasharray |-> "4 2"])
    IN  Group([ e \in up |-> uf[e] ], <<>>)

----------------------------------------------------------------------------
\* Combine the (SVG) definitions, legend, processes, edges, and upEdges
\* into a single (SVG) frame as a visualization of the current TLA+
\* state.  The animator nests frame in an SVG box.  With a file, this
\* is done explicitly.
Frame == Group(<<Legend, EdgesSVG, UpEdgesSVG, Nodes>>, <<>>)

Animation == SVGElemToString(Frame)

----------------------------------------------------------------------------
\* Writes the given string str to a file whose name contains the
\* number n.
\* %%03d to escape %03d in Java format strings.
WriteFrame(str, n) ==
    IOExec(<<"sh", "-c",
             "printf '<svg>%s%s</svg>' "
              \o "'" \o Defs \o "' "
              \o "'" \o str  \o "' "
              \o "> " \o "\"$(printf '%%03d' " \o ToString(n) \o ").svg\"" >>)

====
