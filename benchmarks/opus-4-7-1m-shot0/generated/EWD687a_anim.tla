---- MODULE EWD687a_anim ----
\* Animation wrapper around EWD687a (the Dijkstra-Scholten echo termination-
\* detection algorithm). Produces an SVG visualisation per state plus
\* counter-example properties used to drive an "interesting" trace through
\* the model checker.
\*
\* Last modified Tue Dec 21 17:52:54 PST 2021 by Markus Kuppe
\* Created     Tue Dec 02 17:23:43 PDT 2021 by Markus Kuppe

EXTENDS EWD687a, Naturals, Sequences, FiniteSets, TLC, SVG, IOUtils

\* ------------- network configuration -------------

\* A specific network of processes used by the animation.
NodesOfNetwork == {L, P1, P2, P3, P4, P5}

\* A randomly generated network of processes (used when Edges is mapped here
\* from the .cfg). We pick a random subset of the legal edge set: no
\* self-loops and L is a source (never a sink).
Network ==
  LET Edgs == SUBSET { n \in (NodesOfNetwork \X NodesOfNetwork) :
                          /\ n[1] /= n[2]
                          /\ n[2] /= L }
  IN  TLCEval(RandomElement(Edgs))

\* Print the randomly chosen set of edges.
ASSUME PrintT(<<"Edges", Edges>>)

\* ------------- helper string operations -------------

\* Concatenates the given string str n times. Empty string if n < 1.
\*   "m", 0 -> ""
\*   "m", 1 -> "m"
\*   "m", 2 -> "mm"
RECURSIVE NTimes(_, _)
NTimes(str, n) == IF n < 1 THEN "" ELSE str \o NTimes(str, n - 1)

\* ------------- SVG constants and helpers -------------

NodeDimension == 50      \* ought to be divisible by 2 for clean alignment
ActiveRadius  == 15      \* round (rx=15) when active

BasePos == [x |-> 10, y |-> 10]

\* SVG defs: a black arrow definition referenced by edges below.
ArrowDef ==
  "<defs><marker id='arrow' markerWidth='10' markerHeight='10' " \o
  "refX='15' refY='3' orient='auto' markerUnits='strokeWidth'>" \o
  "<path d='M0,0 L0,6 L9,3 z' fill='black'/></marker></defs>"

\* Position of each process (computed from a layout algorithm).
Layout ==
  [ p \in Procs |->
      [ x |-> 100 * (CHOOSE i \in 1..Cardinality(Procs) :
                       \E f \in [Procs -> 1..Cardinality(Procs)] :
                          /\ f[p] = i
                          /\ \A q,r \in Procs : q /= r => f[q] /= f[r]),
        y |-> 100 ] ]

\* ------------- SVG groups -------------

\* The set of processes drawn as boxes (idle=black square, active=red circle).
NodeGroup ==
  Group([ p \in Procs |->
    LET pos == Layout[p]
        idleSvg == Rect(pos.x, pos.y, NodeDimension, NodeDimension,
                         [fill |-> "black"])
        activeSvg == Circle(pos.x + NodeDimension \div 2,
                            pos.y + NodeDimension \div 2,
                            ActiveRadius, [fill |-> "red"])
    IN
      IF active[p] THEN activeSvg ELSE idleSvg ],
    [ class |-> "nodes" ])

\* Edges drawn as black arrows annotated with in-flight message/ack counts.
EdgeGroup ==
  Group([ e \in Edges |->
    LET p == e[1] q == e[2]
        midLabel == NTimes("m", msgs[<<p,q>>]) \o NTimes("a", acks[<<q,p>>])
        srcQuartLabel  == ToString(- sentUnacked[<<p,q>>])
        sinkQuartLabel == ToString(rcvdUnacked[<<q,p>>])
    IN
      Line(Layout[p].x, Layout[p].y,
           Layout[q].x, Layout[q].y,
           [ stroke |-> "black", marker-end |-> "url(#arrow)",
             label-mid |-> midLabel,
             label-srcq |-> srcQuartLabel,
             label-sinkq |-> sinkQuartLabel ]) ],
    [ class |-> "edges" ])

\* Overlay tree (upEdges) drawn as dashed orange lines.
UpEdgeGroup ==
  Group([ e \in Edges |->
    Line(Layout[e[1]].x, Layout[e[1]].y,
         Layout[e[2]].x, Layout[e[2]].y,
         [ stroke |-> "orange", stroke-dasharray |-> "4,2" ]) ],
    [ class |-> "upedges" ])

\* Legend with four labels at top-left BasePos.
LegendGroup ==
  Group(<< Text("State #" \o ToString(TLCGet("level")), BasePos),
           Text("Prev action: " \o TLCGet("action"),
                [BasePos EXCEPT !.y = @ + 20]),
           Text("Next action: <pending>",
                [BasePos EXCEPT !.y = @ + 40]),
           Text("~neutral procs red, round when also active",
                [BasePos EXCEPT !.y = @ + 60]) >>,
        [ class |-> "legend" ])

\* Combine everything into one SVG frame.
Frame ==
  SVGElem("svg",
    [ width |-> 800, height |-> 600 ],
    << ArrowDef, LegendGroup, NodeGroup, EdgeGroup, UpEdgeGroup >>)

\* Write the frame to file SVG-NNN.svg.
WriteFrame(n) ==
  LET filename == "EWD687a_anim_" \o ToString(n) \o ".svg"
  IN  IOSerialize(filename, Frame)

\* ------------- ALIAS -------------

Alias == [
  active        |-> active,
  sentUnacked   |-> sentUnacked,
  rcvdUnacked   |-> rcvdUnacked,
  msgs          |-> msgs,
  acks          |-> acks,
  toSVG         |-> Frame
]

\* ------------- action constraints / interesting behavior -------------

\* Disable idle steps that leave the variables unchanged.
NoSuperfluousIdleSteps ==
  ~ (UNCHANGED << active, sentUnacked, rcvdUnacked, msgs, acks >>)

\* A counter-example to InterestingBehavior is a prefix of length >= 30
\* with the leader neutral in the final state.
InterestingBehavior ==
  (TLCGet("level") >= 30) => active[Leader]

====
