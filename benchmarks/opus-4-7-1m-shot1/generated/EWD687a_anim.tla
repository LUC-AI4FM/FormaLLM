---- MODULE EWD687a_anim ----
(***************************************************************************)
(* Animation module for EWD687a.                                           *)
(*                                                                         *)
(* Modification History                                                    *)
(* Last modified Tue Dec 21 17:52:54 PST 2021 by Markus Kuppe              *)
(* Created Tue Dec 02 17:23:43 PDT 2021 by Markus Kuppe                    *)
(***************************************************************************)
EXTENDS EWD687a, SVG, Naturals, Sequences, TLC, FiniteSets, IOUtils, Randomization

(***************************************************************************)
(* Concatenates the given string str n times. The empty string is          *)
(* returned if n is less than 1.                                           *)
(*   "m", 0 -> ""                                                          *)
(*   "m", 1 -> "m"                                                         *)
(*   "m", 2 -> "mm"                                                        *)
(*   "m", 3 -> "mmm"                                                       *)
(***************************************************************************)
RECURSIVE NCopies(_, _)
NCopies(str, n) ==
  IF n < 1 THEN "" ELSE str \o NCopies(str, n-1)

(***************************************************************************)
(* Defines an arrow with plain SVG that is referenced in the def of E below*)
(***************************************************************************)
(* Increasing refX moves the arrowhead to the middle of the line away      *)
(* from the tip.                                                           *)
Arrow ==
  "<marker id='arrow' viewBox='0 0 10 10' refX='15' refY='5'"
  \o " markerWidth='6' markerHeight='6' orient='auto-start-reverse'>"
  \o "<path d='M 0 0 L 10 5 L 0 10 z'/></marker>"

NodeDimension == 40  \* divisible by 2 for proper alignment

(***************************************************************************)
(* A function from processes to x,y coordinates                            *)
(***************************************************************************)
Layout(options) ==
  [p \in Procs |->
    [x |-> (CHOOSE i \in 1..Cardinality(Procs) : TRUE) * 80,
     y |-> 200]]

(***************************************************************************)
(* An SVG group containing rectangles denoting the graph of processes.    *)
(* A black square denotes an idle process, a red circle an active one.    *)
(***************************************************************************)
NodesView(layout) ==
  Group([n \in Procs |->
    LET pos == layout[n]
        shape == IF active[n]
                 THEN Circle(pos.x, pos.y, 15, [fill |-> "red"])
                 ELSE Rect(pos.x - 20, pos.y - 20, 40, 40, [fill |-> "black"])
    IN shape ], [class |-> "nodes"])

(***************************************************************************)
(* An SVG group containing lines denoting the (graph) edges.              *)
(***************************************************************************)
EdgesView(layout) ==
  Group([e \in Edges |->
    Line(layout[e[1]].x, layout[e[1]].y,
         layout[e[2]].x, layout[e[2]].y,
         [stroke |-> "black", marker_end |-> "url(#arrow)"]) ],
    [class |-> "edges"])

(***************************************************************************)
(* An SVG group containing the lines visualizing the upEdges of the       *)
(* overlay tree.  An upEdge is denoted by a dashed, orange line.          *)
(***************************************************************************)
UpEdgesView(layout) ==
  Group([e \in {ue \in (Procs \X Procs) : upEdge[ue[1]] = ue[2]} |->
    Line(layout[e[1]].x, layout[e[1]].y,
         layout[e[2]].x, layout[e[2]].y,
         [stroke |-> "orange", stroke_dasharray |-> "5,5"]) ],
    [class |-> "upEdges"])

(***************************************************************************)
(* Legend with four rows of labels.                                        *)
(***************************************************************************)
Legend(basePos) ==
  Group(<<
    Text(basePos.x, basePos.y,      ToString(TLCGet("level")), <<>>),
    Text(basePos.x, basePos.y + 20, "action: in",  <<>>),
    Text(basePos.x, basePos.y + 40, "action: out", <<>>),
    Text(basePos.x, basePos.y + 60, "~neutral procs red, round when also active", <<>>) >>, <<>>)

(***************************************************************************)
(* Combine the (SVG) definitions, legend, processes, edges, and upEdges    *)
(* into a single (SVG) frame.                                              *)
(***************************************************************************)
Frame ==
  LET layout == Layout([type |-> "linear"])
  IN "<svg xmlns='http://www.w3.org/2000/svg'>"
     \o Arrow
     \o EdgesView(layout)
     \o UpEdgesView(layout)
     \o NodesView(layout)
     \o Legend([x |-> 10, y |-> 20])
     \o "</svg>"

Alias ==
  [ active      |-> active,
    sentUnacked |-> sentUnacked,
    rcvdUnacked |-> rcvdUnacked,
    msgs        |-> msgs,
    acks        |-> acks,
    frame       |-> Frame ]

(***************************************************************************)
(* A counter-example that is a violation of this property is a prefix of   *)
(* a behavior of at least 30 states with the Leader neutral in the final  *)
(* state.                                                                  *)
(***************************************************************************)
InterestingBehavior ==
  TLCGet("level") < 30 \/ active[Leader]

(***************************************************************************)
(* Disable Idle steps that leave the variables unchanged (an idle process *)
(* becoming idle) to prevent finite stuttering when simulating.            *)
(***************************************************************************)
NoSuperfluousIdleSteps ==
  <<active, sentUnacked, rcvdUnacked, msgs, acks>>'
    # <<active, sentUnacked, rcvdUnacked, msgs, acks>>

(***************************************************************************)
(* A randomly generated network of processes.                              *)
(***************************************************************************)
NodesOfNetwork == {L, P1, P2, P3, P4, P5}

Network ==
  LET Edgs == SUBSET { n \in (NodesOfNetwork \X NodesOfNetwork) :
                       /\ n[1] # n[2]
                       /\ n[2] # L }
  IN TLCEval(RandomElement(Edgs))

ASSUME PrintT(<<"Edges", Network>>)

====
