---- MODULE EWD687a_anim ----
(***************************************************************************)
(* Animation wrapper for EWD687a termination detection algorithm.          *)
(*                                                                         *)
(* Modification History                                                    *)
(* Last modified Tue Dec 21 17:52:54 PST 2021 by Markus Kuppe              *)
(* Created Tue Dec 02 17:23:43 PDT 2021 by Markus Kuppe                    *)
(***************************************************************************)
EXTENDS EWD687a, TLC, TLCExt, SVG, Functions, Sequences, FiniteSets,
        Naturals, IOUtils, Randomization

-----------------------------------------------------------------------------
\* Processes.
CONSTANTS L, P1, P2, P3, P4, P5

\* A randomly generate network of processes.
NodesOfNetwork ==
    {L, P1, P2, P3, P4, P5}

Network ==
    LET Edgs == SUBSET { n \in (NodesOfNetwork \X NodesOfNetwork):
                        \* No self-loops.
                        /\ n[1] # n[2]
                        \* L is a source and never a sink.
                        /\ n[2] # L }
    IN  TLCEval(RandomElement(Edgs))

\* Print the randomly chosen set of edges.
ASSUME PrintT(<<"Edges", Edges>>)

\* A specific network of processes.

-----------------------------------------------------------------------------
\* A counter-example that is a violation of this property is a prefix of a
\* behavior of at least 30 states with the Leader neutral in the final state.
InterestingBehavior ==
  TLCGet("level") < 30 \/ active[Leader] \/ msgs[Leader] # 0

\* Disable Idle steps that leave the variables unchange (an idle process
\* becoming idle) to prevent finite stuttering when simulating.
NoSuperfluousIdleSteps ==
  ~(/\ active' = active
    /\ msgs' = msgs
    /\ acks' = acks
    /\ sentUnacked' = sentUnacked
    /\ rcvdUnacked' = rcvdUnacked)

Alias ==
  [
    active      |-> active,
    sentUnacked |-> sentUnacked,
    rcvdUnacked |-> rcvdUnacked,
    msgs        |-> msgs,
    acks        |-> acks
  ]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Concatenates the given string str n times. The empty string is          *)
(* returned if n is less than 1.                                           *)
(* "m", 0 -> ""                                                            *)
(* "m", 1 -> "m"                                                           *)
(* "m", 2 -> "mm"                                                          *)
(* "m", 3 -> "mmm"                                                         *)
(***************************************************************************)
RECURSIVE NTimes(_, _)
NTimes(str, n) ==
  IF n < 1 THEN "" ELSE str \o NTimes(str, n - 1)

\* NodeDimension ought to be divisible by 2 for proper alignment of nodes and edges.
NodeDimension == 50

(* Defines an arrow with plain SVG that is referenced in the def of E below. *)
\* Increasing refX moves the arrowhead to the middle of the line away from the tip.
ArrowDefs ==
  "<defs><marker id='arrow' viewBox='0 0 10 10' refX='15' refY='5' " \o
  "markerWidth='6' markerHeight='6' orient='auto-start-reverse'>" \o
  "<path d='M 0 0 L 10 5 L 0 10 z'/></marker></defs>"

(* Legend with four rows of labels (text) whose top-left point is located at BasePos:
   1: The current state ordinal.
   2: The action from the predecessor state to the current state.
   3: The action from the current state to the next/successor state.
   4: "~neutral procs red, round when also active". *)
Legend(BasePos) ==
  Group(<<
    Text(BasePos.x, BasePos.y,      ToString(TLCGet("level")), <<>>),
    \* The name of the action concatenated with the action's context.
    Text(BasePos.x, BasePos.y + 20, "prev",  <<>>),
    Text(BasePos.x, BasePos.y + 40, "next",  <<>>),
    Text(BasePos.x, BasePos.y + 60, "~neutral procs red, round when also active", <<>>)
  >>, <<>>)

(* A function from processes to x,y coordinates: [ Procs -> [x: Nat, y: Nat] *)
(* The coordinates are chosen according to the given layout algorithm
   parameterized by the given "options" record. *)
Layout(options) ==
  [ p \in Procs |-> [x |-> 100 + 100 * CHOOSE i \in 1..Cardinality(Procs) : TRUE,
                     y |-> 100] ]

(* An SVG group containing rectangles denoting the graph of processes. Approximately at
   the center of each node, a text indicates the processes name (Procs). *)
\* A black square denotes an idle process, a red circle an active one.
\* round (rx=15) if node is active.
NodeShapes(pos) ==
  Group([ p \in Procs |->
    Rect(pos[p].x, pos[p].y, NodeDimension, NodeDimension,
         [rx |-> IF active[p] THEN "15" ELSE "0",
          fill |-> IF active[p] THEN "red" ELSE "black"]) ], <<>>)

(* An SVG group containing lines denoting the (graph) edges. *)
\* A solid, black line with an arrow at its tip denotes an edge.
EdgeLines(pos) ==
  Group([ e \in Edges |->
    Line(pos[e[1]].x, pos[e[1]].y, pos[e[2]].x, pos[e[2]].y,
         [stroke |-> "black", marker_end |-> "url(#arrow)"]) ], <<>>)

(* An SVG group containing the lines visualizing the upEdges of the overlay tree. *)
\* An upEdge is denoted by a dashed, orange line.
UpEdgeLines(pos) == Group(<<>>, <<>>)

(* Combine the (SVG) definitions, legend, processes, edges, and upEdges into
   a single (SVG) frame as a visualization of the current TLA+ state. *)
Frame ==
  LET pos == Layout([alg |-> "circle"])
  IN  SVGElemToString(Group(<<
        Legend([x |-> 10, y |-> 10]),
        NodeShapes(pos),
        EdgeLines(pos),
        UpEdgeLines(pos)
      >>, <<>>))

\* The animator nests frame in an SVG box.  With a file, this is done explicitly.
(* Writes the given string str to a file whose name contains the number n. *)
\* %%03d to escape %03d in Java format strings.
WriteToFile(str, n) ==
  LET name == "EWD687a_anim_" \o ToString(n) \o ".svg"
  IN  IOExec(<<"sh", "-c", "echo '" \o str \o "' > " \o name>>)

(* https://animator.tlapl.us (interactively explore the animation) *)
(* The resulting set of EWD687a_anim_???.svg files can be rendered as an animated gif with:
   $ convert -delay 100 -density 200 *.svg EWD687a.gif
   An animated gif is portable across browser, but cannot be advanced/reversed manually,
   unless a user installs a browser plugin such as https://github.com/0ui/gif-scrubber. *)

====
