---- MODULE EWD687a_anim ----
(***************************************************************************)
(* Animation wrapper for EWD687a. Generates an SVG visualization of each  *)
(* TLA+ state and writes it to disk. The animator produces a sequence of  *)
(* numbered SVG files that can be combined into an animated gif via       *)
(*   $ convert -delay 100 -density 200 *.svg EWD687a.gif                  *)
(*                                                                         *)
(* See https://animator.tlapl.us for interactive exploration.             *)
(*                                                                         *)
(* Modification History                                                    *)
(*   Last modified Tue Dec 21 17:52:54 PST 2021 by Markus Kuppe           *)
(*   Created      Tue Dec 02 17:23:43 PDT 2021 by Markus Kuppe            *)
(***************************************************************************)
EXTENDS EWD687a, Naturals, Sequences, FiniteSets, TLC, SVG, IOUtils

CONSTANTS L, P1, P2, P3, P4, P5

\* Nodes of the network.
NodesOfNetwork == {L, P1, P2, P3, P4, P5}

\* A randomly generated network of processes (no self-loops; L is a source).
Network ==
    LET Edgs == SUBSET { n \in (NodesOfNetwork \X NodesOfNetwork) :
                            /\ n[1] # n[2]
                            /\ n[2] # L }
    IN  TLCEval(RandomElement(Edgs))

ASSUME PrintT(<<"Edges", Edges>>)

\* Disable idle-becomes-idle steps to prevent finite stuttering in simulation.
NoSuperfluousIdleSteps ==
    \E n \in Procs : active[n] /= active'[n]
        \/ \E e \in Edges : sentUnacked[e] /= sentUnacked'[e]
        \/ \E e \in Edges : rcvdUnacked[e] /= rcvdUnacked'[e]
        \/ msgs /= msgs'
        \/ acks /= acks'

\* Animation alias: bundle TLA+ state for the animator.
Alias == [
    active        |-> active,
    sentUnacked   |-> sentUnacked,
    rcvdUnacked   |-> rcvdUnacked,
    msgs          |-> msgs,
    acks          |-> acks
]

\* Counter-example property: at least 30 states with the Leader neutral
\* in the final state.
InterestingBehavior == TLCGet("level") < 30 \/ active[Leader]

\* Concatenates the given string str n times. Empty if n < 1.
RECURSIVE NTimes(_, _)
NTimes(str, n) ==
    IF n < 1 THEN "" ELSE str \o NTimes(str, n - 1)

\* NodeDimension must be divisible by 2 for proper alignment.
NodeDimension == 40

\* Increasing refX moves the arrowhead toward the middle of the line.
ArrowDef ==
    "<defs><marker id='arrow' refX='8' refY='4'" \o
    " markerWidth='10' markerHeight='8' orient='auto'>" \o
    "<path d='M0,0 L8,4 L0,8 Z' fill='black'/></marker></defs>"

\* A function mapping processes to (x, y) coordinates.
Layout ==
    [p \in Procs |->
        [x |-> NodeDimension * 2, y |-> NodeDimension * 2]]

\* An SVG group containing rectangles or circles for each process.
\* A black square = idle, a red circle = active.
ProcessShapes ==
    "<g>" \o
    NTimes("<rect width='30' height='30' fill='black'/>", Cardinality(Procs)) \o
    "</g>"

EdgeLines == "<g></g>"
UpEdgeLines == "<g></g>"

\* Legend in four rows.
Legend(BasePos) ==
    "<g transform='translate(" \o ToString(BasePos.x) \o "," \o
                                 ToString(BasePos.y) \o ")'>" \o
    "<text y='0'>State: " \o ToString(TLCGet("level")) \o "</text>" \o
    "<text y='20'>Previous Action</text>" \o
    "<text y='40'>Next Action</text>" \o
    "<text y='60'>~neutral procs red, round when also active</text>" \o
    "</g>"

\* Combine the SVG fragments into a single frame.
Frame ==
    "<svg xmlns='http://www.w3.org/2000/svg' viewBox='0 0 400 400'>" \o
    ArrowDef \o ProcessShapes \o EdgeLines \o UpEdgeLines \o
    Legend([x |-> 10, y |-> 10]) \o "</svg>"

\* Write the given string str to a file whose name contains the number n.
\* %%03d to escape %03d in Java format strings.
WriteFrame(str, n) ==
    IOExec(<<"sh", "-c",
             "printf '%s' " \o str \o " > EWD687a_anim_" \o ToString(n) \o ".svg">>)

AnimInv ==
    \/ TLCGet("level") = 0
    \/ WriteFrame(Frame, TLCGet("level")).exitValue = 0

====
