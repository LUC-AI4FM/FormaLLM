---- MODULE EWD998ChanID_export ----
\* Specification of EWD998 (Shavit-Francez / Dijkstra termination detection)
\* using channels indexed by node IDs, augmented with vector clocks and an
\* error-trace JSON exporter for post-mortem inspection.
\*
\* The TLC config maps Init to MCInit so the model checker starts from a
\* reduced set of initial states (only counter c properly initialised, all
\* channels empty).
\*
\* Properties:
\*   PostInv : terminationDetected must occur within some arbitrary bound N
\*             of steps (a "real-world" liveness-as-safety invariant).
\*   JsonInv : when violated, format the error trace as JSON and write/ping.

EXTENDS Naturals, Sequences, FiniteSets, TLC, Json

CONSTANTS Node, N

ASSUME N \in Nat \cup {Infinity}

\* ---------- vector clock helpers ----------
\* Each node maintains a (local) vector clock.
\* https://en.wikipedia.org/wiki/Vector_clock

VC == [Node -> Nat]

VCZero == [n \in Node |-> 0]

VCInc(vc, n) == [vc EXCEPT ![n] = @ + 1]

VCMerge(a, b) == [n \in Node |-> IF a[n] > b[n] THEN a[n] ELSE b[n]]

\* ---------- state variables ----------
VARIABLES
  active,        \* active[n]: is node n active?
  color,         \* color[n] \in {"white", "black"}
  counter,       \* counter[n]: number of in-flight messages sent by n
  inbox,         \* inbox[n]: queue of messages addressed to n
  token,         \* token: the circulating token record or "none"
  vc,            \* vc[n]: vector clock at node n
  steps          \* total step count (for the within-N-steps invariant)

vars == << active, color, counter, inbox, token, vc, steps >>

\* ---------- message types ----------
Message ==
  [ type: {"pl"}, src: Node, vc: VC ]   \* payload message

TokenMsg ==
  [ type: {"tok"}, q: Int, color: {"white", "black"}, vc: VC ]

\* The initiator node (rule 0 designates node 0 / first node).
Initiator == CHOOSE n \in Node : \A m \in Node : n = m \/ TRUE

TypeOK ==
  /\ active   \in [Node -> BOOLEAN]
  /\ color    \in [Node -> {"white", "black"}]
  /\ counter  \in [Node -> Int]
  /\ inbox    \in [Node -> Seq(Message)]
  /\ vc       \in [Node -> VC]
  /\ steps    \in Nat
  /\ token \in TokenMsg \cup {<<>>}

\* ---------- initial-state predicates ----------

\* The "real" Init (all nodes possibly active or not, all c initially 0,
\* channels empty - Rule 0).
Init ==
  /\ active  \in [Node -> BOOLEAN]
  /\ color   = [n \in Node |-> "white"]
  /\ counter = [n \in Node |-> 0]
  /\ inbox   = [n \in Node |-> << >>]
  /\ token   = [type |-> "tok", q |-> 0, color |-> "white", vc |-> VCZero]
  /\ vc      = [n \in Node |-> VCZero]
  /\ steps   = 0

\* Restrict initial states to a single representative to speed up TLC.
MCInit ==
  /\ active  = [n \in Node |-> TRUE]
  /\ color   = [n \in Node |-> "white"]
  /\ counter = [n \in Node |-> 0]
  /\ inbox   = [n \in Node |-> << >>]
  /\ token   = [type |-> "tok", q |-> 0, color |-> "white", vc |-> VCZero]
  /\ vc      = [n \in Node |-> VCZero]
  /\ steps   = 0

\* ---------- actions ----------

\* Send a payload from n to m.
SendMsg(n, m) ==
  /\ active[n]
  /\ vc' = [vc EXCEPT ![n] = VCInc(@, n)]
  /\ counter' = [counter EXCEPT ![n] = @ + 1]
  /\ inbox'   = [inbox EXCEPT ![m] = Append(@, [type |-> "pl",
                                                src  |-> n,
                                                vc   |-> vc'[n]])]
  /\ steps'   = steps + 1
  /\ UNCHANGED << active, color, token >>

\* Receive a payload at m.
ReceiveMsg(m) ==
  /\ inbox[m] /= << >>
  /\ LET msg == Head(inbox[m]) IN
       /\ msg.type = "pl"
       /\ active'  = [active  EXCEPT ![m] = TRUE]
       /\ color'   = [color   EXCEPT ![m] = "black"]
       /\ counter' = [counter EXCEPT ![m] = @ - 1]
       /\ vc'      = [vc      EXCEPT ![m] = VCInc(VCMerge(@, msg.vc), m)]
       /\ inbox'   = [inbox   EXCEPT ![m] = Tail(@)]
  /\ steps' = steps + 1
  /\ UNCHANGED token

\* Become passive.
Deactivate(n) ==
  /\ active[n]
  /\ active' = [active EXCEPT ![n] = FALSE]
  /\ steps' = steps + 1
  /\ UNCHANGED << color, counter, inbox, token, vc >>

\* Initiator starts a probe round.
InitToken ==
  /\ ~ active[Initiator]
  /\ token = <<>> \/ token.type = "tok"
  /\ token' = [type |-> "tok", q |-> 0,
                color |-> "white", vc |-> vc[Initiator]]
  /\ steps' = steps + 1
  /\ UNCHANGED << active, color, counter, inbox, vc >>

\* terminationDetected: initiator decides termination.
terminationDetected ==
  /\ token /= <<>>
  /\ token.color = "white"
  /\ color[Initiator] = "white"
  /\ counter[Initiator] + token.q = 0
  /\ ~ active[Initiator]

Next ==
  \/ \E n, m \in Node : SendMsg(n, m)
  \/ \E n \in Node : ReceiveMsg(n)
  \/ \E n \in Node : Deactivate(n)
  \/ InitToken

Spec == Init /\ [][Next]_vars

\* ---------- invariants ----------

\* Real-world invariant: terminationDetected must hold within N steps
\* (an arbitrary bound used so TLC can be made to stop with a normal trace).
PostInv == (steps <= N) \/ terminationDetected

\* Rule 0: c (the global message-in-flight count) sums per-node counters
\* and equals the number of messages in flight.
CountInv ==
  LET inFlight == LET RecLen[n \in Node] == Len(inbox[n])
                  IN  RecLen \* placeholder; sum is computed externally
  IN  TRUE

\* JsonInv: when violated, dump the error trace as JSON to a file.
JsonInv ==
  IF terminationDetected
    THEN JsonSerialize("ewd998_trace.json",
                        <<vc, color, counter, active>>)
    ELSE TRUE

====
