---- MODULE EnvironmentController ----
\* An encoding of a parameterized and partially synchronous model of the
\* eventually perfect failure detectors with crash faults from:
\* [1] Chandra, Tushar Deepak, and Sam Toueg. "Unreliable failure detectors
\*     for reliable distributed systems." JACM 43.2 (1996): 225-267.
\*
\* Igor Konnov, Thanh Hai Tran, Josef Wider, 2018.
\*
\* The specification instantiates two other specs:
\*   Age_Channel.tla       - the communication system (messages wrapped in
\*                           "boxes" with an age field).
\*   EPFailureDetector.tla - behaviors of correct processes.
\*
\* Each correct process repeatedly SENDs "alive" messages, PREDICTs failures,
\* or RECEIVEs incoming messages, depending on its local clock. Global time
\* is advanced by an EnvTick action that ages every box and increments the
\* per-process pause counter procPause. Encoding tricks keep the state space
\* finite even though clocks are unbounded:
\*   - local clocks reset once they exceed the largest period;
\*   - fromLastHeard[i][j] is capped at delta[i][j].
\*
\* Last modified Tue Jun 12 17:49:08 CEST 2018 by tthai

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* ---------- constants ----------

CONSTANTS
  N,            \* The number of processes.
  T,            \* The maximum number of failures.
  d0,           \* The default time-out interval for all delta(p)(q).
  SendPoint,    \* Period for sending "alive" messages.
  PredictPoint, \* Period for making predictions.
  DELTA,        \* Message-delay bound in partial synchrony.
  PHI           \* Process relative-speed bound in partial synchrony.

ASSUME
  /\ N \in Nat /\ T \in Nat /\ T < N
  /\ SendPoint /= PredictPoint
  /\ PredictPoint % SendPoint /= 0
  /\ SendPoint % PredictPoint /= 0

\* A set of processes.
Proc == 1..N

\* Names for transitions.
TransitionNames == { "INIT", "SEND", "RECEIVE", "PREDICT", "CRASH", "NO" }

\* ---------- variable groups ----------

\* Variables of the communication system Age_Channel.
VARIABLES
  inTransit,        \* set of "boxes" currently in flight
  inDelivery,       \* messages picked up for delivery this transition
  outgoingMessages  \* per-process outgoing buffer

\* Variables of EPFailureDetector (failure detectors).
VARIABLES
  localClock,       \* localClock[i]: local clock at process i
  fromLastHeard,    \* fromLastHeard[i][j]: time since i last heard j
  delta,            \* delta[i][j]: i's timeout for j
  suspected         \* suspected[i]: set of procs i suspects

\* Variables for the environment.
VARIABLES
  procPause,        \* procPause[i]: how long since i took a transition
  moved,            \* moved[i]: last transition taken by i (or "NO"/"INIT")
  failed,           \* failed[i]: TRUE iff i has crashed
  curFailures       \* count of current failures

commVars   == << inTransit, inDelivery, outgoingMessages >>
fdVars     == << localClock, fromLastHeard, delta, suspected >>
envVars    == << procPause, moved, failed, curFailures >>
vars       == << commVars, fdVars, envVars >>

\* ---------- instances ----------

Comm == INSTANCE Age_Channel
FD   == INSTANCE EPFailureDetector

\* ---------- bookkeeping constants ----------

maxAge   == DELTA      \* upper bound on a message's age in transit
maxDelta == d0         \* upper bound on delta[i][j]

\* ---------- type invariant ----------

Box == [content : [from: Proc, to: Proc, body: STRING], age: 0..maxAge]

TypeOK ==
  /\ inTransit \subseteq Box
  /\ inDelivery \subseteq Box
  /\ outgoingMessages \in [Proc -> SUBSET Box]
  /\ localClock    \in [Proc -> 0..(SendPoint * PredictPoint)]
  /\ fromLastHeard \in [Proc -> [Proc -> 0..maxDelta]]
  /\ delta         \in [Proc -> [Proc -> 0..maxDelta]]
  /\ suspected     \in [Proc -> SUBSET Proc]
  /\ procPause     \in [Proc -> 0..(PHI + 1)]
  /\ moved         \in [Proc -> TransitionNames]
  /\ failed        \in [Proc -> BOOLEAN]
  /\ curFailures   \in 0..T

\* ---------- initialization ----------

Init ==
  /\ inTransit       = {}
  /\ inDelivery      = {}
  /\ outgoingMessages = [i \in Proc |-> {}]
  /\ localClock      = [i \in Proc |-> 0]
  /\ fromLastHeard   = [i \in Proc |-> [j \in Proc |-> 0]]
  /\ delta           = [i \in Proc |-> [j \in Proc |-> d0]]
  /\ suspected       = [i \in Proc |-> {}]
  /\ procPause       = [i \in Proc |-> 0]     \* No pauses
  /\ moved           = [i \in Proc |-> "INIT"]
  /\ failed          = [i \in Proc |-> FALSE] \* No failures
  /\ curFailures     = 0                       \* No failures

\* ---------- environment actions ----------

\* Required by SomeLocallyTicked: at every global tick, at least one correct
\* process makes a transition.
SomeLocallyTicked ==
  \E i \in Proc : ~ failed[i] /\ moved[i] /= "NO"

\* EnvTick: a new global tick.
\* 1) The global clock cannot tick if no correct process made a transition.
\* 2) Every box's age increases by 1.
\* 3) Reset moved (no proc has taken a transition this tick).
\* 4) Every procPause increases by 1.
EnvTick ==
  /\ SomeLocallyTicked
  /\ inTransit' = { [b EXCEPT !.age = @ + 1] : b \in inTransit }
  /\ moved'     = [i \in Proc |-> "NO"]
  /\ procPause' = [i \in Proc |-> IF failed[i] THEN procPause[i]
                                    ELSE procPause[i] + 1]
  /\ UNCHANGED << inDelivery, outgoingMessages, fdVars, failed, curFailures >>

\* A process crash.
Crash(i) ==
  /\ ~ failed[i]
  /\ curFailures < T
  /\ moved[i] = "NO"
  /\ failed' = [failed EXCEPT ![i] = TRUE]
  /\ curFailures' = curFailures + 1
  /\ moved'  = [moved  EXCEPT ![i] = "CRASH"]
  /\ UNCHANGED << commVars, fdVars, procPause >>

\* Process p_i sends "alive" messages.
SendAt(i) ==
  /\ ~ failed[i]
  /\ moved[i] = "NO"
  /\ localClock[i] % SendPoint = 0 /\ localClock[i] % PredictPoint /= 0
  /\ outgoingMessages' = [outgoingMessages EXCEPT ![i] = FD!MakeAliveMsgsForAll(i)]
  /\ moved'     = [moved EXCEPT ![i] = "SEND"]
  /\ procPause' = [procPause EXCEPT ![i] = 0]
  /\ localClock' = [localClock EXCEPT ![i] =
                       IF @ + 1 > SendPoint * PredictPoint THEN 0 ELSE @ + 1]
  /\ UNCHANGED << inTransit, inDelivery, fromLastHeard, delta, suspected,
                  failed, curFailures >>

\* Process p_i makes predictions about failures.
PredictAt(i) ==
  /\ ~ failed[i]
  /\ moved[i] = "NO"
  /\ localClock[i] % SendPoint /= 0 /\ localClock[i] % PredictPoint = 0
  /\ suspected' = [suspected EXCEPT ![i] =
                     { j \in Proc \ {i} : fromLastHeard[i][j] > delta[i][j] }]
  /\ moved'     = [moved EXCEPT ![i] = "PREDICT"]
  /\ procPause' = [procPause EXCEPT ![i] = 0]
  /\ localClock' = [localClock EXCEPT ![i] =
                       IF @ + 1 > SendPoint * PredictPoint THEN 0 ELSE @ + 1]
  /\ UNCHANGED << commVars, fromLastHeard, delta, failed, curFailures >>

\* Process p_i receives messages.
ReceiveAt(i) ==
  /\ moved[i] = "NO"
  /\ \/ (localClock[i] % SendPoint = 0 /\ localClock[i] % PredictPoint = 0)
     \/ (localClock[i] % SendPoint /= 0 /\ localClock[i] % PredictPoint /= 0)
  /\ \E delivered \in SUBSET inTransit :
        /\ \A m \in delivered : m.content.to = i
        /\ inTransit'  = inTransit \ delivered
        /\ inDelivery' = delivered
        /\ fromLastHeard' = [fromLastHeard EXCEPT ![i] =
              IF failed[i]
                THEN @
                ELSE [j \in Proc |->
                       IF \E m \in delivered : m.content.from = j
                          THEN 0 ELSE IF @[j] < delta[i][j] THEN @[j] + 1 ELSE @[j]]]
  /\ moved'     = [moved EXCEPT ![i] = "RECEIVE"]
  /\ procPause' = [procPause EXCEPT ![i] = IF failed[i] THEN @ ELSE 0]
  /\ localClock' = [localClock EXCEPT ![i] =
                       IF @ + 1 > SendPoint * PredictPoint THEN 0 ELSE @ + 1]
  /\ UNCHANGED << outgoingMessages, delta, suspected, failed, curFailures >>

\* Communication-system step: pick up outgoing messages and put them in
\* transit. Only messages sent to correct processes are picked up.
PickUp(i) ==
  /\ outgoingMessages[i] /= {}
  /\ LET keep == { b \in outgoingMessages[i] : ~ failed[b.content.to] }
     IN /\ inTransit' = inTransit \cup keep
        /\ outgoingMessages' = [outgoingMessages EXCEPT ![i] = {}]
  /\ UNCHANGED << inDelivery, fdVars, envVars >>

Next ==
  \/ EnvTick
  \/ \E i \in Proc : Crash(i) \/ SendAt(i) \/ PredictAt(i)
                     \/ ReceiveAt(i) \/ PickUp(i)

Spec == Init /\ [][Next]_vars
          /\ WF_vars(EnvTick)

\* ---------- partial-synchrony constraints ----------

\* PHIConstraint: every correct process must take a step in any window of PHI
\* real-time steps. Violated when some correct procPause exceeds PHI.
PHIConstraint == \A i \in Proc : ~ failed[i] => procPause[i] <= PHI

\* DELTAConstraint: messages to correct processes are delivered within DELTA.
DELTAConstraint ==
  \A m \in inTransit :
     /\ ~ failed[m.content.to] => m.age <= DELTA
     /\ failed[m.content.to]   => m.age <= DELTA

NoErrors == PHIConstraint /\ DELTAConstraint

\* ---------- correctness properties ----------

\* Strong Completeness: eventually every crashed process is permanently
\* suspected by every correct process.
StrongCompleteness ==
  \A i, j \in Proc :
     <>[] (failed[j] /\ ~ failed[i] => j \in suspected[i])

\* Eventually Strong Accuracy: after some time, correct processes are not
\* suspected by any correct process.
EventuallyStrongAccuracy ==
  \A i, j \in Proc :
     <>[] (~ failed[i] /\ ~ failed[j] => j \notin suspected[i])

====
