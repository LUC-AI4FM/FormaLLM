-------------------------- MODULE EnvironmentController --------------------------
\* Parameterized, partially-synchronous model of an eventually perfect failure
\* detector with crash faults (Chandra-Toueg). Composes Age_Channel (channel)
\* and EPFailureDetector (correct-process behavior) under an environment that
\* drives global ticks, message ages, and process pauses.

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    N,            \* number of processes
    T,            \* maximum number of failures
    d0,           \* default time-out interval for delta(p)(q)
    SendPoint,    \* tick interval at which correct processes send "alive"
    PredictPoint, \* tick interval at which correct processes predict failures
    DELTA,        \* upper bound on message delay (partial synchrony)
    PHI           \* upper bound on relative process speeds

ASSUME N \in Nat /\ N >= 1
ASSUME T \in Nat /\ T < N
ASSUME SendPoint \in Nat /\ SendPoint >= 1
ASSUME PredictPoint \in Nat /\ PredictPoint >= 1
ASSUME SendPoint # PredictPoint
ASSUME PredictPoint % SendPoint # 0 /\ SendPoint % PredictPoint # 0
ASSUME DELTA \in Nat /\ PHI \in Nat /\ d0 \in Nat

\* A set of processes.
Proc == 1..N

\* Transition names.
INIT_T   == "INIT"
SEND_T   == "SEND"
RECV_T   == "RECEIVE"
PRED_T   == "PREDICT"
CRASH_T  == "CRASH"
NO_T     == "NO"

Transitions == {INIT_T, SEND_T, RECV_T, PRED_T, CRASH_T, NO_T}

\* Messages: simple records with a sender, receiver, and tag.
Messages == [from : Proc, to : Proc, tag : {"alive"}]

\* A box wraps a message with an integer age (time in transit).
maxAge == DELTA + 1
maxDelta == d0 + DELTA + 1
Boxes == [content : Messages, age : 0..maxAge]

VARIABLES
    \* communication-system variables (Age_Channel)
    inTransit,
    inDelivery,
    \* failure-detector variables (EPFailureDetector)
    suspected,       \* suspected[i]: set of processes p_i suspects
    delta,           \* delta[i][j]: timeout p_i uses for p_j
    fromLastHeard,   \* fromLastHeard[i][j]: ticks since last msg from p_j
    outgoingMessages,\* outgoingMessages[i]: msgs p_i has queued to send
    localClock,      \* local clock of each process
    \* environment variables
    procPause,       \* procPause[i]: ticks since p_i last took a transition
    moved,           \* moved[i]: last transition taken by p_i (or "NO")
    failed,          \* failed[i] = TRUE iff p_i has crashed
    nFailures        \* number of current failures

ChannelVars == <<inTransit, inDelivery>>
DetectorVars == <<suspected, delta, fromLastHeard, outgoingMessages, localClock>>
EnvVars == <<procPause, moved, failed, nFailures>>
vars == <<ChannelVars, DetectorVars, EnvVars>>

Channel == INSTANCE Age_Channel
Detector == INSTANCE EPFailureDetector

\* Initialization.
Init ==
    /\ inTransit = {}
    /\ inDelivery = {}
    /\ suspected = [i \in Proc |-> {}]
    /\ delta = [i \in Proc |-> [j \in Proc |-> d0]]
    /\ fromLastHeard = [i \in Proc |-> [j \in Proc |-> 0]]
    /\ outgoingMessages = [i \in Proc |-> {}]
    /\ localClock = [i \in Proc |-> 0]
    /\ procPause = [i \in Proc |-> 0]
    /\ moved = [i \in Proc |-> INIT_T]
    /\ failed = [i \in Proc |-> FALSE]
    /\ nFailures = 0

\* A process crashes.
Crash(i) ==
    /\ failed[i] = FALSE
    /\ nFailures < T
    /\ failed' = [failed EXCEPT ![i] = TRUE]
    /\ nFailures' = nFailures + 1
    /\ moved' = [moved EXCEPT ![i] = CRASH_T]
    /\ UNCHANGED <<ChannelVars, DetectorVars, procPause>>

\* At every global tick at least one correct process makes a transition.
SomeLocallyTicked ==
    \E i \in Proc : failed[i] = FALSE /\ moved[i] # NO_T

\* New tick of the environmental clock.
EnvTick ==
    /\ SomeLocallyTicked
    /\ inTransit' = { [content |-> b.content,
                       age |-> IF b.age < maxAge THEN b.age + 1 ELSE b.age]
                       : b \in inTransit }
    /\ inDelivery' = {}
    /\ moved' = [i \in Proc |-> IF failed[i] THEN moved[i] ELSE NO_T]
    /\ procPause' = [i \in Proc |->
                       IF failed[i] THEN procPause[i]
                       ELSE IF procPause[i] < PHI + 1 THEN procPause[i] + 1
                            ELSE procPause[i]]
    /\ UNCHANGED <<suspected, delta, fromLastHeard, outgoingMessages,
                   localClock, failed, nFailures>>

\* Correct process p_i sends "alive" messages to all others.
Send(i) ==
    /\ failed[i] = FALSE
    /\ moved[i] = NO_T
    /\ localClock[i] % SendPoint = 0
    /\ localClock[i] % PredictPoint # 0
    /\ LET msgs == {[from |-> i, to |-> j, tag |-> "alive"] : j \in Proc \ {i}}
       IN  /\ outgoingMessages' = [outgoingMessages EXCEPT ![i] = msgs]
           /\ inTransit' = inTransit \cup
                { [content |-> m, age |-> 0] : m \in msgs }
    /\ inDelivery' = {}
    /\ localClock' = [localClock EXCEPT ![i] = (localClock[i] + 1) % maxDelta]
    /\ moved' = [moved EXCEPT ![i] = SEND_T]
    /\ procPause' = [procPause EXCEPT ![i] = 0]
    /\ UNCHANGED <<suspected, delta, fromLastHeard, failed, nFailures>>

\* Correct process p_i predicts failures.
Predict(i) ==
    /\ failed[i] = FALSE
    /\ moved[i] = NO_T
    /\ localClock[i] % SendPoint # 0
    /\ localClock[i] % PredictPoint = 0
    /\ suspected' = [suspected EXCEPT
         ![i] = {j \in Proc \ {i} : fromLastHeard[i][j] > delta[i][j]}]
    /\ localClock' = [localClock EXCEPT ![i] = (localClock[i] + 1) % maxDelta]
    /\ moved' = [moved EXCEPT ![i] = PRED_T]
    /\ procPause' = [procPause EXCEPT ![i] = 0]
    /\ UNCHANGED <<ChannelVars, delta, fromLastHeard, outgoingMessages,
                   failed, nFailures>>

\* Correct process p_i receives the messages in inDelivery aimed at it.
Receive(i) ==
    /\ failed[i] = FALSE
    /\ moved[i] = NO_T
    /\ \/ (localClock[i] % SendPoint = 0 /\ localClock[i] % PredictPoint = 0)
       \/ (localClock[i] % SendPoint # 0 /\ localClock[i] % PredictPoint # 0)
    /\ LET received == {m \in inDelivery : m.to = i}
       IN  fromLastHeard' = [fromLastHeard EXCEPT
             ![i] = [j \in Proc |->
                       IF \E m \in received : m.from = j
                       THEN 0
                       ELSE IF fromLastHeard[i][j] > delta[i][j]
                            THEN fromLastHeard[i][j]
                            ELSE fromLastHeard[i][j] + 1]]
    /\ localClock' = [localClock EXCEPT ![i] = (localClock[i] + 1) % maxDelta]
    /\ moved' = [moved EXCEPT ![i] = RECV_T]
    /\ procPause' = [procPause EXCEPT ![i] = 0]
    /\ UNCHANGED <<ChannelVars, suspected, delta, outgoingMessages,
                   failed, nFailures>>

\* Environment nondeterministically delivers some boxes whose age bounded.
DeliverSome ==
    /\ \E boxes \in SUBSET inTransit :
        /\ boxes # {}
        /\ inDelivery' = {b.content : b \in boxes}
        /\ inTransit' = inTransit \ boxes
    /\ UNCHANGED <<DetectorVars, EnvVars>>

\* Message delivered to a crashed process: discard.
DiscardForCrashed ==
    /\ \E b \in inTransit : failed[b.content.to]
    /\ inTransit' = { b \in inTransit : ~ failed[b.content.to] }
    /\ inDelivery' = {}
    /\ UNCHANGED <<DetectorVars, EnvVars>>

Next ==
    \/ EnvTick
    \/ \E i \in Proc : Send(i) \/ Predict(i) \/ Receive(i) \/ Crash(i)
    \/ DeliverSome
    \/ DiscardForCrashed

Fairness == \A i \in Proc : WF_vars(Send(i) \/ Predict(i) \/ Receive(i))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Partial-synchrony constraints filter the executions considered.
PHIConstraint == \A i \in Proc : ~ failed[i] => procPause[i] <= PHI
DELTAConstraint ==
    /\ \A b \in inTransit : ~ failed[b.content.to] => b.age <= DELTA

NoErrors == TRUE

\* Type invariant.
TypeOK ==
    /\ inTransit \subseteq Boxes
    /\ inDelivery \subseteq Messages
    /\ suspected \in [Proc -> SUBSET Proc]
    /\ delta \in [Proc -> [Proc -> 0..maxDelta]]
    /\ fromLastHeard \in [Proc -> [Proc -> 0..maxDelta]]
    /\ outgoingMessages \in [Proc -> SUBSET Messages]
    /\ localClock \in [Proc -> 0..maxDelta]
    /\ procPause \in [Proc -> 0..(PHI + 1)]
    /\ moved \in [Proc -> Transitions]
    /\ failed \in [Proc -> BOOLEAN]
    /\ nFailures \in 0..T

\* Strong Completeness: eventually every crashed process is permanently
\* suspected by every correct process.
StrongCompleteness ==
    \A i, j \in Proc :
        (failed[j] /\ ~ failed[i]) ~> [](j \in suspected[i])

\* Eventually Strong Accuracy: eventually no correct process is suspected
\* by any correct process.
EventuallyStrongAccuracy ==
    \A i, j \in Proc :
        ~ failed[i] /\ ~ failed[j] ~> [](j \notin suspected[i])

=============================================================================
