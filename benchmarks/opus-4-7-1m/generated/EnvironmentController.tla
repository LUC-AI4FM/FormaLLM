---- MODULE EnvironmentController ----
(***************************************************************************)
(* An encoding of a parameterized and partially synchronous model of      *)
(* eventually perfect failure detectors with crash faults from:           *)
(*   Chandra, Toueg. Unreliable failure detectors for reliable            *)
(*   distributed systems. JACM 43.2 (1996): 225-267.                      *)
(*                                                                         *)
(* Igor Konnov, Thanh Hai Tran, Josef Wider, 2018.                        *)
(*                                                                         *)
(* This module instantiates Age_Channel.tla for the communication system  *)
(* and EPFailureDetector.tla for correct processes.                       *)
(*                                                                         *)
(* Properties verified:                                                    *)
(*   Strong Completeness: eventually every crashed process is permanently *)
(*     suspected by every correct process.                                *)
(*   Eventually Strong Accuracy: there is a time after which correct      *)
(*     processes are not suspected by any correct process.                *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N,            \* The number of processes.
          T,            \* The maximum number of failures.
          d0,           \* Default time-out interval for all delta(p)(q).
          SendPoint,    \* Send "alive" every SendPoint ticks.
          PredictPoint, \* Make a prediction every PredictPoint ticks.
          DELTA,        \* Message-delay upper bound (partial synchrony).
          PHI           \* Relative-speed upper bound (partial synchrony).

\* Assumptions about the constraints.
ASSUME
    /\ N \in Nat /\ T \in Nat /\ N > T
    /\ SendPoint /= PredictPoint
    /\ PredictPoint % SendPoint /= 0
    /\ SendPoint % PredictPoint /= 0

\* A set of processes.
Proc == 1..N

\* maxAge: estimated upper bound on how long a message stays in transit.
maxAge == DELTA + 1

\* maxDelta: upper bound of delta[i][j].
maxDelta == d0 + DELTA

\* Process transition names.
TransitionNames == {"INIT", "SEND", "RECEIVE", "PREDICT", "CRASH", "NO"}

\* A box in transit: a message wrapped with an age.
Box == [content : [from : Proc, to : Proc, type : {"alive"}], age : 0..maxAge]

VARIABLES
    inTransit,      \* set of message boxes sent but not delivered
    inDelivery,     \* boxes delivered in the current transition
    moved,          \* moved[i] = last transition name of process i
    procPause,      \* procPause[i] = how long process i has not moved
    failed,         \* failed[i] = TRUE if process i has crashed
    failNum,        \* number of current failures
    localClock,     \* localClock[i] of process i (finite domain)
    outgoingMessages, \* outgoingMessages[i] = msgs to be sent from i
    suspected,      \* suspected[i] = processes that i suspects
    delta,          \* delta[i][j] = i's waiting time for messages from j
    fromLastHeard   \* fromLastHeard[i][j] = how long since i heard from j

vars == <<inTransit, inDelivery, moved, procPause, failed, failNum,
          localClock, outgoingMessages, suspected, delta, fromLastHeard>>

TypeOK ==
    /\ inTransit \in SUBSET Box
    /\ inDelivery \in SUBSET Box
    /\ moved \in [Proc -> TransitionNames]
    /\ procPause \in [Proc -> 0..PHI]
    /\ failed \in [Proc -> BOOLEAN]
    /\ failNum \in 0..T
    /\ localClock \in [Proc -> 0..(SendPoint + PredictPoint + maxDelta)]
    /\ outgoingMessages \in [Proc -> SUBSET [from : Proc, to : Proc, type : {"alive"}]]
    /\ suspected \in [Proc -> SUBSET Proc]
    /\ delta \in [Proc -> [Proc -> 0..maxDelta]]
    /\ fromLastHeard \in [Proc -> [Proc -> 0..(maxDelta + 1)]]

\* Initialization.
Init ==
    /\ inTransit = {}
    /\ inDelivery = {}
    /\ moved = [i \in Proc |-> "INIT"]
    /\ procPause = [i \in Proc |-> 0]
    /\ failed = [i \in Proc |-> FALSE]
    /\ failNum = 0
    /\ localClock = [i \in Proc |-> 0]
    /\ outgoingMessages = [i \in Proc |-> {}]
    /\ suspected = [i \in Proc |-> {}]
    /\ delta = [i \in Proc |-> [j \in Proc |-> d0]]
    /\ fromLastHeard = [i \in Proc |-> [j \in Proc |-> 0]]

\* A process p_i crashes.
Crash(i) ==
    /\ ~failed[i]
    /\ failNum < T
    /\ failed' = [failed EXCEPT ![i] = TRUE]
    /\ failNum' = failNum + 1
    /\ moved' = [moved EXCEPT ![i] = "CRASH"]
    /\ procPause' = [procPause EXCEPT ![i] = 0]
    /\ UNCHANGED <<inTransit, inDelivery, localClock, outgoingMessages,
                   suspected, delta, fromLastHeard>>

\* At least one correct process makes a transition in this tick.
SomeLocallyTicked ==
    \E i \in Proc : ~failed[i] /\ moved[i] /= "NO"

\* A new tick of the environmental clock.
EnvTick ==
    /\ SomeLocallyTicked
    /\ inTransit' = { [b EXCEPT !.age = @ + 1] : b \in inTransit }
    /\ moved' = [i \in Proc |-> "NO"]
    /\ procPause' = [i \in Proc |->
                       IF moved[i] = "NO" /\ ~failed[i]
                       THEN procPause[i] + 1 ELSE procPause[i]]
    /\ UNCHANGED <<inDelivery, failed, failNum, localClock, outgoingMessages,
                   suspected, delta, fromLastHeard>>

\* A correct process p_i sends "alive" messages to all others.
Send(i) ==
    /\ ~failed[i]
    /\ moved[i] = "NO"
    /\ localClock[i] % SendPoint = 0
    /\ localClock[i] % PredictPoint /= 0
    /\ outgoingMessages' = [outgoingMessages EXCEPT ![i] =
            { [from |-> i, to |-> j, type |-> "alive"] : j \in Proc \ {i} }]
    /\ moved' = [moved EXCEPT ![i] = "SEND"]
    /\ procPause' = [procPause EXCEPT ![i] = 0]
    /\ localClock' = [localClock EXCEPT ![i] = (@ + 1) % (SendPoint * PredictPoint + maxDelta)]
    /\ UNCHANGED <<inTransit, inDelivery, failed, failNum, suspected, delta, fromLastHeard>>

\* A correct process p_i predicts failures.
Predict(i) ==
    /\ ~failed[i]
    /\ moved[i] = "NO"
    /\ localClock[i] % SendPoint /= 0
    /\ localClock[i] % PredictPoint = 0
    /\ suspected' = [suspected EXCEPT ![i] =
            { j \in Proc \ {i} : fromLastHeard[i][j] > delta[i][j] }]
    /\ moved' = [moved EXCEPT ![i] = "PREDICT"]
    /\ procPause' = [procPause EXCEPT ![i] = 0]
    /\ localClock' = [localClock EXCEPT ![i] = (@ + 1) % (SendPoint * PredictPoint + maxDelta)]
    /\ UNCHANGED <<inTransit, inDelivery, failed, failNum, outgoingMessages, delta, fromLastHeard>>

\* A correct process p_i receives messages.
Receive(i) ==
    /\ ~failed[i]
    /\ moved[i] = "NO"
    /\ \/ /\ localClock[i] % SendPoint = 0 /\ localClock[i] % PredictPoint = 0
       \/ /\ localClock[i] % SendPoint /= 0 /\ localClock[i] % PredictPoint /= 0
    /\ \E delivered \in SUBSET { b \in inDelivery : b.content.to = i } :
         fromLastHeard' = [fromLastHeard EXCEPT ![i] =
            [j \in Proc |->
                IF \E b \in delivered : b.content.from = j THEN 0
                ELSE IF @[j] > delta[i][j] THEN @[j] ELSE @[j] + 1]]
    /\ moved' = [moved EXCEPT ![i] = "RECEIVE"]
    /\ procPause' = [procPause EXCEPT ![i] = 0]
    /\ localClock' = [localClock EXCEPT ![i] = (@ + 1) % (SendPoint * PredictPoint + maxDelta)]
    /\ UNCHANGED <<inTransit, inDelivery, failed, failNum, outgoingMessages, suspected, delta>>

\* The communication system picks up outgoing messages into inTransit.
Pickup(i) ==
    /\ outgoingMessages[i] /= {}
    /\ inTransit' = inTransit \cup
            { [content |-> m, age |-> 0] :
                m \in { msg \in outgoingMessages[i] : ~failed[msg.to] } }
    /\ outgoingMessages' = [outgoingMessages EXCEPT ![i] = {}]
    /\ UNCHANGED <<inDelivery, moved, procPause, failed, failNum, localClock,
                   suspected, delta, fromLastHeard>>

\* Deliver messages to a process, even if it crashed (the boxes leave inTransit).
Deliver ==
    /\ \E S \in SUBSET inTransit :
        /\ S /= {}
        /\ inTransit' = inTransit \ S
        /\ inDelivery' = inDelivery \cup S
    /\ UNCHANGED <<moved, procPause, failed, failNum, localClock,
                   outgoingMessages, suspected, delta, fromLastHeard>>

\* PHIConstraint: every correct process moves within PHI real-time steps.
PHIConstraint == \A i \in Proc : ~failed[i] => procPause[i] <= PHI

\* DELTAConstraint: messages deliver within DELTA ticks.
DELTAConstraint ==
    /\ \A b \in inTransit : (failed[b.content.to] => b.age <= DELTA)
    /\ \A b \in inTransit : b.age <= maxAge

Next ==
    \/ EnvTick
    \/ \E i \in Proc : Crash(i) \/ Send(i) \/ Predict(i) \/ Receive(i) \/ Pickup(i)
    \/ Deliver

Spec == Init /\ [][Next]_vars
            /\ WF_vars(Next)
            /\ \A i \in Proc : WF_vars(Send(i) \/ Predict(i) \/ Receive(i))

\* Strong Completeness: eventually every crashed process is permanently
\* suspected by every correct process.
StrongCompleteness ==
    \A i, j \in Proc :
        failed[j] /\ ~failed[i] ~> [](j \in suspected[i])

\* Eventually Strong Accuracy: eventually correct processes are not
\* suspected by any correct process.
EventuallyStrongAccuracy ==
    <>[](\A i, j \in Proc : (~failed[i] /\ ~failed[j]) => j \notin suspected[i])

====
