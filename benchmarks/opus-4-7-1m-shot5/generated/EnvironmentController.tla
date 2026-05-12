---- MODULE EnvironmentController ----
(***************************************************************************)
(* An encoding of a parameterized and partially synchronous model of the   *)
(* eventually perfect failure detectors with crash faults from:            *)
(* [1] Chandra, Tushar Deepak, and Sam Toueg. "Unreliable failure          *)
(*     detectors for reliable distributed systems." Journal of the ACM     *)
(*     (JACM) 43.2 (1996): 225-267.                                        *)
(*                                                                          *)
(* Igor Konnov, Thanh Hai Tran, Josef Wider, 2018                          *)
(* This file is a subject to the license that is bundled together with    *)
(* this package and can be found in the file LICENSE.                     *)
(*                                                                          *)
(* - This specification instances two other specs, Age_Channel.tla for     *)
(*   the communication system, and EPFailureDetector.tla for behaviors of  *)
(*   correct processes.                                                    *)
(* - Every message sent by some process is wrapped into a box with an age *)
(*   which shows how long this message have been in transit. Boxes for    *)
(*   messages which were sent but have not been delivered are stored in a *)
(*   variable inTransit.                                                  *)
(* - Messages which are delivered in the current transition are stored in *)
(*   a variable inDelivery.                                               *)
(* - The system tracks what last transition a process takes, and how long *)
(*   some correct process has not taken a transition. The information are *)
(*   saved in variables moved and procPause, respectively. Crashes are    *)
(*   also tracked.                                                        *)
(* - Every process has its own local clock which is localClock[i].        *)
(* - Every correct process repeatedly sends "alive" messages to other     *)
(*   processes, and repeatedly make predictions about failures. However,  *)
(*   a process cannot send and predict at the same time. A process can    *)
(*   receive messages when it does not execute neither the operation SEND *)
(*   nor the operation PREDICT.                                           *)
(* - "alive" messages are created by calling the operator                 *)
(*   MakeAliveMsgsForAll in EPFailureDetector, and then stored in         *)
(*   outgoingMessages.                                                    *)
(* - In this specification, a correct process sends "alive" messages to   *)
(*   others at every SendPoint tick of its local clock, and makes         *)
(*   predictions about failures at every PredictPoint tick of its local   *)
(*   clock.                                                               *)
(* - The predictions are saved in a variable suspected. If j \in          *)
(*   suspected[i], a process p_i suspects that a process p_j crashed.     *)
(* - Every process p_i has a waiting time, called delta[i][j], for        *)
(*   hearing some messages for other process p_j.                         *)
(* - When a process p_i executes the action Predict, if p_i hasn't        *)
(*   received any message from p_j for a too long period, e.g.            *)
(*   fromLastHeard[i][j] > delta[i][j], p_i puts p_j into its suspected   *)
(*   list.                                                                *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
  N,            \* The number of processes
  T,            \* The maximum number of failures
  d0,           \* The default time-out interval for all delta(p)(q)
  SendPoint,    \* Every correct process sends alive messages to others at every SendPoint ticks of its local clock.
  PredictPoint, \* Every correct process makes predictions about failures at every PredictPoint ticks of its lock clock.
  DELTA,        \* For the constraint of message delay in partial synchrony.
  PHI           \* For the constraint of relative speeds of different processes in partial synchrony.

(***************************************************************************)
(* Assumptions about the constraints in our system.                        *)
(* - SendPoint # PredictPoint: a process cannot both send messages and     *)
(*   receive messages in one transition.                                   *)
(* - PredictPoint % SendPoint # 0 /\ SendPoint % PredictPoint # 0 :        *)
(*   the operation Predict cannot subsume the operation Predict and vice   *)
(*   versa.                                                                *)
(***************************************************************************)
ASSUME
  /\ N \in Nat \ {0}
  /\ T \in Nat
  /\ T < N
  /\ d0 \in Nat \ {0}
  /\ SendPoint \in Nat \ {0}
  /\ PredictPoint \in Nat \ {0}
  /\ SendPoint # PredictPoint
  /\ PredictPoint % SendPoint # 0
  /\ SendPoint % PredictPoint # 0
  /\ DELTA \in Nat \ {0}
  /\ PHI \in Nat \ {0}

Proc == 1..N        \* A set of processes

\* All Names of processes' transitions
TransitionNames == {"INIT", "NO", "SEND", "RECEIVE", "PREDICT", "CRASH"}

\* Required by SomeLocallyTicked
maxAge == DELTA + 1
maxDelta == d0 + 1

(***************************************************************************)
(* Whenever a message is picked up, the communication system puts this    *)
(* message into a box with an age. The age shows how long a message has    *)
(* been in transit. The field "content" points to a message.               *)
(***************************************************************************)
Box == [content : [from : Proc, to : Proc, type : {"alive"}],
        age : 0..maxAge]

VARIABLES
  (* Variables for the communication system *)
  inTransit,         \* A set of messages sent by correct processes wrapped in boxes
  inDelivery,        \* Messages delivered in the current transition
  outgoingMessages,  \* Outgoing alive messages buffered before they enter inTransit
  (* Variables for the specification EPFailureDetector which describes
     behaviors of correct processes *)
  localClock,
  suspected,
  delta,
  fromLastHeard,
  (* Variables for the environment *)
  procPause,         \* How long a process p_i has not taken a transition.
  moved,             \* The last transition that a process p_i took.
  failed,            \* failed[i] = TRUE: a process p_i crashed.
  nFailures          \* A number of current failures

\* All variables
vars == <<inTransit, inDelivery, outgoingMessages,
          localClock, suspected, delta, fromLastHeard,
          procPause, moved, failed, nFailures>>

\* For the communication system: spec Age_Channel
Channel == INSTANCE Age_Channel
\* For correct detectors: spec EPFailureDetector
Detector == INSTANCE EPFailureDetector

----------------------------------------------------------------------------
(* Initialization *)
Init ==
  /\ inTransit = {}
  /\ inDelivery = {}
  /\ outgoingMessages = [i \in Proc |-> {}]
  /\ localClock = [i \in Proc |-> 0]
  /\ suspected = [i \in Proc |-> {}]
  /\ delta = [i \in Proc |-> [j \in Proc |-> d0]]
  /\ fromLastHeard = [i \in Proc |-> [j \in Proc |-> 0]]
  /\ procPause = [i \in Proc |-> 0]    \* No pauses
  /\ moved = [i \in Proc |-> "INIT"]   \* Every process finishes the initialization.
  /\ failed = [i \in Proc |-> FALSE]   \* No failures
  /\ nFailures = 0                     \* No failures

----------------------------------------------------------------------------
(* A process p_i crashes. *)
Crash(i) ==
  /\ ~ failed[i]
  /\ nFailures < T
  /\ failed' = [failed EXCEPT ![i] = TRUE]
  /\ nFailures' = nFailures + 1
  /\ moved' = [moved EXCEPT ![i] = "CRASH"]
  /\ UNCHANGED <<inTransit, inDelivery, outgoingMessages,
                 localClock, suspected, delta, fromLastHeard, procPause>>

\* Required by SomeLocallyTicked: at every global tick, at least one correct process makes a transition.
SomeLocallyTicked ==
  \E i \in Proc : ~ failed[i] /\ moved[i] # "NO"

(***************************************************************************)
(* A new tick of the environmental clock.                                  *)
(* - 1st conj: The global clock cannot have a new tick if no correct       *)
(*   process makes a transition in the last global tick.                   *)
(* - 2nd conj: Every box's age increases by 1.                             *)
(* - 3rd conj: Reset moved.                                                *)
(* - 4th conj: Every pause is increased by 1.                              *)
(***************************************************************************)
EnvTick ==
  /\ SomeLocallyTicked
  /\ inTransit' = { [b EXCEPT !.age = @ + 1] : b \in inTransit }
  /\ moved' = [i \in Proc |-> "NO"]
  /\ procPause' = [i \in Proc |->
        IF failed[i] THEN procPause[i] ELSE procPause[i] + 1]
  /\ UNCHANGED <<inDelivery, outgoingMessages,
                 localClock, suspected, delta, fromLastHeard, failed, nFailures>>

(* Only messages sent to correct processes are picked up. *)
PickUp(i) ==
  /\ ~ failed[i]
  /\ outgoingMessages[i] # {}
  /\ inTransit' = inTransit \cup
        { [content |-> m, age |-> 0] : m \in outgoingMessages[i] }
  /\ outgoingMessages' = [outgoingMessages EXCEPT ![i] = {}]
  /\ UNCHANGED <<inDelivery, localClock, suspected, delta, fromLastHeard,
                 procPause, moved, failed, nFailures>>

(* A process p_i can send "alive" messages to all. *)
Send(i) ==
  /\ ~ failed[i]
  /\ moved[i] = "NO"
  /\ localClock[i] % SendPoint = 0
  /\ localClock[i] % PredictPoint # 0
  /\ outgoingMessages' = [outgoingMessages EXCEPT ![i] =
        { [from |-> i, to |-> j, type |-> "alive"] : j \in Proc \ {i} }]
  /\ moved' = [moved EXCEPT ![i] = "SEND"]
  /\ procPause' = [procPause EXCEPT ![i] = 0]
  /\ UNCHANGED <<inTransit, inDelivery, localClock, suspected,
                 delta, fromLastHeard, failed, nFailures>>

(* A process p_i can makes predictions about failures. *)
Predict(i) ==
  /\ ~ failed[i]
  /\ moved[i] = "NO"
  /\ localClock[i] % SendPoint # 0
  /\ localClock[i] % PredictPoint = 0
  /\ suspected' = [suspected EXCEPT ![i] =
        { j \in Proc \ {i} : fromLastHeard[i][j] > delta[i][j] }]
  /\ moved' = [moved EXCEPT ![i] = "PREDICT"]
  /\ procPause' = [procPause EXCEPT ![i] = 0]
  /\ UNCHANGED <<inTransit, inDelivery, outgoingMessages, localClock,
                 delta, fromLastHeard, failed, nFailures>>

(* Some messages are delivered to a process p_i. *)
Receive(i) ==
  /\ moved[i] = "NO"
  /\ \E S \in SUBSET { b \in inTransit : b.content.to = i } :
        S # {} /\
        inDelivery' = S /\
        inTransit' = inTransit \ S /\
        IF failed[i]
          THEN
            (* However, p_i cannot receive those messages because p_i crashed before. *)
            UNCHANGED <<localClock, suspected, delta, fromLastHeard, procPause, moved>>
          ELSE
            /\ fromLastHeard' = [fromLastHeard EXCEPT ![i] =
                  [j \in Proc |->
                     IF \E b \in S : b.content.from = j
                       THEN 0
                       ELSE @[j] + 1 ]]
            /\ moved' = [moved EXCEPT ![i] = "RECEIVE"]
            /\ procPause' = [procPause EXCEPT ![i] = 0]   \* Reset procPause'[i]
            /\ UNCHANGED <<localClock, suspected, delta>>
  /\ UNCHANGED <<outgoingMessages, failed, nFailures>>

(***************************************************************************)
(* Two constraints PHIConstraint and DELTAConstraint are respectively      *)
(* restrictions on message delay and relative speeds of processes in       *)
(* partial synchrony.                                                      *)
(***************************************************************************)
PHIConstraint ==
  \A i \in Proc : ~ failed'[i] => procPause'[i] <= PHI

PHIConstraint1 ==
  \A i \in Proc : (~ failed'[i]) => (procPause'[i] <= PHI)

DELTAConstraint ==
  /\ \A m \in inTransit' :
        ~ failed'[m.content.to] => m.age <= DELTA
  /\ \A i \in Proc :
        ((failed'[i] = TRUE)
          => ( \A m \in inTransit' : \/ m.content.to # i
                                     \/ m.age <= DELTA ))

\* No errors happen
NoErrors ==
  /\ PHIConstraint
  /\ DELTAConstraint

(* Next transition *)
Next ==
  \/ EnvTick
  \/ \E i \in Proc : Crash(i) \/ PickUp(i) \/ Send(i) \/ Predict(i) \/ Receive(i)

(* The specification *)
Spec == Init /\ [][Next /\ NoErrors]_vars /\ WF_vars(EnvTick)

----------------------------------------------------------------------------
(* Type invariant *)
TypeOK ==
  /\ inTransit \subseteq Box
  /\ inDelivery \subseteq Box
  /\ outgoingMessages \in [Proc -> SUBSET [from : Proc, to : Proc, type : {"alive"}]]
  /\ localClock \in [Proc -> Nat]
  /\ suspected \in [Proc -> SUBSET Proc]
  /\ delta \in [Proc -> [Proc -> Nat]]
  /\ fromLastHeard \in [Proc -> [Proc -> Nat]]
  /\ procPause \in [Proc -> Nat]
  /\ moved \in [Proc -> TransitionNames]
  /\ failed \in [Proc -> BOOLEAN]
  /\ nFailures \in 0..T

(***************************************************************************)
(* Two properties of an eventually perfect failure detector                *)
(* - Strong Completeness: Eventually every process that crashes is         *)
(*   permanently suspected by every correct process.                       *)
(* - Eventually Strong Accuracy: There is a time after which correct       *)
(*   processes are not suspected by any correct process.                   *)
(***************************************************************************)
StrongCompleteness ==
  <>[] \A i, j \in Proc : (failed[j] /\ ~ failed[i]) => j \in suspected[i]

EventuallyStrongAccuracy ==
  <>[] \A i, j \in Proc : (~ failed[i] /\ ~ failed[j]) => j \notin suspected[i]

====
