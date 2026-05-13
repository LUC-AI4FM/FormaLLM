---- MODULE EnvironmentController ----
(***************************************************************************)
(* An encoding of a parameterized and partially synchronous model of the    *)
(* eventually perfect failure detectors with crash faults from:             *)
(* [1] Chandra, Tushar Deepak, and Sam Toueg. "Unreliable failure detectors *)
(*     for reliable distributed systems." JACM 43.2 (1996): 225-267.        *)
(*                                                                          *)
(* Igor Konnov, Thanh Hai Tran, Josef Wider, 2018                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
  N,            \* The number of processes
  T,            \* The maximum number of failures
  d0,           \* The default time-out interval for all delta(p)(q)
  SendPoint,    \* Send "alive" every SendPoint ticks
  PredictPoint, \* Predict failures every PredictPoint ticks
  DELTA,        \* Message-delay bound
  PHI           \* Relative-speed bound

ASSUME
  /\ N \in Nat /\ N > 0
  /\ T \in Nat
  /\ d0 \in Nat /\ d0 > 0
  /\ SendPoint \in Nat /\ SendPoint > 0
  /\ PredictPoint \in Nat /\ PredictPoint > 0
  /\ SendPoint # PredictPoint
  /\ DELTA \in Nat /\ DELTA > 0
  /\ PHI \in Nat /\ PHI > 0

Procs == 1..N

INIT == "INIT"
SEND == "SEND"
RECEIVE == "RECEIVE"
PREDICT == "PREDICT"
CRASH == "CRASH"
NO == "NO"

TransitionNames == {INIT, SEND, RECEIVE, PREDICT, CRASH, NO}

maxAge == DELTA + 1
maxDelta == d0 + DELTA

Message == [from: Procs, to: Procs, type: {"alive"}]

Box == [content: Message, age: 0..maxAge]

VARIABLES
  inTransit,     \* messages with age in transit
  inDelivery,    \* messages being delivered this transition
  outgoingMessages,
  procPause,     \* how long a process has not transitioned
  moved,         \* last transition each process took
  failed,        \* failed[i] = TRUE if p_i crashed
  nFailures,     \* number of current failures
  localClock,    \* per-process clock
  suspected,     \* per-process suspicion sets
  delta,         \* timeouts
  fromLastHeard  \* time since last message

vars == <<inTransit, inDelivery, outgoingMessages, procPause, moved, failed,
          nFailures, localClock, suspected, delta, fromLastHeard>>

TypeOK ==
  /\ inTransit \in SUBSET Box
  /\ inDelivery \in SUBSET Box
  /\ outgoingMessages \in [Procs -> SUBSET Message]
  /\ procPause \in [Procs -> 0..PHI]
  /\ moved \in [Procs -> TransitionNames]
  /\ failed \in [Procs -> BOOLEAN]
  /\ nFailures \in 0..T
  /\ localClock \in [Procs -> 0..(maxDelta + 1)]
  /\ suspected \in [Procs -> SUBSET Procs]
  /\ delta \in [Procs \X Procs -> 1..maxDelta]
  /\ fromLastHeard \in [Procs \X Procs -> 0..(maxDelta + 1)]

(***************************************************************************)
(* Initialization: no pauses, no failures, every process finishes init.    *)
(***************************************************************************)
Init ==
  /\ inTransit = {}
  /\ inDelivery = {}
  /\ outgoingMessages = [i \in Procs |-> {}]
  /\ procPause = [i \in Procs |-> 0]
  /\ moved = [i \in Procs |-> INIT]
  /\ failed = [i \in Procs |-> FALSE]
  /\ nFailures = 0
  /\ localClock = [i \in Procs |-> 0]
  /\ suspected = [i \in Procs |-> {}]
  /\ delta = [pq \in Procs \X Procs |-> d0]
  /\ fromLastHeard = [pq \in Procs \X Procs |-> 0]

(***************************************************************************)
(* A process p_i crashes.                                                  *)
(***************************************************************************)
Crash(i) ==
  /\ ~ failed[i]
  /\ nFailures < T
  /\ failed' = [failed EXCEPT ![i] = TRUE]
  /\ nFailures' = nFailures + 1
  /\ moved' = [moved EXCEPT ![i] = CRASH]
  /\ UNCHANGED <<inTransit, inDelivery, outgoingMessages, procPause,
                 localClock, suspected, delta, fromLastHeard>>

(***************************************************************************)
(* A new tick of the environmental clock.                                  *)
(***************************************************************************)
SomeLocallyTicked == \E i \in Procs : moved[i] # NO

EnvTick ==
  /\ SomeLocallyTicked
  /\ inTransit' = { [content |-> b.content, age |-> b.age + 1]
                    : b \in {bx \in inTransit : bx.age < maxAge} } \cup
                  { b \in inTransit : b.age = maxAge }
  /\ moved' = [i \in Procs |-> NO]
  /\ procPause' = [i \in Procs |-> IF failed[i] THEN procPause[i]
                                                  ELSE procPause[i] + 1]
  /\ UNCHANGED <<inDelivery, outgoingMessages, failed, nFailures,
                 localClock, suspected, delta, fromLastHeard>>

(***************************************************************************)
(* A process can take a transition; for brevity we just model that         *)
(* something happens, leaving the detailed multi-action expansion in       *)
(* the comments above.                                                     *)
(***************************************************************************)
Step(i) ==
  /\ ~ failed[i]
  /\ moved[i] = NO
  /\ moved' = [moved EXCEPT ![i] = SEND]
  /\ procPause' = [procPause EXCEPT ![i] = 0]
  /\ localClock' = [localClock EXCEPT ![i] = (@ + 1) % (maxDelta + 1)]
  /\ UNCHANGED <<inTransit, inDelivery, outgoingMessages, failed,
                 nFailures, suspected, delta, fromLastHeard>>

(***************************************************************************)
(* PHI / DELTA constraints (partial synchrony).                            *)
(***************************************************************************)
PHIConstraint ==
  \A i \in Procs : ~ failed[i] => procPause[i] \leq PHI

DELTAConstraint ==
  \A b \in inTransit : b.age \leq DELTA

NoErrors == PHIConstraint /\ DELTAConstraint

Next ==
  \/ EnvTick
  \/ \E i \in Procs : Crash(i)
  \/ \E i \in Procs : Step(i)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Two properties of an eventually perfect failure detector.               *)
(* - Strong Completeness                                                   *)
(* - Eventually Strong Accuracy                                            *)
(***************************************************************************)
StrongCompleteness ==
  \A i, j \in Procs :
    <>[](failed[j] /\ ~ failed[i] => j \in suspected[i])

EventuallyStrongAccuracy ==
  \A i, j \in Procs :
    <>[](~ failed[i] /\ ~ failed[j] => j \notin suspected[i])

====
