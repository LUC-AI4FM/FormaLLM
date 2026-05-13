---- MODULE EWD998ChanID_export ----
(***************************************************************************)
(* TLA+ wrapper for EWD998ChanID that exports the error-trace as JSON.    *)
(***************************************************************************)
EXTENDS EWD998ChanID, TLC, Json, IOUtils

\* c properly initialized with empty channels. Reduce the number of initial states.
MCInit ==
  /\ active \in [Node -> BOOLEAN]
  /\ \E n \in Node : color = [m \in Node |-> IF m = n THEN "black" ELSE "white"]
  /\ counter = [n \in Node |-> 0]
  /\ inbox = [n \in Node |-> <<>>]
  /\ clock = [n \in Node |-> [m \in Node |-> 0]]
  /\ terminationDetected = FALSE

\* Some real-world invariant (here terminationDetected occurs within N steps
\* where N has been chosen arbitrarily).
PostInv ==
  terminationDetected => TLCGet("level") < 50

\* Format the error-trace as JSON and write to a file.
JsonInv ==
  IF terminationDetected
  THEN /\ PrintT(ToJsonObject([state |-> <<active, color, counter, inbox>>]))
       /\ FALSE  \* Make TLC stop and print the usual error trace.
  ELSE TRUE

\* Format the error-trace as JSON and ping some web endpoint.
PingInv ==
  IF terminationDetected
  THEN /\ IOExec(<<"curl", "-X", "POST", "http://localhost/ping">>)
       /\ FALSE  \* Make TLC stop and print the usual error trace.
  ELSE TRUE

\* Rule 0
\* EWD840
\* Each node maintains a (local) vector clock
\* https://en.wikipedia.org/wiki/Vector_clock

====
