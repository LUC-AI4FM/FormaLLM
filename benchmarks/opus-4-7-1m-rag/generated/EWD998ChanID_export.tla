---- MODULE EWD998ChanID_export ----
\* A model-checking wrapper around EWD998ChanID that exports the
\* error-trace of a synthetic safety violation.  Two flavours of export
\* are provided: a JsonInv that writes the trace to a JSON file, and a
\* PostInv that writes the trace as JSON and POSTs it to a web endpoint.

EXTENDS EWD998ChanID, TLC, TLCExt, Json, IOUtils

\* Init except that active and color are restricted to TRUE and "white"
\* to reduce the number of initial states.
MCInit ==
  (* Each node maintains a (local) vector clock *)
  (* https://en.wikipedia.org/wiki/Vector_clock *)
  /\ clock = [ n \in Node |-> IF n = Initiator
                THEN [ m \in Node |-> IF m = Initiator THEN 1 ELSE 0 ]
                ELSE [ m \in Node |-> 0 ] ]
  (* Rule 0 *)
  /\ counter = [n \in Node |-> 0] \* c properly initialized
  /\ inbox = [n \in Node |-> IF n = Initiator
                              THEN << [type |-> "tok", q |-> 0,
                                       color |-> "black",
                                       vc |-> clock[n] ] >>
                              ELSE <<>>] \* with empty channels.
  (* EWD840 *)
  \* Reduce the number of initial states.
  /\ active \in [Node -> {TRUE}]
  /\ color  \in [Node -> {"white"}]

\* Some real-world invariant (here terminationDetected occurs within N
\* steps where N has been chosen arbitrarily).
Inv ==
    \* terminationDetected occurs within N steps
    \* (here N = 23 is chosen arbitrarily).
    terminationDetected => TLCGet("level") < 23

Alias ==
    [ active   |-> active,
      color    |-> color,
      counter  |-> counter,
      inbox    |-> inbox,
      clock    |-> clock ]

\* Format the error-trace as JSON and write to a file.
JsonInv ==
    \* Make TLC stop and print the usual error trace.
    IF terminationDetected
    THEN /\ JsonSerialize("EWD998ChanID_export.json", Trace)
         /\ FALSE
    ELSE TRUE

\* Format the error-trace as JSON and ping some web endpoint.
PostInv ==
    \* Make TLC stop and print the usual error trace.
    IF terminationDetected
    THEN /\ LET resp == IOExec(<< "curl", "-X", "POST",
                                  "-H", "Content-Type: application/json",
                                  "-d", ToJson(Trace),
                                  "https://example.com/ewd998" >>)
            IN resp.exitValue = 0
         /\ FALSE
    ELSE TRUE

====
