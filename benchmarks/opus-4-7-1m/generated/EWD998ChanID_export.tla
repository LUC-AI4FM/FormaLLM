---- MODULE EWD998ChanID_export ----
(***************************************************************************)
(* Wrapper around EWD998ChanID for exporting error-traces. Reduces the    *)
(* initial states and provides a real-world invariant (terminationDetected*)
(* occurs within N steps). On violation, TLC prints the error trace; this *)
(* module formats it as JSON and writes it to a file or pings an endpoint.*)
(***************************************************************************)
EXTENDS EWD998ChanID, TLC, Naturals, Sequences, FiniteSets, IOUtils, Json

\* Each node maintains a (local) vector clock.
\* https://en.wikipedia.org/wiki/Vector_clock
VARIABLE vc
varsWithVC == <<vars, vc>>

MCInit ==
    \* c is properly initialized with empty channels, reducing initial states.
    /\ Init
    /\ \A n \in Node : inbox[n] = << >>
    /\ vc = [n \in Node |-> [m \in Node |-> 0]]

\* Rule 0: each step bumps a node's own vector-clock entry.
TickVC(n) ==
    vc' = [vc EXCEPT ![n] = [@ EXCEPT ![n] = @ + 1]]

\* Some real-world invariant: terminationDetected occurs within N steps,
\* where N is chosen arbitrarily.
N == 10
PostInv == TLCGet("level") < N \/ ~terminationDetected

\* Format the error-trace as JSON and write to a file.
JsonInv ==
    \/ ~terminationDetected
    \/ JsonSerialize("trace.json", TLCGet("level"))

\* Format the error-trace as JSON and ping some web endpoint.
PingInv ==
    \/ ~terminationDetected
    \/ IOExec(<<"curl", "-X", "POST", "http://example/notify",
                "-d", ToJson(TLCGet("level"))>>).exitValue = 0

====
