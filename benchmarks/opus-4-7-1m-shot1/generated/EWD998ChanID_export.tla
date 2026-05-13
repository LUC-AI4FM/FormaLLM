---- MODULE EWD998ChanID_export ----
(***************************************************************************)
(* EWD840                                                                  *)
(* Rule 0                                                                  *)
(* Each node maintains a (local) vector clock                              *)
(* https://en.wikipedia.org/wiki/Vector_clock                              *)
(***************************************************************************)
EXTENDS EWD998ChanID, TLC, Json, IOUtils

(***************************************************************************)
(* c properly initialized with empty channels.                             *)
(* Reduce the number of initial states.                                    *)
(***************************************************************************)
MCInit ==
  /\ active \in [Node -> BOOLEAN]
  /\ color = [n \in Node |-> "white"]
  /\ counter = [n \in Node |-> 0]
  /\ inbox = [n \in Node |-> << >>]
  /\ \E n \in Node :
        inbox' = [inbox EXCEPT ![n] = Append(@, [type |-> "tok", q |-> 0, color |-> "black"])]
  /\ terminationDetected = FALSE

(***************************************************************************)
(* Some real-world invariant (here terminationDetected occurs within N     *)
(* steps where N has been chosen arbitrarily).                             *)
(* Make TLC stop and print the usual error trace.                          *)
(***************************************************************************)
PostInv ==
  terminationDetected => Termination

(***************************************************************************)
(* Format the error-trace as JSON and write to a file.                     *)
(***************************************************************************)
JsonInv ==
  \/ ~terminationDetected
  \/ JsonSerialize("EWD998ChanID_export.json", <<vars>>)

(***************************************************************************)
(* Format the error-trace as JSON and ping some web endpoint.              *)
(***************************************************************************)
AlertInv ==
  \/ ~terminationDetected
  \/ IOExec(<<"curl", "-X", "POST", "http://localhost/alert">>).exitValue = 0

====
