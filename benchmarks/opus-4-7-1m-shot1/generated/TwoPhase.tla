---- MODULE TwoPhase ----
(***************************************************************************)
(* This specification describes the Two-Phase Commit protocol, in which a  *)
(* transaction manager (TM) coordinates the resource managers (RMs) to     *)
(* implement the Transaction Commit specification of module TCommit.  In   *)
(* this specification, RMs spontaneously issue Prepared messages.  We      *)
(* ignore the Prepare messages that the TM can send to the RMs.            *)
(*                                                                         *)
(* For simplicity, we also eliminate Abort messages sent by an RM when     *)
(* it decides to abort.  Such a message would cause the TM to abort the    *)
(* transaction, an event represented here by the TM spontaneously deciding *)
(* to abort.                                                               *)
(*                                                                         *)
(* This specification describes only the safety properties of the          *)
(* protocol--that is, what is allowed to happen.  What must happen would   *)
(* be described by liveness properties, which we do not specify.           *)
(***************************************************************************)
CONSTANT RM   \* The set of resource managers

VARIABLES
  rmState,       \* $rmState[rm]$ is the state of resource manager RM.
  tmState,       \* The state of the transaction manager.
  tmPrepared,    \* The set of RMs from which the TM has received "Prepared" msgs.
  msgs

(***************************************************************************)
(* In the protocol, processes communicate with one another by sending      *)
(* messages.  Since we are specifying only safety, a process is not        *)
(* required to receive a message, so there is no need to model message     *)
(* loss.  We therefore represent message passing with a variable msgs      *)
(* whose value is the set of all messages that have been sent.  Messages   *)
(* are never removed from msgs.                                            *)
(***************************************************************************)
Message ==
  (***************************************************************************)
  (* The set of all possible messages.  Messages of type "Prepared" are sent *)
  (* from the RM indicated by the message's rm field to the TM.  Messages of *)
  (* type "Commit" and "Abort" are broadcast by the TM.                      *)
  (***************************************************************************)
  [type : {"Prepared"}, rm : RM] \cup [type : {"Commit", "Abort"}]

(***************************************************************************)
(* The type-correctness invariant.                                         *)
(***************************************************************************)
TPTypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "committed", "aborted"}
  /\ tmPrepared \subseteq RM
  /\ msgs \subseteq Message

(***************************************************************************)
(* The initial predicate.                                                  *)
(***************************************************************************)
TPInit ==
  /\ rmState = [rm \in RM |-> "working"]
  /\ tmState = "init"
  /\ tmPrepared = {}
  /\ msgs = {}

(***************************************************************************)
(* We now define the actions that may be performed by the processes,       *)
(* first the TM's actions, then the RMs' actions.                          *)
(***************************************************************************)

(***************************************************************************)
(* The TM receives a "Prepared" message from resource manager rm.          *)
(***************************************************************************)
TMRcvPrepared(rm) ==
  /\ tmState = "init"
  /\ [type |-> "Prepared", rm |-> rm] \in msgs
  /\ tmPrepared' = tmPrepared \cup {rm}
  /\ UNCHANGED <<rmState, tmState, msgs>>

(***************************************************************************)
(* The TM commits the transaction; enabled iff the TM is in its initial    *)
(* state and every RM has sent a "Prepared" message.                       *)
(***************************************************************************)
TMCommit ==
  /\ tmState = "init"
  /\ tmPrepared = RM
  /\ tmState' = "committed"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

(***************************************************************************)
(* The TM spontaneously aborts the transaction.                            *)
(***************************************************************************)
TMAbort ==
  /\ tmState = "init"
  /\ tmState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<rmState, tmPrepared>>

(***************************************************************************)
(* Resource manager rm prepares.                                           *)
(***************************************************************************)
RMPrepare(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", rm |-> rm]}
  /\ UNCHANGED <<tmState, tmPrepared>>

(***************************************************************************)
(* Resource manager rm spontaneously decides to abort.  As noted above,    *)
(* rm does not send any message in our simplified spec.                    *)
(***************************************************************************)
RMChooseToAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

(***************************************************************************)
(* Resource manager rm is told by the TM to commit.                        *)
(***************************************************************************)
RMRcvCommitMsg(rm) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

(***************************************************************************)
(* Resource manager rm is told by the TM to abort.                         *)
(***************************************************************************)
RMRcvAbortMsg(rm) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<tmState, tmPrepared, msgs>>

TPNext ==
  \/ TMCommit \/ TMAbort
  \/ \E rm \in RM :
       TMRcvPrepared(rm) \/ RMPrepare(rm) \/ RMChooseToAbort(rm)
         \/ RMRcvCommitMsg(rm) \/ RMRcvAbortMsg(rm)

(***************************************************************************)
(* The complete spec of the Two-Phase Commit protocol.                     *)
(***************************************************************************)
TPSpec ==
  TPInit /\ [][TPNext]_<<rmState, tmState, tmPrepared, msgs>>

(***************************************************************************)
(* This theorem asserts that the type-correctness predicate TPTypeOK is    *)
(* an invariant of the specification.                                      *)
(***************************************************************************)
THEOREM TPSpec => []TPTypeOK

(***************************************************************************)
(* We now assert that the Two-Phase Commit protocol implements the         *)
(* Transaction Commit protocol of module TCommit.                          *)
(***************************************************************************)
TC == INSTANCE TCommit WITH RM <- RM, rmState <- rmState

(***************************************************************************)
(* This theorem asserts that the specification TPSpec of the Two-Phase     *)
(* Commit protocol implements the specification TCSpec of the Transaction  *)
(* Commit protocol.                                                        *)
(***************************************************************************)
THEOREM TPSpec => TC!TCSpec

(***************************************************************************)
(* The two theorems in this module have been checked with TLC for six      *)
(* RMs, a configuration with 50816 reachable states.                       *)
(***************************************************************************)
====
