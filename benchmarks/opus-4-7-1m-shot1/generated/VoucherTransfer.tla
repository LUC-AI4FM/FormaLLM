---- MODULE VoucherTransfer ----
(***************************************************************************)
(* Copyright (c) 2018, Backyard Innovations Pte. Ltd., Singapore.          *)
(* Released under the terms of the Apache License 2.0                      *)
(*                                                                         *)
(* The description is based on the "Transfer" operation mentioned in RFC   *)
(* 3506. This specification describes the transfer of Voucher between two  *)
(* Holders. It is implemented over the Two-Phase Commit protocol, in which *)
(* a Voucher Transaction Provider (VTP) coordinates the "Source" Voucher   *)
(* Holders (SHs) to trade vouchers (Vs) to "Destination" Voucher Holders   *)
(* (DHs) described in the VoucherLifeCycle specification module.           *)
(***************************************************************************)
CONSTANTS
  V,    \* The set of Vouchers
  SH,   \* The set of "Source" Voucher Holders
  DH    \* The set of "Destination" Voucher Holders

VARIABLES
  vState,        \* vState[v] is the state of voucher v.
  vlcState,      \* vlcState[v] is the state of the voucher life cycle machine.
  shState,       \* shState[sh] is the state of "source" voucher holder sh.
  dhState,       \* dhState[dh] is the state of "destination" voucher holder dh.
  vtpState,      \* The state of the voucher transaction provider.
  vtpTPrepared,  \* The set of SHs and DHs that have sent "Prepared".
  msgs

(***************************************************************************)
(* In the protocol, processes communicate with one another by sending      *)
(* messages.  For simplicity, we represent message passing with the        *)
(* variable msgs whose value is the set of all messages that have been     *)
(* sent.                                                                   *)
(***************************************************************************)

(***************************************************************************)
(* The set of all possible messages.                                       *)
(***************************************************************************)
Messages ==
       [type : {"Prepared"}, vsh : SH]
  \cup [type : {"Prepared"}, vdh : DH]
  \cup [type : {"Transfer", "Abort"}]

(***************************************************************************)
(* The type-correctness invariant.                                         *)
(***************************************************************************)
VTPTypeOK ==
  /\ vState    \in [V  -> {"valid", "transferred"}]
  /\ vlcState  \in [V  -> {"working", "prepared", "transferred", "aborted"}]
  /\ shState   \in [SH -> {"holding", "prepared", "transferred", "aborted"}]
  /\ dhState   \in [DH -> {"waiting", "prepared", "transferred", "aborted"}]
  /\ vtpState  \in {"init", "done"}
  /\ vtpTPrepared \subseteq (SH \cup DH)
  /\ msgs \subseteq Messages

(***************************************************************************)
(* The initial predicate.                                                  *)
(***************************************************************************)
VTPInit ==
  /\ vState    = [v  \in V  |-> "valid"]
  /\ vlcState  = [v  \in V  |-> "working"]
  /\ shState   = [sh \in SH |-> "holding"]
  /\ dhState   = [dh \in DH |-> "waiting"]
  /\ vtpState  = "init"
  /\ vtpTPrepared = {}
  /\ msgs = {}

(***************************************************************************)
(* We now define the actions that may be performed by the processes.       *)
(***************************************************************************)
VTPRcvPrepared(sh, dh) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vsh |-> sh] \in msgs
  /\ [type |-> "Prepared", vdh |-> dh] \in msgs
  /\ vtpTPrepared' = vtpTPrepared \cup {sh, dh}
  /\ UNCHANGED <<vState, vlcState, shState, dhState, vtpState, msgs>>

VTPTransfer ==
  /\ vtpState = "init"
  /\ vtpTPrepared = (SH \cup DH)
  /\ vtpState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Transfer"]}
  /\ UNCHANGED <<vState, vlcState, shState, dhState, vtpTPrepared>>

VTPAbort ==
  /\ vtpState = "init"
  /\ vtpState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<vState, vlcState, shState, dhState, vtpTPrepared>>

SHPrepare(sh) ==
  /\ shState[sh] = "holding"
  /\ shState' = [shState EXCEPT ![sh] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vsh |-> sh]}
  /\ UNCHANGED <<vState, vlcState, dhState, vtpState, vtpTPrepared>>

SHChooseToAbort(sh) ==
  /\ shState[sh] = "holding"
  /\ shState' = [shState EXCEPT ![sh] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, dhState, vtpState, vtpTPrepared, msgs>>

SHRcvTransferMsg(sh) ==
  /\ shState[sh] = "prepared"
  /\ [type |-> "Transfer"] \in msgs
  /\ shState' = [shState EXCEPT ![sh] = "transferred"]
  /\ UNCHANGED <<vState, vlcState, dhState, vtpState, vtpTPrepared, msgs>>

SHRcvAbortMsg(sh) ==
  /\ [type |-> "Abort"] \in msgs
  /\ shState' = [shState EXCEPT ![sh] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, dhState, vtpState, vtpTPrepared, msgs>>

DHPrepare(dh) ==
  /\ dhState[dh] = "waiting"
  /\ dhState' = [dhState EXCEPT ![dh] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vdh |-> dh]}
  /\ UNCHANGED <<vState, vlcState, shState, vtpState, vtpTPrepared>>

DHChooseToAbort(dh) ==
  /\ dhState[dh] = "waiting"
  /\ dhState' = [dhState EXCEPT ![dh] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, shState, vtpState, vtpTPrepared, msgs>>

DHRcvTransferMsg(dh) ==
  /\ dhState[dh] = "prepared"
  /\ [type |-> "Transfer"] \in msgs
  /\ dhState' = [dhState EXCEPT ![dh] = "transferred"]
  /\ UNCHANGED <<vState, vlcState, shState, vtpState, vtpTPrepared, msgs>>

DHRcvAbortMsg(dh) ==
  /\ [type |-> "Abort"] \in msgs
  /\ dhState' = [dhState EXCEPT ![dh] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, shState, vtpState, vtpTPrepared, msgs>>

VTPNext ==
  \/ VTPTransfer \/ VTPAbort
  \/ \E sh \in SH, dh \in DH : VTPRcvPrepared(sh, dh)
  \/ \E sh \in SH :
       SHPrepare(sh) \/ SHChooseToAbort(sh) \/ SHRcvTransferMsg(sh) \/ SHRcvAbortMsg(sh)
  \/ \E dh \in DH :
       DHPrepare(dh) \/ DHChooseToAbort(dh) \/ DHRcvTransferMsg(dh) \/ DHRcvAbortMsg(dh)

(***************************************************************************)
(* A state predicate asserting that a SH and an DH have not reached        *)
(* conflicting decisions. It is an invariant of the specification.         *)
(***************************************************************************)
VTPConsistent ==
  \A sh \in SH, dh \in DH :
    ~ /\ shState[sh] = "transferred"
      /\ dhState[dh] = "aborted"

(***************************************************************************)
(* The complete spec of a Voucher Transfer using Two-Phase Commit protocol.*)
(***************************************************************************)
VTPSpec ==
  VTPInit /\ [][VTPNext]_<<vState, vlcState, shState, dhState, vtpState, vtpTPrepared, msgs>>

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

(***************************************************************************)
(* We now assert that the Voucher Transfer specification implements the    *)
(* Voucher Life Cycle specification.                                       *)
(***************************************************************************)
VSpec == INSTANCE VoucherLifeCycle WITH V <- V, vState <- vState, vlcState <- vlcState

THEOREM VTPSpec => VSpec!VSpec

====
