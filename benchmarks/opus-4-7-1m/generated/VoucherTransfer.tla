---- MODULE VoucherTransfer ----
(***************************************************************************)
(* Copyright (c) 2018, Backyard Innovations Pte. Ltd., Singapore.          *)
(* Released under the terms of the Apache License 2.0                      *)
(*                                                                         *)
(* Authors:                                                                *)
(*   Santhosh Raju  <santhosh@byisystems.com>                              *)
(*   Cherry G. Mathew <cherry@byisystems.com>                              *)
(*   Fransisca Andriani <sisca@byisystems.com>                             *)
(*                                                                         *)
(* This specification is based on the "Transfer" operation of RFC 3506.   *)
(* It describes voucher transfer between two Holders, implemented over    *)
(* the Two-Phase Commit protocol: a Voucher Transaction Provider (VTP)    *)
(* coordinates Source Voucher Holders (SHs) and Destination Voucher       *)
(* Holders (DHs). For simplicity, SHs and DHs spontaneously issue         *)
(* Prepared messages, and the VTP can spontaneously decide to abort.      *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS V,    \* The set of Vouchers.
          SH,   \* The set of "Source" Voucher Holders.
          DH    \* The set of "Destination" Voucher Holders.

VARIABLES vState,        \* vState[v]: the state of voucher v.
          vlcState,      \* vlcState[v]: the state of the voucher life-cycle.
          shState,       \* shState[sh]: state of source voucher holder sh.
          dhState,       \* dhState[dh]: state of dest voucher holder dh.
          vtpState,      \* The state of the voucher transaction provider.
          vtpTPrepared,  \* SHs/DHs from which VTP received "Prepared" msgs.
          msgs           \* The set of all messages sent so far.

vars == <<vState, vlcState, shState, dhState, vtpState, vtpTPrepared, msgs>>

\* The set of all possible messages.
Messages ==
    [type : {"Prepared"}, vsh : SH, vdh : DH]
        \cup [type : {"Transfer", "Abort"}]

\* The type-correctness invariant.
VTPTypeOK ==
    /\ vState   \in [V  -> {"valid", "transferred"}]
    /\ vlcState \in [V  -> {"working", "transferred", "aborted"}]
    /\ shState  \in [SH -> {"holding", "prepared", "transferred", "aborted"}]
    /\ dhState  \in [DH -> {"waiting", "prepared", "transferred", "aborted"}]
    /\ vtpState \in {"init", "done"}
    /\ vtpTPrepared \subseteq (SH \cup DH)
    /\ msgs \subseteq Messages

\* The initial predicate.
VTPInit ==
    /\ vState   = [v  \in V  |-> "valid"]
    /\ vlcState = [v  \in V  |-> "working"]
    /\ shState  = [sh \in SH |-> "holding"]
    /\ dhState  = [dh \in DH |-> "waiting"]
    /\ vtpState = "init"
    /\ vtpTPrepared = {}
    /\ msgs = {}

\*****************************************************************************
\* VTP actions.
\*****************************************************************************

\* The VTP receives a Prepared message from sh and dh.
VTPRcvPrepared(sh, dh) ==
    /\ vtpState = "init"
    /\ [type |-> "Prepared", vsh |-> sh, vdh |-> dh] \in msgs
    /\ vtpTPrepared' = vtpTPrepared \cup {sh, dh}
    /\ UNCHANGED <<vState, vlcState, shState, dhState, vtpState, msgs>>

\* The VTP transfers the voucher: enabled iff every SH and DH has prepared.
VTPTransfer(v) ==
    /\ vtpState = "init"
    /\ vtpTPrepared = SH \cup DH
    /\ vtpState' = "done"
    /\ vState'   = [vState   EXCEPT ![v] = "transferred"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "transferred"]
    /\ msgs' = msgs \cup {[type |-> "Transfer"]}
    /\ UNCHANGED <<shState, dhState, vtpTPrepared>>

\* The VTP spontaneously aborts.
VTPAbort(v) ==
    /\ vtpState = "init"
    /\ vtpState' = "done"
    /\ vlcState' = [vlcState EXCEPT ![v] = "aborted"]
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<vState, shState, dhState, vtpTPrepared>>

\*****************************************************************************
\* SH actions.
\*****************************************************************************

\* Source Voucher holder sh prepares.
SHPrepare(sh) ==
    /\ shState[sh] = "holding"
    /\ shState' = [shState EXCEPT ![sh] = "prepared"]
    /\ \E dh \in DH :
         msgs' = msgs \cup {[type |-> "Prepared", vsh |-> sh, vdh |-> dh]}
    /\ UNCHANGED <<vState, vlcState, dhState, vtpState, vtpTPrepared>>

\* Source Voucher holder sh spontaneously decides to abort.
SHChooseToAbort(sh) ==
    /\ shState[sh] = "holding"
    /\ shState' = [shState EXCEPT ![sh] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, dhState, vtpState, vtpTPrepared, msgs>>

\* Source Voucher holder sh is told by the VTP to Transfer.
SHRcvTransferMsg(sh) ==
    /\ [type |-> "Transfer"] \in msgs
    /\ shState' = [shState EXCEPT ![sh] = "transferred"]
    /\ UNCHANGED <<vState, vlcState, dhState, vtpState, vtpTPrepared, msgs>>

\* Source Voucher holder sh is told by the VTP to abort.
SHRcvAbortMsg(sh) ==
    /\ [type |-> "Abort"] \in msgs
    /\ shState' = [shState EXCEPT ![sh] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, dhState, vtpState, vtpTPrepared, msgs>>

\*****************************************************************************
\* DH actions.
\*****************************************************************************

DHPrepare(dh) ==
    /\ dhState[dh] = "waiting"
    /\ dhState' = [dhState EXCEPT ![dh] = "prepared"]
    /\ \E sh \in SH :
         msgs' = msgs \cup {[type |-> "Prepared", vsh |-> sh, vdh |-> dh]}
    /\ UNCHANGED <<vState, vlcState, shState, vtpState, vtpTPrepared>>

DHChooseToAbort(dh) ==
    /\ dhState[dh] = "waiting"
    /\ dhState' = [dhState EXCEPT ![dh] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, shState, vtpState, vtpTPrepared, msgs>>

DHRcvTransferMsg(dh) ==
    /\ [type |-> "Transfer"] \in msgs
    /\ dhState' = [dhState EXCEPT ![dh] = "transferred"]
    /\ UNCHANGED <<vState, vlcState, shState, vtpState, vtpTPrepared, msgs>>

DHRcvAbortMsg(dh) ==
    /\ [type |-> "Abort"] \in msgs
    /\ dhState' = [dhState EXCEPT ![dh] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, shState, vtpState, vtpTPrepared, msgs>>

VTPNext ==
    \/ \E sh \in SH : \E dh \in DH : VTPRcvPrepared(sh, dh)
    \/ \E v \in V : VTPTransfer(v) \/ VTPAbort(v)
    \/ \E sh \in SH : SHPrepare(sh) \/ SHChooseToAbort(sh)
                       \/ SHRcvTransferMsg(sh) \/ SHRcvAbortMsg(sh)
    \/ \E dh \in DH : DHPrepare(dh) \/ DHChooseToAbort(dh)
                       \/ DHRcvTransferMsg(dh) \/ DHRcvAbortMsg(dh)

VTPSpec == VTPInit /\ [][VTPNext]_vars

\* A state predicate: an SH and DH have not reached conflicting decisions.
VTPConsistent ==
    \A sh \in SH, dh \in DH :
        ~(shState[sh] = "transferred" /\ dhState[dh] = "aborted")
        /\ ~(shState[sh] = "aborted" /\ dhState[dh] = "transferred")

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

\* The Voucher Transfer specification implements the Voucher Life Cycle.
VLC == INSTANCE VoucherLifeCycle WITH V <- V, vState <- vState, vlcState <- vlcState

THEOREM VTPSpec => VLC!VSpec
====
