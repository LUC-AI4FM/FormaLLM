---- MODULE VoucherCancel ----
(***************************************************************************)
(* Copyright (c) 2018, Backyard Innovations Pte. Ltd., Singapore.          *)
(* Released under the terms of the Apache License 2.0                      *)
(*                                                                         *)
(* Authors:                                                                *)
(*   Santhosh Raju  <santhosh@byisystems.com>                              *)
(*   Cherry G. Mathew <cherry@byisystems.com>                              *)
(*   Fransisca Andriani <sisca@byisystems.com>                             *)
(*                                                                         *)
(* This specification describes the cancellation of a Voucher between an  *)
(* Issuer and a Holder, implemented over Two-Phase Commit: a Voucher      *)
(* Transaction Provider (VTP) coordinates Voucher Issuers (Is) to cancel  *)
(* vouchers (Vs) held by Voucher Holders (Hs). Hs and Is spontaneously    *)
(* issue Prepared messages. VTP may spontaneously abort.                  *)
(*                                                                         *)
(* This operation is an addendum to RFC 3506.                              *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS V,  \* The set of Vouchers.
          H,  \* The set of Voucher Holders.
          I   \* The set of Voucher Issuers.

VARIABLES vState,       \* state of voucher v
          vlcState,     \* state of the voucher life-cycle
          hState,       \* state of voucher holder h
          iState,       \* state of voucher issuer i
          vtpState,     \* state of the voucher transaction provider
          vtpCPrepared, \* set of Hs/Is from which VTP got "Prepared"
          msgs          \* set of all messages sent

vars == <<vState, vlcState, hState, iState, vtpState, vtpCPrepared, msgs>>

Messages ==
    [type : {"Prepared"}, vh : H, vc : I]
        \cup [type : {"Cancel", "Abort"}]

VTPTypeOK ==
    /\ vState   \in [V -> {"valid", "cancelled"}]
    /\ vlcState \in [V -> {"working", "cancelled", "aborted"}]
    /\ hState   \in [H -> {"holding", "prepared", "cancelled", "aborted"}]
    /\ iState   \in [I -> {"issued", "prepared", "cancelled", "aborted"}]
    /\ vtpState \in {"init", "done"}
    /\ vtpCPrepared \subseteq (H \cup I)
    /\ msgs \subseteq Messages

VTPInit ==
    /\ vState   = [v \in V |-> "valid"]
    /\ vlcState = [v \in V |-> "working"]
    /\ hState   = [h \in H |-> "holding"]
    /\ iState   = [j \in I |-> "issued"]
    /\ vtpState = "init"
    /\ vtpCPrepared = {}
    /\ msgs = {}

\* VTP receives Prepared from h and i.
VTPRcvPrepared(h, i) ==
    /\ vtpState = "init"
    /\ [type |-> "Prepared", vh |-> h, vc |-> i] \in msgs
    /\ vtpCPrepared' = vtpCPrepared \cup {h, i}
    /\ UNCHANGED <<vState, vlcState, hState, iState, vtpState, msgs>>

\* VTP cancels the voucher.
VTPCancel(v) ==
    /\ vtpState = "init"
    /\ vtpCPrepared = H \cup I
    /\ vtpState' = "done"
    /\ vState'   = [vState   EXCEPT ![v] = "cancelled"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "cancelled"]
    /\ msgs' = msgs \cup {[type |-> "Cancel"]}
    /\ UNCHANGED <<hState, iState, vtpCPrepared>>

\* VTP spontaneously aborts.
VTPAbort(v) ==
    /\ vtpState = "init"
    /\ vtpState' = "done"
    /\ vlcState' = [vlcState EXCEPT ![v] = "aborted"]
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<vState, hState, iState, vtpCPrepared>>

HPrepare(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "prepared"]
    /\ \E i \in I :
         msgs' = msgs \cup {[type |-> "Prepared", vh |-> h, vc |-> i]}
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpCPrepared>>

HChooseToAbort(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpCPrepared, msgs>>

HRcvCancelMsg(h) ==
    /\ [type |-> "Cancel"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "cancelled"]
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpCPrepared, msgs>>

HRcvAbortMsg(h) ==
    /\ [type |-> "Abort"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpCPrepared, msgs>>

IPrepare(i) ==
    /\ iState[i] = "issued"
    /\ iState' = [iState EXCEPT ![i] = "prepared"]
    /\ \E h \in H :
         msgs' = msgs \cup {[type |-> "Prepared", vh |-> h, vc |-> i]}
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpCPrepared>>

IChooseToAbort(i) ==
    /\ iState[i] = "issued"
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpCPrepared, msgs>>

IRcvCancelMsg(i) ==
    /\ [type |-> "Cancel"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "cancelled"]
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpCPrepared, msgs>>

IRcvAbortMsg(i) ==
    /\ [type |-> "Abort"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpCPrepared, msgs>>

VTPNext ==
    \/ \E h \in H : \E i \in I : VTPRcvPrepared(h, i)
    \/ \E v \in V : VTPCancel(v) \/ VTPAbort(v)
    \/ \E h \in H : HPrepare(h) \/ HChooseToAbort(h)
                     \/ HRcvCancelMsg(h) \/ HRcvAbortMsg(h)
    \/ \E i \in I : IPrepare(i) \/ IChooseToAbort(i)
                     \/ IRcvCancelMsg(i) \/ IRcvAbortMsg(i)

VTPSpec == VTPInit /\ [][VTPNext]_vars

\* A H and an I have not reached conflicting decisions.
VTPConsistent ==
    \A h \in H, i \in I :
        /\ ~(hState[h] = "cancelled" /\ iState[i] = "aborted")
        /\ ~(hState[h] = "aborted" /\ iState[i] = "cancelled")

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

VLC == INSTANCE VoucherLifeCycle WITH V <- V, vState <- vState, vlcState <- vlcState

THEOREM VTPSpec => VLC!VSpec
====
