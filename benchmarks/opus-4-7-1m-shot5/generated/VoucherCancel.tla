---- MODULE VoucherCancel ----
(***************************************************************************)
(* Copyright (c) 2018, Backyard Innovations Pte. Ltd., Singapore.          *)
(* Released under the terms of the Apache License 2.0                      *)
(* See: file LICENSE that came with this software for details.             *)
(*                                                                          *)
(* This file contains Intellectual Property that belongs to                *)
(* Backyard Innovations Pte Ltd., Singapore.                               *)
(*                                                                          *)
(* Authors: Santhosh Raju <santhosh@byisystems.com>                        *)
(*          Cherry G. Mathew <cherry@byisystems.com>                       *)
(*          Fransisca Andriani <sisca@byisystems.com>                      *)
(***************************************************************************)

(***************************************************************************)
(* This specification describes the cancellation of Voucher between an    *)
(* Issuer and a Holder. It is implemented over the Two-Phase Commit       *)
(* protocol, in which a Voucher Transaction Provider (VTP) coordinates    *)
(* the Voucher Issuers (Is) to cancel vouchers (Vs) to Voucher Holders    *)
(* (Hs) as described in the VoucherLifeCycle specification module. In    *)
(* this specification, Hs and Is spontaneously issue Prepared messages.  *)
(* We ignore the Prepare messages that the VTP can send to the Hs and    *)
(* Is.                                                                   *)
(*                                                                          *)
(* For simplicity, we also eliminate Abort messages sent by an Hs / Is    *)
(* when it decides to abort. Such a message would cause the VTP to abort *)
(* the transaction, an event represented here by the VTP spontaneously    *)
(* deciding to abort.                                                     *)
(*                                                                          *)
(* Note: This operation is an addendum to the operations described in    *)
(* RFC 3506. This operation is not described in the RFC.                 *)
(***************************************************************************)

CONSTANT
  V,   \* The set of Vouchers
  H,   \* The set of Voucher Holders
  I    \* The set of Voucher Issuers

VARIABLES
  vState,        \* vState[v] is the state of voucher v.
  vlcState,      \* vlcState[v] is the state of the voucher life cycle machine.
  hState,        \* hState[h] is the state of voucher holder h.
  iState,        \* iState[i] is the state of voucher issuer i.
  vtpState,      \* The state of the voucher transaction provider.
  vtpCPrepared,  \* The set of Hs and Is from which the VTP has received "Prepared for Voucher Cancel" messages.
  msgs

(*********************************************************************)
(* In the protocol, processes communicate with one another by sending  *)
(* messages.  For simplicity, we represent message passing with the    *)
(* variable msgs whose value is the set of all messages that have been *)
(* sent.  A message is sent by adding it to the set msgs.              *)
(*********************************************************************)

Messages ==
  (***********************************************************************)
  (* The set of all possible messages.  Messages of type "Prepared" are    *)
  (* sent from the H indicated by the message's vh field to the VTP.       *)
  (* Similar "Prepared" is also sent from I indicated by message's vc      *)
  (* field to the VTP. Messages of type "Cancel" and "Abort" are broadcast *)
  (* by the VTPs, to be received by all Hs and Is.                        *)
  (***********************************************************************)
  [type : {"Prepared"}, vh : H] \cup
  [type : {"Prepared"}, vc : I] \cup
  [type : {"Cancel", "Abort"}]

(***********************************************************************)
(* The type-correctness invariant                                        *)
(***********************************************************************)
VTPTypeOK ==
  /\ vState \in [V -> {"valid", "cancelled", "aborted"}]
  /\ vlcState \in [V -> {"working", "done"}]
  /\ hState \in [H -> {"holding", "prepared", "cancelled", "aborted"}]
  /\ iState \in [I -> {"waiting", "prepared", "cancelled", "aborted"}]
  /\ vtpState \in {"init", "done"}
  /\ vtpCPrepared \subseteq (H \cup I)
  /\ msgs \subseteq Messages

(***********************************************************************)
(* The initial predicate.                                                *)
(***********************************************************************)
VTPInit ==
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ hState = [h \in H |-> "holding"]
  /\ iState = [i \in I |-> "waiting"]
  /\ vtpState = "init"
  /\ vtpCPrepared = {}
  /\ msgs = {}

(***************************************************************************)
(* We now define the actions that may be performed by the processes, first *)
(* the VTP's actions, the Hs' actions, then the Is' actions.               *)
(***************************************************************************)

(***********************************************************************)
(* The VTP receives a "Prepared" message from Voucher Holder h and the   *)
(* Voucher Issuer i.                                                     *)
(***********************************************************************)
VTPRcvPrepared(h, i) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vh |-> h] \in msgs
  /\ [type |-> "Prepared", vc |-> i] \in msgs
  /\ vtpCPrepared' = vtpCPrepared \cup {h, i}
  /\ UNCHANGED <<vState, vlcState, hState, iState, vtpState, msgs>>

(***********************************************************************)
(* The VTP Cancels the voucher; enabled iff the VTP is in its initial    *)
(* state and every H and I has sent a "Prepared" message.                *)
(***********************************************************************)
VTPCancel(v) ==
  /\ vtpState = "init"
  /\ vtpCPrepared = H \cup I
  /\ vtpState' = "done"
  /\ vState' = [vState EXCEPT ![v] = "cancelled"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
  /\ msgs' = msgs \cup {[type |-> "Cancel"]}
  /\ UNCHANGED <<hState, iState, vtpCPrepared>>

(***********************************************************************)
(* The VTP spontaneously aborts the transaction.                         *)
(***********************************************************************)
VTPAbort(v) ==
  /\ vtpState = "init"
  /\ vtpState' = "done"
  /\ vState' = [vState EXCEPT ![v] = "aborted"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<hState, iState, vtpCPrepared>>

(***********************************************************************)
(* Voucher holder h prepares.                                            *)
(***********************************************************************)
HPrepare(h) ==
  /\ hState[h] = "holding"
  /\ hState' = [hState EXCEPT ![h] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
  /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpCPrepared>>

(***********************************************************************)
(* Voucher holder h spontaneously decides to abort.                      *)
(***********************************************************************)
HChooseToAbort(h) ==
  /\ hState[h] = "holding"
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpCPrepared, msgs>>

(***********************************************************************)
(* Voucher holder h is told by the VTP to Cancel.                        *)
(***********************************************************************)
HRcvCancelMsg(h) ==
  /\ hState[h] = "prepared"
  /\ [type |-> "Cancel"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "cancelled"]
  /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpCPrepared, msgs>>

(***********************************************************************)
(* Voucher holder h is told by the VTP to abort.                         *)
(***********************************************************************)
HRcvAbortMsg(h) ==
  /\ hState[h] \in {"holding", "prepared"}
  /\ [type |-> "Abort"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpCPrepared, msgs>>

(***********************************************************************)
(* Voucher issuer i prepares.                                            *)
(***********************************************************************)
IPrepare(i) ==
  /\ iState[i] = "waiting"
  /\ iState' = [iState EXCEPT ![i] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vc |-> i]}
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpCPrepared>>

(***********************************************************************)
(* Voucher issuer i spontaneously decides to abort.                      *)
(***********************************************************************)
IChooseToAbort(i) ==
  /\ iState[i] = "waiting"
  /\ iState' = [iState EXCEPT ![i] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpCPrepared, msgs>>

(***********************************************************************)
(* Voucher issuer i is told by the VTP to Cancel.                        *)
(***********************************************************************)
IRcvCancelMsg(i) ==
  /\ iState[i] = "prepared"
  /\ [type |-> "Cancel"] \in msgs
  /\ iState' = [iState EXCEPT ![i] = "cancelled"]
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpCPrepared, msgs>>

(***********************************************************************)
(* Voucher issuer i is told by the VTP to abort.                         *)
(***********************************************************************)
IRcvAbortMsg(i) ==
  /\ iState[i] \in {"waiting", "prepared"}
  /\ [type |-> "Abort"] \in msgs
  /\ iState' = [iState EXCEPT ![i] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpCPrepared, msgs>>

VTPNext ==
  \/ \E h \in H, i \in I : VTPRcvPrepared(h, i)
  \/ \E v \in V : VTPCancel(v) \/ VTPAbort(v)
  \/ \E h \in H : HPrepare(h) \/ HChooseToAbort(h)
                  \/ HRcvCancelMsg(h) \/ HRcvAbortMsg(h)
  \/ \E i \in I : IPrepare(i) \/ IChooseToAbort(i)
                  \/ IRcvCancelMsg(i) \/ IRcvAbortMsg(i)

(***********************************************************************)
(* A state predicate asserting that a H and an I have not reached        *)
(* conflicting decisions. It is an invariant of the specification.       *)
(***********************************************************************)
VTPConsistent ==
  \A h \in H, i \in I :
    /\ ~ /\ hState[h] = "cancelled"
         /\ iState[i] = "aborted"
    /\ ~ /\ hState[h] = "aborted"
         /\ iState[i] = "cancelled"

(***********************************************************************)
(* The complete spec of the a Voucher Cancel using Two-Phase Commit      *)
(* protocol.                                                             *)
(***********************************************************************)
VTPVars == <<vState, vlcState, hState, iState, vtpState, vtpCPrepared, msgs>>

VTPSpec == VTPInit /\ [][VTPNext]_VTPVars

(***********************************************************************)
(* This theorem asserts the truth of the temporal formula whose meaning  *)
(* is that the state predicate VTPTypeOK /\ VTPConsistent is an          *)
(* invariant of the specification VTPSpec.                              *)
(***********************************************************************)
THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

(***************************************************************************)
(* We now assert that the Voucher Cancel specification implements the     *)
(* Voucher Life Cycle specification of a voucher mentioned in module       *)
(* VoucherLifeCycle. The following statement imports all the definitions   *)
(* from module VoucherLifeCycle into the current module.                   *)
(***************************************************************************)
VLC == INSTANCE VoucherLifeCycle

(***********************************************************************)
(* This theorem asserts that the specification VTPSpec of the Two-Phase  *)
(* Commit protocol implements the specification VSpec of the             *)
(* Voucher life cycle specification.                                     *)
(***********************************************************************)
THEOREM VTPSpec => VLC!VSpec

(***************************************************************************)
(* Modification History                                                    *)
(* Last modified Tue Jun 12 13:03:21 IST 2018 by Fox                       *)
(* Created Fri Mar 16 17:45:37 SGT 2018 by Fox                             *)
(***************************************************************************)
====
