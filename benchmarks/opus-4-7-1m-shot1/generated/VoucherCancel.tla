---- MODULE VoucherCancel ----
(***************************************************************************)
(* Copyright (c) 2018, Backyard Innovations Pte. Ltd., Singapore.          *)
(* Released under the terms of the Apache License 2.0                      *)
(*                                                                         *)
(* This specification describes the cancellation of Voucher between an     *)
(* Issuer and a Holder. It is implemented over the Two-Phase Commit        *)
(* protocol, in which a Voucher Transaction Provider (VTP) coordinates the *)
(* Voucher Issuers (Is) to cancel vouchers (Vs) to Voucher Holders (Hs).   *)
(***************************************************************************)
CONSTANTS
  V,   \* The set of Vouchers
  H,   \* The set of Voucher Holders
  I    \* The set of Voucher Issuers

VARIABLES
  vState,        \* vState[v] is the state of voucher v.
  vlcState,      \* vlcState[v] is the state of the voucher life cycle.
  hState,        \* hState[h] is the state of voucher holder h.
  iState,        \* iState[i] is the state of voucher issuer i.
  vtpState,      \* The state of the voucher transaction provider.
  vtpCPrepared,  \* The set of Hs and Is that have sent "Prepared".
  msgs

(***************************************************************************)
(* The set of all possible messages.                                       *)
(***************************************************************************)
Messages ==
       [type : {"Prepared"}, vh : H]
  \cup [type : {"Prepared"}, vc : I]
  \cup [type : {"Cancel", "Abort"}]

(***************************************************************************)
(* The type-correctness invariant.                                         *)
(***************************************************************************)
VTPTypeOK ==
  /\ vState    \in [V -> {"valid", "cancelled"}]
  /\ vlcState  \in [V -> {"working", "prepared", "cancelled", "aborted"}]
  /\ hState    \in [H -> {"holding", "prepared", "cancelled", "aborted"}]
  /\ iState    \in [I -> {"issued",  "prepared", "cancelled", "aborted"}]
  /\ vtpState  \in {"init", "done"}
  /\ vtpCPrepared \subseteq (H \cup I)
  /\ msgs \subseteq Messages

(***************************************************************************)
(* The initial predicate.                                                  *)
(***************************************************************************)
VTPInit ==
  /\ vState    = [v \in V |-> "valid"]
  /\ vlcState  = [v \in V |-> "working"]
  /\ hState    = [h \in H |-> "holding"]
  /\ iState    = [i \in I |-> "issued"]
  /\ vtpState  = "init"
  /\ vtpCPrepared = {}
  /\ msgs = {}

VTPRcvPrepared(h, i) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vh |-> h] \in msgs
  /\ [type |-> "Prepared", vc |-> i] \in msgs
  /\ vtpCPrepared' = vtpCPrepared \cup {h, i}
  /\ UNCHANGED <<vState, vlcState, hState, iState, vtpState, msgs>>

VTPCancel ==
  /\ vtpState = "init"
  /\ vtpCPrepared = (H \cup I)
  /\ vtpState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Cancel"]}
  /\ UNCHANGED <<vState, vlcState, hState, iState, vtpCPrepared>>

VTPAbort ==
  /\ vtpState = "init"
  /\ vtpState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<vState, vlcState, hState, iState, vtpCPrepared>>

HPrepare(h) ==
  /\ hState[h] = "holding"
  /\ hState' = [hState EXCEPT ![h] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
  /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpCPrepared>>

HChooseToAbort(h) ==
  /\ hState[h] = "holding"
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpCPrepared, msgs>>

HRcvCancelMsg(h) ==
  /\ hState[h] = "prepared"
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
  /\ msgs' = msgs \cup {[type |-> "Prepared", vc |-> i]}
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpCPrepared>>

IChooseToAbort(i) ==
  /\ iState[i] = "issued"
  /\ iState' = [iState EXCEPT ![i] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpCPrepared, msgs>>

IRcvCancelMsg(i) ==
  /\ iState[i] = "prepared"
  /\ [type |-> "Cancel"] \in msgs
  /\ iState' = [iState EXCEPT ![i] = "cancelled"]
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpCPrepared, msgs>>

IRcvAbortMsg(i) ==
  /\ [type |-> "Abort"] \in msgs
  /\ iState' = [iState EXCEPT ![i] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpCPrepared, msgs>>

VTPNext ==
  \/ VTPCancel \/ VTPAbort
  \/ \E h \in H, i \in I : VTPRcvPrepared(h, i)
  \/ \E h \in H :
       HPrepare(h) \/ HChooseToAbort(h) \/ HRcvCancelMsg(h) \/ HRcvAbortMsg(h)
  \/ \E i \in I :
       IPrepare(i) \/ IChooseToAbort(i) \/ IRcvCancelMsg(i) \/ IRcvAbortMsg(i)

(***************************************************************************)
(* A state predicate asserting that a H and an I have not reached          *)
(* conflicting decisions. It is an invariant of the specification.         *)
(***************************************************************************)
VTPConsistent ==
  \A h \in H, i \in I :
    ~ /\ hState[h] = "cancelled"
      /\ iState[i] = "aborted"

(***************************************************************************)
(* The complete spec of a Voucher Cancel using Two-Phase Commit protocol.  *)
(***************************************************************************)
VTPSpec ==
  VTPInit /\ [][VTPNext]_<<vState, vlcState, hState, iState, vtpState, vtpCPrepared, msgs>>

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

VSpec == INSTANCE VoucherLifeCycle WITH V <- V, vState <- vState, vlcState <- vlcState

THEOREM VTPSpec => VSpec!VSpec

====
