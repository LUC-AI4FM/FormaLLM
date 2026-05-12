---- MODULE VoucherCancel ----
\* Copyright (c) 2018, Backyard Innovations Pte. Ltd., Singapore.
\* Released under the terms of the Apache License 2.0.
\* Authors: Santhosh Raju, Cherry G. Mathew, Fransisca Andriani.
\*
\* This specification describes the cancellation of a Voucher between an
\* Issuer and a Holder. It is implemented over the Two-Phase Commit
\* protocol, in which a Voucher Transaction Provider (VTP) coordinates the
\* Voucher Issuers (Is) to cancel vouchers (Vs) held by Voucher Holders (Hs)
\* as described in the VoucherLifeCycle specification module. Hs and Is
\* spontaneously issue "Prepared" messages; we ignore the "Prepare" messages
\* the VTP would send. A H or I that decides to abort does so silently and
\* the VTP eventually aborts spontaneously.
\*
\* Note: This operation is an addendum to RFC 3506; it is not in the RFC.

CONSTANTS
  V,   \* The set of Vouchers
  H,   \* The set of Voucher Holders
  I    \* The set of Voucher Issuers

VARIABLES
  vState,        \* vState[v]: state of voucher v
  vlcState,      \* vlcState[v]: state of the voucher life-cycle machine
  hState,        \* hState[h]: state of voucher holder h
  iState,        \* iState[i]: state of voucher issuer i
  vtpState,      \* state of the Voucher Transaction Provider
  vtpCPrepared,  \* set of Hs/Is from which VTP has received "Prepared"
  msgs

vars == << vState, vlcState, hState, iState, vtpState, vtpCPrepared, msgs >>

\* The set of all possible messages.
Message ==
       [type : {"Prepared"}, vh : H]
  \cup [type : {"Prepared"}, vc : I]
  \cup [type : {"Cancel", "Abort"}]

\* The type-correctness invariant.
VTPTypeOK ==
  /\ vState        \in [V -> {"valid", "cancelled"}]
  /\ vlcState      \in [V -> {"init", "working", "cancelled", "aborted"}]
  /\ hState        \in [H -> {"holding", "prepared", "cancelled", "aborted"}]
  /\ iState        \in [I -> {"issued", "prepared", "cancelled", "aborted"}]
  /\ vtpState      \in {"init", "cancelled", "aborted"}
  /\ vtpCPrepared  \subseteq (H \cup I)
  /\ msgs          \subseteq Message

\* The initial predicate.
VTPInit ==
  /\ vState        = [v \in V |-> "valid"]
  /\ vlcState      = [v \in V |-> "init"]
  /\ hState        = [h \in H |-> "holding"]
  /\ iState        = [i \in I |-> "issued"]
  /\ vtpState      = "init"
  /\ vtpCPrepared  = {}
  /\ msgs          = {}

\* ----- VTP actions -----

VTPRcvPreparedH(h) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vh |-> h] \in msgs
  /\ vtpCPrepared' = vtpCPrepared \cup {h}
  /\ UNCHANGED << vState, vlcState, hState, iState, vtpState, msgs >>

VTPRcvPreparedI(i) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vc |-> i] \in msgs
  /\ vtpCPrepared' = vtpCPrepared \cup {i}
  /\ UNCHANGED << vState, vlcState, hState, iState, vtpState, msgs >>

VTPCancel ==
  /\ vtpState = "init"
  /\ vtpCPrepared = H \cup I
  /\ vtpState' = "cancelled"
  /\ msgs' = msgs \cup {[type |-> "Cancel"]}
  /\ UNCHANGED << vState, vlcState, hState, iState, vtpCPrepared >>

VTPAbort ==
  /\ vtpState = "init"
  /\ vtpState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED << vState, vlcState, hState, iState, vtpCPrepared >>

\* ----- Holder actions -----

HPrepare(h) ==
  /\ hState[h] = "holding"
  /\ hState' = [hState EXCEPT ![h] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
  /\ UNCHANGED << vState, vlcState, iState, vtpState, vtpCPrepared >>

HChooseToAbort(h) ==
  /\ hState[h] = "holding"
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED << vState, vlcState, iState, vtpState, vtpCPrepared, msgs >>

HRcvCancelMsg(h) ==
  /\ [type |-> "Cancel"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "cancelled"]
  /\ UNCHANGED << vState, vlcState, iState, vtpState, vtpCPrepared, msgs >>

HRcvAbortMsg(h) ==
  /\ [type |-> "Abort"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED << vState, vlcState, iState, vtpState, vtpCPrepared, msgs >>

\* ----- Issuer actions -----

IPrepare(i) ==
  /\ iState[i] = "issued"
  /\ iState' = [iState EXCEPT ![i] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vc |-> i]}
  /\ UNCHANGED << vState, vlcState, hState, vtpState, vtpCPrepared >>

IChooseToAbort(i) ==
  /\ iState[i] = "issued"
  /\ iState' = [iState EXCEPT ![i] = "aborted"]
  /\ UNCHANGED << vState, vlcState, hState, vtpState, vtpCPrepared, msgs >>

IRcvCancelMsg(i) ==
  /\ [type |-> "Cancel"] \in msgs
  /\ iState' = [iState EXCEPT ![i] = "cancelled"]
  /\ UNCHANGED << vState, vlcState, hState, vtpState, vtpCPrepared, msgs >>

IRcvAbortMsg(i) ==
  /\ [type |-> "Abort"] \in msgs
  /\ iState' = [iState EXCEPT ![i] = "aborted"]
  /\ UNCHANGED << vState, vlcState, hState, vtpState, vtpCPrepared, msgs >>

\* Consistency: no H/I pair reach conflicting decisions.
VTPConsistent ==
  \A h \in H, i \in I :
     ~ ( (hState[h] = "cancelled" /\ iState[i] = "aborted")
       \/ (hState[h] = "aborted"    /\ iState[i] = "cancelled") )

VTPNext ==
  \/ VTPCancel \/ VTPAbort
  \/ \E h \in H :
       \/ VTPRcvPreparedH(h) \/ HPrepare(h) \/ HChooseToAbort(h)
       \/ HRcvCancelMsg(h) \/ HRcvAbortMsg(h)
  \/ \E i \in I :
       \/ VTPRcvPreparedI(i) \/ IPrepare(i) \/ IChooseToAbort(i)
       \/ IRcvCancelMsg(i) \/ IRcvAbortMsg(i)

VTPSpec == VTPInit /\ [][VTPNext]_vars

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

VLC == INSTANCE VoucherLifeCycle

THEOREM VTPSpec => VLC!VSpec

====
