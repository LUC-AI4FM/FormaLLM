---- MODULE VoucherTransfer ----
\* Copyright (c) 2018, Backyard Innovations Pte. Ltd., Singapore.
\* Released under the terms of the Apache License 2.0
\* Authors: Santhosh Raju, Cherry G. Mathew, Fransisca Andriani.
\*
\* The description is based on the "Transfer" operation mentioned in RFC
\* 3506. This specification describes the transfer of Voucher between two
\* Holders. It is implemented over the Two-Phase Commit protocol, in which a
\* Voucher Transaction Provider (VTP) coordinates the "Source" Voucher
\* Holders (SHs) to trade vouchers (Vs) to "Destination" Voucher Holders
\* (DHs) described in the VoucherLifeCycle specification module. SHs and DHs
\* spontaneously issue "Prepared" messages; "Prepare" messages from the VTP
\* are ignored. For simplicity, an SH or DH that decides to abort does so
\* silently and the VTP eventually aborts spontaneously.

CONSTANTS
  V,   \* The set of Vouchers
  SH,  \* The set of "Source" Voucher Holders
  DH   \* The set of "Destination" Voucher Holders

VARIABLES
  vState,        \* vState[v]: state of voucher v
  vlcState,      \* vlcState[v]: state of the voucher life-cycle machine
  shState,       \* shState[sh]: state of source voucher holder sh
  dhState,       \* dhState[dh]: state of destination voucher holder dh
  vtpState,      \* state of the Voucher Transaction Provider
  vtpTPrepared,  \* set of SHs/DHs from which VTP has received "Prepared"
  msgs

vars == << vState, vlcState, shState, dhState, vtpState, vtpTPrepared, msgs >>

\* The set of all possible messages.
Message ==
       [type : {"Prepared"}, vsh : SH]
  \cup [type : {"Prepared"}, vdh : DH]
  \cup [type : {"Transfer", "Abort"}]

\* The type-correctness invariant.
VTPTypeOK ==
  /\ vState        \in [V  -> {"valid", "transferred", "cancelled"}]
  /\ vlcState      \in [V  -> {"init", "working", "transferred", "aborted"}]
  /\ shState       \in [SH -> {"holding", "prepared", "transferred", "aborted"}]
  /\ dhState       \in [DH -> {"waiting", "prepared", "transferred", "aborted"}]
  /\ vtpState      \in {"init", "transferred", "aborted"}
  /\ vtpTPrepared  \subseteq (SH \cup DH)
  /\ msgs          \subseteq Message

\* The initial predicate.
VTPInit ==
  /\ vState       = [v  \in V  |-> "valid"]
  /\ vlcState     = [v  \in V  |-> "init"]
  /\ shState      = [sh \in SH |-> "holding"]
  /\ dhState      = [dh \in DH |-> "waiting"]
  /\ vtpState     = "init"
  /\ vtpTPrepared = {}
  /\ msgs         = {}

\* ----- VTP actions -----

\* The VTP receives a "Prepared" message from SH sh.
VTPRcvPreparedSH(sh) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vsh |-> sh] \in msgs
  /\ vtpTPrepared' = vtpTPrepared \cup {sh}
  /\ UNCHANGED << vState, vlcState, shState, dhState, vtpState, msgs >>

\* The VTP receives a "Prepared" message from DH dh.
VTPRcvPreparedDH(dh) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vdh |-> dh] \in msgs
  /\ vtpTPrepared' = vtpTPrepared \cup {dh}
  /\ UNCHANGED << vState, vlcState, shState, dhState, vtpState, msgs >>

\* The VTP transfers the voucher.
VTPTransfer ==
  /\ vtpState = "init"
  /\ vtpTPrepared = SH \cup DH
  /\ vtpState' = "transferred"
  /\ msgs' = msgs \cup {[type |-> "Transfer"]}
  /\ UNCHANGED << vState, vlcState, shState, dhState, vtpTPrepared >>

\* The VTP spontaneously aborts the transaction.
VTPAbort ==
  /\ vtpState = "init"
  /\ vtpState' = "aborted"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED << vState, vlcState, shState, dhState, vtpTPrepared >>

\* ----- SH actions -----

SHPrepare(sh) ==
  /\ shState[sh] = "holding"
  /\ shState' = [shState EXCEPT ![sh] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vsh |-> sh]}
  /\ UNCHANGED << vState, vlcState, dhState, vtpState, vtpTPrepared >>

SHChooseToAbort(sh) ==
  /\ shState[sh] = "holding"
  /\ shState' = [shState EXCEPT ![sh] = "aborted"]
  /\ UNCHANGED << vState, vlcState, dhState, vtpState, vtpTPrepared, msgs >>

SHRcvTransferMsg(sh) ==
  /\ [type |-> "Transfer"] \in msgs
  /\ shState' = [shState EXCEPT ![sh] = "transferred"]
  /\ UNCHANGED << vState, vlcState, dhState, vtpState, vtpTPrepared, msgs >>

SHRcvAbortMsg(sh) ==
  /\ [type |-> "Abort"] \in msgs
  /\ shState' = [shState EXCEPT ![sh] = "aborted"]
  /\ UNCHANGED << vState, vlcState, dhState, vtpState, vtpTPrepared, msgs >>

\* ----- DH actions -----

DHPrepare(dh) ==
  /\ dhState[dh] = "waiting"
  /\ dhState' = [dhState EXCEPT ![dh] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vdh |-> dh]}
  /\ UNCHANGED << vState, vlcState, shState, vtpState, vtpTPrepared >>

DHChooseToAbort(dh) ==
  /\ dhState[dh] = "waiting"
  /\ dhState' = [dhState EXCEPT ![dh] = "aborted"]
  /\ UNCHANGED << vState, vlcState, shState, vtpState, vtpTPrepared, msgs >>

DHRcvTransferMsg(dh) ==
  /\ [type |-> "Transfer"] \in msgs
  /\ dhState' = [dhState EXCEPT ![dh] = "transferred"]
  /\ UNCHANGED << vState, vlcState, shState, vtpState, vtpTPrepared, msgs >>

DHRcvAbortMsg(dh) ==
  /\ [type |-> "Abort"] \in msgs
  /\ dhState' = [dhState EXCEPT ![dh] = "aborted"]
  /\ UNCHANGED << vState, vlcState, shState, vtpState, vtpTPrepared, msgs >>

\* Consistency: no SH/DH pair reach conflicting decisions.
VTPConsistent ==
  \A sh \in SH, dh \in DH :
     ~ ( (shState[sh] = "transferred" /\ dhState[dh] = "aborted")
       \/ (shState[sh] = "aborted"    /\ dhState[dh] = "transferred") )

VTPNext ==
  \/ VTPTransfer \/ VTPAbort
  \/ \E sh \in SH :
       \/ VTPRcvPreparedSH(sh) \/ SHPrepare(sh) \/ SHChooseToAbort(sh)
       \/ SHRcvTransferMsg(sh) \/ SHRcvAbortMsg(sh)
  \/ \E dh \in DH :
       \/ VTPRcvPreparedDH(dh) \/ DHPrepare(dh) \/ DHChooseToAbort(dh)
       \/ DHRcvTransferMsg(dh) \/ DHRcvAbortMsg(dh)

VTPSpec == VTPInit /\ [][VTPNext]_vars

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

\* Refinement: this spec implements VoucherLifeCycle's VSpec.
VLC == INSTANCE VoucherLifeCycle

THEOREM VTPSpec => VLC!VSpec

====
