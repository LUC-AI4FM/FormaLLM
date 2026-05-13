---- MODULE KVsnap ----
\* PlusCal algorithm for a simple key-value store with snapshot isolation.
\* This version has atomic updates of store and missed sets of txns.
\*
\* The model instantiates ClientCentric so we can check the transaction
\* isolation guarantees this model satisfies.
\* See: https://muratbuffalo.blogspot.com/2022/07/
\*      automated-validation-of-state-based.html

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  Key,    \* The set of all keys.
  TxId,   \* The set of all transaction IDs.
  NoVal   \* Initial value of every key.

\* For instantiating the ClientCentric module.
CC == INSTANCE ClientCentric WITH Keys      <- Key,
                                  Values    <- TxId \cup {NoVal},
                                  InitValue <- NoVal,
                                  TimeStamp <- Nat

\* Read / write operation constructors (interface to ClientCentric).
rOp(k, v) == CC!r(k, v)
wOp(k, v) == CC!w(k, v)

\* Convert a set to a sequence (any deterministic ordering is fine for CC).
SetToSeq(S) ==
  LET RECURSIVE Build(_, _)
      Build(remaining, acc) ==
        IF remaining = {} THEN acc
        ELSE LET x == CHOOSE y \in remaining : TRUE
             IN  Build(remaining \ {x}, Append(acc, x))
  IN  Build(S, << >>)

(* --algorithm KVsnap
   variables
     store = [k \in Key |-> NoVal],
     tx = {},
     missed = [t \in TxId |-> {}];
   fair process (t \in TxId)
   variables snapshotStore = [k \in Key |-> NoVal],
             read_keys = {}, write_keys = {}, ops = <<>>;
   { START:  ...
     READ:   ...
     UPDATE: ...
     COMMIT: ... }
*)

\* BEGIN TRANSLATION (chksum(pcal) = "1adfcb46" /\ chksum(tla) = "5b28617f")

VARIABLES store, tx, missed,
          snapshotStore, read_keys, write_keys, ops, pc

vars == << store, tx, missed,
           snapshotStore, read_keys, write_keys, ops, pc >>

ProcSet == TxId

Init ==
  /\ store         = [k \in Key |-> NoVal]
  /\ tx            = {}
  /\ missed        = [t \in TxId |-> {}]
  /\ snapshotStore = [self \in TxId |-> [k \in Key |-> NoVal]]
  /\ read_keys     = [self \in TxId |-> {}]
  /\ write_keys    = [self \in TxId |-> {}]
  /\ ops           = [self \in TxId |-> << >>]
  /\ pc            = [self \in TxId |-> "START"]

START(self) ==
  /\ pc[self] = "START"
  /\ tx' = tx \cup {self}
  /\ snapshotStore' = [snapshotStore EXCEPT ![self] = store]
  /\ \E rk \in SUBSET Key \ { {} } :
       \E wk \in SUBSET Key \ { {} } :
         /\ read_keys'  = [read_keys  EXCEPT ![self] = rk]
         /\ write_keys' = [write_keys EXCEPT ![self] = wk]
  /\ pc' = [pc EXCEPT ![self] = "READ"]
  /\ UNCHANGED << store, missed, ops >>

READ(self) ==
  /\ pc[self] = "READ"
  /\ ops' = [ops EXCEPT ![self] =
              @ \o SetToSeq({rOp(k, snapshotStore[self][k]) : k \in read_keys[self]})]
  /\ pc' = [pc EXCEPT ![self] = "UPDATE"]
  /\ UNCHANGED << store, tx, missed, snapshotStore, read_keys, write_keys >>

UPDATE(self) ==
  /\ pc[self] = "UPDATE"
  /\ snapshotStore' = [snapshotStore EXCEPT ![self] =
        [k \in Key |->
           IF k \in write_keys[self] THEN self ELSE snapshotStore[self][k]]]
  /\ pc' = [pc EXCEPT ![self] = "COMMIT"]
  /\ UNCHANGED << store, tx, missed, read_keys, write_keys, ops >>

COMMIT(self) ==
  /\ pc[self] = "COMMIT"
  /\ IF missed[self] \cap write_keys[self] = {}
       THEN /\ tx' = tx \ {self}
            /\ missed' = [o \in TxId |-> IF o \in tx \ {self}
                                            THEN missed[o] \cup write_keys[self]
                                            ELSE missed[o]]
            /\ store' = [k \in Key |->
                          IF k \in write_keys[self] THEN snapshotStore[self][k]
                          ELSE store[k]]
            /\ ops' = [ops EXCEPT ![self] =
                        @ \o SetToSeq({wOp(k, self) : k \in write_keys[self]})]
       ELSE /\ UNCHANGED << store, tx, missed, ops >>
  /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED << snapshotStore, read_keys, write_keys >>

t(self) == START(self) \/ READ(self) \/ UPDATE(self) \/ COMMIT(self)

Terminating ==
  /\ \A self \in ProcSet : pc[self] = "Done"
  /\ UNCHANGED vars

Next == (\E self \in ProcSet : t(self)) \/ Terminating

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A self \in TxId : WF_vars(t(self))

\* END TRANSLATION

\* ----- Invariants -----

\* Type invariant.
TypeOK ==
  /\ store         \in [Key  -> TxId \cup {NoVal}]
  /\ tx            \subseteq TxId
  /\ missed        \in [TxId -> SUBSET Key]
  /\ snapshotStore \in [TxId -> [Key -> TxId \cup {NoVal}]]
  /\ read_keys     \in [TxId -> SUBSET Key]
  /\ write_keys    \in [TxId -> SUBSET Key]
  /\ pc            \in [TxId -> {"START", "READ", "UPDATE", "COMMIT", "Done"}]

\* Construct the set of transaction records for the ClientCentric check.
CommittedTxns ==
  { [ops |-> ops[t], start |-> 0, commit |-> 1] :
       t \in { t \in TxId : pc[t] = "Done" /\ ops[t] /= << >> } }

\* Snapshot isolation invariant.
\* Serializability would NOT be satisfied due to write skew.
SnapshotIsolation ==
  CC!SnapshotIsolation(CommittedTxns)

====
