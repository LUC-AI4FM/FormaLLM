---- MODULE KVsnap ----
(***************************************************************************)
(* Pluscal algorithm for a simple key-value store with snapshot isolation. *)
(* This version has atomic updates of store and missed sets of txns.       *)
(*                                                                         *)
(* Instantiating ClientCentric enables us to check transaction isolation   *)
(* guarantees this model satisfies                                         *)
(* https://muratbuffalo.blogspot.com/2022/07/automated-validation-of-state-based.html *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  Key,    \* The set of all keys.
  TxId,   \* The set of all transaction IDs.
  NoVal   \* NoVal, which all keys are initialized with.

(***************************************************************************)
(* For instantiating the ClientCentric module.                             *)
(***************************************************************************)
CC == INSTANCE ClientCentric WITH Keys <- Key, Values <- TxId \cup {NoVal}, TxId <- TxId

rOp(k, v) == [op |-> "read", key |-> k, value |-> v]
wOp(k, v) == [op |-> "write", key |-> k, value |-> v]

RECURSIVE SetToSeqHelper(_, _)
SetToSeqHelper(S, acc) ==
  IF S = {} THEN acc
  ELSE LET x == CHOOSE x \in S : TRUE
       IN SetToSeqHelper(S \ {x}, Append(acc, x))

SetToSeq(S) == SetToSeqHelper(S, << >>)

(***************************************************************************
--algorithm KVsnap {
  variables
    store = [k \in Key |-> NoVal],   \* A data store mapping keys to values
    tx = {},                          \* The set of open snapshot transactions
    missed = [t \in TxId |-> {}];     \* The set of writes invisible to each tx

  fair process (t \in TxId)
    variables
      snapshotStore = [k \in Key |-> NoVal],
      read_keys = {},
      write_keys = {},
      ops = << >>;
  {
    START: tx := tx \union {self};
           snapshotStore := store;
           with (rk \in SUBSET Key \ {{}}; wk \in SUBSET Key \ {{}}) {
             read_keys := rk;
             write_keys := wk;
           };
    READ:  ops := ops \o SetToSeq({rOp(k, snapshotStore[k]) : k \in read_keys});
    UPDATE: snapshotStore := [k \in Key |-> IF k \in write_keys THEN self ELSE snapshotStore[k]];
    COMMIT: if (missed[self] \intersect write_keys = {}) {
              tx := tx \ {self};
              missed := [o \in TxId |-> IF o \in tx THEN missed[o] \union write_keys ELSE missed[o]];
              store := [k \in Key |-> IF k \in write_keys THEN snapshotStore[k] ELSE store[k]];
              ops := ops \o SetToSeq({wOp(k, self) : k \in write_keys});
            }
  }
}
 ***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES store, tx, missed, snapshotStore, read_keys, write_keys, ops, pc

vars == << store, tx, missed, snapshotStore, read_keys, write_keys, ops, pc >>

ProcSet == TxId

Init ==
  /\ store = [k \in Key |-> NoVal]
  /\ tx = {}
  /\ missed = [t \in TxId |-> {}]
  /\ snapshotStore = [self \in ProcSet |-> [k \in Key |-> NoVal]]
  /\ read_keys = [self \in ProcSet |-> {}]
  /\ write_keys = [self \in ProcSet |-> {}]
  /\ ops = [self \in ProcSet |-> << >>]
  /\ pc = [self \in ProcSet |-> "START"]

START(self) ==
  /\ pc[self] = "START"
  /\ tx' = tx \union {self}
  /\ snapshotStore' = [snapshotStore EXCEPT ![self] = store]
  /\ \E rk \in SUBSET Key \ {{}} : \E wk \in SUBSET Key \ {{}} :
       /\ read_keys' = [read_keys EXCEPT ![self] = rk]
       /\ write_keys' = [write_keys EXCEPT ![self] = wk]
  /\ pc' = [pc EXCEPT ![self] = "READ"]
  /\ UNCHANGED <<store, missed, ops>>

READ(self) ==
  /\ pc[self] = "READ"
  /\ ops' = [ops EXCEPT ![self] =
              @ \o SetToSeq({rOp(k, snapshotStore[self][k]) : k \in read_keys[self]})]
  /\ pc' = [pc EXCEPT ![self] = "UPDATE"]
  /\ UNCHANGED <<store, tx, missed, snapshotStore, read_keys, write_keys>>

UPDATE(self) ==
  /\ pc[self] = "UPDATE"
  /\ snapshotStore' = [snapshotStore EXCEPT ![self] =
                         [k \in Key |-> IF k \in write_keys[self] THEN self ELSE snapshotStore[self][k]]]
  /\ pc' = [pc EXCEPT ![self] = "COMMIT"]
  /\ UNCHANGED <<store, tx, missed, read_keys, write_keys, ops>>

COMMIT(self) ==
  /\ pc[self] = "COMMIT"
  /\ IF missed[self] \intersect write_keys[self] = {}
       THEN /\ tx' = tx \ {self}
            /\ missed' = [o \in TxId |->
                            IF o \in tx' THEN missed[o] \union write_keys[self] ELSE missed[o]]
            /\ store' = [k \in Key |-> IF k \in write_keys[self]
                                          THEN snapshotStore[self][k]
                                          ELSE store[k]]
            /\ ops' = [ops EXCEPT ![self] =
                        @ \o SetToSeq({wOp(k, self) : k \in write_keys[self]})]
       ELSE UNCHANGED <<store, tx, missed, ops>>
  /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED <<snapshotStore, read_keys, write_keys>>

t(self) == START(self) \/ READ(self) \/ UPDATE(self) \/ COMMIT(self)

Next == (\E self \in TxId : t(self))
        \/ (\A self \in ProcSet : pc[self] = "Done" /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in TxId : WF_vars(t(self))
\* END TRANSLATION

(***************************************************************************)
(* Type invariant.                                                         *)
(***************************************************************************)
TypeOK ==
  /\ store \in [Key -> TxId \cup {NoVal}]
  /\ tx \subseteq TxId
  /\ missed \in [TxId -> SUBSET Key]
  /\ pc \in [ProcSet -> {"START", "READ", "UPDATE", "COMMIT", "Done"}]

(***************************************************************************)
(* Snapshot isolation invariant.                                           *)
(***************************************************************************)
SnapshotIsolation ==
  CC!SnapshotIsolation([k \in Key |-> NoVal],
                       { [id |-> t, ops |-> ops[t]] : t \in {tt \in TxId : pc[tt] = "Done"} })

(***************************************************************************)
(* Serializability would not be satisfied due to write-skew.               *)
(***************************************************************************)
Serializability ==
  CC!Serializability([k \in Key |-> NoVal],
                     { [id |-> t, ops |-> ops[t]] : t \in {tt \in TxId : pc[tt] = "Done"} })

====
