---- MODULE KVsnap ----
(***************************************************************************)
(* PlusCal algorithm for a simple key-value store with snapshot isolation.*)
(* Atomic updates of store and missed sets of txns.                       *)
(*                                                                         *)
(* Instantiating ClientCentric allows checking the transaction isolation  *)
(* guarantees: snapshot isolation. Serializability is NOT satisfied due   *)
(* to write-skew.                                                          *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Key, TxId, NoVal

\* Read and write operations (for the ClientCentric interface).
rOp(k, v) == [op |-> "read", key |-> k, value |-> v]
wOp(k, v) == [op |-> "write", key |-> k, value |-> v]

\* Convert a set to a sequence (any total order is acceptable).
RECURSIVE SetToSeq(_)
SetToSeq(S) ==
    IF S = {} THEN << >>
    ELSE LET x == CHOOSE x \in S : TRUE
         IN <<x>> \o SetToSeq(S \ {x})

VARIABLES
    store,         \* data store mapping keys to values
    tx,            \* set of open snapshot transactions
    missed,        \* missed[t] = writes invisible to transaction t
    snapshotStore, \* snapshotStore[t] = t's local snapshot
    read_keys,     \* read_keys[t] = t's read key set
    write_keys,    \* write_keys[t] = t's write key set
    ops,           \* ops[t] = t's log of reads & writes
    pc             \* program counter for each txn

vars == <<store, tx, missed, snapshotStore, read_keys, write_keys, ops, pc>>

Values == TxId \cup {NoVal}

\* Type invariant.
TypeOK ==
    /\ store \in [Key -> Values]
    /\ tx \subseteq TxId
    /\ missed \in [TxId -> SUBSET Key]
    /\ snapshotStore \in [TxId -> [Key -> Values]]
    /\ read_keys  \in [TxId -> SUBSET Key]
    /\ write_keys \in [TxId -> SUBSET Key]
    /\ ops \in [TxId -> Seq([op : {"read", "write"}, key : Key, value : Values])]
    /\ pc \in [TxId -> {"START", "READ", "UPDATE", "COMMIT", "Done"}]

Init ==
    /\ store = [k \in Key |-> NoVal]
    /\ tx = {}
    /\ missed = [t \in TxId |-> {}]
    /\ snapshotStore = [t \in TxId |-> [k \in Key |-> NoVal]]
    /\ read_keys  = [t \in TxId |-> {}]
    /\ write_keys = [t \in TxId |-> {}]
    /\ ops = [t \in TxId |-> << >>]
    /\ pc = [t \in TxId |-> "START"]

START(self) ==
    /\ pc[self] = "START"
    /\ tx' = tx \cup {self}
    /\ snapshotStore' = [snapshotStore EXCEPT ![self] = store]
    /\ \E rk \in SUBSET Key \ {{}} :
       \E wk \in SUBSET Key \ {{}} :
         /\ read_keys'  = [read_keys  EXCEPT ![self] = rk]
         /\ write_keys' = [write_keys EXCEPT ![self] = wk]
    /\ pc' = [pc EXCEPT ![self] = "READ"]
    /\ UNCHANGED <<store, missed, ops>>

READ(self) ==
    /\ pc[self] = "READ"
    /\ ops' = [ops EXCEPT ![self] = @ \o
                  SetToSeq({ rOp(k, snapshotStore[self][k]) : k \in read_keys[self] })]
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
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ IF missed[self] \cap write_keys[self] = {}
       THEN /\ tx' = tx \ {self}
            /\ missed' = [o \in TxId |->
                            IF o \in tx \ {self} THEN missed[o] \cup write_keys[self]
                            ELSE missed[o]]
            /\ store' = [k \in Key |->
                            IF k \in write_keys[self] THEN snapshotStore[self][k]
                            ELSE store[k]]
            /\ ops' = [ops EXCEPT ![self] = @ \o
                          SetToSeq({ wOp(k, self) : k \in write_keys[self] })]
       ELSE UNCHANGED <<tx, missed, store, ops>>
    /\ UNCHANGED <<snapshotStore, read_keys, write_keys>>

t(self) == START(self) \/ READ(self) \/ UPDATE(self) \/ COMMIT(self)

\* Allow infinite stuttering to prevent deadlock on termination.
Terminating == (\A self \in TxId : pc[self] = "Done") /\ UNCHANGED vars

Next == (\E self \in TxId : t(self)) \/ Terminating

Spec == Init /\ [][Next]_vars /\ \A self \in TxId : WF_vars(t(self))

\* Snapshot Isolation via ClientCentric.
CC == INSTANCE ClientCentric WITH Keys <- Key, Values <- Values, InitValue <- NoVal

SnapshotIsolation ==
    LET committedTxns == { ops[t] : t \in TxId } \ {<< >>}
    IN  CC!SnapshotIsolation(committedTxns)
====
