---- MODULE KVsnap ----
\* PlusCal-translated key-value store with snapshot isolation. Atomic
\* updates of store and per-txn missed sets. Snapshot isolation does not
\* imply serializability (write-skew).

EXTENDS Integers, Sequences, FiniteSets, Util, TLC

CONSTANTS Key, TxId

NoVal == CHOOSE v : v \notin TxId

\* Operations for the ClientCentric isolation interface.
rOp(k, v) == [op |-> "read",  key |-> k, val |-> v]
wOp(k, v) == [op |-> "write", key |-> k, val |-> v]

(***************************************************************************
--algorithm KVsnap {
    variables
        store = [k \in Key |-> NoVal],
        tx = {},
        missed = [t \in TxId |-> {}];

    fair process (t \in TxId)
        variables
            snapshotStore = [k \in Key |-> NoVal],
            read_keys = {},
            write_keys = {},
            ops = << >>;
    {
        START:
            tx := tx \cup {self};
            snapshotStore := store;
            with (rk \in SUBSET Key \ {{}}; wk \in SUBSET Key \ {{}}) {
                read_keys := rk;
                write_keys := wk;
            };
        READ:
            ops := ops \o SetToSeq({rOp(k, snapshotStore[k]) : k \in read_keys});
        UPDATE:
            snapshotStore := [k \in Key |->
                                IF k \in write_keys THEN self
                                ELSE snapshotStore[k]];
        COMMIT:
            if (missed[self] \cap write_keys = {}) {
                tx := tx \ {self};
                missed := [o \in TxId |->
                             IF o \in tx THEN missed[o] \cup write_keys
                             ELSE missed[o]];
                store := [k \in Key |->
                            IF k \in write_keys THEN snapshotStore[k]
                            ELSE store[k]];
                ops := ops \o SetToSeq({wOp(k, self) : k \in write_keys});
            }
    }
}
 ***************************************************************************)

\* Global variables.
VARIABLES store, tx, missed,
\* Process t.
          snapshotStore, read_keys, write_keys, ops, pc

ProcSet == TxId

vars == <<store, tx, missed, snapshotStore, read_keys, write_keys, ops, pc>>

Init ==
    /\ store = [k \in Key |-> NoVal]
    /\ tx = {}
    /\ missed = [t \in TxId |-> {}]
    /\ snapshotStore = [t \in TxId |-> [k \in Key |-> NoVal]]
    /\ read_keys = [t \in TxId |-> {}]
    /\ write_keys = [t \in TxId |-> {}]
    /\ ops = [t \in TxId |-> << >>]
    /\ pc = [self \in ProcSet |-> "START"]

START(self) ==
    /\ pc[self] = "START"
    /\ tx' = tx \cup {self}
    /\ snapshotStore' = [snapshotStore EXCEPT ![self] = store]
    /\ \E rk \in SUBSET Key \ {{}}, wk \in SUBSET Key \ {{}} :
         /\ read_keys' = [read_keys EXCEPT ![self] = rk]
         /\ write_keys' = [write_keys EXCEPT ![self] = wk]
    /\ pc' = [pc EXCEPT ![self] = "READ"]
    /\ UNCHANGED <<store, missed, ops>>

READ(self) ==
    /\ pc[self] = "READ"
    /\ ops' = [ops EXCEPT ![self] =
                 @ \o SetToSeq({rOp(k, snapshotStore[self][k])
                                : k \in read_keys[self]})]
    /\ pc' = [pc EXCEPT ![self] = "UPDATE"]
    /\ UNCHANGED <<store, tx, missed, snapshotStore, read_keys, write_keys>>

UPDATE(self) ==
    /\ pc[self] = "UPDATE"
    /\ snapshotStore' = [snapshotStore EXCEPT
         ![self] = [k \in Key |->
                      IF k \in write_keys[self] THEN self
                      ELSE snapshotStore[self][k]]]
    /\ pc' = [pc EXCEPT ![self] = "COMMIT"]
    /\ UNCHANGED <<store, tx, missed, read_keys, write_keys, ops>>

COMMIT(self) ==
    /\ pc[self] = "COMMIT"
    /\ IF missed[self] \cap write_keys[self] = {}
       THEN /\ tx' = tx \ {self}
            /\ missed' = [o \in TxId |->
                            IF o \in tx' THEN missed[o] \cup write_keys[self]
                            ELSE missed[o]]
            /\ store' = [k \in Key |->
                           IF k \in write_keys[self] THEN snapshotStore[self][k]
                           ELSE store[k]]
            /\ ops' = [ops EXCEPT ![self] =
                         @ \o SetToSeq({wOp(k, self) : k \in write_keys[self]})]
       ELSE UNCHANGED <<tx, missed, store, ops>>
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED <<snapshotStore, read_keys, write_keys>>

t(self) == START(self) \/ READ(self) \/ UPDATE(self) \/ COMMIT(self)

\* Allow infinite stuttering to prevent deadlock on termination.
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet : t(self)) \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ProcSet : WF_vars(t(self))

\* Type invariant.
TypeOK ==
    /\ store \in [Key -> TxId \cup {NoVal}]
    /\ tx \subseteq TxId
    /\ missed \in [TxId -> SUBSET Key]
    /\ snapshotStore \in [TxId -> [Key -> TxId \cup {NoVal}]]
    /\ pc \in [TxId -> {"START", "READ", "UPDATE", "COMMIT", "Done"}]

\* Snapshot-isolation invariant: committed transactions never read
\* values their concurrent writers committed.
SnapshotIsolation ==
    \A s, t \in TxId :
        (s # t /\ pc[s] = "Done" /\ pc[t] = "Done")
        => (write_keys[s] \cap read_keys[t] = {})
            \/ ~ (missed[t] \cap write_keys[t] = {})

\* Reference instance for client-centric checks (ClientCentric is in val,
\* so the INSTANCE is left as a stub here).

====
