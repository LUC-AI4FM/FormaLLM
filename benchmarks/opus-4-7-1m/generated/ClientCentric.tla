---- MODULE ClientCentric ----
(***************************************************************************)
(* TLA+ specification of Client Centric Isolation by Crooks et al:         *)
(*   https://dl.acm.org/doi/10.1145/3087801.3087802                        *)
(* Based on work by Tim Soethout et al: Automated Validation of            *)
(* State-Based Client-Centric Isolation with TLA+.                         *)
(*                                                                         *)
(* A database State is a function from Keys to Values. An Operation is a  *)
(* read or write of a key and value. A Transaction is a total order of    *)
(* Operations. An Execution is a sequence of Transactions with their      *)
(* corresponding parent states.                                            *)
(***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Keys, Values, InitValue

ASSUME InitValue \in Values

\* A database state maps keys to values.
State == [Keys -> Values]

\* An operation is a read or a write.
Operation == [op: {"read", "write"}, key: Keys, value: Values]

\* Helpers for constructing operations.
r(k, v) == [op |-> "read",  key |-> k, value |-> v]
w(k, v) == [op |-> "write", key |-> k, value |-> v]

\* A transaction is a sequence of operations.
Transaction == Seq(Operation)

\* The write set of a transaction: keys it updates.
WriteSet(t) == { t[i].key : i \in { j \in DOMAIN t : t[j].op = "write" } }

\* The read set of a transaction.
ReadSet(t) == { t[i].key : i \in { j \in DOMAIN t : t[j].op = "read" } }

\* An ExecutionElem stores parent state and the transaction executed in that state.
ExecutionElem == [parentState: State, transaction: Transaction]

\* The initial system state assigns every key to InitValue.
InitialState == [k \in Keys |-> InitValue]

\* Apply a single operation to a state. Reads do not change state; writes do.
ApplyOp(s, op) == IF op.op = "write" THEN [s EXCEPT ![op.key] = op.value] ELSE s

\* Apply a transaction (sequence of operations) to a state.
RECURSIVE ApplyTxn(_, _)
ApplyTxn(s, t) ==
    IF t = << >> THEN s
    ELSE ApplyTxn(ApplyOp(s, Head(t)), Tail(t))

\* The difference between two states: keys with differing values.
Delta(s1, s2) == { k \in Keys : s1[k] /= s2[k] }

\* NO-CONF_T(s): s and parent state of T differ only outside the write set of T.
NoConf(t, s, sParent) == Delta(s, sParent) \cap WriteSet(t) = {}

\* Set of all permutations of a finite set X (used to enumerate executions).
RECURSIVE PermsOf(_)
PermsOf(X) ==
    IF X = {} THEN { << >> }
    ELSE UNION { { <<x>> \o p : p \in PermsOf(X \ {x}) } : x \in X }

\* Build the sequence of ExecutionElems by folding ApplyTxn over a permutation.
RECURSIVE BuildExec(_, _, _)
BuildExec(state, txns, acc) ==
    IF txns = << >> THEN acc
    ELSE
        LET t == Head(txns) IN
        BuildExec(ApplyTxn(state, t), Tail(txns), Append(acc, [parentState |-> state, transaction |-> t]))

Executions(initialState, transactions) ==
    { BuildExec(initialState, p, << >>) : p \in PermsOf(transactions) }

\* The set of all prior states in an execution, up to (but not including) txn t.
PriorStates(t, execution) ==
    LET idx == CHOOSE i \in DOMAIN execution : execution[i].transaction = t
    IN { execution[j].parentState : j \in 1..idx }

\* Read states for an operation: all prior states whose key matches the read value.
ReadStates(op, t, execution) ==
    IF op.op = "read"
    THEN { s \in PriorStates(t, execution) : s[op.key] = op.value }
    ELSE PriorStates(t, execution)

\* Commit test for Serializability: all reads of T read from T's parent state.
CT_SER(t, execution) ==
    LET pidx == CHOOSE i \in DOMAIN execution : execution[i].transaction = t
        parent == execution[pidx].parentState
    IN \A i \in DOMAIN t :
          t[i].op = "read" => t[i].value = parent[t[i].key]

\* Commit test for Snapshot Isolation: reads from some state s and NO-CONF holds.
CT_SI(t, execution) ==
    LET pidx == CHOOSE i \in DOMAIN execution : execution[i].transaction = t
        parent == execution[pidx].parentState
    IN /\ \E s \in PriorStates(t, execution) \cup {parent} :
            /\ \A i \in DOMAIN t : t[i].op = "read" => t[i].value = s[t[i].key]
            /\ NoConf(t, s, parent)

\* Read Committed: each read sees a value produced by some committed transaction.
CT_RC(t, execution) ==
    \A i \in DOMAIN t :
        t[i].op = "read" =>
            \E s \in PriorStates(t, execution) : s[t[i].key] = t[i].value

\* Read Uncommitted: any prior value is acceptable.
CT_RU(t, execution) == TRUE

\* A storage system satisfies isolation level I iff some execution passes the test
\* for every transaction.
SatisfyIsolationLevel(transactions, commitTest(_, _)) ==
    \E execution \in Executions(InitialState, transactions) :
        \A t \in transactions : commitTest(t, execution)

Serializability(transactions)      == SatisfyIsolationLevel(transactions, CT_SER)
SnapshotIsolation(transactions)    == SatisfyIsolationLevel(transactions, CT_SI)
ReadCommitted(transactions)        == SatisfyIsolationLevel(transactions, CT_RC)
ReadUncommitted(transactions)      == SatisfyIsolationLevel(transactions, CT_RU)

====
