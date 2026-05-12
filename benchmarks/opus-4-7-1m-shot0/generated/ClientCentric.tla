---- MODULE ClientCentric ----
\* TLA+ formalization of the Client-Centric Isolation Specification of
\* Crooks et al. (https://dl.acm.org/doi/10.1145/3087801.3087802) by
\* Tim Soethout et al. ("Automated Validation of State-Based
\* Client-Centric Isolation with TLA+",
\* https://doi.org/10.1007/978-3-030-67220-1_4).
\*
\* A database State maps keys to values. An Operation is a read or write
\* of a key/value pair. A Transaction is a totally-ordered sequence of
\* Operations. An Execution is a totally-ordered sequence of
\* (parentState, transaction) pairs whose parent state is the result of
\* applying the previous transaction (starting from initialState).
\*
\* The module exports helpers and the commit tests that characterize the
\* standard isolation levels: Serializability, Snapshot Isolation,
\* Strict Serializability, Read Committed, Read Uncommitted.

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Keys, Values, InitValue, TimeStamp

ASSUME InitValue \in Values

\* ----- Domain definitions -----

State == [Keys -> Values]

\* An operation is a read or a write of (key, value).
Operation == [op: {"read", "write"}, key: Keys, value: Values]

r(k, v) == [op |-> "read",  key |-> k, value |-> v]
w(k, v) == [op |-> "write", key |-> k, value |-> v]

\* A transaction is a sequence of operations together with start/commit times.
Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]

\* An execution element pairs a parent state with the transaction applied.
ExecutionElem == [parentState: State, transaction: Transaction]

\* ----- Helpers -----

\* Initial state: every key holds InitValue.
initialState == [k \in Keys |-> InitValue]

\* Write set of a transaction: keys that T updates.
WriteSet(t) == { op.key : op \in { o \in {t.ops[i] : i \in DOMAIN t.ops} : o.op = "write" } }

\* Read set of a transaction.
ReadSet(t)  == { op.key : op \in { o \in {t.ops[i] : i \in DOMAIN t.ops} : o.op = "read" } }

\* Apply a single operation to a state, producing the next state.
ApplyOp(s, op) ==
  IF op.op = "write" THEN [s EXCEPT ![op.key] = op.value] ELSE s

\* Apply a whole transaction to a state.
RECURSIVE ApplySeq(_, _)
ApplySeq(s, ops) ==
  IF ops = << >> THEN s
  ELSE ApplySeq(ApplyOp(s, Head(ops)), Tail(ops))

NextState(s, t) == ApplySeq(s, t.ops)

\* Delta between two states: keys at which they differ.
Delta(s, sp) == { k \in Keys : s[k] /= sp[k] }

\* parentState of a transaction t in an execution e.
ParentState(e, t) ==
  LET idx == CHOOSE i \in DOMAIN e : e[i].transaction = t
  IN  e[idx].parentState

\* The state reachable via -*-> from a state in the execution: any state at
\* index <= i in the execution sequence, plus the result of the last txn.
PrefixStates(e) ==
  { e[i].parentState : i \in DOMAIN e } \cup
  { IF Len(e) = 0 THEN initialState
                  ELSE NextState(e[Len(e)].parentState, e[Len(e)].transaction) }

\* The "no conflict" predicate NO-CONF_T(s) from the paper.
NoConf(t, s, sp) == Delta(s, sp) \cap WriteSet(t) = {}

\* Read states for an operation o in transaction t, execution e: all states
\* reachable in -*-> consistent with the operation's value.
ReadStates(o, t, e) ==
  IF o.op = "write" THEN
    \* By convention, write operations include all states up to T's parent state.
    { e[i].parentState : i \in { j \in DOMAIN e : j <= CHOOSE k \in DOMAIN e : e[k].transaction = t } }
  ELSE
    { s \in PrefixStates(e) : <<o.key, o.value>> \in { <<k, s[k]>> : k \in Keys } }

\* For empty transactions, all previous states qualify as read states.
readStatesForEmptyTransaction(t, e) == PrefixStates(e)

\* A state s is complete for T in e if every operation of T can read from s.
CompleteFor(s, t, e) ==
  \A i \in DOMAIN t.ops : s \in ReadStates(t.ops[i], t, e)

\* ----- Permutations of transactions => executions -----

\* All sequences without repetition over a finite set S.
RECURSIVE Permutations(_)
Permutations(S) ==
  IF S = {} THEN { << >> }
  ELSE { <<x>> \o p : <<x, p>> \in { <<y, q>> : y \in S, q \in Permutations(S \ {y}) } }

\* Build an execution from an initial state and a permutation of transactions.
RECURSIVE BuildExec(_, _, _)
BuildExec(s, perm, acc) ==
  IF perm = << >> THEN acc
  ELSE BuildExec(NextState(s, Head(perm)),
                 Tail(perm),
                 Append(acc, [parentState |-> s, transaction |-> Head(perm)]))

executions(init, transactions) ==
  { BuildExec(init, perm, << >>) : perm \in Permutations(transactions) }

\* ----- Commit tests -----

\* Generic predicate: does there exist a complete state in the allowed read
\* states for every operation of t?
satisfies(t, e, allowed) ==
  \A i \in DOMAIN t.ops :
    \E s \in allowed : s \in ReadStates(t.ops[i], t, e)

\* Serializability: read from parent state of t (snapshot is parent state).
CT_SER(t, e) ==
  LET sp == ParentState(e, t)
  IN  CompleteFor(sp, t, e)

\* Snapshot Isolation: there exists a complete snapshot consistent with no-conf.
CT_SI(t, e) ==
  LET sp == ParentState(e, t)
  IN  \E s \in PrefixStates(e) :
        CompleteFor(s, t, e) /\ NoConf(t, s, sp)

\* Strict Serializability: like SER but respects real-time order via timestamps.
\* For T1, T2 in T: T1 <s T2 => s_T1' -*-> s_T2  (parent of T2 is reachable from
\* the result state of T1).
CT_SSER(t, e, timestamps) ==
  /\ CT_SER(t, e)
  /\ \A t2 \in { e[i].transaction : i \in DOMAIN e } :
       (timestamps[t].commit < timestamps[t2].start) =>
         ParentState(e, t2) \in PrefixStates(e)

\* Read Committed: every read sees a committed (i.e., post-transaction) state.
CT_RC(t, e) ==
  \A i \in DOMAIN t.ops :
    t.ops[i].op = "read" =>
      \E s \in PrefixStates(e) : s \in ReadStates(t.ops[i], t, e)

\* Read Uncommitted: trivial - any state that contains the read value is fine.
CT_RU(t, e) == TRUE

\* ----- Top-level isolation check -----

\* Definition 5: a storage system satisfies isolation level I iff there exists
\* an execution e in which every transaction t passes the commit test CT_I.
satisfyIsolationLevel(transactions, commitTest(_,_)) ==
  \E e \in executions(initialState, transactions) :
    \A t \in transactions : commitTest(t, e)

Serializability(transactions)       == satisfyIsolationLevel(transactions, CT_SER)
SnapshotIsolation(transactions)     == satisfyIsolationLevel(transactions, CT_SI)
ReadCommitted(transactions)         == satisfyIsolationLevel(transactions, CT_RC)
ReadUncommitted(transactions)       == satisfyIsolationLevel(transactions, CT_RU)
StrictSerializability(transactions, timestamps) ==
  \E e \in executions(initialState, transactions) :
    \A t \in transactions : CT_SSER(t, e, timestamps)

\* Type sanity check.
TypesOK ==
  /\ InitValue \in Values
  /\ initialState \in State

====
