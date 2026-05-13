---- MODULE nbacc_ray97 ----
\* TLA+ encoding of the NBAC algorithm with crashes in:
\* [1] Raynal, Michel. "A case study of agreement problems in distributed
\*     systems: non-blocking atomic commitment." High-Assurance Systems
\*     Engineering Workshop, 1997. Proceedings. IEEE, 1997.
\*
\* Igor Konnov, Thanh Hai Tran, Josef Widder, 2016.

EXTENDS Naturals, FiniteSets

CONSTANT N           \* number of processes

ASSUME N \in Nat /\ N >= 1

Proc == 1..N

\* program counters
PC == {"INIT", "YES", "NO", "COMMIT", "ABORT", "CRASH"}

VARIABLES
  pc,        \* program counters
  rcvd,      \* messages which are received
  sent,      \* messages which are sent by each process
  fd         \* a failure detector reporting to every process

vars == << pc, rcvd, sent, fd >>

\* All processes, including the crashed ones.
AllProc == Proc

\* A message is a (sender, vote) pair.
Message == [from : Proc, vote : {"YES", "NO"}]

\* Type invariant.
TypeOK ==
  /\ pc   \in [Proc -> PC]
  /\ rcvd \in [Proc -> SUBSET Message]
  /\ sent \in [Proc -> SUBSET Message]
  /\ fd   \in [Proc -> [Proc -> BOOLEAN]]

\* Initially every process is at INIT, no messages, fd reports nothing.
Init ==
  /\ pc   = [i \in Proc |-> "INIT"]
  /\ rcvd = [i \in Proc |-> {}]
  /\ sent = [i \in Proc |-> {}]
  /\ fd   = [i \in Proc |-> [j \in Proc |-> FALSE]]

\* ---------- actions ----------

\* Receive new messages.
Receive(self) ==
  /\ pc[self] /= "CRASH"
  /\ \E msgs \in SUBSET (UNION { sent[j] : j \in Proc }) :
        rcvd' = [rcvd EXCEPT ![self] = @ \cup msgs]
  /\ UNCHANGED << pc, sent, fd >>

\* Failure detector sends a nondeterministic new prediction to self.
FdUpdate(self) ==
  /\ pc[self] /= "CRASH"
  /\ \E pred \in [Proc -> BOOLEAN] :
        fd' = [fd EXCEPT ![self] = pred]
  /\ UNCHANGED << pc, rcvd, sent >>

\* Process self crashes.
Crash(self) ==
  /\ pc[self] /= "CRASH"
  /\ pc' = [pc EXCEPT ![self] = "CRASH"]
  /\ UNCHANGED << rcvd, sent, fd >>

\* Send a YES message.
VoteYes(self) ==
  /\ pc[self] = "INIT"
  /\ pc'   = [pc   EXCEPT ![self] = "YES"]
  /\ sent' = [sent EXCEPT ![self] = @ \cup {[from |-> self, vote |-> "YES"]}]
  /\ UNCHANGED << rcvd, fd >>

\* Send a NO message.
VoteNo(self) ==
  /\ pc[self] = "INIT"
  /\ pc'   = [pc   EXCEPT ![self] = "NO"]
  /\ sent' = [sent EXCEPT ![self] = @ \cup {[from |-> self, vote |-> "NO"]}]
  /\ UNCHANGED << rcvd, fd >>

\* Decide ABORT: voted and received some NO, or voted and FD suspects someone.
Abort(self) ==
  /\ pc[self] \in {"YES", "NO"}
  /\ \/ \E m \in rcvd[self] : m.vote = "NO"
     \/ \E j \in Proc : fd[self][j]
  /\ pc' = [pc EXCEPT ![self] = "ABORT"]
  /\ UNCHANGED << rcvd, sent, fd >>

\* Decide COMMIT: voted YES, received only YES from all processes, all correct.
Commit(self) ==
  /\ pc[self] = "YES"
  /\ \A j \in Proc : \E m \in rcvd[self] :
        m.from = j /\ m.vote = "YES"
  /\ \A j \in Proc : ~ fd[self][j]
  /\ pc' = [pc EXCEPT ![self] = "COMMIT"]
  /\ UNCHANGED << rcvd, sent, fd >>

\* Idle: do nothing (avoids deadlock when waiting).
Idle(self) ==
  /\ pc[self] \in {"YES", "NO", "COMMIT", "ABORT"}
  /\ UNCHANGED vars

Next ==
  \E self \in Proc :
       Receive(self) \/ FdUpdate(self) \/ Crash(self)
    \/ VoteYes(self) \/ VoteNo(self)
    \/ Abort(self)   \/ Commit(self)
    \/ Idle(self)

\* Specification with weak-fairness conditions.
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A self \in Proc :
        WF_vars(Receive(self) \/ VoteYes(self) \/ VoteNo(self)
                 \/ Abort(self) \/ Commit(self))

\* ---------- input scenarios ----------

\* Some processes vote YES, others vote NO.
MixedVote ==
  \E S \in SUBSET Proc :
     /\ S /= {} /\ S /= Proc
     /\ \A i \in S        : pc[i] = "YES"
     /\ \A i \in Proc \ S : pc[i] = "NO"

\* All processes vote YES.
AllYes == \A i \in Proc : pc[i] = "YES"

\* ---------- correctness ----------

\* Non-triviality: if all processes voted YES and no process crashes and the
\* failure detector eventually stops suspecting anyone, then every process
\* eventually commits.
NonTriv ==
  ( /\ \A i \in Proc : pc[i] = "YES"
    /\ [] (\A i \in Proc : pc[i] /= "CRASH")
    /\ <>[] (\A self \in Proc : ~ (\E j \in Proc : fd[self][j])) )
     => <> (\A self \in Proc : pc[self] = "COMMIT")

\* Agreement: no two processes decide differently.
Agreement ==
  \A i, j \in Proc :
     (pc[i] = "COMMIT" /\ pc[j] = "ABORT") => FALSE

====
