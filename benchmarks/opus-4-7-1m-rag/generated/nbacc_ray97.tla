---- MODULE nbacc_ray97 ----
\* TLA+ encoding of the non-blocking atomic commitment algorithm of
\* Raynal (1997), with crashes detected by an unreliable failure detector.

EXTENDS Naturals, FiniteSets

CONSTANTS N

Proc == 1 .. N
Status == {"YES", "NO", "SENT", "COMMIT", "ABORT", "CRASH"}

VARIABLES
    pc,        \* program counters
    rcvd,      \* messages received by each process
    sent,      \* messages sent by each process
    fd,        \* failure detector: fd[i][j] = TRUE iff i thinks j crashed
    allProc    \* set of all processes, including crashed ones

vars == <<pc, rcvd, sent, fd, allProc>>

\* Messages: a record with sender and YES/NO vote.
Messages == [from : Proc, vote : {"YES", "NO"}]

\* Receive new messages.
Receive(self) ==
    /\ pc[self] # "CRASH"
    /\ \E ms \in SUBSET (UNION {sent[j] : j \in Proc}) :
         /\ ms # {}
         /\ rcvd' = [rcvd EXCEPT ![self] = @ \cup ms]
    /\ UNCHANGED <<pc, sent, fd, allProc>>

\* The failure detector sends a nondeterministic new prediction to self.
FDUpdate(self) ==
    /\ pc[self] # "CRASH"
    /\ \E newPred \in [Proc -> BOOLEAN] :
         fd' = [fd EXCEPT ![self] = newPred]
    /\ UNCHANGED <<pc, rcvd, sent, allProc>>

\* Process self crashes.
Crash(self) ==
    /\ pc[self] # "CRASH"
    /\ pc' = [pc EXCEPT ![self] = "CRASH"]
    /\ UNCHANGED <<rcvd, sent, fd, allProc>>

\* Send a YES message.
SendYes(self) ==
    /\ pc[self] = "YES"
    /\ pc' = [pc EXCEPT ![self] = "SENT"]
    /\ sent' = [sent EXCEPT ![self] = @ \cup {[from |-> self, vote |-> "YES"]}]
    /\ UNCHANGED <<rcvd, fd, allProc>>

\* Send a NO message.
SendNo(self) ==
    /\ pc[self] = "NO"
    /\ pc' = [pc EXCEPT ![self] = "SENT"]
    /\ sent' = [sent EXCEPT ![self] = @ \cup {[from |-> self, vote |-> "NO"]}]
    /\ UNCHANGED <<rcvd, fd, allProc>>

\* Decision rules for a SENT process self:
\* - If a NO message has been received, abort.
\* - If the failure detector reports some process has crashed, abort.
\* - If only YES messages have been received from every process and the
\*   failure detector reports all processes correct, commit.
DecideAbortNo(self) ==
    /\ pc[self] = "SENT"
    /\ \E m \in rcvd[self] : m.vote = "NO"
    /\ pc' = [pc EXCEPT ![self] = "ABORT"]
    /\ UNCHANGED <<rcvd, sent, fd, allProc>>

DecideAbortFD(self) ==
    /\ pc[self] = "SENT"
    /\ \E j \in Proc : fd[self][j] = TRUE
    /\ pc' = [pc EXCEPT ![self] = "ABORT"]
    /\ UNCHANGED <<rcvd, sent, fd, allProc>>

DecideCommit(self) ==
    /\ pc[self] = "SENT"
    /\ \A m \in rcvd[self] : m.vote = "YES"
    /\ {m.from : m \in rcvd[self]} = Proc
    /\ \A j \in Proc : fd[self][j] = FALSE
    /\ pc' = [pc EXCEPT ![self] = "COMMIT"]
    /\ UNCHANGED <<rcvd, sent, fd, allProc>>

\* Do nothing but we need this to avoid deadlock.
Stutter == UNCHANGED vars

\* Some processes vote YES. Others vote NO.
Init ==
    /\ pc \in [Proc -> {"YES", "NO"}]
    /\ rcvd = [i \in Proc |-> {}]
    /\ sent = [i \in Proc |-> {}]
    /\ fd \in [Proc -> [Proc -> BOOLEAN]]
    /\ allProc = Proc

\* All processes vote YES.
InitYes ==
    /\ pc = [i \in Proc |-> "YES"]
    /\ rcvd = [i \in Proc |-> {}]
    /\ sent = [i \in Proc |-> {}]
    /\ fd \in [Proc -> [Proc -> BOOLEAN]]
    /\ allProc = Proc

Next ==
    \E self \in Proc :
        \/ Receive(self)
        \/ FDUpdate(self)
        \/ Crash(self)
        \/ SendYes(self)
        \/ SendNo(self)
        \/ DecideAbortNo(self)
        \/ DecideAbortFD(self)
        \/ DecideCommit(self)
        \/ Stutter

\* Add the weak fairness condition.
Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E self \in Proc :
                 Receive(self) \/ SendYes(self) \/ SendNo(self)
                 \/ DecideAbortNo(self) \/ DecideAbortFD(self)
                 \/ DecideCommit(self))

SpecYes ==
    /\ InitYes
    /\ [][Next]_vars
    /\ WF_vars(\E self \in Proc :
                 Receive(self) \/ SendYes(self) \/ SendNo(self)
                 \/ DecideAbortNo(self) \/ DecideAbortFD(self)
                 \/ DecideCommit(self))

TypeOK ==
    /\ pc \in [Proc -> Status]
    /\ rcvd \in [Proc -> SUBSET Messages]
    /\ sent \in [Proc -> SUBSET Messages]
    /\ fd \in [Proc -> [Proc -> BOOLEAN]]
    /\ allProc = Proc

\* Agreement: no two processes decide differently.
Agreement ==
    [](~ \E i, j \in Proc : pc[i] = "COMMIT" /\ pc[j] = "ABORT")

\* Non-triviality: if everyone votes YES, no process crashes, and the
\* failure detector eventually reports no crashes, then commit holds.
NonTriv ==
    /\ \A i \in Proc : pc[i] = "YES"
    /\ [] (\A i \in Proc : pc[i] # "CRASH")
    /\ <>[] (\A self \in Proc : \A j \in Proc : fd[self][j] = FALSE)
    => <> (\A self \in Proc : pc[self] = "COMMIT")

====
