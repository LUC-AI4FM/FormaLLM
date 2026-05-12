---- MODULE HDiskSynod ----
\* Hierarchical Disk Synod / Disk Paxos.
\*
\* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai
\* Created Sat Jan 26 15:23:57 CET 2019 by tthai
\*
\* The comments hint at the invariant
\*     bk.bal = 0  <=>  bk.inp = NotAnInput
\* which is the standard "empty disk block" invariant in Disk Paxos:
\* a block with ballot 0 is treated as "uninitialised" and carries the
\* sentinel input NotAnInput.

EXTENDS Naturals, FiniteSets

CONSTANTS Proc,        \* set of processes
          Inputs,      \* set of legal input values
          Disk,        \* set of disks
          IsMajority(_), \* predicate: a set of disks is a majority
          Ballot(_)    \* function Proc -> set of ballot numbers a process may use

NotAnInput == CHOOSE v : v \notin Inputs

Any == CHOOSE v : v \notin Inputs \cup {NotAnInput}

\* A disk block holds a ballot, an "mbal" (max ballot seen) and an input.
DiskBlock ==
  [mbal: Nat, bal: Nat, inp: Inputs \cup {NotAnInput}]

InitDB == [mbal |-> 0, bal |-> 0, inp |-> NotAnInput]

\* ----- State variables -----
VARIABLES
  disk,           \* disk[d][p] : block held on disk d for proc p
  dblock,         \* dblock[p]  : proc p's local copy of its block
  phase,          \* phase[p]   : 0 = idle, 1 = read, 2 = write, 3 = done
  proposed,       \* proposed[p]: input p is trying to commit
  chosen,         \* chosen[p]  : output once p decides
  input,          \* input[p]   : initial proposal
  disksWritten,   \* disksWritten[p]: set of disks p has written this phase
  blocksRead      \* blocksRead[p][q]: set of blocks p has read for q this phase

vars == << disk, dblock, phase, proposed, chosen, input,
           disksWritten, blocksRead >>

TypeOK ==
  /\ disk \in [Disk -> [Proc -> DiskBlock]]
  /\ dblock \in [Proc -> DiskBlock]
  /\ phase \in [Proc -> 0..3]
  /\ proposed \in [Proc -> Inputs \cup {NotAnInput}]
  /\ chosen \in [Proc -> Inputs \cup {NotAnInput}]
  /\ input \in [Proc -> Inputs \cup {NotAnInput}]
  /\ disksWritten \in [Proc -> SUBSET Disk]
  /\ blocksRead \in [Proc -> [Proc -> SUBSET DiskBlock]]

\* The hinted invariant: ballot 0 iff input is NotAnInput.
InvBallotInput ==
  \A d \in Disk, p \in Proc :
     (disk[d][p].bal = 0) <=> (disk[d][p].inp = NotAnInput)

Init ==
  /\ disk = [d \in Disk |-> [p \in Proc |-> InitDB]]
  /\ dblock = [p \in Proc |-> InitDB]
  /\ phase = [p \in Proc |-> 0]
  /\ proposed = [p \in Proc |-> NotAnInput]
  /\ chosen   = [p \in Proc |-> NotAnInput]
  /\ input    \in [Proc -> Inputs]
  /\ disksWritten = [p \in Proc |-> {}]
  /\ blocksRead   = [p \in Proc |-> [q \in Proc |-> {}]]

\* Start a new ballot b for proc p.
StartBallot(p, b) ==
  /\ phase[p] = 0
  /\ b \in Ballot(p)
  /\ dblock' = [dblock EXCEPT ![p] = [@ EXCEPT !.mbal = b]]
  /\ phase'  = [phase  EXCEPT ![p] = 1]
  /\ disksWritten' = [disksWritten EXCEPT ![p] = {}]
  /\ blocksRead'   = [blocksRead   EXCEPT ![p] = [q \in Proc |-> {}]]
  /\ UNCHANGED << disk, proposed, chosen, input >>

\* Write own block to a disk.
WriteDisk(p, d) ==
  /\ phase[p] \in {1, 2}
  /\ disk' = [disk EXCEPT ![d][p] = dblock[p]]
  /\ disksWritten' = [disksWritten EXCEPT ![p] = @ \cup {d}]
  /\ UNCHANGED << dblock, phase, proposed, chosen, input, blocksRead >>

\* Read block of process q from disk d.
ReadDisk(p, d, q) ==
  /\ phase[p] \in {1, 2}
  /\ blocksRead' = [blocksRead EXCEPT ![p][q] = @ \cup {disk[d][q]}]
  /\ UNCHANGED << disk, dblock, phase, proposed, chosen, input, disksWritten >>

\* End of phase 1: choose a value (input or max-bal value read).
EndPhase1(p) ==
  /\ phase[p] = 1
  /\ IsMajority(disksWritten[p])
  /\ LET observed == UNION { blocksRead[p][q] : q \in Proc }
         maxBal == IF observed = {} THEN 0
                   ELSE LET sel == CHOOSE b \in observed :
                                     \A c \in observed : c.bal <= b.bal
                        IN sel.bal
         chosenInp ==
           IF observed = {} \/ maxBal = 0
              THEN input[p]
           ELSE LET sel == CHOOSE b \in observed :
                              /\ b.bal = maxBal
                              /\ b.inp /= NotAnInput
                IN sel.inp
     IN
       /\ dblock' = [dblock EXCEPT ![p] = [@ EXCEPT !.bal = dblock[p].mbal,
                                                     !.inp = chosenInp]]
       /\ proposed' = [proposed EXCEPT ![p] = chosenInp]
  /\ phase' = [phase EXCEPT ![p] = 2]
  /\ disksWritten' = [disksWritten EXCEPT ![p] = {}]
  /\ UNCHANGED << disk, chosen, input >>

\* End of phase 2: decide.
EndPhase2(p) ==
  /\ phase[p] = 2
  /\ IsMajority(disksWritten[p])
  /\ chosen' = [chosen EXCEPT ![p] = proposed[p]]
  /\ phase'  = [phase  EXCEPT ![p] = 3]
  /\ UNCHANGED << disk, dblock, proposed, input, disksWritten, blocksRead >>

\* Abort to try a higher ballot.
Abort(p) ==
  /\ phase[p] \in {1, 2}
  /\ \E q \in Proc, d \in Disk :
        disk[d][q].mbal > dblock[p].mbal
  /\ phase' = [phase EXCEPT ![p] = 0]
  /\ UNCHANGED << disk, dblock, proposed, chosen, input, disksWritten, blocksRead >>

Next ==
  \/ \E p \in Proc, b \in Nat : StartBallot(p, b)
  \/ \E p \in Proc, d \in Disk : WriteDisk(p, d)
  \/ \E p \in Proc, d \in Disk, q \in Proc : ReadDisk(p, d, q)
  \/ \E p \in Proc : EndPhase1(p)
  \/ \E p \in Proc : EndPhase2(p)
  \/ \E p \in Proc : Abort(p)

Spec == Init /\ [][Next]_vars

\* Safety: any two decisions agree.
Agreement ==
  \A p, q \in Proc :
     (chosen[p] /= NotAnInput /\ chosen[q] /= NotAnInput) =>
        chosen[p] = chosen[q]

\* Validity: a decided value was proposed by some process.
Validity ==
  \A p \in Proc :
     (chosen[p] /= NotAnInput) => \E q \in Proc : chosen[p] = input[q]

====
