---- MODULE HDiskSynod ----
(***************************************************************************)
(* HDiskSynod: a hierarchical variant of the Disk Synod consensus          *)
(* protocol. Processors communicate via shared disks. Each processor       *)
(* writes ballot blocks to disks and reads from a majority to decide.      *)
(*                                                                         *)
(* Modification History                                                    *)
(*   Last modified Sat Jan 26 15:52:41 CET 2019 by tthai                   *)
(*   Created      Sat Jan 26 15:23:57 CET 2019 by tthai                    *)
(*                                                                         *)
(* Invariant on every block bk:                                            *)
(*   (bk.bal = 0) <=> (bk.inp = NotAnInput)                                *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Proc,        \* The set of processors.
          Disk,        \* The set of disks.
          Inputs,      \* The set of possible inputs.
          IsMajority(_) \* IsMajority(S) is TRUE iff S is a majority of Disk.

ASSUME  /\ Inputs # {}
        /\ \A S, T \in SUBSET Disk : IsMajority(S) /\ IsMajority(T) => S \cap T # {}

NotAnInput == CHOOSE i : i \notin Inputs

Ballot == Nat

DiskBlock == [mbal: Ballot, bal: Ballot, inp: Inputs \cup {NotAnInput}]

InitDB == [mbal |-> 0, bal |-> 0, inp |-> NotAnInput]

VARIABLES input,    \* input[p] is the input value for processor p
          output,   \* output[p] is the decided value for processor p (or NotAnInput)
          disk,     \* disk[d][p] is the block written by p on disk d
          phase,    \* phase[p] tracks protocol phase for p
          dblock,   \* dblock[p] is p's local copy of its block
          disksWritten, \* disks p has written this phase
          blocksRead    \* blocks p has read this phase

vars == <<input, output, disk, phase, dblock, disksWritten, blocksRead>>

TypeOK ==
    /\ input \in [Proc -> Inputs]
    /\ output \in [Proc -> Inputs \cup {NotAnInput}]
    /\ disk \in [Disk -> [Proc -> DiskBlock]]
    /\ phase \in [Proc -> 0..3]
    /\ dblock \in [Proc -> DiskBlock]
    /\ disksWritten \in [Proc -> SUBSET Disk]
    /\ blocksRead \in [Proc -> [Disk -> SUBSET [proc: Proc, block: DiskBlock]]]

\* Block invariant: bal = 0 iff inp = NotAnInput.
BlockInv ==
    \A p \in Proc :
        (dblock[p].bal = 0) <=> (dblock[p].inp = NotAnInput)

Init ==
    /\ input \in [Proc -> Inputs]
    /\ output = [p \in Proc |-> NotAnInput]
    /\ disk = [d \in Disk |-> [p \in Proc |-> InitDB]]
    /\ phase = [p \in Proc |-> 0]
    /\ dblock = [p \in Proc |-> InitDB]
    /\ disksWritten = [p \in Proc |-> {}]
    /\ blocksRead = [p \in Proc |-> [d \in Disk |-> {}]]

StartBallot(p) ==
    /\ phase[p] = 0
    /\ \E b \in Ballot \ {0} :
         /\ b > dblock[p].mbal
         /\ dblock' = [dblock EXCEPT ![p].mbal = b]
    /\ phase' = [phase EXCEPT ![p] = 1]
    /\ disksWritten' = [disksWritten EXCEPT ![p] = {}]
    /\ blocksRead' = [blocksRead EXCEPT ![p] = [d \in Disk |-> {}]]
    /\ UNCHANGED <<input, output, disk>>

WriteDisk(p, d) ==
    /\ phase[p] \in {1, 2}
    /\ d \notin disksWritten[p]
    /\ disk' = [disk EXCEPT ![d][p] = dblock[p]]
    /\ disksWritten' = [disksWritten EXCEPT ![p] = @ \cup {d}]
    /\ UNCHANGED <<input, output, phase, dblock, blocksRead>>

ReadDisk(p, d) ==
    /\ phase[p] \in {1, 2}
    /\ d \in disksWritten[p]
    /\ \E reads \in SUBSET { [proc |-> q, block |-> disk[d][q]] : q \in Proc \ {p} } :
         /\ \A r \in reads : r.block.mbal < dblock[p].mbal
         /\ blocksRead' = [blocksRead EXCEPT ![p][d] = reads]
    /\ UNCHANGED <<input, output, disk, phase, dblock, disksWritten>>

EndPhase1or2(p) ==
    /\ phase[p] \in {1, 2}
    /\ IsMajority(disksWritten[p])
    /\ \/ /\ phase[p] = 1
          /\ LET allReadBlocks == UNION { { r.block : r \in blocksRead[p][d] } : d \in Disk }
                 nonInit       == { b \in allReadBlocks : b.bal > 0 }
             IN  IF nonInit = {}
                 THEN dblock' = [dblock EXCEPT ![p].inp = input[p]]
                 ELSE LET maxBal == CHOOSE b \in nonInit : \A c \in nonInit : c.bal <= b.bal
                      IN  dblock' = [dblock EXCEPT ![p].inp = maxBal.inp]
          /\ phase' = [phase EXCEPT ![p] = 2]
       \/ /\ phase[p] = 2
          /\ dblock' = [dblock EXCEPT ![p].bal = dblock[p].mbal]
          /\ phase' = [phase EXCEPT ![p] = 3]
    /\ disksWritten' = [disksWritten EXCEPT ![p] = {}]
    /\ blocksRead' = [blocksRead EXCEPT ![p] = [d \in Disk |-> {}]]
    /\ UNCHANGED <<input, output, disk>>

Decide(p) ==
    /\ phase[p] = 3
    /\ output' = [output EXCEPT ![p] = dblock[p].inp]
    /\ phase' = [phase EXCEPT ![p] = 0]
    /\ UNCHANGED <<input, disk, dblock, disksWritten, blocksRead>>

Fail(p) ==
    /\ phase' = [phase EXCEPT ![p] = 0]
    /\ dblock' = [dblock EXCEPT ![p] = InitDB]
    /\ disksWritten' = [disksWritten EXCEPT ![p] = {}]
    /\ blocksRead' = [blocksRead EXCEPT ![p] = [d \in Disk |-> {}]]
    /\ UNCHANGED <<input, output, disk>>

Next ==
    \E p \in Proc :
        \/ StartBallot(p)
        \/ \E d \in Disk : WriteDisk(p, d)
        \/ \E d \in Disk : ReadDisk(p, d)
        \/ EndPhase1or2(p)
        \/ Decide(p)
        \/ Fail(p)

Spec == Init /\ [][Next]_vars

\* Safety: if two processors decide, they decide the same value.
Agreement ==
    \A p, q \in Proc :
        (output[p] /= NotAnInput /\ output[q] /= NotAnInput) => output[p] = output[q]

\* Validity: decided values come from some input.
Validity ==
    \A p \in Proc :
        output[p] /= NotAnInput => \E q \in Proc : output[p] = input[q]

====
