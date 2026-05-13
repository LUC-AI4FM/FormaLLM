---- MODULE HDiskSynod ----
(***************************************************************************)
(* Modification History                                                    *)
(* Last modified Sat Jan 26 15:52:41 CET 2019 by tthai                     *)
(* Created Sat Jan 26 15:23:57 CET 2019 by tthai                          *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, Inputs, Disk, Quorum

ASSUME
  /\ N \in Nat
  /\ Disk # {}
  /\ \A Q \in Quorum : Q \subseteq Disk

Proc == 1..N
NotAnInput == CHOOSE v : v \notin Inputs

DiskBlock == [mbal : Nat, bal : Nat, inp : Inputs \cup {NotAnInput}]
InitDB == [mbal |-> 0, bal |-> 0, inp |-> NotAnInput]

VARIABLES
  input,
  output,
  disk,
  dblock,
  phase,
  disksWritten,
  blocksRead

vars == <<input, output, disk, dblock, phase, disksWritten, blocksRead>>

allBlocksRead(p) ==
  LET allRdBlks == UNION { blocksRead[p][d] : d \in Disk }
  IN  { br.block : br \in allRdBlks }

hasRead(p, d, q) ==
  \E br \in blocksRead[p][d] : br.proc = q

InitializePhase(p) ==
  /\ disksWritten' = [disksWritten EXCEPT ![p] = {}]
  /\ blocksRead'   = [blocksRead   EXCEPT ![p] = [d \in Disk |-> {}]]

StartBallot(p) ==
  /\ phase[p] \in {1, 2}
  /\ phase' = [phase EXCEPT ![p] = 1]
  /\ \E b \in Nat :
        /\ b > dblock[p].mbal
        /\ dblock' = [dblock EXCEPT ![p].mbal = b]
  /\ InitializePhase(p)
  /\ UNCHANGED <<input, output, disk>>

Phase1or2Write(p, d) ==
  /\ phase[p] \in {1, 2}
  /\ disk' = [disk EXCEPT ![d][p] = dblock[p]]
  /\ disksWritten' = [disksWritten EXCEPT ![p] = @ \cup {d}]
  /\ UNCHANGED <<input, output, phase, dblock, blocksRead>>

Phase1or2Read(p, d, q) ==
  /\ d \in disksWritten[p]
  /\ disk[d][q].mbal < dblock[p].mbal
  /\ blocksRead' = [blocksRead EXCEPT
        ![p][d] = @ \cup {[block |-> disk[d][q], proc |-> q]}]
  /\ UNCHANGED <<input, output, disk, dblock, phase, disksWritten>>

EndPhase1or2(p) ==
  /\ \E Q \in Quorum :
        \A d \in Q : /\ d \in disksWritten[p]
                     /\ \A q \in Proc : hasRead(p, d, q)
  /\ \/ /\ phase[p] = 1
        /\ dblock' = [dblock EXCEPT
              ![p].bal = dblock[p].mbal,
              ![p].inp =
                LET blocksSeen == allBlocksRead(p)
                    nonInitBlks ==
                      {bk \in blocksSeen : bk.inp # NotAnInput}
                    maxBlk == CHOOSE b \in nonInitBlks :
                                \A c \in nonInitBlks : b.bal >= c.bal
                IN  IF nonInitBlks = {} THEN input[p] ELSE maxBlk.inp]
        /\ phase' = [phase EXCEPT ![p] = 2]
        /\ UNCHANGED <<input, output, disk>>
     \/ /\ phase[p] = 2
        /\ output' = [output EXCEPT ![p] = dblock[p].inp]
        /\ phase' = [phase EXCEPT ![p] = 3]
        /\ UNCHANGED <<input, disk, dblock>>
  /\ InitializePhase(p)

Fail(p) ==
  /\ \E ip \in Inputs :
        /\ input' = [input EXCEPT ![p] = ip]
        /\ phase' = [phase EXCEPT ![p] = 0]
        /\ dblock' = [dblock EXCEPT ![p] = InitDB]
        /\ output' = [output EXCEPT ![p] = NotAnInput]
  /\ InitializePhase(p)
  /\ UNCHANGED disk

Init ==
  /\ input \in [Proc -> Inputs]
  /\ output = [p \in Proc |-> NotAnInput]
  /\ disk = [d \in Disk |-> [p \in Proc |-> InitDB]]
  /\ phase = [p \in Proc |-> 0]
  /\ dblock = [p \in Proc |-> InitDB]
  /\ disksWritten = [p \in Proc |-> {}]
  /\ blocksRead = [p \in Proc |-> [d \in Disk |-> {}]]

Next ==
  \E p \in Proc :
    \/ StartBallot(p)
    \/ \E d \in Disk : Phase1or2Write(p, d) \/ \E q \in Proc : Phase1or2Read(p, d, q)
    \/ EndPhase1or2(p)
    \/ Fail(p)

Spec == Init /\ [][Next]_vars

\* /\ (bk.bal = 0) === (bk.inp = NotAnInput)
HInv ==
  \A p \in Proc :
    \A d \in Disk :
      (disk[d][p].bal = 0) <=> (disk[d][p].inp = NotAnInput)

====
