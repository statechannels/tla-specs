----------------------------- MODULE ForceMove -----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS
    Alice, \* A model value
    Names, \* A set of model values
    Participants, \* A set of model values
    NumHistories,
    NULL \* A model value representing null.

ChallengeStatus == [
  CLEARED |-> "CLEARED",
  ACTIVE  |-> "ACTIVE",
  EXPIRED |-> "EXPIRED"
]

Range(f) == { f[x] : x \in DOMAIN f }
StartingTurnNumber == 1
NumParticipants == Len(Participants)

ASSUME
  /\ Alice \in Names
  /\ Cardinality(Names) = NumParticipants
  /\ Len(Participants) >= 2
  /\ NumHistories \in Nat
  /\ \A p \in Range(Participants) : p \in Names
            
(* --algorithm forceMove

variables
    challenge = [turnNumber |-> 0, challengeStatus |-> ChallengeStatus.CLEARED],
    submittedChallenge = NULL

define
mover(turnNumber) == 1 + ((turnNumber-1) % NumParticipants)
challengeIsPresent == challenge.status # ChallengeStatus.CLEARED
end define;

macro respondWithMove(turnNumber, signer)
begin skip;
end macro;

macro respondWithAlternativeMove(turnNumber, signer)
begin skip;
end macro;

macro refute(turnNumber, signer)
begin skip;
end macro;

macro forceMove(turnNumber)
begin
submittedChallenge := [
  turnNumber    |-> turnNumber,
  status        |-> ChallengeStatus.ACTIVE
];

end macro;

fair process adjudicator = 0
begin
(***************************************************************************)
(* This process expires challenges.                                        *)
(***************************************************************************)
HandleChallenge:
while challenge.status # ChallengeStatus.EXPIRED
do
    either
        ExpireChallenge: 
            await challenge.status = ChallengeStatus.ACTIVE;
            challenge := [ status |-> ChallengeStatus.EXPIRED ] @@ challenge;
    or
        RecordChallenge:
            await submittedChallenge # NULL;
            challenge := submittedChallenge;
    end either;
end while;
end process;

fair process archie = 1
begin
(***************************************************************************)
(* Alice has commitments (n - numParticipants)..(n-1).  He wants to end    *)
(* up with commitments (n - numParticipants + 1)..n.                       *)
(*                                                                         *)
(* He is allowed to:                                                       *)
(*   - Call forceMove with any states that he currently has                *)
(*   - Call refute with any state that he has                              *)
(*   - Call respondWithMove or respondWithMove whenever there's an active  *)
(*     challenge where it's his turn to move                               *)
(***************************************************************************)
AliceMoves: skip;
end process;

fair process eve = 2
begin
(****************************************************************************)
(* Eve can do almost anything.  She has k different histories that each    *)
(* contain commitments 1...(n-1).  She can sign any data with any private  *)
(* key other than Alice's.  She can call any adjudicator function, at any  *)
(* time.  She can front-run any transaction an arbitrary number of times:  *)
(* if anyone else calls an adjudicator function in a transaction tx, she   *)
(* can then choose to submit any transaction before tx is mined.  She can  *)
(* expire challenges whenever the current challenge doesn't allow          *)
(***************************************************************************)
EveMoves: skip;
end process;


end algorithm;
*)


\* BEGIN TRANSLATION
VARIABLES challenge, submittedChallenge, pc

(* define statement *)
mover(turnNumber) == 1 + ((turnNumber-1) % NumParticipants)
challengeIsPresent == challenge.status # ChallengeStatus.CLEARED


vars == << challenge, submittedChallenge, pc >>

ProcSet == {0} \cup {1} \cup {2}

Init == (* Global variables *)
        /\ challenge = [turnNumber |-> 0, challengeStatus |-> ChallengeStatus.CLEARED]
        /\ submittedChallenge = NULL
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "HandleChallenge"
                                        [] self = 1 -> "AliceMoves"
                                        [] self = 2 -> "EveMoves"]

HandleChallenge == /\ pc[0] = "HandleChallenge"
                   /\ IF challenge.status # ChallengeStatus.EXPIRED
                         THEN /\ \/ /\ pc' = [pc EXCEPT ![0] = "ExpireChallenge"]
                                 \/ /\ pc' = [pc EXCEPT ![0] = "RecordChallenge"]
                         ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                   /\ UNCHANGED << challenge, submittedChallenge >>

ExpireChallenge == /\ pc[0] = "ExpireChallenge"
                   /\ challenge.status = ChallengeStatus.ACTIVE
                   /\ challenge' = [ status |-> ChallengeStatus.EXPIRED ] @@ challenge
                   /\ pc' = [pc EXCEPT ![0] = "HandleChallenge"]
                   /\ UNCHANGED submittedChallenge

RecordChallenge == /\ pc[0] = "RecordChallenge"
                   /\ submittedChallenge # NULL
                   /\ challenge' = submittedChallenge
                   /\ pc' = [pc EXCEPT ![0] = "HandleChallenge"]
                   /\ UNCHANGED submittedChallenge

adjudicator == HandleChallenge \/ ExpireChallenge \/ RecordChallenge

AliceMoves == /\ pc[1] = "AliceMoves"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![1] = "Done"]
              /\ UNCHANGED << challenge, submittedChallenge >>

archie == AliceMoves

EveMoves == /\ pc[2] = "EveMoves"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![2] = "Done"]
            /\ UNCHANGED << challenge, submittedChallenge >>

eve == EveMoves

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == adjudicator \/ archie \/ eve
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(adjudicator)
        /\ WF_vars(archie)
        /\ WF_vars(eve)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

AllowedTurnNumbers == 0..(StartingTurnNumber + NumParticipants)
AllowedChallenges ==
  [
    turnNumber: AllowedTurnNumbers,
    status: Range(ChallengeStatus)
  ]


\* Safety properties

\*TypeOK ==
\*  /\ challenge \in AllowedChallenges

\* TODO: Get TurnNumberDoesNotDecrease and StaysTerminated
\* For some reason, state[p].turnNumber' is not valid
\*TurnNumberDoesNotDecrease ==
\*  /\ \A p \in ParticipantIndices: state[p].turnNumber' >= state[p].turnNumber

\* Once a process has terminated, its state does not change.
\*StaysTerminated == \A p \in ParticipantIndices: (Terminated(state[p]) => (state'[p] = state[p]))
  
\* Liveness properties
\*ProtocolTerminatesWhenChallengeDoesNotExpire == 
\*    \/ <>[]( /\ challenge.status = ChallengeStatus.EXPIRED
\*             /\ \E p \in ParticipantIndices: state[p].type = Types.TERMINATED)
\*    \/ (\A p \in ParticipantIndices: <>[](/\ state[p].type = Types.SUCCESS
\*                                          /\ state[p].turnNumber = StartingTurnNumber + NumParticipants))
\*    \/ (\A p \in ParticipantIndices: <>[](/\ state[p].type = Types.ABORTED
\*                                          /\ state[p].turnNumber = state[1].turnNumber))


=============================================================================
\* Modification History
\* Last modified Fri Aug 23 16:38:52 MDT 2019 by andrewstewart
\* Created Tue Aug 06 14:38:11 MDT 2019 by andrewstewart
