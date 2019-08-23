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

macro forceMove(turnNumber, votesRequired)
begin
challenge := [
  turnNumber    |-> turnNumber,
  status        |-> ChallengeStatus.ACTIVE,
  votesRequired |-> votesRequired
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
    await challenge.status = ChallengeStatus.ACTIVE;
    ExpireChallenge:
        challenge := [ status |-> ChallengeStatus.EXPIRED ] @@ challenge;
end while;
end process;

fair process alice = 1
begin
(***************************************************************************)
(* Alice has commitments (n - numParticipants)..(n-1).  She wants to end   *)
(* up with commitments (n - numParticipants + 1)..n.  She is allowed to:   *)
(*   - Call forceMove with any states that she currently has               *)
(*   - Call refute with any state that she has                             *)
(*   - Call respondWithMove whenever there's an active challenge forcing   *)
(*     her to move                                                         *)
(***************************************************************************)
HandleChallenge:
while challenge.status # ChallengeStatus.EXPIRED
do
    await challenge.status = ChallengeStatus.ACTIVE;
    ExpireChallenge:
        challenge := [ status |-> ChallengeStatus.EXPIRED ] @@ challenge;
end while;
end process;

fair process eve = 2
begin
(***************************************************************************)
(* Eve can do almost anything.  She has k different histories that each    *)
(* contain commitments 1...(n-1).  She can sign any data with any private  *)
(* key other than Alice's.  She can call any adjudicator function, at any  *)
(* time.  She can front-run any transaction an arbitrary number of times:  *)
(* if anyone else calls an adjudicator function in a transaction tx, she   *)
(* can then choose to submit any transaction before tx is mined.           *)
(***************************************************************************)
HandleChallenge:
while challenge.status # ChallengeStatus.EXPIRED
do
    await challenge.status = ChallengeStatus.ACTIVE;
    ExpireChallenge:
        challenge := [ status |-> ChallengeStatus.EXPIRED ] @@ challenge;
end while;
end process;


end algorithm;
*)


\* BEGIN TRANSLATION
\* Label HandleChallenge of process adjudicator at line 54 col 1 changed to HandleChallenge_
\* Label ExpireChallenge of process adjudicator at line 58 col 9 changed to ExpireChallenge_
\* Label HandleChallenge of process alice at line 73 col 1 changed to HandleChallenge_a
\* Label ExpireChallenge of process alice at line 77 col 9 changed to ExpireChallenge_a
VARIABLES challenge, submittedChallenge, pc

(* define statement *)
mover(turnNumber) == 1 + ((turnNumber-1) % NumParticipants)
challengeIsPresent == challenge.status # ChallengeStatus.CLEARED


vars == << challenge, submittedChallenge, pc >>

ProcSet == {0} \cup {1} \cup {2}

Init == (* Global variables *)
        /\ challenge = [turnNumber |-> 0, challengeStatus |-> ChallengeStatus.CLEARED]
        /\ submittedChallenge = NULL
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "HandleChallenge_"
                                        [] self = 1 -> "HandleChallenge_a"
                                        [] self = 2 -> "HandleChallenge"]

HandleChallenge_ == /\ pc[0] = "HandleChallenge_"
                    /\ IF challenge.status # ChallengeStatus.EXPIRED
                          THEN /\ challenge.status = ChallengeStatus.ACTIVE
                               /\ pc' = [pc EXCEPT ![0] = "ExpireChallenge_"]
                          ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                    /\ UNCHANGED << challenge, submittedChallenge >>

ExpireChallenge_ == /\ pc[0] = "ExpireChallenge_"
                    /\ challenge' = [ status |-> ChallengeStatus.EXPIRED ] @@ challenge
                    /\ pc' = [pc EXCEPT ![0] = "HandleChallenge_"]
                    /\ UNCHANGED submittedChallenge

adjudicator == HandleChallenge_ \/ ExpireChallenge_

HandleChallenge_a == /\ pc[1] = "HandleChallenge_a"
                     /\ IF challenge.status # ChallengeStatus.EXPIRED
                           THEN /\ challenge.status = ChallengeStatus.ACTIVE
                                /\ pc' = [pc EXCEPT ![1] = "ExpireChallenge_a"]
                           ELSE /\ pc' = [pc EXCEPT ![1] = "Done"]
                     /\ UNCHANGED << challenge, submittedChallenge >>

ExpireChallenge_a == /\ pc[1] = "ExpireChallenge_a"
                     /\ challenge' = [ status |-> ChallengeStatus.EXPIRED ] @@ challenge
                     /\ pc' = [pc EXCEPT ![1] = "HandleChallenge_a"]
                     /\ UNCHANGED submittedChallenge

alice == HandleChallenge_a \/ ExpireChallenge_a

HandleChallenge == /\ pc[2] = "HandleChallenge"
                   /\ IF challenge.status # ChallengeStatus.EXPIRED
                         THEN /\ challenge.status = ChallengeStatus.ACTIVE
                              /\ pc' = [pc EXCEPT ![2] = "ExpireChallenge"]
                         ELSE /\ pc' = [pc EXCEPT ![2] = "Done"]
                   /\ UNCHANGED << challenge, submittedChallenge >>

ExpireChallenge == /\ pc[2] = "ExpireChallenge"
                   /\ challenge' = [ status |-> ChallengeStatus.EXPIRED ] @@ challenge
                   /\ pc' = [pc EXCEPT ![2] = "HandleChallenge"]
                   /\ UNCHANGED submittedChallenge

eve == HandleChallenge \/ ExpireChallenge

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == adjudicator \/ alice \/ eve
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(adjudicator)
        /\ WF_vars(alice)
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
\* Last modified Fri Aug 23 16:08:24 MDT 2019 by andrewstewart
\* Created Tue Aug 06 14:38:11 MDT 2019 by andrewstewart
