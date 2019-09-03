----------------------------- MODULE ForceMove -----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS
    Alice,
    Eve,
    StartingTurnNumber,
    NumParticipants,
    AlicesIDX,
    NULL \* A model value representing null.

ChannelMode == [
  OPEN |-> "OPEN",
  CHALLENGE  |-> "CHALLENGE",
  FINALIZED |-> "FINALIZED"
]

Range(f) == { f[x] : x \in DOMAIN f }

LatestTurnNumber == StartingTurnNumber + NumParticipants - 1
AlicesGoalTurnNumber == LatestTurnNumber + 1
Names == { Alice, Eve }
ParticipantIDXs == 1..NumParticipants
AlicesCommitments == StartingTurnNumber..LatestTurnNumber
ParticipantIDX(turnNumber) == 1 + ((turnNumber - 1) % NumParticipants)
AlicesMove(turnNumber) == ParticipantIDX(turnNumber) = AlicesIDX

Maximum(a,b) == IF a > b THEN a ELSE b

ASSUME
  /\ StartingTurnNumber \in Nat
  /\ NumParticipants \in Nat \ { 1 }
  /\ AlicesIDX \in ParticipantIDXs
  /\ ~AlicesMove(LatestTurnNumber + 1)
            
(* --algorithm forceMove

variables
    channel = [turnNumber |-> [p \in ParticipantIDXs |-> 0], mode |-> ChannelMode.OPEN, challenge |-> NULL ],
    challenge = NULL

define
challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen == channel.mode = ChannelMode.OPEN
challengerSigIsValid(turnNumber, challenger) ==
    IF AlicesMove(turnNumber)
    THEN challenge = Alice
    ELSE challenger = Eve
progressesChannel(commitment) == commitment.turnNumber >= channel.turnNumber[commitment.signer]
validCommitment(c) == c \in [ turnNumber: Nat, signer: ParticipantIDXs ]
validTransition(commitment) ==
    /\ commitment.turnNumber = channel.challenge.turnNumber + 1
    /\ commitment.signer = ParticipantIDX(commitment.turnNumber)
    
AliceCanTakeAction == channel.mode # ChannelMode.FINALIZED
EveCanTakeAction == AliceCanTakeAction

Refutable(n) == TRUE
    /\ n % NumParticipants = channel.challenge.signer % NumParticipants
    /\ n > channel.challenge.turnNumber
end define;

macro clearChallenge(turnNumber)
begin
assert turnNumber \in Nat;
channel := [ mode |-> ChannelMode.OPEN, turnNumber |-> [p \in ParticipantIDXs |-> Maximum(channel.turnNumber[p], turnNumber)], challenge |-> NULL ];
end macro;


macro setChallenge(commitment)
begin
\*assert validCommitment(commitment);
challenge := commitment;
end macro;

macro respondWithMove(commitment)
begin
if
    /\ challengeOngoing
    /\ validTransition(commitment)
then clearChallenge(commitment.turnNumber);
else
    assert FALSE;
end if;
end macro;

macro respondWithAlternativeMove(commitment)
begin
if
    /\ challengeOngoing
    /\ commitment.turnNumber > channel.challenge.turnNumber + 1
then clearChallenge(commitment.turnNumber);
end if;
end macro;

macro refute(turnNumber)
begin
if
    /\ challengeOngoing
    /\ turnNumber > channel.turnNumber[ParticipantIDX(turnNumber)]
then
channel := [
    mode |-> ChannelMode.OPEN,
    challenge  |-> NULL,
    turnNumber |-> [i \in {ParticipantIDX(turnNumber)} |-> turnNumber] @@ channel.turnNumber  
];
end if;
end macro;

macro forceMove(commitment)
begin
assert validCommitment(commitment);
if
    /\ channelOpen
    /\ progressesChannel(commitment)
then setChallenge(commitment)
end if;

end macro;

fair process adjudicator = "Adjudicator"
begin
(***************************************************************************)
(* This process records submitted channels.                                *)
(***************************************************************************)
Adjudicator:
while
    \/ AliceCanTakeAction
    \/ EveCanTakeAction
do  HandleChallenge:
    if challenge # NULL then
        channel := [ mode |-> ChannelMode.CHALLENGE, challenge |-> challenge ] @@ channel;
        challenge := NULL;
    end if;
end while;
end process;

fair process alice = Alice
begin
(***************************************************************************)
(* Alice has commitments (n - numParticipants)..(n-1).  She wants to end   *)
(* up with commitments (n - numParticipants + 1)..n.                       *)
(*                                                                         *)
(* She is allowed to:                                                      *)
(*   - Call forceMove with any states that she currently has               *)
(*   - Call refute with any state that she has                             *)
(*   - Call respondWithMove or respondWithMove whenever there's an active  *)
(*     challenge where it's her turn to move                               *)
(***************************************************************************)
AliceMoves:
while AliceCanTakeAction
do
    if channel.mode = ChannelMode.CHALLENGE then
        if
            /\ channel.challenge.turnNumber < StartingTurnNumber
        then
            \* Alice has signed commitments from StartingTurnNumber up to LastTurnNumber.
            \* She can therefore call refute with exactly one commitment, according to
            \* the channel's current turnNumber.
            Refute:
                refute(
                    CHOOSE n \in AlicesCommitments : ParticipantIDX(n) = channel.challenge.signer
                );
        elsif
            /\ channel.challenge.turnNumber >= StartingTurnNumber
            /\ AlicesMove(channel.challenge.turnNumber+1)
        then
            Respond:
                respondWithMove([ turnNumber |-> channel.challenge.turnNumber + 1, signer |-> AlicesIDX ]);
        else
            \* If the challenge wasn't cleared, then Alice's strategy has failed, finalizing the channel.
            Finalize:
                channel := [ mode |-> ChannelMode.FINALIZED, turnNumber |-> [p \in ParticipantIDXs |-> channel.challenge.turnNumber] ] @@ channel;
        end if;
    elsif challenge = NULL then
        forceMove([ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ]);
    end if;
end while;
end process;

fair process eve = Eve
begin
(***************************************************************************)
(* Eve can do almost anything.                                             *)
(*                                                                         *)
(*   - She can sign any data with any private key, except she cannot sign  *)
(*     a commitment with Alice's private key when the turn number is       *)
(*     greater than or equal to StartingTurnNumber                         *)
(*   - She can call any adjudicator function, at any time                  *)
(*   - She can front-run any transaction an arbitrary number of times: if  *)
(*     anyone else calls an adjudicator function in a transaction tx, she  *)
(*     can then choose to submit any transaction before tx is mined.       *)
(*   - She can choose not to do anything, thus causing any active          *)
(*     challenge to expire.                                                *)
(***************************************************************************)
EveMoves:
while EveCanTakeAction do
   ForceMove:
    with n \in NumParticipants..LatestTurnNumber, idx \in ParticipantIDXs \ { AlicesIDX } do
        forceMove([ turnNumber |-> n, signer |-> idx ]);
    end with;
end while;
end process;

end algorithm;
*)


\* BEGIN TRANSLATION
VARIABLES channel, challenge, pc

(* define statement *)
challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen == channel.mode = ChannelMode.OPEN
challengerSigIsValid(turnNumber, challenger) ==
    IF AlicesMove(turnNumber)
    THEN challenge = Alice
    ELSE challenger = Eve
progressesChannel(commitment) == commitment.turnNumber >= channel.turnNumber[commitment.signer]
validCommitment(c) == c \in [ turnNumber: Nat, signer: ParticipantIDXs ]
validTransition(commitment) ==
    /\ commitment.turnNumber = channel.challenge.turnNumber + 1
    /\ commitment.signer = ParticipantIDX(commitment.turnNumber)

AliceCanTakeAction == channel.mode # ChannelMode.FINALIZED
EveCanTakeAction == AliceCanTakeAction

Refutable(n) == TRUE
    /\ n % NumParticipants = channel.challenge.signer % NumParticipants
    /\ n > channel.challenge.turnNumber


vars == << channel, challenge, pc >>

ProcSet == {"Adjudicator"} \cup {Alice} \cup {Eve}

Init == (* Global variables *)
        /\ channel = [turnNumber |-> [p \in ParticipantIDXs |-> 0], mode |-> ChannelMode.OPEN, challenge |-> NULL ]
        /\ challenge = NULL
        /\ pc = [self \in ProcSet |-> CASE self = "Adjudicator" -> "Adjudicator"
                                        [] self = Alice -> "AliceMoves"
                                        [] self = Eve -> "EveMoves"]

Adjudicator == /\ pc["Adjudicator"] = "Adjudicator"
               /\ IF \/ AliceCanTakeAction
                     \/ EveCanTakeAction
                     THEN /\ pc' = [pc EXCEPT !["Adjudicator"] = "HandleChallenge"]
                     ELSE /\ pc' = [pc EXCEPT !["Adjudicator"] = "Done"]
               /\ UNCHANGED << channel, challenge >>

HandleChallenge == /\ pc["Adjudicator"] = "HandleChallenge"
                   /\ IF challenge # NULL
                         THEN /\ channel' = [ mode |-> ChannelMode.CHALLENGE, challenge |-> challenge ] @@ channel
                              /\ challenge' = NULL
                         ELSE /\ TRUE
                              /\ UNCHANGED << channel, challenge >>
                   /\ pc' = [pc EXCEPT !["Adjudicator"] = "Adjudicator"]

adjudicator == Adjudicator \/ HandleChallenge

AliceMoves == /\ pc[Alice] = "AliceMoves"
              /\ IF AliceCanTakeAction
                    THEN /\ IF channel.mode = ChannelMode.CHALLENGE
                               THEN /\ IF /\ channel.challenge.turnNumber < StartingTurnNumber
                                          THEN /\ pc' = [pc EXCEPT ![Alice] = "Refute"]
                                          ELSE /\ IF /\ channel.challenge.turnNumber >= StartingTurnNumber
                                                     /\ AlicesMove(channel.challenge.turnNumber+1)
                                                     THEN /\ pc' = [pc EXCEPT ![Alice] = "Respond"]
                                                     ELSE /\ pc' = [pc EXCEPT ![Alice] = "Finalize"]
                                    /\ UNCHANGED challenge
                               ELSE /\ IF challenge = NULL
                                          THEN /\ Assert(validCommitment(([ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ])), 
                                                         "Failure of assertion at line 111, column 1 of macro called at line 175, column 9.")
                                               /\ IF /\ channelOpen
                                                     /\ progressesChannel(([ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ]))
                                                     THEN /\ challenge' = [ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ]
                                                     ELSE /\ TRUE
                                                          /\ UNCHANGED challenge
                                          ELSE /\ TRUE
                                               /\ UNCHANGED challenge
                                    /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
                    ELSE /\ pc' = [pc EXCEPT ![Alice] = "Done"]
                         /\ UNCHANGED challenge
              /\ UNCHANGED channel

Refute == /\ pc[Alice] = "Refute"
          /\ IF /\ challengeOngoing
                /\ (CHOOSE n \in AlicesCommitments : ParticipantIDX(n) = channel.challenge.signer) > channel.turnNumber[ParticipantIDX((CHOOSE n \in AlicesCommitments : ParticipantIDX(n) = channel.challenge.signer))]
                THEN /\ channel' =            [
                                       mode |-> ChannelMode.OPEN,
                                       challenge  |-> NULL,
                                       turnNumber |-> [i \in {ParticipantIDX((CHOOSE n \in AlicesCommitments : ParticipantIDX(n) = channel.challenge.signer))} |-> (CHOOSE n \in AlicesCommitments : ParticipantIDX(n) = channel.challenge.signer)] @@ channel.turnNumber
                                   ]
                ELSE /\ TRUE
                     /\ UNCHANGED channel
          /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
          /\ UNCHANGED challenge

Respond == /\ pc[Alice] = "Respond"
           /\ IF /\ challengeOngoing
                 /\ validTransition(([ turnNumber |-> channel.challenge.turnNumber + 1, signer |-> AlicesIDX ]))
                 THEN /\ Assert((([ turnNumber |-> channel.challenge.turnNumber + 1, signer |-> AlicesIDX ]).turnNumber) \in Nat, 
                                "Failure of assertion at line 64, column 1 of macro called at line 168, column 17.")
                      /\ channel' = [ mode |-> ChannelMode.OPEN, turnNumber |-> [p \in ParticipantIDXs |-> Maximum(channel.turnNumber[p], (([ turnNumber |-> channel.challenge.turnNumber + 1, signer |-> AlicesIDX ]).turnNumber))], challenge |-> NULL ]
                 ELSE /\ Assert(FALSE, 
                                "Failure of assertion at line 82, column 5 of macro called at line 168, column 17.")
                      /\ UNCHANGED channel
           /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
           /\ UNCHANGED challenge

Finalize == /\ pc[Alice] = "Finalize"
            /\ channel' = [ mode |-> ChannelMode.FINALIZED, turnNumber |-> [p \in ParticipantIDXs |-> channel.challenge.turnNumber] ] @@ channel
            /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
            /\ UNCHANGED challenge

alice == AliceMoves \/ Refute \/ Respond \/ Finalize

EveMoves == /\ pc[Eve] = "EveMoves"
            /\ IF EveCanTakeAction
                  THEN /\ pc' = [pc EXCEPT ![Eve] = "ForceMove"]
                  ELSE /\ pc' = [pc EXCEPT ![Eve] = "Done"]
            /\ UNCHANGED << channel, challenge >>

ForceMove == /\ pc[Eve] = "ForceMove"
             /\ \E n \in NumParticipants..LatestTurnNumber:
                  \E idx \in ParticipantIDXs \ { AlicesIDX }:
                    /\ Assert(validCommitment(([ turnNumber |-> n, signer |-> idx ])), 
                              "Failure of assertion at line 111, column 1 of macro called at line 199, column 9.")
                    /\ IF /\ channelOpen
                          /\ progressesChannel(([ turnNumber |-> n, signer |-> idx ]))
                          THEN /\ challenge' = [ turnNumber |-> n, signer |-> idx ]
                          ELSE /\ TRUE
                               /\ UNCHANGED challenge
             /\ pc' = [pc EXCEPT ![Eve] = "EveMoves"]
             /\ UNCHANGED channel

eve == EveMoves \/ ForceMove

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
AllowedChallenges == [ turnNumber: AllowedTurnNumbers, signer: ParticipantIDXs ] \cup { NULL }
AllowedChannels == [ turnNumber: [ParticipantIDXs -> Nat] , mode: Range(ChannelMode), challenge: AllowedChallenges ]

\* Safety properties

TypeOK ==
  /\ channel   \in AllowedChannels
  /\ challenge \in AllowedChallenges
  
\* Liveness properties
AliceCanProgressChannel == <>[](
    /\ channel.mode = ChannelMode.OPEN
    /\ channel.turnNumber[AlicesIDX] = AlicesGoalTurnNumber
)

FinalizedWithLatestTurnNumber == <>[](
    /\ channel.mode = ChannelMode.FINALIZED
    /\ channel.turnNumber[AlicesIDX] = LatestTurnNumber
)

AliceDoesNotLoseFunds ==
    \/ AliceCanProgressChannel
    \/ FinalizedWithLatestTurnNumber

\* By checking this property, we can verify Alice's ability to front-run and replace Alice's pending challenge with another challenge.
EveDoesNotFrontRun == [][
    \/ challenge = NULL
    \/ challenge' = NULL
]_<<challenge>>

=============================================================================
\* Modification History
\* Last modified Tue Sep 03 14:59:29 PDT 2019 by andrewstewart
\* Created Tue Aug 06 14:38:11 MDT 2019 by andrewstewart
