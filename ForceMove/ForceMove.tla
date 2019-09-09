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


TX_Type == [
  FORCE_MOVE |-> "FORCE_MOVE"
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
            
(* --algorithm submitForceMove

variables
    channel = [turnNumber |-> [p \in ParticipantIDXs |-> 0], mode |-> ChannelMode.OPEN, challenge |-> NULL ],
    submittedTX = NULL

define
challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen == channel.mode = ChannelMode.OPEN
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
channel := [
    mode |-> ChannelMode.OPEN,
    turnNumber |-> [p \in ParticipantIDXs |-> Maximum(channel.turnNumber[p], turnNumber)],
    challenge |-> NULL
];
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
if
    /\ channelOpen
    /\ progressesChannel(commitment)
then
    channel := [ mode |-> ChannelMode.CHALLENGE, challenge |-> commitment ] @@ channel;
end if;
end macro;

macro submitForceMove(commitment)
begin
assert submittedTX = NULL;
submittedTX := [ commitment |-> commitment, type |-> TX_Type.FORCE_MOVE ];
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
do
    if submittedTX # NULL then
        forceMove(submittedTX.commitment);
        submittedTX := NULL;
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
(*   - Call submitForceMove with any states that she currently has               *)
(*   - Call refute with any state that she has                             *)
(*   - Call respondWithMove or respondWithMove whenever there's an active  *)
(*     challenge where it's her turn to move                               *)
(***************************************************************************)
AliceMoves:
while AliceCanTakeAction
do
    if challengeOngoing then
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
            \* Alice has run out of allowed actions, resulting in the channel being finalized
            Finalize:
                channel := [ mode |-> ChannelMode.FINALIZED, turnNumber |-> [p \in ParticipantIDXs |-> channel.challenge.turnNumber] ] @@ channel;
        end if;
    elsif submittedTX # NULL then
        submitForceMove([ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ]);
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
    either ForceMove:
        with n \in NumParticipants..LatestTurnNumber,
             idx \in ParticipantIDXs \ { AlicesIDX }
        do
            forceMove([ turnNumber |-> n, signer |-> idx ]);
        end with;
    or Respond:
        if
            /\ challengeOngoing
            /\ ~AlicesMove(channel.challenge.turnNumber)
        then skip;
\*            respondWithMove([
\*                turnNumber |-> channel.challenge.turnNumber + 1,
\*                signer |-> ParticipantIDX(channel.challenge.turnNumber)
\*            ]);
        end if;
    or Refute:
        if
            /\ challengeOngoing
            /\ ~AlicesMove(channel.challenge.turnNumber)
        then skip;
        end if;
    end either;
end while;
end process;

end algorithm;
*)


\* BEGIN TRANSLATION
\* Label Refute of process alice at line 96 col 1 changed to Refute_
\* Label Respond of process alice at line 76 col 1 changed to Respond_
VARIABLES channel, submittedTX, pc

(* define statement *)
challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen == channel.mode = ChannelMode.OPEN
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


vars == << channel, submittedTX, pc >>

ProcSet == {"Adjudicator"} \cup {Alice} \cup {Eve}

Init == (* Global variables *)
        /\ channel = [turnNumber |-> [p \in ParticipantIDXs |-> 0], mode |-> ChannelMode.OPEN, challenge |-> NULL ]
        /\ submittedTX = NULL
        /\ pc = [self \in ProcSet |-> CASE self = "Adjudicator" -> "Adjudicator"
                                        [] self = Alice -> "AliceMoves"
                                        [] self = Eve -> "EveMoves"]

Adjudicator == /\ pc["Adjudicator"] = "Adjudicator"
               /\ IF \/ AliceCanTakeAction
                     \/ EveCanTakeAction
                     THEN /\ IF submittedTX # NULL
                                THEN /\ IF /\ channelOpen
                                           /\ progressesChannel((submittedTX.commitment))
                                           THEN /\ channel' = [ mode |-> ChannelMode.CHALLENGE, challenge |-> (submittedTX.commitment) ] @@ channel
                                           ELSE /\ TRUE
                                                /\ UNCHANGED channel
                                     /\ submittedTX' = NULL
                                ELSE /\ TRUE
                                     /\ UNCHANGED << channel, submittedTX >>
                          /\ pc' = [pc EXCEPT !["Adjudicator"] = "Adjudicator"]
                     ELSE /\ pc' = [pc EXCEPT !["Adjudicator"] = "Done"]
                          /\ UNCHANGED << channel, submittedTX >>

adjudicator == Adjudicator

AliceMoves == /\ pc[Alice] = "AliceMoves"
              /\ IF AliceCanTakeAction
                    THEN /\ IF challengeOngoing
                               THEN /\ IF /\ channel.challenge.turnNumber < StartingTurnNumber
                                          THEN /\ pc' = [pc EXCEPT ![Alice] = "Refute_"]
                                          ELSE /\ IF /\ channel.challenge.turnNumber >= StartingTurnNumber
                                                     /\ AlicesMove(channel.challenge.turnNumber+1)
                                                     THEN /\ pc' = [pc EXCEPT ![Alice] = "Respond_"]
                                                     ELSE /\ pc' = [pc EXCEPT ![Alice] = "Finalize"]
                                    /\ UNCHANGED submittedTX
                               ELSE /\ IF submittedTX # NULL
                                          THEN /\ Assert(submittedTX = NULL, 
                                                         "Failure of assertion at line 120, column 1 of macro called at line 179, column 9.")
                                               /\ submittedTX' = [ commitment |-> ([ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ]), type |-> TX_Type.FORCE_MOVE ]
                                          ELSE /\ TRUE
                                               /\ UNCHANGED submittedTX
                                    /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
                    ELSE /\ pc' = [pc EXCEPT ![Alice] = "Done"]
                         /\ UNCHANGED submittedTX
              /\ UNCHANGED channel

Refute_ == /\ pc[Alice] = "Refute_"
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
           /\ UNCHANGED submittedTX

Respond_ == /\ pc[Alice] = "Respond_"
            /\ IF /\ challengeOngoing
                  /\ validTransition(([ turnNumber |-> channel.challenge.turnNumber + 1, signer |-> AlicesIDX ]))
                  THEN /\ Assert((([ turnNumber |-> channel.challenge.turnNumber + 1, signer |-> AlicesIDX ]).turnNumber) \in Nat, 
                                 "Failure of assertion at line 66, column 1 of macro called at line 172, column 17.")
                       /\ channel' =            [
                                         mode |-> ChannelMode.OPEN,
                                         turnNumber |-> [p \in ParticipantIDXs |-> Maximum(channel.turnNumber[p], (([ turnNumber |-> channel.challenge.turnNumber + 1, signer |-> AlicesIDX ]).turnNumber))],
                                         challenge |-> NULL
                                     ]
                  ELSE /\ Assert(FALSE, 
                                 "Failure of assertion at line 81, column 5 of macro called at line 172, column 17.")
                       /\ UNCHANGED channel
            /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
            /\ UNCHANGED submittedTX

Finalize == /\ pc[Alice] = "Finalize"
            /\ channel' = [ mode |-> ChannelMode.FINALIZED, turnNumber |-> [p \in ParticipantIDXs |-> channel.challenge.turnNumber] ] @@ channel
            /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
            /\ UNCHANGED submittedTX

alice == AliceMoves \/ Refute_ \/ Respond_ \/ Finalize

EveMoves == /\ pc[Eve] = "EveMoves"
            /\ IF EveCanTakeAction
                  THEN /\ \/ /\ pc' = [pc EXCEPT ![Eve] = "ForceMove"]
                          \/ /\ pc' = [pc EXCEPT ![Eve] = "Respond"]
                          \/ /\ pc' = [pc EXCEPT ![Eve] = "Refute"]
                  ELSE /\ pc' = [pc EXCEPT ![Eve] = "Done"]
            /\ UNCHANGED << channel, submittedTX >>

ForceMove == /\ pc[Eve] = "ForceMove"
             /\ \E n \in NumParticipants..LatestTurnNumber:
                  \E idx \in ParticipantIDXs \ { AlicesIDX }:
                    IF /\ channelOpen
                       /\ progressesChannel(([ turnNumber |-> n, signer |-> idx ]))
                       THEN /\ channel' = [ mode |-> ChannelMode.CHALLENGE, challenge |-> ([ turnNumber |-> n, signer |-> idx ]) ] @@ channel
                       ELSE /\ TRUE
                            /\ UNCHANGED channel
             /\ pc' = [pc EXCEPT ![Eve] = "EveMoves"]
             /\ UNCHANGED submittedTX

Respond == /\ pc[Eve] = "Respond"
           /\ IF /\ challengeOngoing
                 /\ ~AlicesMove(channel.challenge.turnNumber)
                 THEN /\ TRUE
                 ELSE /\ TRUE
           /\ pc' = [pc EXCEPT ![Eve] = "EveMoves"]
           /\ UNCHANGED << channel, submittedTX >>

Refute == /\ pc[Eve] = "Refute"
          /\ IF /\ challengeOngoing
                /\ ~AlicesMove(channel.challenge.turnNumber)
                THEN /\ TRUE
                ELSE /\ TRUE
          /\ pc' = [pc EXCEPT ![Eve] = "EveMoves"]
          /\ UNCHANGED << channel, submittedTX >>

eve == EveMoves \/ ForceMove \/ Respond \/ Refute

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
AllowedCommitments == [ turnNumber: AllowedTurnNumbers, signer: ParticipantIDXs ]

AllowedTransactions == { NULL }
    \cup [ type: { TX_Type.FORCE_MOVE }, commitment: AllowedCommitments ]

AllowedChannels == [ turnNumber: [ParticipantIDXs -> Nat] , mode: Range(ChannelMode), challenge: AllowedCommitments \cup { NULL } ]

\* Safety properties

TypeOK ==
  /\ channel \in AllowedChannels
  /\ submittedTX \in AllowedTransactions
  
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


=============================================================================
\* Modification History
\* Last modified Mon Sep 09 15:19:03 MDT 2019 by andrewstewart
\* Created Tue Aug 06 14:38:11 MDT 2019 by andrewstewart
