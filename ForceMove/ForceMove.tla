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

ASSUME
  /\ StartingTurnNumber \in Nat
  /\ NumParticipants \in Nat \ { 1 }
  /\ AlicesIDX \in ParticipantIDXs
            
(* --algorithm forceMove

variables
    channel = [turnNumber |-> 0, mode |-> ChannelMode.OPEN ],
    challenge = NULL

define
alicesMove(turnNumber) == (turnNumber % NumParticipants) = AlicesIDX
challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen == channel.mode = ChannelMode.OPEN
challengerSigIsValid(turnNumber, challenger) ==
    IF alicesMove(turnNumber)
    THEN challenge = Alice
    ELSE challenger = Eve
progressesChannel(turnNumber) == turnNumber > channel.turnNumber
validCommitment(c) == c \in [ turnNumber: Nat, signer: ParticipantIDXs ]
validTransition(c, s) ==
    /\ c.turnNumber = channel.turnNumber + 1
    /\ IF alicesMove(channel.turnNumber) THEN s = Alice ELSE s = Eve
end define;

macro clearChallenge(turnNumber)
begin
assert turnNumber \in Nat;
channel := [ mode |-> ChannelMode.OPEN, turnNumber |-> turnNumber ];
end macro;

macro setChallenge(commitment)
begin
\*assert validCommitment(commitment);
challenge := commitment;
end macro;

macro respondWithMove(commitment, signer)
begin
if
    /\ challengeOngoing
    /\ validTransition(commitment, signer)
then clearChallenge(commitment.turnNumber);
end if;
end macro;

macro respondWithAlternativeMove(commitment, signer)
\* turnNumber is the turn number of the last state in the round.
begin
if
    /\ challengeOngoing
    /\ commitment.turnNumber > channel.turnNumber
then clearChallenge(commitment.turnNumber);
end if;
end macro;

macro refute(turnNumber)
begin
if
    /\ challengeOngoing
    /\ turnNumber > channel.turnNumber
then clearChallenge(channel.turnNumber);
end if;
end macro;

macro forceMove(commitment)
begin
assert validCommitment(commitment);
if
    /\ channelOpen
    /\ progressesChannel(commitment.turnNumber)
then setChallenge(commitment)
end if;

end macro;

fair process adjudicator = "Adjudicator"
begin
(***************************************************************************)
(* This process expires active channels and records submitted              *)
(* channels.                                                               *)
(***************************************************************************)
HandleChallenge:
while channel.mode # ChannelMode.FINALIZED
do 
    await \/ channel.mode = ChannelMode.CHALLENGE
          \/ challenge # NULL;
    if challenge = NULL
    then
        assert channel.mode = ChannelMode.CHALLENGE;
        channel := [ mode |-> ChannelMode.FINALIZED, turnNumber |-> channel.turnNumber ];
    else
        assert challenge # NULL;
        channel := [ mode |-> ChannelMode.CHALLENGE ] @@ challenge;
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
while channel.turnNumber < AlicesGoalTurnNumber do
    either
        await channel.mode = ChannelMode.CHALLENGE;
        if
            /\ alicesMove(channel.turnNumber)
            /\ channel.turnNumber >= StartingTurnNumber
        then
            RespondWithMove:
                respondWithMove([ turnNumber |-> channel.turnNumber + 1 ], Alice);
        elsif FALSE then RespondWithAlternativeMove: skip;
        elsif
            /\ channel.turnNumber < StartingTurnNumber
        then
            Refute:
                \* Alice has signed commitments from StartingTurnNumber up to LastTurnNumber.
                \* She can therefore call refute with exactly one commitment, according to
                \* the channel's current turnNumber.
                \* 1. Get the challenger's idx
                \* 2. Refute with the proper turn number
                refute(1);
        end if;
    or
        await channel.mode = ChannelMode.OPEN;
        ForceMove: forceMove([ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ]);
    end either;
    
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
while TRUE do
    either
       ForceMove:
        with n \in NumParticipants..StartingTurnNumber, idx \in ParticipantIDXs \ { AlicesIDX } do
            forceMove([ turnNumber |-> n, signer |-> idx ]);
        end with;
    or RespondWithMove: skip;
    or RespondWithAlternativeMove: skip;
    or Refute: skip
    or Sleep: skip;
    end either;
end while;
end process;

end algorithm;
*)


\* BEGIN TRANSLATION
\* Label RespondWithMove of process alice at line 64 col 1 changed to RespondWithMove_
\* Label RespondWithAlternativeMove of process alice at line 146 col 54 changed to RespondWithAlternativeMove_
\* Label Refute of process alice at line 83 col 1 changed to Refute_
\* Label ForceMove of process alice at line 92 col 1 changed to ForceMove_
VARIABLES channel, challenge, pc

(* define statement *)
alicesMove(turnNumber) == (turnNumber % NumParticipants) = AlicesIDX
challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen == channel.mode = ChannelMode.OPEN
challengerSigIsValid(turnNumber, challenger) ==
    IF alicesMove(turnNumber)
    THEN challenge = Alice
    ELSE challenger = Eve
progressesChannel(turnNumber) == turnNumber > channel.turnNumber
validCommitment(c) == c \in [ turnNumber: Nat, signer: ParticipantIDXs ]
validTransition(c, s) ==
    /\ c.turnNumber = channel.turnNumber + 1
    /\ IF alicesMove(channel.turnNumber) THEN s = Alice ELSE s = Eve


vars == << channel, challenge, pc >>

ProcSet == {"Adjudicator"} \cup {Alice} \cup {Eve}

Init == (* Global variables *)
        /\ channel = [turnNumber |-> 0, mode |-> ChannelMode.OPEN ]
        /\ challenge = NULL
        /\ pc = [self \in ProcSet |-> CASE self = "Adjudicator" -> "HandleChallenge"
                                        [] self = Alice -> "AliceMoves"
                                        [] self = Eve -> "EveMoves"]

HandleChallenge == /\ pc["Adjudicator"] = "HandleChallenge"
                   /\ IF channel.mode # ChannelMode.FINALIZED
                         THEN /\ \/ channel.mode = ChannelMode.CHALLENGE
                                 \/ challenge # NULL
                              /\ IF challenge = NULL
                                    THEN /\ Assert(channel.mode = ChannelMode.CHALLENGE, 
                                                   "Failure of assertion at line 114, column 9.")
                                         /\ channel' = [ mode |-> ChannelMode.FINALIZED, turnNumber |-> channel.turnNumber ]
                                         /\ UNCHANGED challenge
                                    ELSE /\ Assert(challenge # NULL, 
                                                   "Failure of assertion at line 117, column 9.")
                                         /\ channel' = [ mode |-> ChannelMode.CHALLENGE ] @@ challenge
                                         /\ challenge' = NULL
                              /\ pc' = [pc EXCEPT !["Adjudicator"] = "HandleChallenge"]
                         ELSE /\ pc' = [pc EXCEPT !["Adjudicator"] = "Done"]
                              /\ UNCHANGED << channel, challenge >>

adjudicator == HandleChallenge

AliceMoves == /\ pc[Alice] = "AliceMoves"
              /\ IF channel.turnNumber < AlicesGoalTurnNumber
                    THEN /\ \/ /\ channel.mode = ChannelMode.CHALLENGE
                               /\ IF /\ alicesMove(channel.turnNumber)
                                     /\ channel.turnNumber >= StartingTurnNumber
                                     THEN /\ pc' = [pc EXCEPT ![Alice] = "RespondWithMove_"]
                                     ELSE /\ IF FALSE
                                                THEN /\ pc' = [pc EXCEPT ![Alice] = "RespondWithAlternativeMove_"]
                                                ELSE /\ IF /\ channel.turnNumber < StartingTurnNumber
                                                           THEN /\ pc' = [pc EXCEPT ![Alice] = "Refute_"]
                                                           ELSE /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
                            \/ /\ channel.mode = ChannelMode.OPEN
                               /\ pc' = [pc EXCEPT ![Alice] = "ForceMove_"]
                    ELSE /\ pc' = [pc EXCEPT ![Alice] = "Done"]
              /\ UNCHANGED << channel, challenge >>

RespondWithMove_ == /\ pc[Alice] = "RespondWithMove_"
                    /\ IF /\ challengeOngoing
                          /\ validTransition(([ turnNumber |-> channel.turnNumber + 1 ]), Alice)
                          THEN /\ Assert((([ turnNumber |-> channel.turnNumber + 1 ]).turnNumber) \in Nat, 
                                         "Failure of assertion at line 52, column 1 of macro called at line 145, column 17.")
                               /\ channel' = [ mode |-> ChannelMode.OPEN, turnNumber |-> (([ turnNumber |-> channel.turnNumber + 1 ]).turnNumber) ]
                          ELSE /\ TRUE
                               /\ UNCHANGED channel
                    /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
                    /\ UNCHANGED challenge

RespondWithAlternativeMove_ == /\ pc[Alice] = "RespondWithAlternativeMove_"
                               /\ TRUE
                               /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
                               /\ UNCHANGED << channel, challenge >>

Refute_ == /\ pc[Alice] = "Refute_"
           /\ IF /\ challengeOngoing
                 /\ 1 > channel.turnNumber
                 THEN /\ Assert((channel.turnNumber) \in Nat, 
                                "Failure of assertion at line 52, column 1 of macro called at line 156, column 17.")
                      /\ channel' = [ mode |-> ChannelMode.OPEN, turnNumber |-> (channel.turnNumber) ]
                 ELSE /\ TRUE
                      /\ UNCHANGED channel
           /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
           /\ UNCHANGED challenge

ForceMove_ == /\ pc[Alice] = "ForceMove_"
              /\ Assert(validCommitment(([ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ])), 
                        "Failure of assertion at line 92, column 1 of macro called at line 160, column 20.")
              /\ IF /\ channelOpen
                    /\ progressesChannel(([ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ]).turnNumber)
                    THEN /\ challenge' = [ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ]
                    ELSE /\ TRUE
                         /\ UNCHANGED challenge
              /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
              /\ UNCHANGED channel

alice == AliceMoves \/ RespondWithMove_ \/ RespondWithAlternativeMove_
            \/ Refute_ \/ ForceMove_

EveMoves == /\ pc[Eve] = "EveMoves"
            /\ \/ /\ pc' = [pc EXCEPT ![Eve] = "ForceMove"]
               \/ /\ pc' = [pc EXCEPT ![Eve] = "RespondWithMove"]
               \/ /\ pc' = [pc EXCEPT ![Eve] = "RespondWithAlternativeMove"]
               \/ /\ pc' = [pc EXCEPT ![Eve] = "Refute"]
               \/ /\ pc' = [pc EXCEPT ![Eve] = "Sleep"]
            /\ UNCHANGED << channel, challenge >>

ForceMove == /\ pc[Eve] = "ForceMove"
             /\ \E n \in NumParticipants..StartingTurnNumber:
                  \E idx \in ParticipantIDXs \ { AlicesIDX }:
                    /\ Assert(validCommitment(([ turnNumber |-> n, signer |-> idx ])), 
                              "Failure of assertion at line 92, column 1 of macro called at line 186, column 13.")
                    /\ IF /\ channelOpen
                          /\ progressesChannel(([ turnNumber |-> n, signer |-> idx ]).turnNumber)
                          THEN /\ challenge' = [ turnNumber |-> n, signer |-> idx ]
                          ELSE /\ TRUE
                               /\ UNCHANGED challenge
             /\ pc' = [pc EXCEPT ![Eve] = "EveMoves"]
             /\ UNCHANGED channel

RespondWithMove == /\ pc[Eve] = "RespondWithMove"
                   /\ TRUE
                   /\ pc' = [pc EXCEPT ![Eve] = "EveMoves"]
                   /\ UNCHANGED << channel, challenge >>

RespondWithAlternativeMove == /\ pc[Eve] = "RespondWithAlternativeMove"
                              /\ TRUE
                              /\ pc' = [pc EXCEPT ![Eve] = "EveMoves"]
                              /\ UNCHANGED << channel, challenge >>

Refute == /\ pc[Eve] = "Refute"
          /\ TRUE
          /\ pc' = [pc EXCEPT ![Eve] = "EveMoves"]
          /\ UNCHANGED << channel, challenge >>

Sleep == /\ pc[Eve] = "Sleep"
         /\ TRUE
         /\ pc' = [pc EXCEPT ![Eve] = "EveMoves"]
         /\ UNCHANGED << channel, challenge >>

eve == EveMoves \/ ForceMove \/ RespondWithMove
          \/ RespondWithAlternativeMove \/ Refute \/ Sleep

Next == adjudicator \/ alice \/ eve

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(adjudicator)
        /\ WF_vars(alice)
        /\ WF_vars(eve)

\* END TRANSLATION

AllowedTurnNumbers == 0..(StartingTurnNumber + NumParticipants)
AllowedChannels == {}
  \cup [ turnNumber: AllowedTurnNumbers, mode: { ChannelMode.OPEN, ChannelMode.FINALIZED } ]
  \cup [ turnNumber: AllowedTurnNumbers, mode: { ChannelMode.CHALLENGE }, signer: ParticipantIDXs ]
AllowedChallenges == { NULL }
  \cup [ turnNumber: AllowedTurnNumbers, signer: ParticipantIDXs ]


\* Safety properties

TypeOK ==
  /\ channel \in AllowedChannels
  /\ challenge \in AllowedChallenges
  
\* Liveness properties
AliceCanProgressChannel == <>[](
    /\ channel.mode = ChannelMode.OPEN
    /\ channel.turnNumber = AlicesGoalTurnNumber
)

FinalizedWithLatestTurnNumber == <>[](
    /\ channel.mode = ChannelMode.FINALIZED
    /\ channel.turnNumber = LatestTurnNumber
)

AliceDoesNotLoseFunds ==
    \/ AliceCanProgressChannel
    \/ FinalizedWithLatestTurnNumber

=============================================================================
\* Modification History
\* Last modified Wed Aug 28 12:11:37 MDT 2019 by andrewstewart
\* Created Tue Aug 06 14:38:11 MDT 2019 by andrewstewart
