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

ASSUME
  /\ StartingTurnNumber \in Nat
  /\ NumParticipants \in Nat \ { 1 }
  /\ AlicesIDX \in 1..NumParticipants
            
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
validCommitment(c) == c \in [ turnNumber: Nat ]
validTransition(c, s) ==
    /\ c.turnNumber = channel.turnNumber + 1
    /\ IF alicesMove(channel.turnNumber) THEN s = Alice ELSE s = Eve
end define;

macro clearChallenge(commitment)
begin
assert validCommitment(commitment);
channel := [ mode |-> ChannelMode.OPEN ] @@ commitment;
end macro;

macro setChallenge(commitment)
begin
assert validCommitment(commitment);
challenge := commitment;
end macro;

macro respondWithMove(commitment, signer)
begin
if
    /\ challengeOngoing
    /\ validTransition(commitment, signer)
then clearChallenge(commitment);
end if;
end macro;

macro respondWithAlternativeMove(commitment, signer)
\* turnNumber is the turn number of the last state in the round.
begin
if
    /\ challengeOngoing
    /\ commitment.turnNumber > channel.turnNumber
then clearChallenge(commitment);
end if;
end macro;

macro refute(commitment)
begin
if
    /\ challengeOngoing
    /\ commitment.turnNumber > channel.turnNumber
then clearChallenge(commitment);
end if;
end macro;

macro forceMove(commitment, challenger)
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
        channel := [ turnNumber |-> challenge.turnNumber, mode |-> ChannelMode.CHALLENGE ];
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
                assert ~alicesMove(channel.turnNumber);
                \* Alice has signed commitments from StartingTurnNumber up to LastTurnNumber.
                \* She can therefore call refute with exactly one commitment, according to
                \* the channel's current turnNumber.
                skip; \* TODO
        end if;
    or
        await channel.mode = ChannelMode.OPEN;
        ForceMove: forceMove([ turnNumber |-> LatestTurnNumber ], Alice);
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
        with n \in NumParticipants..StartingTurnNumber do
            forceMove([ turnNumber |-> n ], Eve);
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
\* Label RespondWithMove of process alice at line 63 col 1 changed to RespondWithMove_
\* Label Refute of process alice at line 148 col 33 changed to Refute_
\* Label ForceMove of process alice at line 91 col 1 changed to ForceMove_
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
validCommitment(c) == c \in [ turnNumber: Nat ]
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
                                                   "Failure of assertion at line 118, column 9.")
                                         /\ channel' = [ turnNumber |-> challenge.turnNumber, mode |-> ChannelMode.CHALLENGE ]
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
                                     ELSE /\ IF TRUE
                                                THEN /\ pc' = [pc EXCEPT ![Alice] = "Refute_"]
                                                ELSE /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
                            \/ /\ channel.mode = ChannelMode.OPEN
                               /\ pc' = [pc EXCEPT ![Alice] = "ForceMove_"]
                    ELSE /\ pc' = [pc EXCEPT ![Alice] = "Done"]
              /\ UNCHANGED << channel, challenge >>

RespondWithMove_ == /\ pc[Alice] = "RespondWithMove_"
                    /\ IF /\ challengeOngoing
                          /\ validTransition(([ turnNumber |-> channel.turnNumber + 1 ]), Alice)
                          THEN /\ Assert(validCommitment(([ turnNumber |-> channel.turnNumber + 1 ])), 
                                         "Failure of assertion at line 51, column 1 of macro called at line 146, column 17.")
                               /\ channel' = [ mode |-> ChannelMode.OPEN ] @@ ([ turnNumber |-> channel.turnNumber + 1 ])
                          ELSE /\ TRUE
                               /\ UNCHANGED channel
                    /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
                    /\ UNCHANGED challenge

Refute_ == /\ pc[Alice] = "Refute_"
           /\ TRUE
           /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
           /\ UNCHANGED << channel, challenge >>

ForceMove_ == /\ pc[Alice] = "ForceMove_"
              /\ Assert(validCommitment(([ turnNumber |-> LatestTurnNumber ])), 
                        "Failure of assertion at line 91, column 1 of macro called at line 152, column 20.")
              /\ IF /\ channelOpen
                    /\ progressesChannel(([ turnNumber |-> LatestTurnNumber ]).turnNumber)
                    THEN /\ Assert(validCommitment(([ turnNumber |-> LatestTurnNumber ])), 
                                   "Failure of assertion at line 57, column 1 of macro called at line 152, column 20.")
                         /\ challenge' = [ turnNumber |-> LatestTurnNumber ]
                    ELSE /\ TRUE
                         /\ UNCHANGED challenge
              /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
              /\ UNCHANGED channel

alice == AliceMoves \/ RespondWithMove_ \/ Refute_ \/ ForceMove_

EveMoves == /\ pc[Eve] = "EveMoves"
            /\ \/ /\ pc' = [pc EXCEPT ![Eve] = "ForceMove"]
               \/ /\ pc' = [pc EXCEPT ![Eve] = "RespondWithMove"]
               \/ /\ pc' = [pc EXCEPT ![Eve] = "RespondWithAlternativeMove"]
               \/ /\ pc' = [pc EXCEPT ![Eve] = "Refute"]
               \/ /\ pc' = [pc EXCEPT ![Eve] = "Sleep"]
            /\ UNCHANGED << channel, challenge >>

ForceMove == /\ pc[Eve] = "ForceMove"
             /\ \E n \in NumParticipants..StartingTurnNumber:
                  /\ Assert(validCommitment(([ turnNumber |-> n ])), 
                            "Failure of assertion at line 91, column 1 of macro called at line 178, column 13.")
                  /\ IF /\ channelOpen
                        /\ progressesChannel(([ turnNumber |-> n ]).turnNumber)
                        THEN /\ Assert(validCommitment(([ turnNumber |-> n ])), 
                                       "Failure of assertion at line 57, column 1 of macro called at line 178, column 13.")
                             /\ challenge' = [ turnNumber |-> n ]
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
AllowedChannels ==
  [
    turnNumber: AllowedTurnNumbers,
    mode: Range(ChannelMode)
  ]


\* Safety properties

TypeOK ==
  /\ channel \in AllowedChannels
  
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
\* Last modified Wed Aug 28 11:39:40 MDT 2019 by andrewstewart
\* Created Tue Aug 06 14:38:11 MDT 2019 by andrewstewart
