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
(* This process records submitted channels.                                *)
(***************************************************************************)
Adjudicator:
while channel.mode # ChannelMode.FINALIZED
do  HandleChallenge:
    if challenge # NULL then
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
while
    /\ channel.turnNumber < AlicesGoalTurnNumber
    /\ channel.mode # ChannelMode.FINALIZED
do
    if channel.mode = ChannelMode.CHALLENGE then
        if
            /\ alicesMove(channel.turnNumber)
            /\ channel.turnNumber >= StartingTurnNumber
        then respondWithMove([ turnNumber |-> channel.turnNumber + 1 ], Alice);
        elsif FALSE then skip;
        elsif
            /\ channel.turnNumber < StartingTurnNumber
        then
            \* Alice has signed commitments from StartingTurnNumber up to LastTurnNumber.
            \* She can therefore call refute with exactly one commitment, according to
            \* the channel's current turnNumber.
            \* 1. Get the challenger's idx
            \* 2. Refute with the proper turn number
            refute(CHOOSE n \in AlicesCommitments : n % NumParticipants = channel.signer % NumParticipants);
        end if;
        
        \* If the challenge wasn't cleared, then Alice's strategy has failed, finalizing the channel.
        if channel.mode = ChannelMode.CHALLENGE then
            FinalizeChannel: 
            channel := [ mode |-> ChannelMode.FINALIZED, turnNumber |-> channel.turnNumber ];
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
while channel.mode # ChannelMode.FINALIZED do
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
        /\ pc = [self \in ProcSet |-> CASE self = "Adjudicator" -> "Adjudicator"
                                        [] self = Alice -> "AliceMoves"
                                        [] self = Eve -> "EveMoves"]

Adjudicator == /\ pc["Adjudicator"] = "Adjudicator"
               /\ IF channel.mode # ChannelMode.FINALIZED
                     THEN /\ pc' = [pc EXCEPT !["Adjudicator"] = "HandleChallenge"]
                     ELSE /\ pc' = [pc EXCEPT !["Adjudicator"] = "Done"]
               /\ UNCHANGED << channel, challenge >>

HandleChallenge == /\ pc["Adjudicator"] = "HandleChallenge"
                   /\ IF challenge # NULL
                         THEN /\ channel' = [ mode |-> ChannelMode.CHALLENGE ] @@ challenge
                              /\ challenge' = NULL
                         ELSE /\ TRUE
                              /\ UNCHANGED << channel, challenge >>
                   /\ pc' = [pc EXCEPT !["Adjudicator"] = "Adjudicator"]

adjudicator == Adjudicator \/ HandleChallenge

AliceMoves == /\ pc[Alice] = "AliceMoves"
              /\ IF /\ channel.turnNumber < AlicesGoalTurnNumber
                    /\ channel.mode # ChannelMode.FINALIZED
                    THEN /\ IF channel.mode = ChannelMode.CHALLENGE
                               THEN /\ IF /\ alicesMove(channel.turnNumber)
                                          /\ channel.turnNumber >= StartingTurnNumber
                                          THEN /\ IF /\ challengeOngoing
                                                     /\ validTransition(([ turnNumber |-> channel.turnNumber + 1 ]), Alice)
                                                     THEN /\ Assert((([ turnNumber |-> channel.turnNumber + 1 ]).turnNumber) \in Nat, 
                                                                    "Failure of assertion at line 53, column 1 of macro called at line 138, column 14.")
                                                          /\ channel' = [ mode |-> ChannelMode.OPEN, turnNumber |-> (([ turnNumber |-> channel.turnNumber + 1 ]).turnNumber) ]
                                                     ELSE /\ TRUE
                                                          /\ UNCHANGED channel
                                          ELSE /\ IF FALSE
                                                     THEN /\ TRUE
                                                          /\ UNCHANGED channel
                                                     ELSE /\ IF /\ channel.turnNumber < StartingTurnNumber
                                                                THEN /\ IF /\ challengeOngoing
                                                                           /\ (CHOOSE n \in AlicesCommitments : n % NumParticipants = channel.signer % NumParticipants) > channel.turnNumber
                                                                           THEN /\ Assert((channel.turnNumber) \in Nat, 
                                                                                          "Failure of assertion at line 53, column 1 of macro called at line 148, column 13.")
                                                                                /\ channel' = [ mode |-> ChannelMode.OPEN, turnNumber |-> (channel.turnNumber) ]
                                                                           ELSE /\ TRUE
                                                                                /\ UNCHANGED channel
                                                                ELSE /\ TRUE
                                                                     /\ UNCHANGED channel
                                    /\ IF channel'.mode = ChannelMode.CHALLENGE
                                          THEN /\ pc' = [pc EXCEPT ![Alice] = "FinalizeChannel"]
                                          ELSE /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
                                    /\ UNCHANGED challenge
                               ELSE /\ IF challenge = NULL
                                          THEN /\ Assert(validCommitment(([ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ])), 
                                                         "Failure of assertion at line 93, column 1 of macro called at line 157, column 9.")
                                               /\ IF /\ channelOpen
                                                     /\ progressesChannel(([ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ]).turnNumber)
                                                     THEN /\ challenge' = [ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ]
                                                     ELSE /\ TRUE
                                                          /\ UNCHANGED challenge
                                          ELSE /\ TRUE
                                               /\ UNCHANGED challenge
                                    /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
                                    /\ UNCHANGED channel
                    ELSE /\ pc' = [pc EXCEPT ![Alice] = "Done"]
                         /\ UNCHANGED << channel, challenge >>

FinalizeChannel == /\ pc[Alice] = "FinalizeChannel"
                   /\ channel' = [ mode |-> ChannelMode.FINALIZED, turnNumber |-> channel.turnNumber ]
                   /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
                   /\ UNCHANGED challenge

alice == AliceMoves \/ FinalizeChannel

EveMoves == /\ pc[Eve] = "EveMoves"
            /\ IF channel.mode # ChannelMode.FINALIZED
                  THEN /\ \/ /\ pc' = [pc EXCEPT ![Eve] = "ForceMove"]
                          \/ /\ pc' = [pc EXCEPT ![Eve] = "RespondWithMove"]
                          \/ /\ pc' = [pc EXCEPT ![Eve] = "RespondWithAlternativeMove"]
                          \/ /\ pc' = [pc EXCEPT ![Eve] = "Refute"]
                          \/ /\ pc' = [pc EXCEPT ![Eve] = "Sleep"]
                  ELSE /\ pc' = [pc EXCEPT ![Eve] = "Done"]
            /\ UNCHANGED << channel, challenge >>

ForceMove == /\ pc[Eve] = "ForceMove"
             /\ \E n \in NumParticipants..StartingTurnNumber:
                  \E idx \in ParticipantIDXs \ { AlicesIDX }:
                    /\ Assert(validCommitment(([ turnNumber |-> n, signer |-> idx ])), 
                              "Failure of assertion at line 93, column 1 of macro called at line 182, column 13.")
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
\* Last modified Wed Aug 28 12:52:17 MDT 2019 by andrewstewart
\* Created Tue Aug 06 14:38:11 MDT 2019 by andrewstewart
