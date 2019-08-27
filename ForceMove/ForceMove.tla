----------------------------- MODULE ForceMove -----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS
    Alice, \* A model value
    Eve, \* A set of model values
    StartingTurnNumber,
    NumParticipants,
    NULL \* A model value representing null.

ChannelMode == [
  OPEN |-> "OPEN",
  CHALLENGE  |-> "CHALLENGE",
  FINALIZED |-> "FINALIZED"
]

Range(f) == { f[x] : x \in DOMAIN f }

AlicesGoalTurnNumber == StartingTurnNumber + NumParticipants
Names == { Alice, Eve }

ASSUME
  /\ StartingTurnNumber \in Nat
  /\ NumParticipants \in Nat \ { 1 }
            
(* --algorithm forceMove

variables
    channel = [turnNumber |-> 0, mode |-> ChannelMode.OPEN ],
    challenge = NULL

define
mover(turnNumber) == 1 + ((turnNumber-1) % NumParticipants)
challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen ==      channel.mode = ChannelMode.OPEN

\* TODO: Fill out these checks.
challengerSigIsValid(challenger) == challenger \in Names
progressesChannel(round) == TRUE
validTransition(turnNumber, signer) == TRUE
validCommitment(c) == c \in [ turnNumber: Nat ]

end define;

macro clearChallenge(commitment)
begin
assert validCommitment(commitment);
channel := [ mode |-> ChannelMode.OPEN ] @@ commitment;
end macro;

macro setChallenge(commitment)
begin
assert validCommitment(commitment);
channel := [ mode |-> ChannelMode.CHALLENGE ] @@ commitment;
end macro;

macro respondWithMove(commitment, signer)
begin
if
    /\ challengeOngoing
    /\ validTransition(signer, commitment)
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
    /\ challengerSigIsValid(challenger)
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
    either
        ExpireChallenge: 
            await channel.mode = ChannelMode.CHALLENGE;
            \* TODO: How can we ensure that Alice can clear a challenge before it expires?
            \* Maybe we should skip this step if it's her turn.
            channel := [ mode |-> ChannelMode.FINALIZED ] @@ channel;
    or
        RecordChallenge:
            await challenge # NULL;
            channel := [ turnNumber |-> challenge.turnNumber, mode |-> ChannelMode.CHALLENGE ];
            challenge := NULL;
    end either;
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
        if    TRUE then RespondWithMove: skip;
        elsif TRUE then RespondWithAlternativeMove: skip;
        elsif TRUE then Refute: skip;
        end if;
    or
        await channel.mode = ChannelMode.OPEN;
        ForceMove: skip;
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
       ForceMove: skip;
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
\* Label RespondWithMove of process alice at line 136 col 42 changed to RespondWithMove_
\* Label RespondWithAlternativeMove of process alice at line 137 col 53 changed to RespondWithAlternativeMove_
\* Label Refute of process alice at line 138 col 33 changed to Refute_
\* Label ForceMove of process alice at line 142 col 20 changed to ForceMove_
VARIABLES channel, challenge, pc

(* define statement *)
mover(turnNumber) == 1 + ((turnNumber-1) % NumParticipants)
challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen ==      channel.mode = ChannelMode.OPEN


challengerSigIsValid(challenger) == challenger \in Names
progressesChannel(round) == TRUE
validTransition(turnNumber, signer) == TRUE
validCommitment(c) == c \in [ turnNumber: Nat ]


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
                         THEN /\ \/ /\ pc' = [pc EXCEPT !["Adjudicator"] = "ExpireChallenge"]
                                 \/ /\ pc' = [pc EXCEPT !["Adjudicator"] = "RecordChallenge"]
                         ELSE /\ pc' = [pc EXCEPT !["Adjudicator"] = "Done"]
                   /\ UNCHANGED << channel, challenge >>

ExpireChallenge == /\ pc["Adjudicator"] = "ExpireChallenge"
                   /\ channel.mode = ChannelMode.CHALLENGE
                   /\ channel' = [ mode |-> ChannelMode.FINALIZED ] @@ channel
                   /\ pc' = [pc EXCEPT !["Adjudicator"] = "HandleChallenge"]
                   /\ UNCHANGED challenge

RecordChallenge == /\ pc["Adjudicator"] = "RecordChallenge"
                   /\ challenge # NULL
                   /\ channel' = [ turnNumber |-> challenge.turnNumber, mode |-> ChannelMode.CHALLENGE ]
                   /\ challenge' = NULL
                   /\ pc' = [pc EXCEPT !["Adjudicator"] = "HandleChallenge"]

adjudicator == HandleChallenge \/ ExpireChallenge \/ RecordChallenge

AliceMoves == /\ pc[Alice] = "AliceMoves"
              /\ IF channel.turnNumber < AlicesGoalTurnNumber
                    THEN /\ \/ /\ channel.mode = ChannelMode.CHALLENGE
                               /\ IF TRUE
                                     THEN /\ pc' = [pc EXCEPT ![Alice] = "RespondWithMove_"]
                                     ELSE /\ IF TRUE
                                                THEN /\ pc' = [pc EXCEPT ![Alice] = "RespondWithAlternativeMove_"]
                                                ELSE /\ IF TRUE
                                                           THEN /\ pc' = [pc EXCEPT ![Alice] = "Refute_"]
                                                           ELSE /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
                            \/ /\ channel.mode = ChannelMode.OPEN
                               /\ pc' = [pc EXCEPT ![Alice] = "ForceMove_"]
                    ELSE /\ pc' = [pc EXCEPT ![Alice] = "Done"]
              /\ UNCHANGED << channel, challenge >>

RespondWithMove_ == /\ pc[Alice] = "RespondWithMove_"
                    /\ TRUE
                    /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
                    /\ UNCHANGED << channel, challenge >>

RespondWithAlternativeMove_ == /\ pc[Alice] = "RespondWithAlternativeMove_"
                               /\ TRUE
                               /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
                               /\ UNCHANGED << channel, challenge >>

Refute_ == /\ pc[Alice] = "Refute_"
           /\ TRUE
           /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
           /\ UNCHANGED << channel, challenge >>

ForceMove_ == /\ pc[Alice] = "ForceMove_"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
              /\ UNCHANGED << channel, challenge >>

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
             /\ TRUE
             /\ pc' = [pc EXCEPT ![Eve] = "EveMoves"]
             /\ UNCHANGED << channel, challenge >>

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
AliceCanProgressChannel ==
    \/ <>[](
            /\ channel.mode = ChannelMode.FINALIZED
            /\ channel.turnNumber \in StartingTurnNumber..AlicesGoalTurnNumber
       )
    \/ <>[](
            /\ channel.mode = ChannelMode.OPEN
            /\ channel.turnNumber = AlicesGoalTurnNumber
       )

=============================================================================
\* Modification History
\* Last modified Tue Aug 27 14:38:51 MDT 2019 by andrewstewart
\* Created Tue Aug 06 14:38:11 MDT 2019 by andrewstewart
