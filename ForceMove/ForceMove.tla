----------------------------- MODULE ForceMove -----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS
    Archie, \* A model value
    Names, \* A set of model values
    Participants, \* A set of model values
    Histories,
    HistoryIDs,
    NULL \* A model value representing null.

ChannelMode == [
  OPEN |-> "OPEN",
  CHALLENGE  |-> "CHALLENGE",
  FINALIZED |-> "FINALIZED"
]

Range(f) == { f[x] : x \in DOMAIN f }
NumParticipants == Len(Participants)
AllowedHistories == [ start: Nat, length: Nat, id: HistoryIDs ] \* TODO: Fill out the allowed histories.
MainHistory == Histories[1]
StartingTurnNumber == MainHistory.start + MainHistory.length - 1
                  
Maximum(S) == 
  (*************************************************************************)
  (* If $S$ is a set of numbers, then this define $Maximum(S)$ to be the   *)
  (* maximum of those numbers, or $-1$ if $S$ is empty.                    *)
  (*************************************************************************)
  LET Max[T \in SUBSET S] == 
        IF T = {} THEN -1
                  ELSE LET n    == CHOOSE n \in T : TRUE
                           rmax == Max[T \ {n}]
                       IN  IF n \geq rmax THEN n ELSE rmax
  IN  Max[S]
ArchiesGoalTurnNumber == MainHistory.start + MainHistory.length

ASSUME
  /\ Archie \notin Names
  /\ NumParticipants = Cardinality(Names) + 1
  /\ Len(Participants) >= 2
  /\ \A h \in Range(Histories) : h \in AllowedHistories
  /\ Range(Participants) = { Archie } \cup Names
            
(* --algorithm forceMove

variables
    channel = [turnNumber |-> 0, mode |-> ChannelMode.OPEN, history |-> MainHistory.id ],
    challenge = NULL

define
mover(turnNumber) == 1 + ((turnNumber-1) % NumParticipants)
challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen ==      channel.mode = ChannelMode.OPEN

\* TODO: Fill out these checks.
challengerSigIsValid(challenger) == challenger \in Names
progressesChannel(round) == TRUE
validTransition(turnNumber, signer) == TRUE
validCommitment(c) == c \in [ turnNumber: Nat, history: HistoryIDs ]

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

fair process adjudicator = 0
begin
(***************************************************************************)
(* This process expires active channels and records submitted            *)
(* channels.                                                             *)
(***************************************************************************)
HandleChallenge:
while channel.mode # ChannelMode.FINALIZED
do
    either
        ExpireChallenge: 
            await channel.mode = ChannelMode.CHALLENGE;
            \* TODO: How can we ensure that Archie can clear a challenge before it expires?
            \* Maybe we should skip this step if it's his turn.
            channel := [ mode |-> ChannelMode.FINALIZED ] @@ channel;
    or
        RecordChallenge:
            await challenge # NULL;
            channel := [ turnNumber |-> challenge.turnNumber, mode |-> ChannelMode.CHALLENGE ];
            challenge := NULL;
    end either;
end while;
end process;

fair process archie = Archie
begin
(***************************************************************************)
(* Archie has commitments (n - numParticipants)..(n-1).  He wants to end   *)
(* up with commitments (n - numParticipants + 1)..n.                       *)
(*                                                                         *)
(* He is allowed to:                                                       *)
(*   - Call forceMove with any states that he currently has                *)
(*   - Call refute with any state that he has                              *)
(*   - Call respondWithMove or respondWithMove whenever there's an active  *)
(*     challenge where it's his turn to move                               *)
(***************************************************************************)
ArchieMoves:
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
end process;

fair process eve \in HistoryIDs
begin
(***************************************************************************)
(* Eve can do almost anything.  She has k different histories that each    *)
(* contain commitments 1...(n-1), where one of them is the same history as *)
(* Archie's.  She can sign any data with any private key other than        *)
(* Archie's.  She can call any adjudicator function, at any time.  She can *)
(* front-run any transaction an arbitrary number of times: if anyone else  *)
(* calls an adjudicator function in a transaction tx, she can then choose  *)
(* to submit any transaction before tx is mined.  She can choose not to do *)
(* anything, thus causing any active challenge to expire.                  *)
(***************************************************************************)
EveMoves:
either
   ForceMove: skip;
or RespondWithMove: skip;
or RespondWithAlternativeMove: skip;
or Refute: skip
or Sleep: skip;
end either;
end process;

end algorithm;
*)


\* BEGIN TRANSLATION
\* Label RespondWithMove of process archie at line 153 col 38 changed to RespondWithMove_
\* Label RespondWithAlternativeMove of process archie at line 154 col 49 changed to RespondWithAlternativeMove_
\* Label Refute of process archie at line 155 col 29 changed to Refute_
\* Label ForceMove of process archie at line 159 col 16 changed to ForceMove_
VARIABLES channel, challenge, pc

(* define statement *)
mover(turnNumber) == 1 + ((turnNumber-1) % NumParticipants)
challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen ==      channel.mode = ChannelMode.OPEN


challengerSigIsValid(challenger) == challenger \in Names
progressesChannel(round) == TRUE
validTransition(turnNumber, signer) == TRUE
validCommitment(c) == c \in [ turnNumber: Nat, history: HistoryIDs ]


vars == << channel, challenge, pc >>

ProcSet == {0} \cup {Archie} \cup (HistoryIDs)

Init == (* Global variables *)
        /\ channel = [turnNumber |-> 0, mode |-> ChannelMode.OPEN, history |-> MainHistory.id ]
        /\ challenge = NULL
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "HandleChallenge"
                                        [] self = Archie -> "ArchieMoves"
                                        [] self \in HistoryIDs -> "EveMoves"]

HandleChallenge == /\ pc[0] = "HandleChallenge"
                   /\ IF channel.mode # ChannelMode.FINALIZED
                         THEN /\ \/ /\ pc' = [pc EXCEPT ![0] = "ExpireChallenge"]
                                 \/ /\ pc' = [pc EXCEPT ![0] = "RecordChallenge"]
                         ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                   /\ UNCHANGED << channel, challenge >>

ExpireChallenge == /\ pc[0] = "ExpireChallenge"
                   /\ channel.mode = ChannelMode.CHALLENGE
                   /\ channel' = [ mode |-> ChannelMode.FINALIZED ] @@ channel
                   /\ pc' = [pc EXCEPT ![0] = "HandleChallenge"]
                   /\ UNCHANGED challenge

RecordChallenge == /\ pc[0] = "RecordChallenge"
                   /\ challenge # NULL
                   /\ channel' = [ turnNumber |-> challenge.turnNumber, mode |-> ChannelMode.CHALLENGE ]
                   /\ challenge' = NULL
                   /\ pc' = [pc EXCEPT ![0] = "HandleChallenge"]

adjudicator == HandleChallenge \/ ExpireChallenge \/ RecordChallenge

ArchieMoves == /\ pc[Archie] = "ArchieMoves"
               /\ \/ /\ channel.mode = ChannelMode.CHALLENGE
                     /\ IF TRUE
                           THEN /\ pc' = [pc EXCEPT ![Archie] = "RespondWithMove_"]
                           ELSE /\ IF TRUE
                                      THEN /\ pc' = [pc EXCEPT ![Archie] = "RespondWithAlternativeMove_"]
                                      ELSE /\ IF TRUE
                                                 THEN /\ pc' = [pc EXCEPT ![Archie] = "Refute_"]
                                                 ELSE /\ pc' = [pc EXCEPT ![Archie] = "Done"]
                  \/ /\ channel.mode = ChannelMode.OPEN
                     /\ pc' = [pc EXCEPT ![Archie] = "ForceMove_"]
               /\ UNCHANGED << channel, challenge >>

RespondWithMove_ == /\ pc[Archie] = "RespondWithMove_"
                    /\ TRUE
                    /\ pc' = [pc EXCEPT ![Archie] = "Done"]
                    /\ UNCHANGED << channel, challenge >>

RespondWithAlternativeMove_ == /\ pc[Archie] = "RespondWithAlternativeMove_"
                               /\ TRUE
                               /\ pc' = [pc EXCEPT ![Archie] = "Done"]
                               /\ UNCHANGED << channel, challenge >>

Refute_ == /\ pc[Archie] = "Refute_"
           /\ TRUE
           /\ pc' = [pc EXCEPT ![Archie] = "Done"]
           /\ UNCHANGED << channel, challenge >>

ForceMove_ == /\ pc[Archie] = "ForceMove_"
              /\ TRUE
              /\ pc' = [pc EXCEPT ![Archie] = "Done"]
              /\ UNCHANGED << channel, challenge >>

archie == ArchieMoves \/ RespondWithMove_ \/ RespondWithAlternativeMove_
             \/ Refute_ \/ ForceMove_

EveMoves(self) == /\ pc[self] = "EveMoves"
                  /\ \/ /\ pc' = [pc EXCEPT ![self] = "ForceMove"]
                     \/ /\ pc' = [pc EXCEPT ![self] = "RespondWithMove"]
                     \/ /\ pc' = [pc EXCEPT ![self] = "RespondWithAlternativeMove"]
                     \/ /\ pc' = [pc EXCEPT ![self] = "Refute"]
                     \/ /\ pc' = [pc EXCEPT ![self] = "Sleep"]
                  /\ UNCHANGED << channel, challenge >>

ForceMove(self) == /\ pc[self] = "ForceMove"
                   /\ TRUE
                   /\ pc' = [pc EXCEPT ![self] = "Done"]
                   /\ UNCHANGED << channel, challenge >>

RespondWithMove(self) == /\ pc[self] = "RespondWithMove"
                         /\ TRUE
                         /\ pc' = [pc EXCEPT ![self] = "Done"]
                         /\ UNCHANGED << channel, challenge >>

RespondWithAlternativeMove(self) == /\ pc[self] = "RespondWithAlternativeMove"
                                    /\ TRUE
                                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                                    /\ UNCHANGED << channel, challenge >>

Refute(self) == /\ pc[self] = "Refute"
                /\ TRUE
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << channel, challenge >>

Sleep(self) == /\ pc[self] = "Sleep"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << channel, challenge >>

eve(self) == EveMoves(self) \/ ForceMove(self) \/ RespondWithMove(self)
                \/ RespondWithAlternativeMove(self) \/ Refute(self)
                \/ Sleep(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == adjudicator \/ archie
           \/ (\E self \in HistoryIDs: eve(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(adjudicator)
        /\ WF_vars(archie)
        /\ \A self \in HistoryIDs : WF_vars(eve(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

AllowedTurnNumbers == 0..(StartingTurnNumber + NumParticipants)
AllowedChannels ==
  [
    turnNumber: AllowedTurnNumbers,
    mode: Range(ChannelMode),
    history: HistoryIDs
  ]


\* Safety properties

TypeOK ==
  /\ channel \in AllowedChannels
  
\* Liveness properties
ArchieCanProgressChannel ==
    \/ <>[](
            /\ channel.mode = ChannelMode.FINALIZED
            /\ channel.turnNumber \in MainHistory.start..(MainHistory.start + MainHistory.length)
       )
    \/ <>[](
            /\ channel.mode = ChannelMode.OPEN
            /\ channel.turnNumber = ArchiesGoalTurnNumber
       )

=============================================================================
\* Modification History
\* Last modified Tue Aug 27 12:07:25 MDT 2019 by andrewstewart
\* Created Tue Aug 06 14:38:11 MDT 2019 by andrewstewart
