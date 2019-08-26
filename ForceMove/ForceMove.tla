----------------------------- MODULE ForceMove -----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS
    Archie, \* A model value
    Names, \* A set of model values
    Participants, \* A set of model values
    Histories,
    NULL \* A model value representing null.

ChannelMode == [
  OPEN |-> "OPEN",
  CHALLENGE  |-> "CHALLENGE",
  FINALIZED |-> "FINALIZED"
]

Range(f) == { f[x] : x \in DOMAIN f }
StartingTurnNumber == 1
NumParticipants == Len(Participants)
AllowedHistories == {} \* TODO: Fill out the allowed histories.
MainHistory == Histories[0]
ArchiesHistory == LET start == Len(MainHistory) - NumParticipants
                  IN [i \in start..(start + NumParticipants - 1) |-> MainHistory[i]]

ASSUME
  /\ Archie \in Names
  /\ Cardinality(Names) = NumParticipants
  /\ Len(Participants) >= 2
  /\ Histories \in AllowedHistories
  /\ \A p \in Range(Participants) : p \in Names
            
(* --algorithm forceMove

variables
    channel = [turnNumber |-> 0, mode |-> ChannelMode.OPEN],
    challenge = NULL

define
mover(turnNumber) == 1 + ((turnNumber-1) % NumParticipants)
challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen ==      channel.mode = ChannelMode.OPEN

\* TODO: Fill out these checks.
roundIsValid(round) == TRUE
challengerSigIsValid(challenger) == TRUE
progressesChannel(round) == TRUE
validTransition(turnNumber, signer) == TRUE

end define;

macro clearChallenge(turnNumber)
begin
channel := [ turnNumber |-> turnNumber, mode |-> ChannelMode.OPEN ];
end macro;

macro setChallenge(turnNumber)
begin
channel := [ turnNumber |-> turnNumber, mode |-> ChannelMode.CHALLENGE ];
end macro;

macro respondWithMove(turnNumber, signer)
begin
if
    /\ challengeOngoing
    /\ validTransition(signer, turnNumber)
then clearChallenge(turnNumber)
end if;
end macro;

macro respondWithAlternativeMove(round, signer)
begin
if
    /\ roundIsValid(round)
    /\ challengeOngoing
    /\ round[NumParticipants].turnNumber > channel.turnNumber
then clearChallenge(round[NumParticipants].turnNumber);
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

macro forceMove(turnNumber, round, challenger)
begin
if
    /\ roundIsValid(round)
    /\ channelOpen
    /\ challengerSigIsValid(challenger)
    /\ progressesChannel(round)
then setChallenge(turnNumber)
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
            channel := [ mode |-> ChannelMode.FINALIZED ] @@ channel;
    or
        RecordChallenge:
            await challenge # NULL;
            channel := [ turnNumber |-> challenge.turnNumber, mode |-> ChannelMode.CHALLENGE ];
            challenge := NULL;
    end either;
end while;
end process;

fair process archie = 1
begin
(***************************************************************************)
(* Archie has commitments (n - numParticipants)..(n-1).  He wants to end    *)
(* up with commitments (n - numParticipants + 1)..n.                       *)
(*                                                                         *)
(* He is allowed to:                                                       *)
(*   - Call forceMove with any states that he currently has                *)
(*   - Call refute with any state that he has                              *)
(*   - Call respondWithMove or respondWithMove whenever there's an active  *)
(*     channel where it's his turn to move                               *)
(***************************************************************************)
ArchieMoves: skip;
end process;

fair process eve = 2
begin
(****************************************************************************)
(* Eve can do almost anything.  She has k different histories that each    *)
(* contain commitments 1...(n-1).  She can sign any data with any private  *)
(* key other than Archie's.  She can call any adjudicator function, at any  *)
(* time.  She can front-run any transaction an arbitrary number of times:  *)
(* if anyone else calls an adjudicator function in a transaction tx, she   *)
(* can then choose to submit any transaction before tx is mined.  She can  *)
(* expire channels whenever the current channel doesn't allow          *)
(***************************************************************************)
EveMoves: skip;
end process;


end algorithm;
*)


\* BEGIN TRANSLATION
VARIABLES channel, challenge, pc

(* define statement *)
mover(turnNumber) == 1 + ((turnNumber-1) % NumParticipants)
challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen ==      channel.mode = ChannelMode.OPEN


roundIsValid(round) == TRUE
challengerSigIsValid(challenger) == TRUE
progressesChannel(round) == TRUE
validTransition(turnNumber, signer) == TRUE


vars == << channel, challenge, pc >>

ProcSet == {0} \cup {1} \cup {2}

Init == (* Global variables *)
        /\ channel = [turnNumber |-> 0, mode |-> ChannelMode.OPEN]
        /\ challenge = NULL
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "HandleChallenge"
                                        [] self = 1 -> "One"
                                        [] self = 2 -> "EveMoves"]

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

One == /\ pc[1] = "One"
       /\ IF /\ roundIsValid(({}))
             /\ channelOpen
             /\ challengerSigIsValid(Archie)
             /\ progressesChannel(({}))
             THEN /\ channel' = [ turnNumber |-> 2, mode |-> ChannelMode.CHALLENGE ]
             ELSE /\ TRUE
                  /\ UNCHANGED channel
       /\ pc' = [pc EXCEPT ![1] = "Two"]
       /\ UNCHANGED challenge

Two == /\ pc[1] = "Two"
       /\ IF /\ challengeOngoing
             /\ validTransition(Archie, 3)
             THEN /\ channel' = [ turnNumber |-> 3, mode |-> ChannelMode.OPEN ]
             ELSE /\ TRUE
                  /\ UNCHANGED channel
       /\ pc' = [pc EXCEPT ![1] = "Three"]
       /\ UNCHANGED challenge

Three == /\ pc[1] = "Three"
         /\ IF /\ roundIsValid(({}))
               /\ challengeOngoing
               /\ ({})[NumParticipants].turnNumber > channel.turnNumber
               THEN /\ channel' = [ turnNumber |-> (({})[NumParticipants].turnNumber), mode |-> ChannelMode.OPEN ]
               ELSE /\ TRUE
                    /\ UNCHANGED channel
         /\ pc' = [pc EXCEPT ![1] = "Four"]
         /\ UNCHANGED challenge

Four == /\ pc[1] = "Four"
        /\ IF /\ challengeOngoing
              /\ 5 > channel.turnNumber
              THEN /\ channel' = [ turnNumber |-> (channel.turnNumber), mode |-> ChannelMode.OPEN ]
              ELSE /\ TRUE
                   /\ UNCHANGED channel
        /\ pc' = [pc EXCEPT ![1] = "Done"]
        /\ UNCHANGED challenge

archie == One \/ Two \/ Three \/ Four

EveMoves == /\ pc[2] = "EveMoves"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![2] = "Done"]
            /\ UNCHANGED << channel, challenge >>

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
    mode: Range(ChannelMode)
  ]


\* Safety properties

\*TypeOK ==
\*  /\ channel \in AllowedChallenges

\* TODO: Get TurnNumberDoesNotDecrease and StaysTerminated
\* For some reason, state[p].turnNumber' is not valid
\*TurnNumberDoesNotDecrease ==
\*  /\ \A p \in ParticipantIndices: state[p].turnNumber' >= state[p].turnNumber

\* Once a process has terminated, its state does not change.
\*StaysTerminated == \A p \in ParticipantIndices: (Terminated(state[p]) => (state'[p] = state[p]))
  
\* Liveness properties
\*ProtocolTerminatesWhenChallengeDoesNotExpire == 
\*    \/ <>[]( /\ channel.mode = ChannelMode.FINALIZED
\*             /\ \E p \in ParticipantIndices: state[p].type = Types.TERMINATED)
\*    \/ (\A p \in ParticipantIndices: <>[](/\ state[p].type = Types.SUCCESS
\*                                          /\ state[p].turnNumber = StartingTurnNumber + NumParticipants))
\*    \/ (\A p \in ParticipantIndices: <>[](/\ state[p].type = Types.ABORTED
\*                                          /\ state[p].turnNumber = state[1].turnNumber))


=============================================================================
\* Modification History
\* Last modified Mon Aug 26 11:29:08 MDT 2019 by andrewstewart
\* Created Tue Aug 06 14:38:11 MDT 2019 by andrewstewart
