----------------------------- MODULE ForceMove -----------------------------
EXTENDS Integers, TLC, Utils
CONSTANTS
    StartingTurnNumber,
    NumParticipants,
    NULL
(***************************************************************************)
(* The purpose of this specification is to outline an algorithm that       *)
(* guarantees that a challenge is registered on chain with turnNumber      *)
(* equal to LatestTurnNumber.  It is guaranteed even with an antagonist    *)
(* who can do anything (including front-run Alice an arbitrary number of   *)
(* times) except                                                           *)
(*  - signing data with Alice's private key                                *)
(*  - corrupting the blockchain                                            *)
(*                                                                         *)
(* This guarantee has a key assumption, namely:                            *)
(*  1. When a challenge is recorded on the adjudicator, Alice is always    *)
(*     able to                                                             *)
(*         a) notice the event                                             *)
(*         b) submit a transaction                                         *)
(*         c) receive confirmation that that transaction was mined         *)
(*     all before the challenge times out.                                 *)
(*                                                                         *)
(* If guarantee is met, then either                                        *)
(*  A. the channel concludes at this state; or                             *)
(*  B. someone responds with a move that progresses the channel            *)
(*  C. someone checkpoints with a move that progresses the                 *)
(*     channel                                                             *)
(*                                                                         *)
(* Alice must accept A.  She must also accept C -- indeed, she must accept *)
(* any supported state that is recorded on chain, since she must have      *)
(* signed at least one "recent" state in its support, and has no control   *)
(* over what the other participants does after that state.  She would be   *)
(* most satisfied with B.                                                  *)
(*                                                                         *)
(* In reality, it is possible that Alice receives a state with turnNumber  *)
(* LatestTurnNumber+1, and in this case Alice could (gracefully) abort her *)
(* algorithm and continue the channel.  A future version of this           *)
(* specification could consider this possibility.                          *)
(*                                                                         *)
(* By inductively applying her algorithm, Alice can therefore guarantee    *)
(* that either the channel progresses as long as she wishes, or it         *)
(* concludes on the latest state that she has.                             *)
(***************************************************************************)


ASSUME
  /\ StartingTurnNumber \in Nat
  /\ /\ NumParticipants \in Nat
     /\ NumParticipants > 1

            
(* --algorithm forceMove
(***************************************************************************)
(* Alice calls adjudicator functions by submitting a pending transaction   *)
(* with the function type and arguments.  The adjudicator processes this   *)
(* transaction and modifies the channel state on her behalf.  However,     *)
(* when Eve calls functions, she directly modifies the channel state.      *)
(* This emulates a reality where Eve can consistently front-run Alice's    *)
(* transactions, when desired.                                             *)
(***************************************************************************)

variables
    channel = [turnNumber |-> 0, mode |-> ChannelMode.OPEN ],
    submittedTX = NULL,
    Alice \in ParticipantIDXs \ { ParticipantIDX(LatestTurnNumber + 1) },
    alicesActionCount = 0
    \* We can't specify any properties that require any memory of the
    \* behaviour up to the certain point (ie. the behaviour has passed through state X seven times in a row)
    \* we thus have to embed the "memory" of the behaviour in the state itself,
    \* if we want to check some property the depends on the history of the behaviour

define
Number == Nat \cup { 0 }
LatestTurnNumber == StartingTurnNumber + NumParticipants - 1
ParticipantIDXs == 1..NumParticipants
ParticipantIDX(turnNumber) == 1 + ((turnNumber - 1) % NumParticipants)
Signer(commitment) == ParticipantIDX(commitment.turnNumber)

KnownTurnNumbers == 0..(StartingTurnNumber + NumParticipants)
ValidCommitments == [ turnNumber: Nat ]
AlicesCommitments == { c \in ValidCommitments :
    /\ c.turnNumber \in KnownTurnNumbers
}
StoredCommitments == { c \in AlicesCommitments : c.turnNumber >= StartingTurnNumber }

AlicesNextTurnNumber == CHOOSE n \in (LatestTurnNumber+1)..(LatestTurnNumber+NumParticipants) : ParticipantIDX(n) = Alice
TargetTurnNumbers == (LatestTurnNumber + 1)..(AlicesNextTurnNumber - 1)

\* The spec makes an assumption about what supported commitments Eve has:
\* Since Eve cannot forge Alice's signature, Eve cannot have a supported state with turn number
\* greater than or equal to AlicesNextTurnNumber
EvesSupportedCommitments == { c \in ValidCommitments : c.turnNumber < AlicesNextTurnNumber}
EvesCommitments == EvesSupportedCommitments \union { c \in ValidCommitments : ParticipantIDX(c.turnNumber) # Alice }

challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen == channel.mode = ChannelMode.OPEN

increasesTurnNumber(commitment) == commitment.turnNumber > channel.turnNumber

validCommitment(c) == c \in ValidCommitments

validTransition(c) ==
    /\ challengeOngoing
    /\ c.turnNumber = channel.turnNumber + 1

AlicesGoalMet == channel.turnNumber \in TargetTurnNumbers
end define;

macro validateCommitment(c, type)
begin
if ~validCommitment(c) then
    print(<<type, c>>);
    assert FALSE;
end if;
end macro;

macro clearChallenge(turnNumber)
begin
assert turnNumber \in Nat;
channel := [
    mode |-> ChannelMode.OPEN,
    turnNumber |-> turnNumber
];
end macro;


macro respondWithMove(commitment)
begin
validateCommitment(commitment, "respond");
if validTransition(commitment)
then clearChallenge(commitment.turnNumber);
end if;
end macro;

macro checkpoint(commitment)
begin
validateCommitment(commitment, "checkpoint");
if increasesTurnNumber(commitment)
then clearChallenge(commitment.turnNumber);
end if;
end macro;

macro forceMove(commitment)
begin
validateCommitment(commitment, "forceMove");
if
    \/ /\ channelOpen
       /\ commitment.turnNumber >= channel.turnNumber
    \/ /\ challengeOngoing
       /\ commitment.turnNumber > channel.turnNumber
then
    channel := [ mode |-> ChannelMode.CHALLENGE, turnNumber |-> commitment.turnNumber ];
end if;
end macro;

fair process adjudicator = "Adjudicator"
begin
(***************************************************************************)
(* This process records submitted transactions.                            *)
(***************************************************************************)
Adjudicator:
while ~AlicesGoalMet \/ submittedTX # NULL do
    if submittedTX # NULL then
        if    submittedTX.type = ForceMoveAPI.FORCE_MOVE then forceMove(submittedTX.commitment);
        elsif submittedTX.type = ForceMoveAPI.RESPOND    then respondWithMove(submittedTX.commitment);
        elsif submittedTX.type = ForceMoveAPI.CHECKPOINT then checkpoint(submittedTX.commitment);
        else assert FALSE;
        end if;
        submittedTX := NULL;
    end if;
end while;
end process;

fair+ process alice = "Alice"
begin
(***************************************************************************)
(* Alice has commitments (n - numParticipants)..(n-1).  She wants to end   *)
(* up with commitments (n - numParticipants + 1)..n.                       *)
(*                                                                         *)
(* She is allowed to:                                                      *)
(*   A. Call submitForceMove with any states that she currently has        *)
(*   B. Call respondWithMove  whenever there's an active challenge where   *)
(*      it's her turn to move                                              *)
(*   C. Call checkpoint at any time.                                       *)
(***************************************************************************)
A:
while ~AlicesGoalMet do
    await submittedTX = NULL;
    if challengeOngoing then with turnNumber = channel.turnNumber do
        if turnNumber < LatestTurnNumber then
            \* Alice has signed commitments from StartingTurnNumber up to LastTurnNumber.
            \* She would therefore call forceMove with the latest commitment
            with  commitment = CHOOSE c \in StoredCommitments : c.turnNumber = LatestTurnNumber do 
            submittedTX := [ type |-> ForceMoveAPI.FORCE_MOVE, commitment |-> commitment]; end with;
            alicesActionCount := alicesActionCount + 1;
        end if;
    end with; else 
        submittedTX := [
            commitment |-> [turnNumber |-> LatestTurnNumber ],
            type |-> ForceMoveAPI.FORCE_MOVE
        ];
        alicesActionCount := alicesActionCount + 1;
    end if;
end while;
end process;

fair process eve = "Eve"
begin
(***************************************************************************)
(* Eve can do almost anything.                                             *)
(*                                                                         *)
(*   a. She can sign any data with any private key, except she cannot sign *)
(*      a commitment with Alice's private key when the turn number is      *)
(*      greater than or equal to StartingTurnNumber                        *)
(*   b. She can call any adjudicator function, at any time                 *)
(*   c. She can front-run any transaction an arbitrary number of times: if *)
(*      anyone else calls an adjudicator function in a transaction tx, she *)
(*      can then choose to submit any transaction before tx is mined.      *)
(*   d. She can choose not to do anything, thus causing any active         *)
(*      challenge to expire.                                               *)
(*                                                                         *)
(* (d) is emulated by behaviours where execution is either                 *)
(* Alice->Adjudicator or Adjudicator->Alice                                *)
(***************************************************************************)
E:
while ~AlicesGoalMet do
    either
        \* TODO: challenge with more commitments than this
        with commitment \in EvesSupportedCommitments
        do forceMove(commitment);
        end with;
    or if challengeOngoing
        then either with commitment \in EvesSupportedCommitments
        do respondWithMove(commitment); end with;
        or with commitment \in EvesSupportedCommitments
        do checkpoint(commitment); end with;
        end either;
    end if; end either;
end while;
end process;

end algorithm;
*)


\* BEGIN TRANSLATION - the hash of the PCal code: PCal-e9eef9089541312909bf46e5d5f4770c
VARIABLES channel, submittedTX, Alice, alicesActionCount, pc

(* define statement *)
Number == Nat \cup { 0 }
LatestTurnNumber == StartingTurnNumber + NumParticipants - 1
ParticipantIDXs == 1..NumParticipants
ParticipantIDX(turnNumber) == 1 + ((turnNumber - 1) % NumParticipants)
Signer(commitment) == ParticipantIDX(commitment.turnNumber)

KnownTurnNumbers == 0..(StartingTurnNumber + NumParticipants)
ValidCommitments == [ turnNumber: Nat ]
AlicesCommitments == { c \in ValidCommitments :
    /\ c.turnNumber \in KnownTurnNumbers
}
StoredCommitments == { c \in AlicesCommitments : c.turnNumber >= StartingTurnNumber }

AlicesNextTurnNumber == CHOOSE n \in (LatestTurnNumber+1)..(LatestTurnNumber+NumParticipants) : ParticipantIDX(n) = Alice
TargetTurnNumbers == (LatestTurnNumber + 1)..(AlicesNextTurnNumber - 1)




EvesSupportedCommitments == { c \in ValidCommitments : c.turnNumber < AlicesNextTurnNumber}
EvesCommitments == EvesSupportedCommitments \union { c \in ValidCommitments : ParticipantIDX(c.turnNumber) # Alice }

challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen == channel.mode = ChannelMode.OPEN

increasesTurnNumber(commitment) == commitment.turnNumber > channel.turnNumber

validCommitment(c) == c \in ValidCommitments

validTransition(c) ==
    /\ challengeOngoing
    /\ c.turnNumber = channel.turnNumber + 1

AlicesGoalMet == channel.turnNumber \in TargetTurnNumbers


vars == << channel, submittedTX, Alice, alicesActionCount, pc >>

ProcSet == {"Adjudicator"} \cup {"Alice"} \cup {"Eve"}

Init == (* Global variables *)
        /\ channel = [turnNumber |-> 0, mode |-> ChannelMode.OPEN ]
        /\ submittedTX = NULL
        /\ Alice \in ParticipantIDXs \ { ParticipantIDX(LatestTurnNumber + 1) }
        /\ alicesActionCount = 0
        /\ pc = [self \in ProcSet |-> CASE self = "Adjudicator" -> "Adjudicator"
                                        [] self = "Alice" -> "A"
                                        [] self = "Eve" -> "E"]

Adjudicator == /\ pc["Adjudicator"] = "Adjudicator"
               /\ IF ~AlicesGoalMet \/ submittedTX # NULL
                     THEN /\ IF submittedTX # NULL
                                THEN /\ IF submittedTX.type = ForceMoveAPI.FORCE_MOVE
                                           THEN /\ IF ~validCommitment((submittedTX.commitment))
                                                      THEN /\ PrintT((<<"forceMove", (submittedTX.commitment)>>))
                                                           /\ Assert(FALSE, 
                                                                     "Failure of assertion at line 114, column 5 of macro called at line 165, column 63.")
                                                      ELSE /\ TRUE
                                                /\ IF \/ /\ channelOpen
                                                         /\ (submittedTX.commitment).turnNumber >= channel.turnNumber
                                                      \/ /\ challengeOngoing
                                                         /\ (submittedTX.commitment).turnNumber > channel.turnNumber
                                                      THEN /\ channel' = [ mode |-> ChannelMode.CHALLENGE, turnNumber |-> (submittedTX.commitment).turnNumber ]
                                                      ELSE /\ TRUE
                                                           /\ UNCHANGED channel
                                           ELSE /\ IF submittedTX.type = ForceMoveAPI.RESPOND
                                                      THEN /\ IF ~validCommitment((submittedTX.commitment))
                                                                 THEN /\ PrintT((<<"respond", (submittedTX.commitment)>>))
                                                                      /\ Assert(FALSE, 
                                                                                "Failure of assertion at line 114, column 5 of macro called at line 166, column 63.")
                                                                 ELSE /\ TRUE
                                                           /\ IF validTransition((submittedTX.commitment))
                                                                 THEN /\ Assert(((submittedTX.commitment).turnNumber) \in Nat, 
                                                                                "Failure of assertion at line 120, column 1 of macro called at line 166, column 63.")
                                                                      /\ channel' =            [
                                                                                        mode |-> ChannelMode.OPEN,
                                                                                        turnNumber |-> ((submittedTX.commitment).turnNumber)
                                                                                    ]
                                                                 ELSE /\ TRUE
                                                                      /\ UNCHANGED channel
                                                      ELSE /\ IF submittedTX.type = ForceMoveAPI.CHECKPOINT
                                                                 THEN /\ IF ~validCommitment((submittedTX.commitment))
                                                                            THEN /\ PrintT((<<"checkpoint", (submittedTX.commitment)>>))
                                                                                 /\ Assert(FALSE, 
                                                                                           "Failure of assertion at line 114, column 5 of macro called at line 167, column 63.")
                                                                            ELSE /\ TRUE
                                                                      /\ IF increasesTurnNumber((submittedTX.commitment))
                                                                            THEN /\ Assert(((submittedTX.commitment).turnNumber) \in Nat, 
                                                                                           "Failure of assertion at line 120, column 1 of macro called at line 167, column 63.")
                                                                                 /\ channel' =            [
                                                                                                   mode |-> ChannelMode.OPEN,
                                                                                                   turnNumber |-> ((submittedTX.commitment).turnNumber)
                                                                                               ]
                                                                            ELSE /\ TRUE
                                                                                 /\ UNCHANGED channel
                                                                 ELSE /\ Assert(FALSE, 
                                                                                "Failure of assertion at line 168, column 14.")
                                                                      /\ UNCHANGED channel
                                     /\ submittedTX' = NULL
                                ELSE /\ TRUE
                                     /\ UNCHANGED << channel, submittedTX >>
                          /\ pc' = [pc EXCEPT !["Adjudicator"] = "Adjudicator"]
                     ELSE /\ pc' = [pc EXCEPT !["Adjudicator"] = "Done"]
                          /\ UNCHANGED << channel, submittedTX >>
               /\ UNCHANGED << Alice, alicesActionCount >>

adjudicator == Adjudicator

A == /\ pc["Alice"] = "A"
     /\ IF ~AlicesGoalMet
           THEN /\ submittedTX = NULL
                /\ IF challengeOngoing
                      THEN /\ LET turnNumber == channel.turnNumber IN
                                IF turnNumber < LatestTurnNumber
                                   THEN /\ LET commitment == CHOOSE c \in StoredCommitments : c.turnNumber = LatestTurnNumber IN
                                             submittedTX' = [ type |-> ForceMoveAPI.FORCE_MOVE, commitment |-> commitment]
                                        /\ alicesActionCount' = alicesActionCount + 1
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << submittedTX, 
                                                        alicesActionCount >>
                      ELSE /\ submittedTX' =                [
                                                 commitment |-> [turnNumber |-> LatestTurnNumber ],
                                                 type |-> ForceMoveAPI.FORCE_MOVE
                                             ]
                           /\ alicesActionCount' = alicesActionCount + 1
                /\ pc' = [pc EXCEPT !["Alice"] = "A"]
           ELSE /\ pc' = [pc EXCEPT !["Alice"] = "Done"]
                /\ UNCHANGED << submittedTX, alicesActionCount >>
     /\ UNCHANGED << channel, Alice >>

alice == A

E == /\ pc["Eve"] = "E"
     /\ IF ~AlicesGoalMet
           THEN /\ \/ /\ \E commitment \in EvesSupportedCommitments:
                           /\ IF ~validCommitment(commitment)
                                 THEN /\ PrintT((<<"forceMove", commitment>>))
                                      /\ Assert(FALSE, 
                                                "Failure of assertion at line 114, column 5 of macro called at line 231, column 12.")
                                 ELSE /\ TRUE
                           /\ IF \/ /\ channelOpen
                                    /\ commitment.turnNumber >= channel.turnNumber
                                 \/ /\ challengeOngoing
                                    /\ commitment.turnNumber > channel.turnNumber
                                 THEN /\ channel' = [ mode |-> ChannelMode.CHALLENGE, turnNumber |-> commitment.turnNumber ]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED channel
                   \/ /\ IF challengeOngoing
                            THEN /\ \/ /\ \E commitment \in EvesSupportedCommitments:
                                            /\ IF ~validCommitment(commitment)
                                                  THEN /\ PrintT((<<"respond", commitment>>))
                                                       /\ Assert(FALSE, 
                                                                 "Failure of assertion at line 114, column 5 of macro called at line 235, column 12.")
                                                  ELSE /\ TRUE
                                            /\ IF validTransition(commitment)
                                                  THEN /\ Assert((commitment.turnNumber) \in Nat, 
                                                                 "Failure of assertion at line 120, column 1 of macro called at line 235, column 12.")
                                                       /\ channel' =            [
                                                                         mode |-> ChannelMode.OPEN,
                                                                         turnNumber |-> (commitment.turnNumber)
                                                                     ]
                                                  ELSE /\ TRUE
                                                       /\ UNCHANGED channel
                                    \/ /\ \E commitment \in EvesSupportedCommitments:
                                            /\ IF ~validCommitment(commitment)
                                                  THEN /\ PrintT((<<"checkpoint", commitment>>))
                                                       /\ Assert(FALSE, 
                                                                 "Failure of assertion at line 114, column 5 of macro called at line 237, column 12.")
                                                  ELSE /\ TRUE
                                            /\ IF increasesTurnNumber(commitment)
                                                  THEN /\ Assert((commitment.turnNumber) \in Nat, 
                                                                 "Failure of assertion at line 120, column 1 of macro called at line 237, column 12.")
                                                       /\ channel' =            [
                                                                         mode |-> ChannelMode.OPEN,
                                                                         turnNumber |-> (commitment.turnNumber)
                                                                     ]
                                                  ELSE /\ TRUE
                                                       /\ UNCHANGED channel
                            ELSE /\ TRUE
                                 /\ UNCHANGED channel
                /\ pc' = [pc EXCEPT !["Eve"] = "E"]
           ELSE /\ pc' = [pc EXCEPT !["Eve"] = "Done"]
                /\ UNCHANGED channel
     /\ UNCHANGED << submittedTX, Alice, alicesActionCount >>

eve == E

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == adjudicator \/ alice \/ eve
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(adjudicator)
        /\ SF_vars(alice)
        /\ WF_vars(eve)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-df2717bc801d3517735d9ef3a9202745

AllowedTransactions == [ type: Range(ForceMoveAPI), commitment: ValidCommitments ]
AllowedChannels == [ mode: Range(ChannelMode), turnNumber: Number ]

\* Safety & liveness properties

TypeOK ==
    /\  channel \in AllowedChannels
    /\  \/ submittedTX \in AllowedTransactions
        \/ submittedTX = NULL

AliceCanProgressChannel == <>[](channel.turnNumber \in TargetTurnNumbers)
    
\* We can verify that Alice can never directly modify the channel with this property, with
\* the exception that she can finalize the channel.
AliceMustSubmitTransactions == [][
        /\ submittedTX = NULL
        /\ submittedTX' # NULL
    => UNCHANGED channel
]_<<submittedTX, channel>>

TurnNumberIncrements == [][
    channel'.turnNumber >= channel.turnNumber
]_<<channel>>


\* Alice should be able to accomplish her goal by submitting a single transaction.
AliceCannotBeGriefed == alicesActionCount <= 1

=============================================================================
\* Modification History
\* Last modified Mon Jun 08 13:37:18 PDT 2020 by andrewstewart
\* Created Tue Aug 06 14:38:11 MDT 2019 by andrewstewart
