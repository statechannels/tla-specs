----------------------------- MODULE ForceMove -----------------------------
EXTENDS Integers, TLC, Utils
CONSTANTS
    StartingTurnNumber,
    NumParticipants,
    MaxActions,
    CountActions,
    EveRefutes,
    EveCheckpoints,
    AlicesStrategy,
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
Signer(state) == ParticipantIDX(state.turnNumber)

KnownTurnNumbers == 0..(StartingTurnNumber + NumParticipants)
ValidStates == [ turnNumber: Nat ]
AlicesStates == { c \in ValidStates :
    /\ c.turnNumber \in KnownTurnNumbers
}
StoredStates == { c \in AlicesStates : c.turnNumber >= StartingTurnNumber }

AlicesNextTurnNumber == CHOOSE n \in (LatestTurnNumber+1)..(LatestTurnNumber+NumParticipants) : ParticipantIDX(n) = Alice
TargetTurnNumbers == (LatestTurnNumber + 1)..(AlicesNextTurnNumber - 1)

\* The spec makes an assumption about what supported states Eve has:
\* Since Eve cannot forge Alice's signature, Eve cannot have a supported state with turn number
\* greater than or equal to AlicesNextTurnNumber
EvesSupportedStates == { c \in ValidStates : c.turnNumber < AlicesNextTurnNumber}
EvesStates == EvesSupportedStates \union { c \in ValidStates : ParticipantIDX(c.turnNumber) # Alice }

challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen == channel.mode = ChannelMode.OPEN

increasesTurnNumber(state) == state.turnNumber > channel.turnNumber

validState(c) == c \in ValidStates

validTransition(c) ==
    /\ challengeOngoing
    /\ c.turnNumber = channel.turnNumber + 1

AlicesGoalMet == channel.turnNumber \in TargetTurnNumbers
end define;

macro validateState(c, type)
begin
if ~validState(c) then
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


macro respondWithMove(state)
begin
validateState(state, "respond");
if validTransition(state)
then clearChallenge(state.turnNumber);
end if;
end macro;

macro checkpoint(state)
begin
validateState(state, "checkpoint");
if increasesTurnNumber(state)
then clearChallenge(state.turnNumber);
end if;
end macro;

macro forceMove(state)
begin
validateState(state, "forceMove");
if
    \/ /\ channelOpen
       /\ state.turnNumber >= channel.turnNumber
    \/ /\ challengeOngoing
       /\ state.turnNumber > channel.turnNumber
then
    channel := [ mode |-> ChannelMode.CHALLENGE, turnNumber |-> state.turnNumber ];
end if;
end macro;

macro refute(state)
begin
validateState(state, "refute");
if
    /\ challengeOngoing
    /\ ParticipantIDX(state.turnNumber) = ParticipantIDX(channel.turnNumber)
    /\ state.turnNumber > channel.turnNumber
then clearChallenge(channel.turnNumber)
end if;
end macro;

macro submitTX(transaction)
begin
if submittedTX # NULL
then
    print(<<submittedTX, transaction>>);
    assert FALSE;
end if;
submittedTX := transaction;
if CountActions then alicesActionCount := alicesActionCount + 1; end if;
end macro;

fair process adjudicator = "Adjudicator"
begin
(***************************************************************************)
(* This process records submitted transactions.                            *)
(***************************************************************************)
Adjudicator:
while ~AlicesGoalMet \/ submittedTX # NULL do
    if submittedTX # NULL then
        if    submittedTX.type = ForceMoveAPI.FORCE_MOVE then forceMove(submittedTX.state);
        elsif submittedTX.type = ForceMoveAPI.RESPOND    then respondWithMove(submittedTX.state);
        elsif submittedTX.type = ForceMoveAPI.REFUTE     then refute(submittedTX.state);
        elsif submittedTX.type = ForceMoveAPI.CHECKPOINT then checkpoint(submittedTX.state);
        else assert FALSE;
        end if;
        submittedTX := NULL;
    end if;
end while;
end process;

fair process alice = "Alice"
begin
(***************************************************************************)
(* Alice has states (n - numParticipants)..(n-1).  She wants to end up     *)
(* with states (n - numParticipants + 1)..n.                               *)
(*                                                                         *)
(* She is allowed to:                                                      *)
(*   A. Call submitForceMove with any states that she currently has        *)
(*   B. Call respondWithMove  whenever there's an active challenge where   *)
(*      it's her turn to move                                              *)
(*   C. Call checkpoint at any time.                                       *)
(*   D. Call refute at any time.                                           *)
(***************************************************************************)
A:
while ~AlicesGoalMet do
    await submittedTX = NULL;
    if challengeOngoing then with turnNumber = channel.turnNumber do
        if turnNumber < LatestTurnNumber then
            if AlicesStrategy = "Refute" then with  state = CHOOSE s \in StoredStates :
                /\ s.turnNumber > channel.turnNumber
                /\ ParticipantIDX(s.turnNumber) = ParticipantIDX(channel.turnNumber)
             do submitTX([ type |-> ForceMoveAPI.REFUTE, state |-> state]);
            end with;
            elsif AlicesStrategy = "Checkpoint" then 
             submitTX([ type |-> ForceMoveAPI.CHECKPOINT, state |-> [turnNumber -> LatestTurnNumber ]]);
            end if;
        end if;
    end with; else 
        submitTX([state |-> [turnNumber |-> LatestTurnNumber ], type |-> ForceMoveAPI.FORCE_MOVE]);
    end if;
end while;
end process;

fair process eve = "Eve"
begin
(***************************************************************************)
(* Eve can do almost anything.  She can sign any data with any private     *)
(* key, except she cannot sign a state with Alice's private key when the   *)
(* turn number is greater than or equal to StartingTurnNumber              *)
(*                                                                         *)
(* She can front-run any transaction an arbitrary number of times: if      *)
(* Alice else calls an adjudicator function by submitting a transaction,   *)
(* Eve can then instantly mine a transaction before Alice's is mined       *)
(***************************************************************************)
E:
while ~AlicesGoalMet do
    either
        \* TODO: challenge with more states than this
        with state \in EvesSupportedStates
        do forceMove(state);
        end with;
    or if challengeOngoing
        then either
        with state \in EvesSupportedStates do respondWithMove(state); end with;
        or if EveCheckpoints then with state \in EvesSupportedStates do checkpoint(state); end with; end if;
        or if EveRefutes then with state \in EvesStates do refute(state); end with; end if;
        end either;
    end if; end either;
end while;
end process;

end algorithm;
*)


\* BEGIN TRANSLATION - the hash of the PCal code: PCal-71d32936f1ae107cf1093254c788ee17
VARIABLES channel, submittedTX, Alice, alicesActionCount, pc

(* define statement *)
Number == Nat \cup { 0 }
LatestTurnNumber == StartingTurnNumber + NumParticipants - 1
ParticipantIDXs == 1..NumParticipants
ParticipantIDX(turnNumber) == 1 + ((turnNumber - 1) % NumParticipants)
Signer(state) == ParticipantIDX(state.turnNumber)

KnownTurnNumbers == 0..(StartingTurnNumber + NumParticipants)
ValidStates == [ turnNumber: Nat ]
AlicesStates == { c \in ValidStates :
    /\ c.turnNumber \in KnownTurnNumbers
}
StoredStates == { c \in AlicesStates : c.turnNumber >= StartingTurnNumber }

AlicesNextTurnNumber == CHOOSE n \in (LatestTurnNumber+1)..(LatestTurnNumber+NumParticipants) : ParticipantIDX(n) = Alice
TargetTurnNumbers == (LatestTurnNumber + 1)..(AlicesNextTurnNumber - 1)




EvesSupportedStates == { c \in ValidStates : c.turnNumber < AlicesNextTurnNumber}
EvesStates == EvesSupportedStates \union { c \in ValidStates : ParticipantIDX(c.turnNumber) # Alice }

challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen == channel.mode = ChannelMode.OPEN

increasesTurnNumber(state) == state.turnNumber > channel.turnNumber

validState(c) == c \in ValidStates

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
                                           THEN /\ IF ~validState((submittedTX.state))
                                                      THEN /\ PrintT((<<"forceMove", (submittedTX.state)>>))
                                                           /\ Assert(FALSE, 
                                                                     "Failure of assertion at line 119, column 5 of macro called at line 192, column 63.")
                                                      ELSE /\ TRUE
                                                /\ IF \/ /\ channelOpen
                                                         /\ (submittedTX.state).turnNumber >= channel.turnNumber
                                                      \/ /\ challengeOngoing
                                                         /\ (submittedTX.state).turnNumber > channel.turnNumber
                                                      THEN /\ channel' = [ mode |-> ChannelMode.CHALLENGE, turnNumber |-> (submittedTX.state).turnNumber ]
                                                      ELSE /\ TRUE
                                                           /\ UNCHANGED channel
                                           ELSE /\ IF submittedTX.type = ForceMoveAPI.RESPOND
                                                      THEN /\ IF ~validState((submittedTX.state))
                                                                 THEN /\ PrintT((<<"respond", (submittedTX.state)>>))
                                                                      /\ Assert(FALSE, 
                                                                                "Failure of assertion at line 119, column 5 of macro called at line 193, column 63.")
                                                                 ELSE /\ TRUE
                                                           /\ IF validTransition((submittedTX.state))
                                                                 THEN /\ Assert(((submittedTX.state).turnNumber) \in Nat, 
                                                                                "Failure of assertion at line 125, column 1 of macro called at line 193, column 63.")
                                                                      /\ channel' =            [
                                                                                        mode |-> ChannelMode.OPEN,
                                                                                        turnNumber |-> ((submittedTX.state).turnNumber)
                                                                                    ]
                                                                 ELSE /\ TRUE
                                                                      /\ UNCHANGED channel
                                                      ELSE /\ IF submittedTX.type = ForceMoveAPI.REFUTE
                                                                 THEN /\ IF ~validState((submittedTX.state))
                                                                            THEN /\ PrintT((<<"refute", (submittedTX.state)>>))
                                                                                 /\ Assert(FALSE, 
                                                                                           "Failure of assertion at line 119, column 5 of macro called at line 194, column 63.")
                                                                            ELSE /\ TRUE
                                                                      /\ IF /\ challengeOngoing
                                                                            /\ ParticipantIDX((submittedTX.state).turnNumber) = ParticipantIDX(channel.turnNumber)
                                                                            /\ (submittedTX.state).turnNumber > channel.turnNumber
                                                                            THEN /\ Assert((channel.turnNumber) \in Nat, 
                                                                                           "Failure of assertion at line 125, column 1 of macro called at line 194, column 63.")
                                                                                 /\ channel' =            [
                                                                                                   mode |-> ChannelMode.OPEN,
                                                                                                   turnNumber |-> (channel.turnNumber)
                                                                                               ]
                                                                            ELSE /\ TRUE
                                                                                 /\ UNCHANGED channel
                                                                 ELSE /\ IF submittedTX.type = ForceMoveAPI.CHECKPOINT
                                                                            THEN /\ IF ~validState((submittedTX.state))
                                                                                       THEN /\ PrintT((<<"checkpoint", (submittedTX.state)>>))
                                                                                            /\ Assert(FALSE, 
                                                                                                      "Failure of assertion at line 119, column 5 of macro called at line 195, column 63.")
                                                                                       ELSE /\ TRUE
                                                                                 /\ IF increasesTurnNumber((submittedTX.state))
                                                                                       THEN /\ Assert(((submittedTX.state).turnNumber) \in Nat, 
                                                                                                      "Failure of assertion at line 125, column 1 of macro called at line 195, column 63.")
                                                                                            /\ channel' =            [
                                                                                                              mode |-> ChannelMode.OPEN,
                                                                                                              turnNumber |-> ((submittedTX.state).turnNumber)
                                                                                                          ]
                                                                                       ELSE /\ TRUE
                                                                                            /\ UNCHANGED channel
                                                                            ELSE /\ Assert(FALSE, 
                                                                                           "Failure of assertion at line 196, column 14.")
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
                                   THEN /\ IF AlicesStrategy = "Refute"
                                              THEN /\ LET state ==                                             CHOOSE s \in StoredStates :
                                                                   /\ s.turnNumber > channel.turnNumber
                                                                   /\ ParticipantIDX(s.turnNumber) = ParticipantIDX(channel.turnNumber) IN
                                                        /\ IF submittedTX # NULL
                                                              THEN /\ PrintT((<<submittedTX, ([ type |-> ForceMoveAPI.REFUTE, state |-> state])>>))
                                                                   /\ Assert(FALSE, 
                                                                             "Failure of assertion at line 178, column 5 of macro called at line 224, column 17.")
                                                              ELSE /\ TRUE
                                                        /\ submittedTX' = [ type |-> ForceMoveAPI.REFUTE, state |-> state]
                                                        /\ IF CountActions
                                                              THEN /\ alicesActionCount' = alicesActionCount + 1
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED alicesActionCount
                                              ELSE /\ IF AlicesStrategy = "Checkpoint"
                                                         THEN /\ IF submittedTX # NULL
                                                                    THEN /\ PrintT((<<submittedTX, ([ type |-> ForceMoveAPI.CHECKPOINT, state |-> [turnNumber -> LatestTurnNumber ]])>>))
                                                                         /\ Assert(FALSE, 
                                                                                   "Failure of assertion at line 178, column 5 of macro called at line 227, column 14.")
                                                                    ELSE /\ TRUE
                                                              /\ submittedTX' = [ type |-> ForceMoveAPI.CHECKPOINT, state |-> [turnNumber -> LatestTurnNumber ]]
                                                              /\ IF CountActions
                                                                    THEN /\ alicesActionCount' = alicesActionCount + 1
                                                                    ELSE /\ TRUE
                                                                         /\ UNCHANGED alicesActionCount
                                                         ELSE /\ TRUE
                                                              /\ UNCHANGED << submittedTX, 
                                                                              alicesActionCount >>
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << submittedTX, 
                                                        alicesActionCount >>
                      ELSE /\ IF submittedTX # NULL
                                 THEN /\ PrintT((<<submittedTX, ([state |-> [turnNumber |-> LatestTurnNumber ], type |-> ForceMoveAPI.FORCE_MOVE])>>))
                                      /\ Assert(FALSE, 
                                                "Failure of assertion at line 178, column 5 of macro called at line 231, column 9.")
                                 ELSE /\ TRUE
                           /\ submittedTX' = [state |-> [turnNumber |-> LatestTurnNumber ], type |-> ForceMoveAPI.FORCE_MOVE]
                           /\ IF CountActions
                                 THEN /\ alicesActionCount' = alicesActionCount + 1
                                 ELSE /\ TRUE
                                      /\ UNCHANGED alicesActionCount
                /\ pc' = [pc EXCEPT !["Alice"] = "A"]
           ELSE /\ pc' = [pc EXCEPT !["Alice"] = "Done"]
                /\ UNCHANGED << submittedTX, alicesActionCount >>
     /\ UNCHANGED << channel, Alice >>

alice == A

E == /\ pc["Eve"] = "E"
     /\ IF ~AlicesGoalMet
           THEN /\ \/ /\ \E state \in EvesSupportedStates:
                           /\ IF ~validState(state)
                                 THEN /\ PrintT((<<"forceMove", state>>))
                                      /\ Assert(FALSE, 
                                                "Failure of assertion at line 119, column 5 of macro called at line 252, column 12.")
                                 ELSE /\ TRUE
                           /\ IF \/ /\ channelOpen
                                    /\ state.turnNumber >= channel.turnNumber
                                 \/ /\ challengeOngoing
                                    /\ state.turnNumber > channel.turnNumber
                                 THEN /\ channel' = [ mode |-> ChannelMode.CHALLENGE, turnNumber |-> state.turnNumber ]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED channel
                   \/ /\ IF challengeOngoing
                            THEN /\ \/ /\ \E state \in EvesSupportedStates:
                                            /\ IF ~validState(state)
                                                  THEN /\ PrintT((<<"respond", state>>))
                                                       /\ Assert(FALSE, 
                                                                 "Failure of assertion at line 119, column 5 of macro called at line 256, column 47.")
                                                  ELSE /\ TRUE
                                            /\ IF validTransition(state)
                                                  THEN /\ Assert((state.turnNumber) \in Nat, 
                                                                 "Failure of assertion at line 125, column 1 of macro called at line 256, column 47.")
                                                       /\ channel' =            [
                                                                         mode |-> ChannelMode.OPEN,
                                                                         turnNumber |-> (state.turnNumber)
                                                                     ]
                                                  ELSE /\ TRUE
                                                       /\ UNCHANGED channel
                                    \/ /\ IF EveCheckpoints
                                             THEN /\ \E state \in EvesSupportedStates:
                                                       /\ IF ~validState(state)
                                                             THEN /\ PrintT((<<"checkpoint", state>>))
                                                                  /\ Assert(FALSE, 
                                                                            "Failure of assertion at line 119, column 5 of macro called at line 257, column 73.")
                                                             ELSE /\ TRUE
                                                       /\ IF increasesTurnNumber(state)
                                                             THEN /\ Assert((state.turnNumber) \in Nat, 
                                                                            "Failure of assertion at line 125, column 1 of macro called at line 257, column 73.")
                                                                  /\ channel' =            [
                                                                                    mode |-> ChannelMode.OPEN,
                                                                                    turnNumber |-> (state.turnNumber)
                                                                                ]
                                                             ELSE /\ TRUE
                                                                  /\ UNCHANGED channel
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED channel
                                    \/ /\ IF EveRefutes
                                             THEN /\ \E state \in EvesStates:
                                                       /\ IF ~validState(state)
                                                             THEN /\ PrintT((<<"refute", state>>))
                                                                  /\ Assert(FALSE, 
                                                                            "Failure of assertion at line 119, column 5 of macro called at line 258, column 60.")
                                                             ELSE /\ TRUE
                                                       /\ IF /\ challengeOngoing
                                                             /\ ParticipantIDX(state.turnNumber) = ParticipantIDX(channel.turnNumber)
                                                             /\ state.turnNumber > channel.turnNumber
                                                             THEN /\ Assert((channel.turnNumber) \in Nat, 
                                                                            "Failure of assertion at line 125, column 1 of macro called at line 258, column 60.")
                                                                  /\ channel' =            [
                                                                                    mode |-> ChannelMode.OPEN,
                                                                                    turnNumber |-> (channel.turnNumber)
                                                                                ]
                                                             ELSE /\ TRUE
                                                                  /\ UNCHANGED channel
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
        /\ WF_vars(alice)
        /\ WF_vars(eve)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-2d45a55f9c307902a3c6eb3e4bb6a687

AllowedTransactions == [ type: Range(ForceMoveAPI), state: ValidStates ]
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
AliceCannotBeGriefed == alicesActionCount <= MaxActions

\* Eve front runs if she changes the channel after Alice submitted a transaction, but before 
\* the transaction is processed
\* Violations of this property are therefore _examples_ of Eve's ability to front-run
\* Alice's transactions
EveCannotFrontRun == [][~(
    /\ submittedTX # NULL \* transaction has been submitted
    /\ submittedTX' = submittedTX \* transaction is not processed
    /\ channel' # channel \* channel is changed
)]_<<submittedTX, channel>>


=============================================================================
\* Modification History
\* Last modified Tue Jun 09 12:20:51 MDT 2020 by andrewstewart
\* Created Tue Aug 06 14:38:11 MDT 2019 by andrewstewart
