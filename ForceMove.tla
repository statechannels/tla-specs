----------------------------- MODULE ForceMove -----------------------------
EXTENDS Integers, TLC, Utils
CONSTANTS
    StartingTurnNumber,
    NumParticipants,
    MaxActions,
    CountActions,
    EveRefutes,
    EveCheckpoints,
    ForceMoveOverwrites,
    AliceRefutes,
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
(*  1. When a challenge is recorded on the adjudicator, Alice is  *)
(*     always able to                                                      *)
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
(* with the function type and arguments.  The TransactionProcessor         *)
(* processes this transaction and modifies the adjudicator state on her        *)
(* behalf.  However, when Eve calls functions, she directly modifies the   *)
(* adjudicator state.  This emulates a reality where Eve can consistently      *)
(* front-run Alice's transactions, when desired.                           *)
(***************************************************************************)

variables
    adjudicator = [turnNumber |-> 0, mode |-> ChannelMode.OPEN ],
    TranactionPool = NULL,
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

challengeOngoing == adjudicator.mode = ChannelMode.CHALLENGE
channelOpen == adjudicator.mode = ChannelMode.OPEN

increasesTurnNumber(state) == state.turnNumber > adjudicator.turnNumber

validState(c) == c \in ValidStates

validTransition(c) ==
    /\ challengeOngoing
    /\ c.turnNumber = adjudicator.turnNumber + 1

AlicesGoalMet == adjudicator.turnNumber \in TargetTurnNumbers
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
adjudicator := [
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
       /\ state.turnNumber >= adjudicator.turnNumber
    \/ /\ challengeOngoing
       /\ ForceMoveOverwrites
       /\ state.turnNumber > adjudicator.turnNumber
then
    adjudicator := [ mode |-> ChannelMode.CHALLENGE, turnNumber |-> state.turnNumber ];
end if;
end macro;

macro refute(state)
begin
validateState(state, "refute");
if
    /\ challengeOngoing
    /\ ParticipantIDX(state.turnNumber) = ParticipantIDX(adjudicator.turnNumber)
    /\ state.turnNumber > adjudicator.turnNumber
then clearChallenge(adjudicator.turnNumber)
end if;
end macro;

macro submitTX(transaction)
begin
if TranactionPool # NULL
then
    print(<<TranactionPool, transaction>>);
    assert FALSE;
end if;
TranactionPool := transaction;
if CountActions then alicesActionCount := alicesActionCount + 1; end if;
end macro;

fair process TransactionProcessor = "TransactionProcessor"
begin
(***************************************************************************)
(* This process records submitted transactions.                            *)
(***************************************************************************)
TransactionProcessor:
while ~AlicesGoalMet \/ TranactionPool # NULL do
    if TranactionPool # NULL then
        if    TranactionPool.type = ForceMoveAPI.FORCE_MOVE then forceMove(TranactionPool.state);
        elsif TranactionPool.type = ForceMoveAPI.RESPOND    then respondWithMove(TranactionPool.state);
        elsif TranactionPool.type = ForceMoveAPI.REFUTE     then refute(TranactionPool.state);
        elsif TranactionPool.type = ForceMoveAPI.CHECKPOINT then checkpoint(TranactionPool.state);
        else assert FALSE;
        end if;
        TranactionPool := NULL;
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
    await TranactionPool = NULL;
    if challengeOngoing then with turnNumber = adjudicator.turnNumber do
        if turnNumber < LatestTurnNumber then
            if AliceRefutes then with  state = CHOOSE s \in StoredStates :
                /\ s.turnNumber > adjudicator.turnNumber
                /\ ParticipantIDX(s.turnNumber) = ParticipantIDX(adjudicator.turnNumber)
             do submitTX([ type |-> ForceMoveAPI.REFUTE, state |-> state]);
            end with;
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


\* BEGIN TRANSLATION - the hash of the PCal code: PCal-7553a0e9503658653aa4bda6917162f2
\* Label TransactionProcessor of process TransactionProcessor at line 192 col 1 changed to TransactionProcessor_
VARIABLES adjudicator, TranactionPool, Alice, alicesActionCount, pc

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

challengeOngoing == adjudicator.mode = ChannelMode.CHALLENGE
channelOpen == adjudicator.mode = ChannelMode.OPEN

increasesTurnNumber(state) == state.turnNumber > adjudicator.turnNumber

validState(c) == c \in ValidStates

validTransition(c) ==
    /\ challengeOngoing
    /\ c.turnNumber = adjudicator.turnNumber + 1

AlicesGoalMet == adjudicator.turnNumber \in TargetTurnNumbers


vars == << adjudicator, TranactionPool, Alice, alicesActionCount, pc >>

ProcSet == {"TransactionProcessor"} \cup {"Alice"} \cup {"Eve"}

Init == (* Global variables *)
        /\ adjudicator = [turnNumber |-> 0, mode |-> ChannelMode.OPEN ]
        /\ TranactionPool = NULL
        /\ Alice \in ParticipantIDXs \ { ParticipantIDX(LatestTurnNumber + 1) }
        /\ alicesActionCount = 0
        /\ pc = [self \in ProcSet |-> CASE self = "TransactionProcessor" -> "TransactionProcessor_"
                                        [] self = "Alice" -> "A"
                                        [] self = "Eve" -> "E"]

TransactionProcessor_ == /\ pc["TransactionProcessor"] = "TransactionProcessor_"
                         /\ IF ~AlicesGoalMet \/ TranactionPool # NULL
                               THEN /\ IF TranactionPool # NULL
                                          THEN /\ IF TranactionPool.type = ForceMoveAPI.FORCE_MOVE
                                                     THEN /\ IF ~validState((TranactionPool.state))
                                                                THEN /\ PrintT((<<"forceMove", (TranactionPool.state)>>))
                                                                     /\ Assert(FALSE, 
                                                                               "Failure of assertion at line 120, column 5 of macro called at line 194, column 66.")
                                                                ELSE /\ TRUE
                                                          /\ IF \/ /\ channelOpen
                                                                   /\ (TranactionPool.state).turnNumber >= adjudicator.turnNumber
                                                                \/ /\ challengeOngoing
                                                                   /\ ForceMoveOverwrites
                                                                   /\ (TranactionPool.state).turnNumber > adjudicator.turnNumber
                                                                THEN /\ adjudicator' = [ mode |-> ChannelMode.CHALLENGE, turnNumber |-> (TranactionPool.state).turnNumber ]
                                                                ELSE /\ TRUE
                                                                     /\ UNCHANGED adjudicator
                                                     ELSE /\ IF TranactionPool.type = ForceMoveAPI.RESPOND
                                                                THEN /\ IF ~validState((TranactionPool.state))
                                                                           THEN /\ PrintT((<<"respond", (TranactionPool.state)>>))
                                                                                /\ Assert(FALSE, 
                                                                                          "Failure of assertion at line 120, column 5 of macro called at line 195, column 66.")
                                                                           ELSE /\ TRUE
                                                                     /\ IF validTransition((TranactionPool.state))
                                                                           THEN /\ Assert(((TranactionPool.state).turnNumber) \in Nat, 
                                                                                          "Failure of assertion at line 126, column 1 of macro called at line 195, column 66.")
                                                                                /\ adjudicator' =                [
                                                                                                      mode |-> ChannelMode.OPEN,
                                                                                                      turnNumber |-> ((TranactionPool.state).turnNumber)
                                                                                                  ]
                                                                           ELSE /\ TRUE
                                                                                /\ UNCHANGED adjudicator
                                                                ELSE /\ IF TranactionPool.type = ForceMoveAPI.REFUTE
                                                                           THEN /\ IF ~validState((TranactionPool.state))
                                                                                      THEN /\ PrintT((<<"refute", (TranactionPool.state)>>))
                                                                                           /\ Assert(FALSE, 
                                                                                                     "Failure of assertion at line 120, column 5 of macro called at line 196, column 66.")
                                                                                      ELSE /\ TRUE
                                                                                /\ IF /\ challengeOngoing
                                                                                      /\ ParticipantIDX((TranactionPool.state).turnNumber) = ParticipantIDX(adjudicator.turnNumber)
                                                                                      /\ (TranactionPool.state).turnNumber > adjudicator.turnNumber
                                                                                      THEN /\ Assert((adjudicator.turnNumber) \in Nat, 
                                                                                                     "Failure of assertion at line 126, column 1 of macro called at line 196, column 66.")
                                                                                           /\ adjudicator' =                [
                                                                                                                 mode |-> ChannelMode.OPEN,
                                                                                                                 turnNumber |-> (adjudicator.turnNumber)
                                                                                                             ]
                                                                                      ELSE /\ TRUE
                                                                                           /\ UNCHANGED adjudicator
                                                                           ELSE /\ IF TranactionPool.type = ForceMoveAPI.CHECKPOINT
                                                                                      THEN /\ IF ~validState((TranactionPool.state))
                                                                                                 THEN /\ PrintT((<<"checkpoint", (TranactionPool.state)>>))
                                                                                                      /\ Assert(FALSE, 
                                                                                                                "Failure of assertion at line 120, column 5 of macro called at line 197, column 66.")
                                                                                                 ELSE /\ TRUE
                                                                                           /\ IF increasesTurnNumber((TranactionPool.state))
                                                                                                 THEN /\ Assert(((TranactionPool.state).turnNumber) \in Nat, 
                                                                                                                "Failure of assertion at line 126, column 1 of macro called at line 197, column 66.")
                                                                                                      /\ adjudicator' =                [
                                                                                                                            mode |-> ChannelMode.OPEN,
                                                                                                                            turnNumber |-> ((TranactionPool.state).turnNumber)
                                                                                                                        ]
                                                                                                 ELSE /\ TRUE
                                                                                                      /\ UNCHANGED adjudicator
                                                                                      ELSE /\ Assert(FALSE, 
                                                                                                     "Failure of assertion at line 198, column 14.")
                                                                                           /\ UNCHANGED adjudicator
                                               /\ TranactionPool' = NULL
                                          ELSE /\ TRUE
                                               /\ UNCHANGED << adjudicator, 
                                                               TranactionPool >>
                                    /\ pc' = [pc EXCEPT !["TransactionProcessor"] = "TransactionProcessor_"]
                               ELSE /\ pc' = [pc EXCEPT !["TransactionProcessor"] = "Done"]
                                    /\ UNCHANGED << adjudicator, 
                                                    TranactionPool >>
                         /\ UNCHANGED << Alice, alicesActionCount >>

TransactionProcessor == TransactionProcessor_

A == /\ pc["Alice"] = "A"
     /\ IF ~AlicesGoalMet
           THEN /\ TranactionPool = NULL
                /\ IF challengeOngoing
                      THEN /\ LET turnNumber == adjudicator.turnNumber IN
                                IF turnNumber < LatestTurnNumber
                                   THEN /\ IF AliceRefutes
                                              THEN /\ LET state ==                                CHOOSE s \in StoredStates :
                                                                   /\ s.turnNumber > adjudicator.turnNumber
                                                                   /\ ParticipantIDX(s.turnNumber) = ParticipantIDX(adjudicator.turnNumber) IN
                                                        /\ IF TranactionPool # NULL
                                                              THEN /\ PrintT((<<TranactionPool, ([ type |-> ForceMoveAPI.REFUTE, state |-> state])>>))
                                                                   /\ Assert(FALSE, 
                                                                             "Failure of assertion at line 180, column 5 of macro called at line 226, column 17.")
                                                              ELSE /\ TRUE
                                                        /\ TranactionPool' = [ type |-> ForceMoveAPI.REFUTE, state |-> state]
                                                        /\ IF CountActions
                                                              THEN /\ alicesActionCount' = alicesActionCount + 1
                                                              ELSE /\ TRUE
                                                                   /\ UNCHANGED alicesActionCount
                                              ELSE /\ TRUE
                                                   /\ UNCHANGED << TranactionPool, 
                                                                   alicesActionCount >>
                                   ELSE /\ TRUE
                                        /\ UNCHANGED << TranactionPool, 
                                                        alicesActionCount >>
                      ELSE /\ IF TranactionPool # NULL
                                 THEN /\ PrintT((<<TranactionPool, ([state |-> [turnNumber |-> LatestTurnNumber ], type |-> ForceMoveAPI.FORCE_MOVE])>>))
                                      /\ Assert(FALSE, 
                                                "Failure of assertion at line 180, column 5 of macro called at line 231, column 9.")
                                 ELSE /\ TRUE
                           /\ TranactionPool' = [state |-> [turnNumber |-> LatestTurnNumber ], type |-> ForceMoveAPI.FORCE_MOVE]
                           /\ IF CountActions
                                 THEN /\ alicesActionCount' = alicesActionCount + 1
                                 ELSE /\ TRUE
                                      /\ UNCHANGED alicesActionCount
                /\ pc' = [pc EXCEPT !["Alice"] = "A"]
           ELSE /\ pc' = [pc EXCEPT !["Alice"] = "Done"]
                /\ UNCHANGED << TranactionPool, alicesActionCount >>
     /\ UNCHANGED << adjudicator, Alice >>

alice == A

E == /\ pc["Eve"] = "E"
     /\ IF ~AlicesGoalMet
           THEN /\ \/ /\ \E state \in EvesSupportedStates:
                           /\ IF ~validState(state)
                                 THEN /\ PrintT((<<"forceMove", state>>))
                                      /\ Assert(FALSE, 
                                                "Failure of assertion at line 120, column 5 of macro called at line 252, column 12.")
                                 ELSE /\ TRUE
                           /\ IF \/ /\ channelOpen
                                    /\ state.turnNumber >= adjudicator.turnNumber
                                 \/ /\ challengeOngoing
                                    /\ ForceMoveOverwrites
                                    /\ state.turnNumber > adjudicator.turnNumber
                                 THEN /\ adjudicator' = [ mode |-> ChannelMode.CHALLENGE, turnNumber |-> state.turnNumber ]
                                 ELSE /\ TRUE
                                      /\ UNCHANGED adjudicator
                   \/ /\ IF challengeOngoing
                            THEN /\ \/ /\ \E state \in EvesSupportedStates:
                                            /\ IF ~validState(state)
                                                  THEN /\ PrintT((<<"respond", state>>))
                                                       /\ Assert(FALSE, 
                                                                 "Failure of assertion at line 120, column 5 of macro called at line 256, column 47.")
                                                  ELSE /\ TRUE
                                            /\ IF validTransition(state)
                                                  THEN /\ Assert((state.turnNumber) \in Nat, 
                                                                 "Failure of assertion at line 126, column 1 of macro called at line 256, column 47.")
                                                       /\ adjudicator' =                [
                                                                             mode |-> ChannelMode.OPEN,
                                                                             turnNumber |-> (state.turnNumber)
                                                                         ]
                                                  ELSE /\ TRUE
                                                       /\ UNCHANGED adjudicator
                                    \/ /\ IF EveCheckpoints
                                             THEN /\ \E state \in EvesSupportedStates:
                                                       /\ IF ~validState(state)
                                                             THEN /\ PrintT((<<"checkpoint", state>>))
                                                                  /\ Assert(FALSE, 
                                                                            "Failure of assertion at line 120, column 5 of macro called at line 257, column 73.")
                                                             ELSE /\ TRUE
                                                       /\ IF increasesTurnNumber(state)
                                                             THEN /\ Assert((state.turnNumber) \in Nat, 
                                                                            "Failure of assertion at line 126, column 1 of macro called at line 257, column 73.")
                                                                  /\ adjudicator' =                [
                                                                                        mode |-> ChannelMode.OPEN,
                                                                                        turnNumber |-> (state.turnNumber)
                                                                                    ]
                                                             ELSE /\ TRUE
                                                                  /\ UNCHANGED adjudicator
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED adjudicator
                                    \/ /\ IF EveRefutes
                                             THEN /\ \E state \in EvesStates:
                                                       /\ IF ~validState(state)
                                                             THEN /\ PrintT((<<"refute", state>>))
                                                                  /\ Assert(FALSE, 
                                                                            "Failure of assertion at line 120, column 5 of macro called at line 258, column 60.")
                                                             ELSE /\ TRUE
                                                       /\ IF /\ challengeOngoing
                                                             /\ ParticipantIDX(state.turnNumber) = ParticipantIDX(adjudicator.turnNumber)
                                                             /\ state.turnNumber > adjudicator.turnNumber
                                                             THEN /\ Assert((adjudicator.turnNumber) \in Nat, 
                                                                            "Failure of assertion at line 126, column 1 of macro called at line 258, column 60.")
                                                                  /\ adjudicator' =                [
                                                                                        mode |-> ChannelMode.OPEN,
                                                                                        turnNumber |-> (adjudicator.turnNumber)
                                                                                    ]
                                                             ELSE /\ TRUE
                                                                  /\ UNCHANGED adjudicator
                                             ELSE /\ TRUE
                                                  /\ UNCHANGED adjudicator
                            ELSE /\ TRUE
                                 /\ UNCHANGED adjudicator
                /\ pc' = [pc EXCEPT !["Eve"] = "E"]
           ELSE /\ pc' = [pc EXCEPT !["Eve"] = "Done"]
                /\ UNCHANGED adjudicator
     /\ UNCHANGED << TranactionPool, Alice, alicesActionCount >>

eve == E

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == TransactionProcessor \/ alice \/ eve
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(TransactionProcessor)
        /\ WF_vars(alice)
        /\ WF_vars(eve)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-909bec0176088e127165e58e0167acee

AllowedTransactions == [ type: Range(ForceMoveAPI), state: ValidStates ]
AllowedChannels == [ mode: Range(ChannelMode), turnNumber: Number ]

\* Safety & liveness properties

TypeOK ==
    /\  adjudicator \in AllowedChannels
    /\  \/ TranactionPool \in AllowedTransactions
        \/ TranactionPool = NULL

AliceCanProgressChannel == <>[](adjudicator.turnNumber \in TargetTurnNumbers)
    
\* We can verify that Alice can never directly modify the adjudicator with this property, with
\* the exception that she can finalize the channel.
AliceMustSubmitTransactions == [][
        /\ TranactionPool = NULL
        /\ TranactionPool' # NULL
    => UNCHANGED adjudicator
]_<<TranactionPool, adjudicator>>

TurnNumberIncrements == [][
    adjudicator'.turnNumber >= adjudicator.turnNumber
]_<<adjudicator>>


\* Alice should be able to accomplish her goal by submitting a single transaction.
AliceCannotBeGriefed == alicesActionCount <= MaxActions

\* Eve front runs if she changes the adjudicator after Alice submitted a transaction, but before 
\* the transaction is processed
\* Violations of this property are therefore _examples_ of Eve's ability to front-run
\* Alice's transactions
EveDoesntFrontRun == [][~(
    /\ TranactionPool # NULL \* transaction has been submitted
    /\ TranactionPool' = TranactionPool \* transaction is not processed
    /\ adjudicator' # adjudicator \* adjudicator is changed
)]_<<TranactionPool, adjudicator>>


=============================================================================
\* Modification History
\* Last modified Fri Jun 12 08:38:05 MDT 2020 by andrewstewart
\* Created Tue Aug 06 14:38:11 MDT 2019 by andrewstewart
