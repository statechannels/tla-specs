----------------------------- MODULE ForceMove -----------------------------
EXTENDS Integers, TLC, Utils
CONSTANTS
    StartingTurnNumber,
    NumParticipants,
    NumHistories,
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
(*  C. someone responds with an alternative move that progresses the       *)
(*     channel                                                             *)
(*                                                                         *)
(* Alice must accept A.  She must also accept C -- indeed, she must accept *)
(* any alternative round that is recorded on chain, since she must have    *)
(* signed exactly one state in that round, and has no control over what    *)
(* the other participants does after that state.  She would be most        *)
(* satisfied with B.                                                       *)
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
  /\ NumHistories \in Nat
            
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
    channel = [turnNumber |-> [p \in ParticipantIDXs |-> 0], mode |-> ChannelMode.OPEN ],
    submittedTX = NULL,
    AlicesIDX \in ParticipantIDXs \ { ParticipantIDX(LatestTurnNumber + 1) },
    counter = 0 \* Auxilliary variable used in some properties and invariants.
    \* We can't specify any properties that require any memory of the
    \* behaviour up to the certain point (ie. the behaviour has passed through state X seven times in a row)
    \* we thus have to embed the "memory" of the behaviour in the state itself,
    \* if we want to check some property the depends on the history of the behaviour

define
Histories == 1..NumHistories
MainHistory == 1

LatestTurnNumber == StartingTurnNumber + NumParticipants - 1
ParticipantIDXs == 1..NumParticipants
ParticipantIDX(turnNumber) == 1 + ((turnNumber - 1) % NumParticipants)
Signer(commitment) == ParticipantIDX(commitment.turnNumber)

MainHistoryTurnNumbers == 0..(StartingTurnNumber + NumParticipants)
ValidCommitments == [ turnNumber: Nat,history: Histories ]
AlicesCommitments == { c \in ValidCommitments :
    /\ c.history = MainHistory
    /\ c.turnNumber \in MainHistoryTurnNumbers
}
StoredCommitments == { c \in AlicesCommitments : c.turnNumber >= StartingTurnNumber }
EvesCommitments == { c \in ValidCommitments : Signer(c) = AlicesIDX => c \in AlicesCommitments }

challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen == channel.mode = ChannelMode.OPEN
progressesChannel(commitment, challenger) == commitment.turnNumber >= channel.turnNumber[challenger]
validCommitment(c) == c \in ValidCommitments
validTransition(commitment) ==
    /\ commitment.turnNumber = channel.challenge.turnNumber + 1
    /\ commitment.history = channel.challenge.history
AlicesMove(turnNumber) == ParticipantIDX(turnNumber) = AlicesIDX
AlicesGoalMet ==
    /\ channel.mode = ChannelMode.CHALLENGE
    /\ channel.challenge.turnNumber = LatestTurnNumber
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
    turnNumber |-> [p \in ParticipantIDXs |-> Maximum(channel.turnNumber[p], turnNumber)]
];
end macro;

macro respondWithMove(commitment)
begin
validateCommitment(commitment, "respond");
if
    /\ challengeOngoing
    /\ validTransition(commitment)
then clearChallenge(commitment.turnNumber);
end if;
end macro;

macro refute(commitment)
begin
validateCommitment(commitment, "refute");
with refutation = commitment.turnNumber do
if
    /\ challengeOngoing
    /\ Signer(commitment) = channel.challenger
    /\ refutation > channel.turnNumber[channel.challenger]
    /\ refutation > channel.challenge.turnNumber
then
channel := [
    mode |-> ChannelMode.OPEN,
    turnNumber |-> [i \in {Signer(commitment)} |-> refutation] @@ channel.turnNumber
    \* By switching to the following effect, we can see how Eve could infinitely grief
    \* with the previous version of the force-move protocol.
\*    turnNumber |-> channel.turnNumber
];
end if; end with;
end macro;

macro forceMove(commitment, challenger)
begin
validateCommitment(commitment, "forceMove");
if
    /\ channelOpen
    /\ progressesChannel(commitment, challenger)
then
    channel := [ mode |-> ChannelMode.CHALLENGE, challenge |-> commitment, challenger |-> challenger ] @@ channel;
    \* By incrementing the number of forceMoves that have been called, we
    \* multiply the number of distinct states by a large amount, but we can specify properties like
    \* "Eve has not submitted 5 force moves"
\*    counter := counter + 1;
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
        if    submittedTX.type = TX_Type.FORCE_MOVE then forceMove(submittedTX.commitment, submittedTX.challenger);
        elsif submittedTX.type = TX_Type.REFUTE     then refute(submittedTX.commitment);
        elsif submittedTX.type = TX_Type.RESPOND    then respondWithMove(submittedTX.commitment);
        else assert FALSE;
        end if;
        submittedTX := NULL;
    end if;
end while;
end process;

fair process alice = "Alice"
begin
(***************************************************************************)
(* Alice has commitments (n - numParticipants)..(n-1).  She wants to end   *)
(* up with commitments (n - numParticipants + 1)..n.                       *)
(*                                                                         *)
(* She is allowed to:                                                      *)
(*   - Call submitForceMove with any states that she currently has         *)
(*   - Call refute with any state that she has                             *)
(*   - Call respondWithMove  whenever there's an active challenge where    *)
(*     it's her turn to move                                               *)
(***************************************************************************)
A:
while ~AlicesGoalMet do
    await submittedTX = NULL;
    if challengeOngoing then with turnNumber = channel.challenge.turnNumber do
        if turnNumber < StartingTurnNumber then
            \* Alice has signed commitments from StartingTurnNumber up to LastTurnNumber.
            \* She can therefore call refute with exactly one commitment, according to
            \* the channel's current turnNumber.
            with  commitment = CHOOSE c \in StoredCommitments : Signer(c) = channel.challenger do 
            submittedTX := [ type |-> TX_Type.REFUTE, commitment |-> commitment]; end with;
        elsif turnNumber < LatestTurnNumber then
            with commitment = CHOOSE c \in StoredCommitments : c.turnNumber = channel.challenge.turnNumber + 1
            do submittedTX := [ type |-> TX_Type.RESPOND, commitment |-> commitment ];
            end with;
        else skip; \* Alice has run out of allowed actions.
        end if;
    end with; else 
        submittedTX := [
            commitment |-> [turnNumber |-> LatestTurnNumber, history |-> MainHistory],
            challenger |-> AlicesIDX,
            type |-> TX_Type.FORCE_MOVE
        ];
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
        with commitment \in {c \in EvesCommitments : c.turnNumber <= LatestTurnNumber },  
             challenger \in ParticipantIDXs \ { AlicesIDX }
        do forceMove(commitment, challenger);
        end with;
    or if challengeOngoing
        then either with commitment = CHOOSE c \in EvesCommitments :
            /\ c.turnNumber = channel.challenge.turnNumber + 1
            /\ c.history = channel.challenge.history
        do respondWithMove(commitment); end with;
        or with commitment = CHOOSE c \in EvesCommitments :
            /\ Signer(c) = channel.challenger
            /\ c.turnNumber > channel.challenge.turnNumber
        do refute(commitment); end with;
        end either;
        end if;
    end either;
end while;
end process;

end algorithm;
*)


\* BEGIN TRANSLATION
VARIABLES channel, submittedTX, AlicesIDX, counter, pc

(* define statement *)
Histories == 1..NumHistories
MainHistory == 1

LatestTurnNumber == StartingTurnNumber + NumParticipants - 1
ParticipantIDXs == 1..NumParticipants
ParticipantIDX(turnNumber) == 1 + ((turnNumber - 1) % NumParticipants)
Signer(commitment) == ParticipantIDX(commitment.turnNumber)

MainHistoryTurnNumbers == 0..(StartingTurnNumber + NumParticipants)
ValidCommitments == [ turnNumber: Nat,history: Histories ]
AlicesCommitments == { c \in ValidCommitments :
    /\ c.history = MainHistory
    /\ c.turnNumber \in MainHistoryTurnNumbers
}
StoredCommitments == { c \in AlicesCommitments : c.turnNumber >= StartingTurnNumber }
EvesCommitments == { c \in ValidCommitments : Signer(c) = AlicesIDX => c \in AlicesCommitments }

challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen == channel.mode = ChannelMode.OPEN
progressesChannel(commitment, challenger) == commitment.turnNumber >= channel.turnNumber[challenger]
validCommitment(c) == c \in ValidCommitments
validTransition(commitment) ==
    /\ commitment.turnNumber = channel.challenge.turnNumber + 1
    /\ commitment.history = channel.challenge.history
AlicesMove(turnNumber) == ParticipantIDX(turnNumber) = AlicesIDX
AlicesGoalMet ==
    /\ channel.mode = ChannelMode.CHALLENGE
    /\ channel.challenge.turnNumber = LatestTurnNumber


vars == << channel, submittedTX, AlicesIDX, counter, pc >>

ProcSet == {"Adjudicator"} \cup {"Alice"} \cup {"Eve"}

Init == (* Global variables *)
        /\ channel = [turnNumber |-> [p \in ParticipantIDXs |-> 0], mode |-> ChannelMode.OPEN ]
        /\ submittedTX = NULL
        /\ AlicesIDX \in ParticipantIDXs \ { ParticipantIDX(LatestTurnNumber + 1) }
        /\ counter = 0
        /\ pc = [self \in ProcSet |-> CASE self = "Adjudicator" -> "Adjudicator"
                                        [] self = "Alice" -> "A"
                                        [] self = "Eve" -> "E"]

Adjudicator == /\ pc["Adjudicator"] = "Adjudicator"
               /\ IF ~AlicesGoalMet \/ submittedTX # NULL
                     THEN /\ IF submittedTX # NULL
                                THEN /\ IF submittedTX.type = TX_Type.FORCE_MOVE
                                           THEN /\ IF ~validCommitment((submittedTX.commitment))
                                                      THEN /\ PrintT((<<"forceMove", (submittedTX.commitment)>>))
                                                           /\ Assert(FALSE, 
                                                                     "Failure of assertion at line 108, column 5 of macro called at line 174, column 58.")
                                                      ELSE /\ TRUE
                                                /\ IF /\ channelOpen
                                                      /\ progressesChannel((submittedTX.commitment), (submittedTX.challenger))
                                                      THEN /\ channel' = [ mode |-> ChannelMode.CHALLENGE, challenge |-> (submittedTX.commitment), challenger |-> (submittedTX.challenger) ] @@ channel
                                                      ELSE /\ TRUE
                                                           /\ UNCHANGED channel
                                           ELSE /\ IF submittedTX.type = TX_Type.REFUTE
                                                      THEN /\ IF ~validCommitment((submittedTX.commitment))
                                                                 THEN /\ PrintT((<<"refute", (submittedTX.commitment)>>))
                                                                      /\ Assert(FALSE, 
                                                                                "Failure of assertion at line 108, column 5 of macro called at line 175, column 58.")
                                                                 ELSE /\ TRUE
                                                           /\ LET refutation == (submittedTX.commitment).turnNumber IN
                                                                IF /\ challengeOngoing
                                                                   /\ Signer((submittedTX.commitment)) = channel.challenger
                                                                   /\ refutation > channel.turnNumber[channel.challenger]
                                                                   /\ refutation > channel.challenge.turnNumber
                                                                   THEN /\ channel' =            [
                                                                                          mode |-> ChannelMode.OPEN,
                                                                                          turnNumber |-> [i \in {Signer((submittedTX.commitment))} |-> refutation] @@ channel.turnNumber
                                                                                      
                                                                                      
                                                                                      
                                                                                      ]
                                                                   ELSE /\ TRUE
                                                                        /\ UNCHANGED channel
                                                      ELSE /\ IF submittedTX.type = TX_Type.RESPOND
                                                                 THEN /\ IF ~validCommitment((submittedTX.commitment))
                                                                            THEN /\ PrintT((<<"respond", (submittedTX.commitment)>>))
                                                                                 /\ Assert(FALSE, 
                                                                                           "Failure of assertion at line 108, column 5 of macro called at line 176, column 58.")
                                                                            ELSE /\ TRUE
                                                                      /\ IF /\ challengeOngoing
                                                                            /\ validTransition((submittedTX.commitment))
                                                                            THEN /\ Assert(((submittedTX.commitment).turnNumber) \in Nat, 
                                                                                           "Failure of assertion at line 114, column 1 of macro called at line 176, column 58.")
                                                                                 /\ channel' =            [
                                                                                                   mode |-> ChannelMode.OPEN,
                                                                                                   turnNumber |-> [p \in ParticipantIDXs |-> Maximum(channel.turnNumber[p], ((submittedTX.commitment).turnNumber))]
                                                                                               ]
                                                                            ELSE /\ TRUE
                                                                                 /\ UNCHANGED channel
                                                                 ELSE /\ Assert(FALSE, 
                                                                                "Failure of assertion at line 177, column 14.")
                                                                      /\ UNCHANGED channel
                                     /\ submittedTX' = NULL
                                ELSE /\ TRUE
                                     /\ UNCHANGED << channel, submittedTX >>
                          /\ pc' = [pc EXCEPT !["Adjudicator"] = "Adjudicator"]
                     ELSE /\ pc' = [pc EXCEPT !["Adjudicator"] = "Done"]
                          /\ UNCHANGED << channel, submittedTX >>
               /\ UNCHANGED << AlicesIDX, counter >>

adjudicator == Adjudicator

A == /\ pc["Alice"] = "A"
     /\ IF ~AlicesGoalMet
           THEN /\ submittedTX = NULL
                /\ IF challengeOngoing
                      THEN /\ LET turnNumber == channel.challenge.turnNumber IN
                                IF turnNumber < StartingTurnNumber
                                   THEN /\ LET commitment == CHOOSE c \in StoredCommitments : Signer(c) = channel.challenger IN
                                             submittedTX' = [ type |-> TX_Type.REFUTE, commitment |-> commitment]
                                   ELSE /\ IF turnNumber < LatestTurnNumber
                                              THEN /\ LET commitment == CHOOSE c \in StoredCommitments : c.turnNumber = channel.challenge.turnNumber + 1 IN
                                                        submittedTX' = [ type |-> TX_Type.RESPOND, commitment |-> commitment ]
                                              ELSE /\ TRUE
                                                   /\ UNCHANGED submittedTX
                      ELSE /\ submittedTX' =                [
                                                 commitment |-> [turnNumber |-> LatestTurnNumber, history |-> MainHistory],
                                                 challenger |-> AlicesIDX,
                                                 type |-> TX_Type.FORCE_MOVE
                                             ]
                /\ pc' = [pc EXCEPT !["Alice"] = "A"]
           ELSE /\ pc' = [pc EXCEPT !["Alice"] = "Done"]
                /\ UNCHANGED submittedTX
     /\ UNCHANGED << channel, AlicesIDX, counter >>

alice == A

E == /\ pc["Eve"] = "E"
     /\ IF ~AlicesGoalMet
           THEN /\ \/ /\ \E commitment \in {c \in EvesCommitments : c.turnNumber <= LatestTurnNumber }:
                           \E challenger \in ParticipantIDXs \ { AlicesIDX }:
                             /\ IF ~validCommitment(commitment)
                                   THEN /\ PrintT((<<"forceMove", commitment>>))
                                        /\ Assert(FALSE, 
                                                  "Failure of assertion at line 108, column 5 of macro called at line 246, column 12.")
                                   ELSE /\ TRUE
                             /\ IF /\ channelOpen
                                   /\ progressesChannel(commitment, challenger)
                                   THEN /\ channel' = [ mode |-> ChannelMode.CHALLENGE, challenge |-> commitment, challenger |-> challenger ] @@ channel
                                   ELSE /\ TRUE
                                        /\ UNCHANGED channel
                   \/ /\ IF challengeOngoing
                            THEN /\ \/ /\ LET commitment ==                           CHOOSE c \in EvesCommitments :
                                                            /\ c.turnNumber = channel.challenge.turnNumber + 1
                                                            /\ c.history = channel.challenge.history IN
                                            /\ IF ~validCommitment(commitment)
                                                  THEN /\ PrintT((<<"respond", commitment>>))
                                                       /\ Assert(FALSE, 
                                                                 "Failure of assertion at line 108, column 5 of macro called at line 252, column 12.")
                                                  ELSE /\ TRUE
                                            /\ IF /\ challengeOngoing
                                                  /\ validTransition(commitment)
                                                  THEN /\ Assert((commitment.turnNumber) \in Nat, 
                                                                 "Failure of assertion at line 114, column 1 of macro called at line 252, column 12.")
                                                       /\ channel' =            [
                                                                         mode |-> ChannelMode.OPEN,
                                                                         turnNumber |-> [p \in ParticipantIDXs |-> Maximum(channel.turnNumber[p], (commitment.turnNumber))]
                                                                     ]
                                                  ELSE /\ TRUE
                                                       /\ UNCHANGED channel
                                    \/ /\ LET commitment ==                  CHOOSE c \in EvesCommitments :
                                                            /\ Signer(c) = channel.challenger
                                                            /\ c.turnNumber > channel.challenge.turnNumber IN
                                            /\ IF ~validCommitment(commitment)
                                                  THEN /\ PrintT((<<"refute", commitment>>))
                                                       /\ Assert(FALSE, 
                                                                 "Failure of assertion at line 108, column 5 of macro called at line 256, column 12.")
                                                  ELSE /\ TRUE
                                            /\ LET refutation == commitment.turnNumber IN
                                                 IF /\ challengeOngoing
                                                    /\ Signer(commitment) = channel.challenger
                                                    /\ refutation > channel.turnNumber[channel.challenger]
                                                    /\ refutation > channel.challenge.turnNumber
                                                    THEN /\ channel' =            [
                                                                           mode |-> ChannelMode.OPEN,
                                                                           turnNumber |-> [i \in {Signer(commitment)} |-> refutation] @@ channel.turnNumber
                                                                       
                                                                       
                                                                       
                                                                       ]
                                                    ELSE /\ TRUE
                                                         /\ UNCHANGED channel
                            ELSE /\ TRUE
                                 /\ UNCHANGED channel
                /\ pc' = [pc EXCEPT !["Eve"] = "E"]
           ELSE /\ pc' = [pc EXCEPT !["Eve"] = "Done"]
                /\ UNCHANGED channel
     /\ UNCHANGED << submittedTX, AlicesIDX, counter >>

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

\* END TRANSLATION

AllowedTransactions == { NULL }
    \cup [ type: { TX_Type.REFUTE, TX_Type.RESPOND }, commitment: ValidCommitments ]
    \cup [ type: { TX_Type.FORCE_MOVE }, commitment: ValidCommitments, challenger: { AlicesIDX } ]
OpenChannels == [mode: { ChannelMode.OPEN }, turnNumber: [ParticipantIDXs -> Nat]]
ChallengeChannels == {
    c \in [
        mode: { ChannelMode.CHALLENGE },
        turnNumber: [ParticipantIDXs -> Nat],
        challenge: ValidCommitments,
        challenger: ParticipantIDXs
        
    ] : c.challenge.turnNumber >= c.turnNumber[c.challenger]
   
}
AllowedChannels == OpenChannels \cup ChallengeChannels

\* Safety & liveness properties

TypeOK ==
  /\ channel \in AllowedChannels
  /\ submittedTX \in AllowedTransactions

AliceCanProgressChannel == <>[](
    /\ channel.mode = ChannelMode.CHALLENGE
    /\ channel.challenge.turnNumber = LatestTurnNumber
)
    
\* We can verify that Alice can never directly modify the channel with this property, with
\* the exception that she can finalize the channel.
AliceMustSubmitTransactions == [][
        /\ pc["Alice"] = "AliceTakesAction"
        /\ pc'["Alice"] = "AliceMoves"
    => UNCHANGED channel
]_<<pc, channel>>

TurnNumberIncrements == [][
    \A p \in ParticipantIDXs : channel'.turnNumber[p] >= channel.turnNumber[p]
]_<<channel>>

\* It's useful to specify the following invariants or properties, since we can
\* inspect the trace of behaviours that violate them to verify that the model
\* checker is working as intended.

EveCanGrieveAlice == counter < 5

\* Behaviours that violate this property exhibit Eve's ability to front-run:
\* Alice always submits a transaction that would change the channel state, if
\* it took effect immediately. Therefore, if the channel state is not changed
\* when a pending transaction is processed, Eve must have called a function
\* already.
EveCannotFrontRun ==[][
        /\ submittedTX # NULL
        /\ submittedTX' = NULL
    =>
        \/ channel' # channel
        \* By uncommenting the following line, one can inspect traces where Eve might
        \* have front-run Alice multiple times
\*        \/ counter <= 3
]_<<submittedTX, channel>>


=============================================================================
\* Modification History
\* Last modified Thu Sep 12 15:55:13 MDT 2019 by andrewstewart
\* Created Tue Aug 06 14:38:11 MDT 2019 by andrewstewart
