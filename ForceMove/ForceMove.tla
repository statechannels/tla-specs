----------------------------- MODULE ForceMove -----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS
    StartingTurnNumber,
    NumParticipants,
    AlicesIDX,
    NULL \* A model value representing null.

ChannelMode == [
  OPEN |-> "OPEN",
  CHALLENGE  |-> "CHALLENGE"
]

TX_Type == [
  FORCE_MOVE |-> "FORCE_MOVE",
  REFUTE     |-> "REFUTE",
  RESPOND    |-> "RESPOND"
]

Range(f) == { f[x] : x \in DOMAIN f }
Maximum(a,b) == IF a > b THEN a ELSE b

LatestTurnNumber == StartingTurnNumber + NumParticipants - 1
AlicesCommitments == StartingTurnNumber..LatestTurnNumber

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

ParticipantIDXs == 1..NumParticipants
ParticipantIDX(turnNumber) == 1 + ((turnNumber - 1) % NumParticipants)
AlicesMove(turnNumber) == ParticipantIDX(turnNumber) = AlicesIDX

ASSUME
  /\ StartingTurnNumber \in Nat
  /\ NumParticipants \in Nat \ { 1 }
  /\ AlicesIDX \in ParticipantIDXs
  /\ ~AlicesMove(LatestTurnNumber + 1)
            
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
    channel = [turnNumber |-> [p \in ParticipantIDXs |-> 0], mode |-> ChannelMode.OPEN, challenge |-> NULL ],
    submittedTX = NULL,
    numForces = 0

define
challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen == channel.mode = ChannelMode.OPEN
progressesChannel(commitment) == commitment.turnNumber >= channel.turnNumber[commitment.signer]
validCommitment(c) == c \in [ turnNumber: Nat, signer: ParticipantIDXs ]
validTransition(commitment) ==
    /\ commitment.turnNumber = channel.challenge.turnNumber + 1
    /\ commitment.signer = ParticipantIDX(commitment.turnNumber)
AlicesGoalMet ==
    /\ channel.mode = ChannelMode.CHALLENGE
    /\ channel.challenge.turnNumber = LatestTurnNumber
end define;

macro clearChallenge(turnNumber)
begin
assert turnNumber \in Nat;
channel := [
    mode |-> ChannelMode.OPEN,
    turnNumber |-> [p \in ParticipantIDXs |-> Maximum(channel.turnNumber[p], turnNumber)],
    challenge |-> NULL
];
end macro;

macro respondWithMove(commitment)
begin
if
    /\ challengeOngoing
    /\ validTransition(commitment)
then clearChallenge(commitment.turnNumber);
end if;
end macro;

macro refute(turnNumber)
begin
if
    /\ challengeOngoing
    /\ ParticipantIDX(turnNumber) = channel.challenge.signer
    /\ turnNumber > channel.turnNumber[ParticipantIDX(turnNumber)]
    /\ turnNumber > channel.challenge.turnNumber
then
channel := [
    mode |-> ChannelMode.OPEN,
    challenge  |-> NULL,
    turnNumber |-> [i \in {ParticipantIDX(turnNumber)} |-> turnNumber] @@ channel.turnNumber
    \* By switching to the following effect, we can see how Eve could infinitely grief
    \* with the previous version of the force-move protocol.
\*    turnNumber |-> channel.turnNumber
];
end if;
end macro;

macro forceMove(commitment)
begin
if
    /\ channelOpen
    /\ progressesChannel(commitment)
then
    channel := [ mode |-> ChannelMode.CHALLENGE, challenge |-> commitment ] @@ channel;
    
    \* We can't specify any properties that require any memory of the
    \* behaviour up to the certain point (ie. the behaviour has passed through state X seven times in a row)
    \* we have to embed the "memory" of the behaviour in the state itself.
    \* By incrementing the number of forceMoves that have been called, we
    \* multiply the number of distinct states by a large amount, but we can specify properties like
    \* "Eve has not submitted 5 force moves"
\*    numForces := numForces + 1;
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
        if    submittedTX.type = TX_Type.FORCE_MOVE then forceMove(submittedTX.commitment);
        elsif submittedTX.type = TX_Type.REFUTE     then refute(submittedTX.turnNumber);
        elsif submittedTX.type = TX_Type.RESPOND    then respondWithMove(submittedTX.commitment);
        else assert FALSE;
        end if;
        submittedTX := NULL;
    end if;
end while;
end process;

fair process alice = "Alice"
begin
(****************************************************************************
Alice has commitments (n - numParticipants)..(n-1).  She wants to end
up with commitments (n - numParticipants + 1)..n.

She is allowed to:
  - Call submitForceMove with any states that she currently has
  - Call refute with any state that she has
  - Call respondWithMove or respondWithMove whenever there's an active
    challenge where it's her turn to move
****************************************************************************)
A:
while ~AlicesGoalMet do
    await submittedTX = NULL;
    if challengeOngoing then with turnNumber = channel.challenge.turnNumber do
        if turnNumber < StartingTurnNumber then
            \* Alice has signed commitments from StartingTurnNumber up to LastTurnNumber.
            \* She can therefore call refute with exactly one commitment, according to
            \* the channel's current turnNumber.
            with refutation = CHOOSE n \in AlicesCommitments : ParticipantIDX(n) = channel.challenge.signer
            do submittedTX := [ type |-> TX_Type.REFUTE, turnNumber |-> refutation]; end with;
        elsif turnNumber < LatestTurnNumber then
            with response = turnNumber + 1,
                 commitment = [ turnNumber |-> response, signer |-> ParticipantIDX(response) ]
            do
                assert response \in AlicesCommitments;
                submittedTX := [ type |-> TX_Type.RESPOND, commitment |-> commitment ];
            end with;
        else skip; \* Alice has run out of allowed actions.
        end if;
    end with; else 
        submittedTX := [
            commitment |-> [ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ],
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
E:
while ~AlicesGoalMet do
    either
        with n \in NumParticipants..LatestTurnNumber,
             idx \in ParticipantIDXs \ { AlicesIDX }
        do
            forceMove([ turnNumber |-> n, signer |-> idx ]);
        end with;
    or if challengeOngoing
        then either with
            turnNumber = channel.challenge.turnNumber + 1,
            commitment = [ turnNumber |-> turnNumber, signer |-> ParticipantIDX(turnNumber)]
        do respondWithMove(commitment); end with;
        or with turnNumber \in {}
            \* Eve can refute with any state she has. Alice has seen all of these states.
            \cup 0..LatestTurnNumber
            \* Since Eve can sign arbitrary data with any private key other than Alice's,
            \* she can also refute with arbitrarily states, as long as it's not Alice's
            \* turn in that state.
            \cup { n \in Nat : ~AlicesMove(n) }
        do refute(turnNumber); end with;
        end either;
        end if;
    or skip; \* Eve goes offline
    end either;
end while;
end process;

end algorithm;
*)


\* BEGIN TRANSLATION
VARIABLES channel, submittedTX, numForces, pc

(* define statement *)
challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen == channel.mode = ChannelMode.OPEN
progressesChannel(commitment) == commitment.turnNumber >= channel.turnNumber[commitment.signer]
validCommitment(c) == c \in [ turnNumber: Nat, signer: ParticipantIDXs ]
validTransition(commitment) ==
    /\ commitment.turnNumber = channel.challenge.turnNumber + 1
    /\ commitment.signer = ParticipantIDX(commitment.turnNumber)
AlicesGoalMet ==
    /\ channel.mode = ChannelMode.CHALLENGE
    /\ channel.challenge.turnNumber = LatestTurnNumber


vars == << channel, submittedTX, numForces, pc >>

ProcSet == {"Adjudicator"} \cup {"Alice"} \cup {"Eve"}

Init == (* Global variables *)
        /\ channel = [turnNumber |-> [p \in ParticipantIDXs |-> 0], mode |-> ChannelMode.OPEN, challenge |-> NULL ]
        /\ submittedTX = NULL
        /\ numForces = 0
        /\ pc = [self \in ProcSet |-> CASE self = "Adjudicator" -> "Adjudicator"
                                        [] self = "Alice" -> "A"
                                        [] self = "Eve" -> "E"]

Adjudicator == /\ pc["Adjudicator"] = "Adjudicator"
               /\ IF ~AlicesGoalMet \/ submittedTX # NULL
                     THEN /\ IF submittedTX # NULL
                                THEN /\ IF submittedTX.type = TX_Type.FORCE_MOVE
                                           THEN /\ IF /\ channelOpen
                                                      /\ progressesChannel((submittedTX.commitment))
                                                      THEN /\ channel' = [ mode |-> ChannelMode.CHALLENGE, challenge |-> (submittedTX.commitment) ] @@ channel
                                                      ELSE /\ TRUE
                                                           /\ UNCHANGED channel
                                           ELSE /\ IF submittedTX.type = TX_Type.REFUTE
                                                      THEN /\ IF /\ challengeOngoing
                                                                 /\ ParticipantIDX((submittedTX.turnNumber)) = channel.challenge.signer
                                                                 /\ (submittedTX.turnNumber) > channel.turnNumber[ParticipantIDX((submittedTX.turnNumber))]
                                                                 /\ (submittedTX.turnNumber) > channel.challenge.turnNumber
                                                                 THEN /\ channel' =            [
                                                                                        mode |-> ChannelMode.OPEN,
                                                                                        challenge  |-> NULL,
                                                                                        turnNumber |-> [i \in {ParticipantIDX((submittedTX.turnNumber))} |-> (submittedTX.turnNumber)] @@ channel.turnNumber
                                                                                    
                                                                                    
                                                                                    
                                                                                    ]
                                                                 ELSE /\ TRUE
                                                                      /\ UNCHANGED channel
                                                      ELSE /\ IF submittedTX.type = TX_Type.RESPOND
                                                                 THEN /\ IF /\ challengeOngoing
                                                                            /\ validTransition((submittedTX.commitment))
                                                                            THEN /\ Assert(((submittedTX.commitment).turnNumber) \in Nat, 
                                                                                           "Failure of assertion at line 104, column 1 of macro called at line 168, column 58.")
                                                                                 /\ channel' =            [
                                                                                                   mode |-> ChannelMode.OPEN,
                                                                                                   turnNumber |-> [p \in ParticipantIDXs |-> Maximum(channel.turnNumber[p], ((submittedTX.commitment).turnNumber))],
                                                                                                   challenge |-> NULL
                                                                                               ]
                                                                            ELSE /\ TRUE
                                                                                 /\ UNCHANGED channel
                                                                 ELSE /\ Assert(FALSE, 
                                                                                "Failure of assertion at line 169, column 14.")
                                                                      /\ UNCHANGED channel
                                     /\ submittedTX' = NULL
                                ELSE /\ TRUE
                                     /\ UNCHANGED << channel, submittedTX >>
                          /\ pc' = [pc EXCEPT !["Adjudicator"] = "Adjudicator"]
                     ELSE /\ pc' = [pc EXCEPT !["Adjudicator"] = "Done"]
                          /\ UNCHANGED << channel, submittedTX >>
               /\ UNCHANGED numForces

adjudicator == Adjudicator

A == /\ pc["Alice"] = "A"
     /\ IF ~AlicesGoalMet
           THEN /\ submittedTX = NULL
                /\ IF challengeOngoing
                      THEN /\ LET turnNumber == channel.challenge.turnNumber IN
                                IF turnNumber < StartingTurnNumber
                                   THEN /\ LET refutation == CHOOSE n \in AlicesCommitments : ParticipantIDX(n) = channel.challenge.signer IN
                                             submittedTX' = [ type |-> TX_Type.REFUTE, turnNumber |-> refutation]
                                   ELSE /\ IF turnNumber < LatestTurnNumber
                                              THEN /\ LET response == turnNumber + 1 IN
                                                        LET commitment == [ turnNumber |-> response, signer |-> ParticipantIDX(response) ] IN
                                                          /\ Assert(response \in AlicesCommitments, 
                                                                    "Failure of assertion at line 202, column 17.")
                                                          /\ submittedTX' = [ type |-> TX_Type.RESPOND, commitment |-> commitment ]
                                              ELSE /\ TRUE
                                                   /\ UNCHANGED submittedTX
                      ELSE /\ submittedTX' =                [
                                                 commitment |-> [ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ],
                                                 type |-> TX_Type.FORCE_MOVE
                                             ]
                /\ pc' = [pc EXCEPT !["Alice"] = "A"]
           ELSE /\ pc' = [pc EXCEPT !["Alice"] = "Done"]
                /\ UNCHANGED submittedTX
     /\ UNCHANGED << channel, numForces >>

alice == A

E == /\ pc["Eve"] = "E"
     /\ IF ~AlicesGoalMet
           THEN /\ \/ /\ \E n \in NumParticipants..LatestTurnNumber:
                           \E idx \in ParticipantIDXs \ { AlicesIDX }:
                             IF /\ channelOpen
                                /\ progressesChannel(([ turnNumber |-> n, signer |-> idx ]))
                                THEN /\ channel' = [ mode |-> ChannelMode.CHALLENGE, challenge |-> ([ turnNumber |-> n, signer |-> idx ]) ] @@ channel
                                ELSE /\ TRUE
                                     /\ UNCHANGED channel
                   \/ /\ IF challengeOngoing
                            THEN /\ \/ /\ LET turnNumber == channel.challenge.turnNumber + 1 IN
                                            LET commitment == [ turnNumber |-> turnNumber, signer |-> ParticipantIDX(turnNumber)] IN
                                              IF /\ challengeOngoing
                                                 /\ validTransition(commitment)
                                                 THEN /\ Assert((commitment.turnNumber) \in Nat, 
                                                                "Failure of assertion at line 104, column 1 of macro called at line 243, column 12.")
                                                      /\ channel' =            [
                                                                        mode |-> ChannelMode.OPEN,
                                                                        turnNumber |-> [p \in ParticipantIDXs |-> Maximum(channel.turnNumber[p], (commitment.turnNumber))],
                                                                        challenge |-> NULL
                                                                    ]
                                                 ELSE /\ TRUE
                                                      /\ UNCHANGED channel
                                    \/ /\ \E turnNumber \in                    {}
                                                            
                                                            \cup 0..LatestTurnNumber
                                                            
                                                            
                                                            
                                                            \cup { n \in Nat : ~AlicesMove(n) }:
                                            IF /\ challengeOngoing
                                               /\ ParticipantIDX(turnNumber) = channel.challenge.signer
                                               /\ turnNumber > channel.turnNumber[ParticipantIDX(turnNumber)]
                                               /\ turnNumber > channel.challenge.turnNumber
                                               THEN /\ channel' =            [
                                                                      mode |-> ChannelMode.OPEN,
                                                                      challenge  |-> NULL,
                                                                      turnNumber |-> [i \in {ParticipantIDX(turnNumber)} |-> turnNumber] @@ channel.turnNumber
                                                                  
                                                                  
                                                                  
                                                                  ]
                                               ELSE /\ TRUE
                                                    /\ UNCHANGED channel
                            ELSE /\ TRUE
                                 /\ UNCHANGED channel
                   \/ /\ TRUE
                      /\ UNCHANGED channel
                /\ pc' = [pc EXCEPT !["Eve"] = "E"]
           ELSE /\ pc' = [pc EXCEPT !["Eve"] = "Done"]
                /\ UNCHANGED channel
     /\ UNCHANGED << submittedTX, numForces >>

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

AllowedTurnNumbers == 0..(StartingTurnNumber + NumParticipants)
AllowedCommitments == [ turnNumber: AllowedTurnNumbers, signer: ParticipantIDXs ]

AllowedTransactions == { NULL }
    \cup [ type: { TX_Type.FORCE_MOVE, TX_Type.RESPOND }, commitment: AllowedCommitments ]
    \cup [ type: { TX_Type.REFUTE }, turnNumber: AllowedTurnNumbers ]

AllowedChannels == [ turnNumber: [ParticipantIDXs -> Nat] , mode: Range(ChannelMode), challenge: AllowedCommitments \cup { NULL } ]

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

\* It's useful to specify the following invariants or properties, since we can
\* inspect the trace of behaviours that violate them to verify that the model
\* checker is working as intended.

EveCanGrieveAlice == numForces < 5

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
\*        \/ numForces <= 3
]_<<submittedTX, channel>>


=============================================================================
\* Modification History
\* Last modified Tue Sep 10 18:34:08 MDT 2019 by andrewstewart
\* Created Tue Aug 06 14:38:11 MDT 2019 by andrewstewart
