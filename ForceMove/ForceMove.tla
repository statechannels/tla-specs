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


TX_Type == [
  FORCE_MOVE |-> "FORCE_MOVE",
  REFUTE     |-> "REFUTE",
  RESPOND    |-> "RESPOND"
]

Range(f) == { f[x] : x \in DOMAIN f }
Maximum(a,b) == IF a > b THEN a ELSE b

LatestTurnNumber == StartingTurnNumber + NumParticipants - 1
AlicesGoalTurnNumber == LatestTurnNumber + 1
AlicesCommitments == StartingTurnNumber..LatestTurnNumber

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
AlicesGoalUnmet ==
    /\ channel.mode # ChannelMode.FINALIZED
    /\ channel.turnNumber[AlicesIDX] < AlicesGoalTurnNumber
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
    /\ turnNumber > channel.turnNumber[ParticipantIDX(turnNumber)]
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
while AlicesGoalUnmet do AdjudicatorProcesses:
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

fair process alice = Alice
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
AliceMoves:
while AlicesGoalUnmet do AliceTakesAction:
    if
        /\ submittedTX = NULL
        /\ challengeOngoing
    then
        if
            /\ channel.challenge.turnNumber < StartingTurnNumber
            /\ submittedTX = NULL
        then
            \* Alice has signed commitments from StartingTurnNumber up to LastTurnNumber.
            \* She can therefore call refute with exactly one commitment, according to
            \* the channel's current turnNumber.
            with turnNumber = CHOOSE n \in AlicesCommitments : ParticipantIDX(n) = channel.challenge.signer
            do submittedTX := [ type |-> TX_Type.REFUTE, turnNumber |-> turnNumber];
            end with;
        elsif
            /\ channel.challenge.turnNumber >= StartingTurnNumber
            /\ AlicesMove(channel.challenge.turnNumber+1)
        then
                with commitment = [ turnNumber |-> channel.challenge.turnNumber + 1, signer |-> AlicesIDX ]
                do submittedTX := [ type |-> TX_Type.RESPOND, commitment |-> commitment ];
                end with;
        else
        \* Alice has run out of allowed actions, resulting in the channel being finalized
            channel := [ mode |-> ChannelMode.FINALIZED, turnNumber |-> [p \in ParticipantIDXs |-> channel.challenge.turnNumber] ] @@ channel;
        end if;
    elsif
        /\ submittedTX = NULL
        /\ ~challengeOngoing
    then 
        submittedTX := [
            commitment |-> [ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ],
            type |-> TX_Type.FORCE_MOVE
        ];
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
while AlicesGoalUnmet do EveTakesAction:
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
        or with turnNumber \in 0..LatestTurnNumber \cup { n \in Nat : n > LatestTurnNumber /\ ~AlicesMove(n) }
        do refute(turnNumber); end with;
        end either;
        end if;
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
AlicesGoalUnmet ==
    /\ channel.mode # ChannelMode.FINALIZED
    /\ channel.turnNumber[AlicesIDX] < AlicesGoalTurnNumber


vars == << channel, submittedTX, numForces, pc >>

ProcSet == {"Adjudicator"} \cup {Alice} \cup {Eve}

Init == (* Global variables *)
        /\ channel = [turnNumber |-> [p \in ParticipantIDXs |-> 0], mode |-> ChannelMode.OPEN, challenge |-> NULL ]
        /\ submittedTX = NULL
        /\ numForces = 0
        /\ pc = [self \in ProcSet |-> CASE self = "Adjudicator" -> "Adjudicator"
                                        [] self = Alice -> "AliceMoves"
                                        [] self = Eve -> "EveMoves"]

Adjudicator == /\ pc["Adjudicator"] = "Adjudicator"
               /\ IF AlicesGoalUnmet
                     THEN /\ pc' = [pc EXCEPT !["Adjudicator"] = "AdjudicatorProcesses"]
                     ELSE /\ pc' = [pc EXCEPT !["Adjudicator"] = "Done"]
               /\ UNCHANGED << channel, submittedTX, numForces >>

AdjudicatorProcesses == /\ pc["Adjudicator"] = "AdjudicatorProcesses"
                        /\ IF submittedTX # NULL
                              THEN /\ IF submittedTX.type = TX_Type.FORCE_MOVE
                                         THEN /\ IF /\ channelOpen
                                                    /\ progressesChannel((submittedTX.commitment))
                                                    THEN /\ channel' = [ mode |-> ChannelMode.CHALLENGE, challenge |-> (submittedTX.commitment) ] @@ channel
                                                    ELSE /\ TRUE
                                                         /\ UNCHANGED channel
                                         ELSE /\ IF submittedTX.type = TX_Type.REFUTE
                                                    THEN /\ IF /\ challengeOngoing
                                                               /\ (submittedTX.turnNumber) > channel.turnNumber[ParticipantIDX((submittedTX.turnNumber))]
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
                                                                                         "Failure of assertion at line 73, column 1 of macro called at line 135, column 58.")
                                                                               /\ channel' =            [
                                                                                                 mode |-> ChannelMode.OPEN,
                                                                                                 turnNumber |-> [p \in ParticipantIDXs |-> Maximum(channel.turnNumber[p], ((submittedTX.commitment).turnNumber))],
                                                                                                 challenge |-> NULL
                                                                                             ]
                                                                          ELSE /\ TRUE
                                                                               /\ UNCHANGED channel
                                                               ELSE /\ Assert(FALSE, 
                                                                              "Failure of assertion at line 136, column 14.")
                                                                    /\ UNCHANGED channel
                                   /\ submittedTX' = NULL
                              ELSE /\ TRUE
                                   /\ UNCHANGED << channel, submittedTX >>
                        /\ pc' = [pc EXCEPT !["Adjudicator"] = "Adjudicator"]
                        /\ UNCHANGED numForces

adjudicator == Adjudicator \/ AdjudicatorProcesses

AliceMoves == /\ pc[Alice] = "AliceMoves"
              /\ IF AlicesGoalUnmet
                    THEN /\ pc' = [pc EXCEPT ![Alice] = "AliceTakesAction"]
                    ELSE /\ pc' = [pc EXCEPT ![Alice] = "Done"]
              /\ UNCHANGED << channel, submittedTX, numForces >>

AliceTakesAction == /\ pc[Alice] = "AliceTakesAction"
                    /\ IF /\ submittedTX = NULL
                          /\ challengeOngoing
                          THEN /\ IF /\ channel.challenge.turnNumber < StartingTurnNumber
                                     /\ submittedTX = NULL
                                     THEN /\ LET turnNumber == CHOOSE n \in AlicesCommitments : ParticipantIDX(n) = channel.challenge.signer IN
                                               submittedTX' = [ type |-> TX_Type.REFUTE, turnNumber |-> turnNumber]
                                          /\ UNCHANGED channel
                                     ELSE /\ IF /\ channel.challenge.turnNumber >= StartingTurnNumber
                                                /\ AlicesMove(channel.challenge.turnNumber+1)
                                                THEN /\ LET commitment == [ turnNumber |-> channel.challenge.turnNumber + 1, signer |-> AlicesIDX ] IN
                                                          submittedTX' = [ type |-> TX_Type.RESPOND, commitment |-> commitment ]
                                                     /\ UNCHANGED channel
                                                ELSE /\ channel' = [ mode |-> ChannelMode.FINALIZED, turnNumber |-> [p \in ParticipantIDXs |-> channel.challenge.turnNumber] ] @@ channel
                                                     /\ UNCHANGED submittedTX
                          ELSE /\ IF /\ submittedTX = NULL
                                     /\ ~challengeOngoing
                                     THEN /\ submittedTX' =                [
                                                                commitment |-> [ turnNumber |-> LatestTurnNumber, signer |-> AlicesIDX ],
                                                                type |-> TX_Type.FORCE_MOVE
                                                            ]
                                     ELSE /\ TRUE
                                          /\ UNCHANGED submittedTX
                               /\ UNCHANGED channel
                    /\ pc' = [pc EXCEPT ![Alice] = "AliceMoves"]
                    /\ UNCHANGED numForces

alice == AliceMoves \/ AliceTakesAction

EveMoves == /\ pc[Eve] = "EveMoves"
            /\ IF AlicesGoalUnmet
                  THEN /\ pc' = [pc EXCEPT ![Eve] = "EveTakesAction"]
                  ELSE /\ pc' = [pc EXCEPT ![Eve] = "Done"]
            /\ UNCHANGED << channel, submittedTX, numForces >>

EveTakesAction == /\ pc[Eve] = "EveTakesAction"
                  /\ \/ /\ \E n \in NumParticipants..LatestTurnNumber:
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
                                                                  "Failure of assertion at line 73, column 1 of macro called at line 221, column 12.")
                                                        /\ channel' =            [
                                                                          mode |-> ChannelMode.OPEN,
                                                                          turnNumber |-> [p \in ParticipantIDXs |-> Maximum(channel.turnNumber[p], (commitment.turnNumber))],
                                                                          challenge |-> NULL
                                                                      ]
                                                   ELSE /\ TRUE
                                                        /\ UNCHANGED channel
                                      \/ /\ \E turnNumber \in 0..LatestTurnNumber \cup { n \in Nat : n > LatestTurnNumber /\ ~AlicesMove(n) }:
                                              IF /\ challengeOngoing
                                                 /\ turnNumber > channel.turnNumber[ParticipantIDX(turnNumber)]
                                                 THEN /\ channel' =            [
                                                                        mode |-> ChannelMode.OPEN,
                                                                        challenge  |-> NULL,
                                                                        turnNumber |-> [i \in {ParticipantIDX(turnNumber)} |-> turnNumber] @@ channel.turnNumber
                                                                    
                                                                    
                                                                    
                                                                    ]
                                                 ELSE /\ TRUE
                                                      /\ UNCHANGED channel
                              ELSE /\ TRUE
                                   /\ UNCHANGED channel
                  /\ pc' = [pc EXCEPT ![Eve] = "EveMoves"]
                  /\ UNCHANGED << submittedTX, numForces >>

eve == EveMoves \/ EveTakesAction

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

\* Safety properties

TypeOK ==
  /\ channel \in AllowedChannels
  /\ submittedTX \in AllowedTransactions
  
\* Liveness properties
AliceCanProgressChannel == <>[](
    /\ channel.mode = ChannelMode.OPEN
    /\ channel.turnNumber[AlicesIDX] = AlicesGoalTurnNumber
)

FinalizedWithLatestTurnNumber == <>[](
    /\ channel.mode = ChannelMode.FINALIZED
    /\ channel.turnNumber[AlicesIDX] = LatestTurnNumber
)

AliceDoesNotLoseFunds ==
    \/ AliceCanProgressChannel
    \/ FinalizedWithLatestTurnNumber
    
    
\* We can verify that Alice can never directly modify the channel with this property, with
\* the exception that she can finalize the channel.
AliceMustSubmitTransactions == [][
        /\ pc[Alice] = "AliceTakesAction"
        /\ pc'[Alice] = "AliceMoves"
    =>
        \/ UNCHANGED channel
        \/ channel'.mode = ChannelMode.FINALIZED
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
\* Last modified Tue Sep 10 12:06:45 MDT 2019 by andrewstewart
\* Created Tue Aug 06 14:38:11 MDT 2019 by andrewstewart
