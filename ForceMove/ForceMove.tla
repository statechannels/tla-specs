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

LatestTurnNumber == StartingTurnNumber + NumParticipants - 1
AlicesCommitments == StartingTurnNumber..LatestTurnNumber
ParticipantIDXs == 1..NumParticipants
ParticipantIDX(turnNumber) == 1 + ((turnNumber - 1) % NumParticipants)
AllowedTurnNumbers == 0..(StartingTurnNumber + NumParticipants)

ASSUME
  /\ StartingTurnNumber \in Nat
  /\ NumParticipants \in Nat \ { 1 }
            
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
    AlicesIDX \in ParticipantIDXs \ { ParticipantIDX(LatestTurnNumber + 1) },
    counter = 0 \* Auxilliary variable used in some properties and invariants.
    \* We can't specify any properties that require any memory of the
    \* behaviour up to the certain point (ie. the behaviour has passed through state X seven times in a row)
    \* we thus have to embed the "memory" of the behaviour in the state itself,
    \* if we want to check some property the depends on the history of the behaviour

define
AllowedCommitments == {
    c \in [ turnNumber: Nat, signer: ParticipantIDXs ] :
        /\ c.signer = ParticipantIDX(c.turnNumber)
        /\ c.signer = AlicesIDX => c.turnNumber \in AllowedTurnNumbers
    }

challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen == channel.mode = ChannelMode.OPEN
progressesChannel(commitment) == commitment.turnNumber >= channel.turnNumber[commitment.signer]
validCommitment(c) == c \in [ turnNumber: Nat, signer: ParticipantIDXs ]
validTransition(commitment) ==
    /\ commitment.turnNumber = channel.challenge.turnNumber + 1
    /\ commitment.signer = ParticipantIDX(commitment.turnNumber)
AlicesMove(turnNumber) == ParticipantIDX(turnNumber) = AlicesIDX
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

macro refute(commitment)
begin
assert commitment \in AllowedCommitments;
with refutation = commitment.turnNumber, signer = commitment.signer do
if
    /\ challengeOngoing
    /\ signer = channel.challenge.signer
    /\ refutation > channel.turnNumber[signer]
    /\ refutation > channel.challenge.turnNumber
then
channel := [
    mode |-> ChannelMode.OPEN,
    challenge  |-> NULL,
    turnNumber |-> [i \in {signer} |-> refutation] @@ channel.turnNumber
    \* By switching to the following effect, we can see how Eve could infinitely grief
    \* with the previous version of the force-move protocol.
\*    turnNumber |-> channel.turnNumber
];
end if; end with;
end macro;

macro forceMove(commitment)
begin
if
    /\ channelOpen
    /\ progressesChannel(commitment)
then
    channel := [ mode |-> ChannelMode.CHALLENGE, challenge |-> commitment ] @@ channel;
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
        if    submittedTX.type = TX_Type.FORCE_MOVE then forceMove(submittedTX.commitment);
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
            with refutation = CHOOSE n \in AlicesCommitments : ParticipantIDX(n) = channel.challenge.signer,
                 commitment = [ turnNumber |-> refutation, signer |-> channel.challenge.signer ]
            do submittedTX := [ type |-> TX_Type.REFUTE, commitment |-> commitment]; end with;
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
        with  signer \in ParticipantIDXs \ { AlicesIDX },
              turnNumber \in { n \in NumParticipants..LatestTurnNumber : ParticipantIDX(n) = signer }
        do
            forceMove([ turnNumber |-> turnNumber, signer |-> signer ]);
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
            \cup { n \in Nat : ~AlicesMove(n) },
            commitment = [ turnNumber |-> turnNumber, signer |-> ParticipantIDX(turnNumber) ]
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
AllowedCommitments == {
    c \in [ turnNumber: Nat, signer: ParticipantIDXs ] :
        /\ c.signer = ParticipantIDX(c.turnNumber)
        /\ c.signer = AlicesIDX => c.turnNumber \in AllowedTurnNumbers
    }

challengeOngoing == channel.mode = ChannelMode.CHALLENGE
channelOpen == channel.mode = ChannelMode.OPEN
progressesChannel(commitment) == commitment.turnNumber >= channel.turnNumber[commitment.signer]
validCommitment(c) == c \in [ turnNumber: Nat, signer: ParticipantIDXs ]
validTransition(commitment) ==
    /\ commitment.turnNumber = channel.challenge.turnNumber + 1
    /\ commitment.signer = ParticipantIDX(commitment.turnNumber)
AlicesMove(turnNumber) == ParticipantIDX(turnNumber) = AlicesIDX
AlicesGoalMet ==
    /\ channel.mode = ChannelMode.CHALLENGE
    /\ channel.challenge.turnNumber = LatestTurnNumber


vars == << channel, submittedTX, AlicesIDX, counter, pc >>

ProcSet == {"Adjudicator"} \cup {"Alice"} \cup {"Eve"}

Init == (* Global variables *)
        /\ channel = [turnNumber |-> [p \in ParticipantIDXs |-> 0], mode |-> ChannelMode.OPEN, challenge |-> NULL ]
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
                                           THEN /\ IF /\ channelOpen
                                                      /\ progressesChannel((submittedTX.commitment))
                                                      THEN /\ channel' = [ mode |-> ChannelMode.CHALLENGE, challenge |-> (submittedTX.commitment) ] @@ channel
                                                      ELSE /\ TRUE
                                                           /\ UNCHANGED channel
                                           ELSE /\ IF submittedTX.type = TX_Type.REFUTE
                                                      THEN /\ Assert((submittedTX.commitment) \in AllowedCommitments, 
                                                                     "Failure of assertion at line 117, column 1 of macro called at line 159, column 58.")
                                                           /\ LET refutation == (submittedTX.commitment).turnNumber IN
                                                                LET signer == (submittedTX.commitment).signer IN
                                                                  IF /\ challengeOngoing
                                                                     /\ signer = channel.challenge.signer
                                                                     /\ refutation > channel.turnNumber[signer]
                                                                     /\ refutation > channel.challenge.turnNumber
                                                                     THEN /\ channel' =            [
                                                                                            mode |-> ChannelMode.OPEN,
                                                                                            challenge  |-> NULL,
                                                                                            turnNumber |-> [i \in {signer} |-> refutation] @@ channel.turnNumber
                                                                                        
                                                                                        
                                                                                        
                                                                                        ]
                                                                     ELSE /\ TRUE
                                                                          /\ UNCHANGED channel
                                                      ELSE /\ IF submittedTX.type = TX_Type.RESPOND
                                                                 THEN /\ IF /\ challengeOngoing
                                                                            /\ validTransition((submittedTX.commitment))
                                                                            THEN /\ Assert(((submittedTX.commitment).turnNumber) \in Nat, 
                                                                                           "Failure of assertion at line 98, column 1 of macro called at line 160, column 58.")
                                                                                 /\ channel' =            [
                                                                                                   mode |-> ChannelMode.OPEN,
                                                                                                   turnNumber |-> [p \in ParticipantIDXs |-> Maximum(channel.turnNumber[p], ((submittedTX.commitment).turnNumber))],
                                                                                                   challenge |-> NULL
                                                                                               ]
                                                                            ELSE /\ TRUE
                                                                                 /\ UNCHANGED channel
                                                                 ELSE /\ Assert(FALSE, 
                                                                                "Failure of assertion at line 161, column 14.")
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
                                   THEN /\ LET refutation == CHOOSE n \in AlicesCommitments : ParticipantIDX(n) = channel.challenge.signer IN
                                             LET commitment == [ turnNumber |-> refutation, signer |-> channel.challenge.signer ] IN
                                               submittedTX' = [ type |-> TX_Type.REFUTE, commitment |-> commitment]
                                   ELSE /\ IF turnNumber < LatestTurnNumber
                                              THEN /\ LET response == turnNumber + 1 IN
                                                        LET commitment == [ turnNumber |-> response, signer |-> ParticipantIDX(response) ] IN
                                                          /\ Assert(response \in AlicesCommitments, 
                                                                    "Failure of assertion at line 195, column 17.")
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
     /\ UNCHANGED << channel, AlicesIDX, counter >>

alice == A

E == /\ pc["Eve"] = "E"
     /\ IF ~AlicesGoalMet
           THEN /\ \/ /\ \E signer \in ParticipantIDXs \ { AlicesIDX }:
                           \E turnNumber \in { n \in NumParticipants..LatestTurnNumber : ParticipantIDX(n) = signer }:
                             IF /\ channelOpen
                                /\ progressesChannel(([ turnNumber |-> turnNumber, signer |-> signer ]))
                                THEN /\ channel' = [ mode |-> ChannelMode.CHALLENGE, challenge |-> ([ turnNumber |-> turnNumber, signer |-> signer ]) ] @@ channel
                                ELSE /\ TRUE
                                     /\ UNCHANGED channel
                   \/ /\ IF challengeOngoing
                            THEN /\ \/ /\ LET turnNumber == channel.challenge.turnNumber + 1 IN
                                            LET commitment == [ turnNumber |-> turnNumber, signer |-> ParticipantIDX(turnNumber)] IN
                                              IF /\ challengeOngoing
                                                 /\ validTransition(commitment)
                                                 THEN /\ Assert((commitment.turnNumber) \in Nat, 
                                                                "Failure of assertion at line 98, column 1 of macro called at line 239, column 12.")
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
                                            LET commitment == [ turnNumber |-> turnNumber, signer |-> ParticipantIDX(turnNumber) ] IN
                                              /\ Assert(commitment \in AllowedCommitments, 
                                                        "Failure of assertion at line 117, column 1 of macro called at line 248, column 12.")
                                              /\ LET refutation == commitment.turnNumber IN
                                                   LET signer == commitment.signer IN
                                                     IF /\ challengeOngoing
                                                        /\ signer = channel.challenge.signer
                                                        /\ refutation > channel.turnNumber[signer]
                                                        /\ refutation > channel.challenge.turnNumber
                                                        THEN /\ channel' =            [
                                                                               mode |-> ChannelMode.OPEN,
                                                                               challenge  |-> NULL,
                                                                               turnNumber |-> [i \in {signer} |-> refutation] @@ channel.turnNumber
                                                                           
                                                                           
                                                                           
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
    \cup [ type: Range(TX_Type), commitment: AllowedCommitments ]

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
\* Last modified Thu Sep 12 11:59:55 MDT 2019 by andrewstewart
\* Created Tue Aug 06 14:38:11 MDT 2019 by andrewstewart
