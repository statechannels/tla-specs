# README

This repository contains TLA+ specifications of various protocols used by wallets in the nitro protocol.

## Getting started

1. First, you'll need to [grab the TLA+ toolbox](https://lamport.azurewebsites.net/tla/toolbox.html).
2. The learning curve is pretty tough. These [videos](http://lamport.azurewebsites.net/video/videos.html) are a good, but dense intro. You're on your own.

## Getting started quickly

1. You'll still need to [grab the TLA+ toolbox](https://lamport.azurewebsites.net/tla/toolbox.html).
2. Read [this article](https://medium.com/@bellmar/introduction-to-tla-model-checking-in-the-command-line-c6871700a6a2).
3. If you didn't read the article, follow [these instructions](https://github.com/pmer/tla-bin#installation).
   - The TLA+ Toolkit isn't _that_ bad. It makes your specs look nice!
4. Try out a model: `tlc Version1 -config Success.cfg`.
5. Try out a model that "fails": `tlc Version1 -config EveCannotFrontRun.cfg`
  - This actually produces an error trace that exhibits Eve's ability to "front-run", according to the spec's design.

## Interpretation of `EveCannotFrontRun`

First, here's the definition 
```
EveCannotFrontRun == [][~(
    /\ submittedTX # NULL \* transaction has been submitted
    /\ submittedTX' = submittedTX \* transaction is not processed
    /\ channel' # channel \* channel is changed
)]_<<submittedTX, channel>>
```

This is a temporal property, which specifies how variables can change:
`channel` is the value of the `channel` variable before the action, and
`channel'` is the value of the `channel` variable after the action.

In plain English, the property states:
> It is never true that
> 1. the submitted transaction `submittedTx` is not null AND
> 2. the submitted transaction `submittedTx` does not change AND
> 3. the channel `channel` does change

Of course, if Eve takes an action after Alice has submitted a transaction, but before
that transaction is recorded, then 1-3 will all hold.

Therefore, violations of this property are examples of Eve front-running Alice:


```
Error: Action property EveCannotFrontRun is violated.
Error: The behavior up to this point is:
State 1: <Initial predicate>
/\ submittedTX = NULL
/\ pc = [Alice |-> "A", Adjudicator |-> "Adjudicator", Eve |-> "E"]
/\ channel = [turnNumber |-> 0, mode |-> "OPEN"]
/\ Alice = 2
/\ alicesActionCount = 0

# In this state, Alice "submits a transaction", with turn number 6
State 2: <A line 359, col 6 to line 379, col 38 of module ForceMove>
/\ submittedTX = [state |-> [turnNumber |-> 6], type |-> "FORCE_MOVE"]
/\ pc = [Alice |-> "A", Adjudicator |-> "Adjudicator", Eve |-> "E"]
/\ channel = [turnNumber |-> 0, mode |-> "OPEN"]
/\ Alice = 2
/\ alicesActionCount = 1

# In this state, the transaction is still submitted, but the (on-chain) channel 
# state has been updated before the adjudicator processed the transaction.
# Eve has mined a ForceMove transaction before Alice's transaction is mined,
# updating the `channell` variable to a challenge mode.
State 3: <E line 383, col 6 to line 434, col 61 of module ForceMove>
/\ submittedTX = [state |-> [turnNumber |-> 6], type |-> "FORCE_MOVE"]
/\ pc = [Alice |-> "A", Adjudicator |-> "Adjudicator", Eve |-> "E"]
/\ channel = [turnNumber |-> 0, mode |-> "CHALLENGE"]
/\ Alice = 2
/\ alicesActionCount = 1
```

This gives us confidence that our spec is accurately emulating Eve's ability to front-run transactions.

If we wish, we can observe more interesting traces, where we force some specific on-chain state while Alice's transaction is pending:

```
EveCannotFrontRun == [][~(
    /\ submittedTX # NULL \* transaction has been submitted
    /\ submittedTX' = submittedTX \* transaction is not processed
    /\ channel' # channel \* channel is changed
    /\ channel'.turnNumber \in { 3,4 }
    /\ channel'.mode = ChannelMode.OPEN
)]_<<submittedTX, channel>>
```

This resulted in
```
Error: Action property EveCannotFrontRun is violated.
Error: The behavior up to this point is:
State 1: <Initial predicate>
/\ submittedTX = NULL
/\ pc = [Alice |-> "A", Adjudicator |-> "Adjudicator", Eve |-> "E"]
/\ channel = [turnNumber |-> 0, mode |-> "OPEN"]
/\ Alice = 2
/\ alicesActionCount = 0

# Alice submitted a ForceMove transaction
State 2: <A line 359, col 6 to line 379, col 38 of module ForceMove>
/\ submittedTX = [state |-> [turnNumber |-> 6], type |-> "FORCE_MOVE"]
/\ pc = [Alice |-> "A", Adjudicator |-> "Adjudicator", Eve |-> "E"]
/\ channel = [turnNumber |-> 0, mode |-> "OPEN"]
/\ Alice = 2
/\ alicesActionCount = 1

# Eve mined a ForceMove transaction
State 3: <E line 383, col 6 to line 434, col 61 of module ForceMove>
/\ submittedTX = [state |-> [turnNumber |-> 6], type |-> "FORCE_MOVE"]
/\ pc = [Alice |-> "A", Adjudicator |-> "Adjudicator", Eve |-> "E"]
/\ channel = [turnNumber |-> 0, mode |-> "CHALLENGE"]
/\ Alice = 2
/\ alicesActionCount = 1

# Eve mined a Checkpoint transaction
State 4: <E line 383, col 6 to line 434, col 61 of module ForceMove>
/\ submittedTX = [state |-> [turnNumber |-> 6], type |-> "FORCE_MOVE"]
/\ pc = [Alice |-> "A", Adjudicator |-> "Adjudicator", Eve |-> "E"]
/\ channel = [turnNumber |-> 3, mode |-> "OPEN"]
/\ Alice = 2
/\ alicesActionCount = 1
```