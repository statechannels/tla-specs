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
4. Try out a model: `tlc TwoParticipants -config Success.cfg`.
5. Try out a model that "fails": `tlc TwoParticipants -config EveCannotFrontRun.cfg`
  - This actually produces an error trace that exhibits Eve's ability to "front-run", according to the spec's design.

## Interpretation of `EveCannotFrontRun`

```
Error: Action property EveCannotFrontRun is violated.
Error: The behavior up to this point is:
State 1: <Initial predicate>
/\ submittedTX = NULL
/\ counter = 0
/\ pc = [Alice |-> "A", Adjudicator |-> "Adjudicator", Eve |-> "E"]
/\ channel = [turnNumber |-> 0, mode |-> "OPEN"]
/\ Alice = 2

# In this state, Alice "submits a transaction", with turn number 6
State 2: <A line 352, col 6 to line 369, col 47 of module ForceMove>
/\ submittedTX = [commitment |-> [turnNumber |-> 6], type |-> "FORCE_MOVE"]
/\ counter = 0
/\ pc = [Alice |-> "A", Adjudicator |-> "Adjudicator", Eve |-> "E"]
/\ channel = [turnNumber |-> 0, mode |-> "OPEN"]
/\ Alice = 2

# In this state, the transaction is still submitted, but the (on-chain) channel 
# state has been updated before the adjudicator processed the transaction.
# FIXME: It happened to be a challenge state with the same turn number.
# I don't know why that's a violation.
State 3: <E line 373, col 6 to line 424, col 51 of module ForceMove>
/\ submittedTX = [commitment |-> [turnNumber |-> 6], type |-> "FORCE_MOVE"]
/\ counter = 0
/\ pc = [Alice |-> "A", Adjudicator |-> "Adjudicator", Eve |-> "E"]
/\ channel = [turnNumber |-> 6, mode |-> "CHALLENGE"]
/\ Alice = 2

# Alice's transaction is dropped
State 4: <Adjudicator line 293, col 16 to line 348, col 48 of module ForceMove>
/\ submittedTX = NULL
/\ counter = 0
/\ pc = [Alice |-> "A", Adjudicator |-> "Adjudicator", Eve |-> "E"]
/\ channel = [turnNumber |-> 6, mode |-> "CHALLENGE"]
```

See `ForceMove/EveCannotFrontRun.md` for a more interesting example.