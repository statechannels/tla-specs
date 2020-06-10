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
5. Try out a model that "fails": `tlc Version1 -config EveDoesntFrontRun.cfg`

- This actually produces an error trace that exhibits Eve's ability to "front-run", according to the spec's design.

## Interpretation of `EveDoesntFrontRun`

First, here's the definition

```
EveDoesntFrontRun == [][~(
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
>
> 1. the submitted transaction `submittedTx` is not null AND
> 2. the submitted transaction `submittedTx` does not change AND
> 3. the channel `channel` does change

Of course, if Eve takes an action after Alice has submitted a transaction, but before
that transaction is recorded, then 1-3 will all hold.

Therefore, violations of this property are examples of Eve front-running Alice:

```
Error: Action property EveDoesntFrontRun is violated.
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
EveDoesntFrontRun == [][~(
    /\ submittedTX # NULL \* transaction has been submitted
    /\ submittedTX' = submittedTX \* transaction is not processed
    /\ channel' # channel \* channel is changed
    /\ channel'.turnNumber \in { 3,4 }
    /\ channel'.mode = ChannelMode.OPEN
)]_<<submittedTX, channel>>
```

This resulted in

```
Error: Action property EveDoesntFrontRun is violated.
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

# Protocol versions

## V1

| State       | Action               | NextState   | Requirements       |
| ----------- | -------------------- | ----------- | ------------------ |
| Open(n)     | forceMove(m, s\*, p) | Chal(m,s,p) | m >= n             |
| Chal(n,s,p) | respond(n+1,s, s')   | Open(n+1)   | s->s'              |
| Chal(n,s,p) | refute(m, s, s')     | Open(n)     | m > n, p signed s' |
| Chal(n,s,p) | altRespond(n+1)      | Open(n+1)   |                    |

In this version of the spec, we ignore responding with alternative moves.
Alice employs the strategy of calling `forceMove` when she can, and otherwise
calling `refute` if Eve calls `forceMove` with a stale state.

Running `❯ tlc Version1.tla -config Success.cfg > v1-problems.txt`, and inspecting the [error trace](v1-problems.txt), we see that Eve was able to enter an infinite cycle, since she is able to cycle between `[turnNumber |-> 0, mode |-> "OPEN"]` and `[turnNumber |-> 0, mode |-> "CHALLENGE"]`.

TLC can detect the infinite loop if we didn't increment a counter whenever Alice submits transactions.
We can see that by running `❯ tlc Version1NoCounter.tla -config Success.cfg > v1-no-counter.txt`, and inspecting its [error trace](v1-no-counter.txt)

## V2

| State       | Action               | NextState   | Requirements |
| ----------- | -------------------- | ----------- | ------------ |
| Open(n)     | forceMove(m, s\*, p) | Chal(m,s,p) | m >= n       |
| Chal(n,s,p) | respond(n+1,s, s')   | Open(n+1)   | s->s'        |
| Chal(n,s,p) | altRespond(n+1)      | Open(n+1)   |              |

Since Eve can force an infinite loop if she can reliably front-run, we have no choice but to remove `refute` from the ForceMove API.

This yields a successful result: Alice is guaranteed to be able to progress the channel:

```
❯ tlc Version2 -config Success.cfg
Starting... (2020-06-09 21:16:32)
Implied-temporal checking--satisfiability problem has 2 branches.
Computing initial states...
Finished computing initial states: 1 distinct state generated at 2020-06-09 21:16:32.
Progress(6) at 2020-06-09 21:16:32: 561 states generated, 52 distinct states found, 0 states left on queue.
Checking 2 branches of temporal properties for the complete state space with 104 total distinct states at (2020-06-09 21:16:32)
Finished checking temporal properties in 00s at 2020-06-09 21:16:32
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 1.4E-15
561 states generated, 52 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 6.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 9 and the 95th percentile is 7).
Finished in 01s at (2020-06-09 21:16:32)
```

However, this is not satisfactory. Eve can grief Alice by front-running `forceMove(s10^*)` with `forceMove(s0^*)`, then `forceMove(s1^*)`, etc. Running `❯ tlc Version2NoGrief.tla -config Success.cfg > v2-no-grief.txt`, [we see that](v2-no-grief.txt) needs to submit as many transactions as there are states to force the channel to a certain turn number.

## V3

| State       | Action            | NextState    | Requirements |
| ----------- | ----------------- | ------------ | ------------ |
| Open(n)     | forceMove(m,s,p)  | Chal(m,s,p)  | m >= n       |
| Chal(n,s,p) | forceMove(m,s',p) | Chal(m,s',p) | m > n        |
| Open(n,s)   | checkpoint(m)     | Open(m)      | m > n        |
| Chal(n,s,p) | checkpoint(m)     | Open(m)      | m > n        |
| Chal(n,s,p) | respond(s,s')     | Open(n+1)    | s->s'        |

Thus, we change the semantics of `forceMove` to overwrite existing challenges, if it increases the turn number.
This maximally simplifies Alice's strategy -- she can submit a `forceMove` transaction with her latest supported state, and no amount of front-running will prevent her from progressing the channel in a constant number of actions:

```
❯ tlc Version3.tla -config Success.cfg
Starting... (2020-06-09 22:05:03)
Implied-temporal checking--satisfiability problem has 2 branches.
Computing initial states...
Finished computing initial states: 1 distinct state generated at 2020-06-09 22:05:03.
Progress(7) at 2020-06-09 22:05:03: 614 states generated, 69 distinct states found, 0 states left on queue.
Checking 2 branches of temporal properties for the complete state space with 138 total distinct states at (2020-06-09 22:05:03)
Finished checking temporal properties in 00s at 2020-06-09 22:05:03
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 2.0E-15
614 states generated, 69 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 7.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 9 and the 95th percentile is 7).
Finished in 01s at (2020-06-09 22:05:03)
```

In this version, we also introduced a `checkpoint` operation: the original `respondWithAlternativeMove` described in the nitro paper (TODO: LINK) had two limitations:

- the turn number must increase by exactly 1
- the channel must be in the challenge mode.

While exploring other strategies for Alice using TLA+, it became clear that these limitations were unnecessary, and lifting them provided many benefits.
