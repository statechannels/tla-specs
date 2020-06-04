Here's a more interesting violation of `EveCannotFrontRun`.

First, here's the definition 
```
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
        \* You should also uncomment the line which increments the counter, above.
        \/ counter <= 2
]_<<submittedTX, channel>>
```

This is a temporal property saying:
> It's always true that
>  - IF submittedTX changes from not NULL to NULL
>  - THEN
>       * EITHER the value of `channel` must change
        * OR `counter` must be at most 3

The following error is produced by uncommenting some code, so that eve increments the counter when she "front-runs".
```
Error: Action property EveCannotFrontRun is violated.
Error: The behavior up to this point is:
State 1: <Initial predicate>
/\ submittedTX = NULL
/\ counter = 0
/\ pc = [Alice |-> "A", Adjudicator |-> "Adjudicator", Eve |-> "E"]
/\ channel = [turnNumber |-> 0, mode |-> "OPEN"]
/\ Alice = 2

State 2: <A line 356, col 6 to line 373, col 47 of module ForceMove>
/\ submittedTX = [commitment |-> [turnNumber |-> 6], type |-> "FORCE_MOVE"]
/\ counter = 0
/\ pc = [Alice |-> "A", Adjudicator |-> "Adjudicator", Eve |-> "E"]
/\ channel = [turnNumber |-> 0, mode |-> "OPEN"]
/\ Alice = 2

State 3: <E line 377, col 6 to line 430, col 42 of module ForceMove>
/\ submittedTX = [commitment |-> [turnNumber |-> 6], type |-> "FORCE_MOVE"]
/\ counter = 1
/\ pc = [Alice |-> "A", Adjudicator |-> "Adjudicator", Eve |-> "E"]
/\ channel = [turnNumber |-> 0, mode |-> "CHALLENGE"]
/\ Alice = 2

State 4: <E line 377, col 6 to line 430, col 42 of module ForceMove>
/\ submittedTX = [commitment |-> [turnNumber |-> 6], type |-> "FORCE_MOVE"]
/\ counter = 2
/\ pc = [Alice |-> "A", Adjudicator |-> "Adjudicator", Eve |-> "E"]
/\ channel = [turnNumber |-> 1, mode |-> "CHALLENGE"]
/\ Alice = 2

State 5: <E line 377, col 6 to line 430, col 42 of module ForceMove>
/\ submittedTX = [commitment |-> [turnNumber |-> 6], type |-> "FORCE_MOVE"]
/\ counter = 3
/\ pc = [Alice |-> "A", Adjudicator |-> "Adjudicator", Eve |-> "E"]
/\ channel = [turnNumber |-> 6, mode |-> "CHALLENGE"]
/\ Alice = 2

State 6: <Adjudicator line 293, col 16 to line 352, col 32 of module ForceMove>
/\ submittedTX = NULL
/\ counter = 3
/\ pc = [Alice |-> "A", Adjudicator |-> "Adjudicator", Eve |-> "E"]
/\ channel = [turnNumber |-> 6, mode |-> "CHALLENGE"]
/\ Alice = 2
```

This trace gives us confidence about what actions Eve can take.