------------------------------- MODULE Utils -------------------------------
EXTENDS Integers
ChannelMode == [
  OPEN      |-> "OPEN",
  CHALLENGE |-> "CHALLENGE"
]

ForceMoveAPI == [
  FORCE_MOVE |-> "FORCE_MOVE",
  RESPOND    |-> "RESPOND",
  CHECKPOINT |-> "CHECKPOINT",
  REFUTE     |-> "REFUTE"
]

Range(f) == { f[x] : x \in DOMAIN f }
Maximum(a,b) == IF a > b THEN a ELSE b

=============================================================================
\* Modification History
\* Last modified Mon Jun 08 14:03:44 PDT 2020 by andrewstewart
\* Created Tue Sep 10 18:35:45 MDT 2019 by andrewstewart
