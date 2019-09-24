------------------------------- MODULE Utils -------------------------------
EXTENDS Integers
ChannelMode == [
  OPEN      |-> "OPEN",
  CHALLENGE |-> "CHALLENGE"
]

ForceMoveAPI == [
  FORCE_MOVE |-> "FORCE_MOVE",
  RESPOND    |-> "RESPOND",
  CHECKPOINT |-> "CHECKPOINT"
]

Range(f) == { f[x] : x \in DOMAIN f }
Maximum(a,b) == IF a > b THEN a ELSE b

=============================================================================
\* Modification History
\* Last modified Tue Sep 24 17:45:22 MDT 2019 by andrewstewart
\* Created Tue Sep 10 18:35:45 MDT 2019 by andrewstewart
