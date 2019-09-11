------------------------------- MODULE Utils -------------------------------
EXTENDS Integers
ChannelMode == [
  OPEN      |-> "OPEN",
  CHALLENGE |-> "CHALLENGE"
]

TX_Type == [
  FORCE_MOVE |-> "FORCE_MOVE",
  REFUTE     |-> "REFUTE",
  RESPOND    |-> "RESPOND"
]

Range(f) == { f[x] : x \in DOMAIN f }
Maximum(a,b) == IF a > b THEN a ELSE b

=============================================================================
\* Modification History
\* Last modified Tue Sep 10 18:36:13 MDT 2019 by andrewstewart
\* Created Tue Sep 10 18:35:45 MDT 2019 by andrewstewart
