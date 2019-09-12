---- MODULE FiveParticipants ----
EXTENDS ForceMove, TLC

const_StartingTurnNumber == 6
const_NumParticipants == 5
const_MainHistory == 1
const_Histories == { 1 }
def_ov_Nat == 0..15
=============================================================================