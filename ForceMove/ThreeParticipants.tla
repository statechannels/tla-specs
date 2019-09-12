---- MODULE ThreeParticipants ----
EXTENDS ForceMove, TLC

const_StartingTurnNumber == 5
const_NumParticipants == 3
const_MainHistory == 1
const_Histories == { 1 }
def_ov_Nat == 0..20
=============================================================================