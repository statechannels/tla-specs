---- MODULE Version1 ----
EXTENDS ForceMove, TLC

const_StartingTurnNumber == 5
const_NumParticipants == 2
const_MaxActions == 1
const_CountActions == TRUE
const_AlicesStrategy == "Refute"
const_EveCheckpoints == TRUE
const_EveRefutes == FALSE
def_ov_Nat == 0..20
=============================================================================