---- MODULE Version2 ----
EXTENDS ForceMove, TLC

const_StartingTurnNumber == 5
const_NumParticipants == 2
const_MaxActions == 1
const_CountActions == FALSE
const_ForceMoveOverwrites == FALSE
const_AlicesStrategy == ""
const_EveCheckpoints == TRUE
const_EveRefutes == FALSE
def_ov_Nat == 0..20
=============================================================================