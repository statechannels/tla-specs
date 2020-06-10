---- MODULE Version1NoCounter ----
EXTENDS ForceMove, TLC

const_StartingTurnNumber == 5
const_NumParticipants == 2
const_MaxActions == 3
const_CountActions == FALSE
const_ForceMoveOverwrites == FALSE
const_AliceRefutes == TRUE
const_EveCheckpoints == FALSE
const_EveRefutes == TRUE
def_ov_Nat == 0..20
=============================================================================