---- MODULE Version2NoGrief ----
EXTENDS ForceMove, TLC

const_StartingTurnNumber == 10
const_NumParticipants == 2
const_MaxActions == 10
const_CountActions == TRUE
const_ForceMoveOverwrites == FALSE
const_AlicesStrategy == ""
const_EveCheckpoints == TRUE
const_EveRefutes == FALSE
def_ov_Nat == 0..20
=============================================================================