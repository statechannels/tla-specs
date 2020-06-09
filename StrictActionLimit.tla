---- MODULE StrictActionLimit ----
EXTENDS ForceMove, TLC

const_StartingTurnNumber == 5
const_NumParticipants == 2
const_MaxActions == 1
def_ov_Nat == 0..20
=============================================================================