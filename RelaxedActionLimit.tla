---- MODULE TwoParticipants ----
EXTENDS ForceMove, TLC

const_StartingTurnNumber == 5
const_NumParticipants == 2
const_MaxActions == 5
def_ov_Nat == 0..20
=============================================================================