---- MODULE TwoParticipantsLongHistory ----
EXTENDS ForceMove, TLC

const_StartingTurnNumber == 31
const_NumParticipants == 2
const_NumHistories == 1
def_ov_Nat == 0..64
=============================================================================