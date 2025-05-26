---- MODULE SolveDieHard ----
EXTENDS DieHard, TLC

\* INVARIANT definition @modelCorrectnessInvariants:1
SolutionNotReached == big /= 4

=============================
