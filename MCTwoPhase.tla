---- MODULE MCTwoPhase ----
EXTENDS TwoPhase, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3
----

\* MV CONSTANT definitions RM
RMS == {r1, r2, r3}
----

\* SYMMETRY definition
RMS_SYMM == Permutations(RMS)
----

=============================================================================
\* Modification History
\* Created Mon May 26 16:03:38 BRT 2025 by bernborgess
