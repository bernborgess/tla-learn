---- MODULE MCPaxosCommit ----
EXTENDS PaxosCommit, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2
----

\* MV CONSTANT definitions Acceptor
ACCEPTORS == {a1, a2, a3}
----

\* MV CONSTANT definitions RM
RMS == {r1, r2}
----

\* SYMMETRY definition
SYMM_ACCEPTORS_RMS == Permutations(ACCEPTORS) \union Permutations(RMS)
----

\* CONSTANT definitions @modelParameterConstants:0Ballot
BALLOT == {0,1}
----

\* CONSTANT definitions @modelParameterConstants:2Majority
MAJORITY == {{a1,a2},{a1,a3},{a2,a3}}
----

=============================================================================
\* Modification History
\* Created Mon May 26 17:12:12 BRT 2025 by bernborgess
