---- MODULE MCRaft ----

\* @type: Set(SERVER);
Server == {
    "sv1_OF_SERVER",
    "sv2_OF_SERVER",
    "sv3_OF_SERVER"
    }

\* @type: Int;
MaxClientRequests == 8

\* @type: Int;
MaxLogLength == 8

\* @type: STATE;
Follower == "Follower_OF_STATE"
\* @type: STATE;
Candidate == "Candidate_OF_STATE"
\* @type: STATE;
Leader == "Leader_OF_STATE"

\* @type: MESSAGE_TYPE;
RequestVoteRequest == "RequestVoteRequest_OF_MESSAGE_TYPE"
\* @type: MESSAGE_TYPE;
RequestVoteResponse == "RequestVoteResponse_OF_MESSAGE_TYPE"
\* @type: MESSAGE_TYPE;
AppendEntriesRequest == "AppendEntriesRequest_OF_MESSAGE_TYPE"
\* @type: MESSAGE_TYPE;
AppendEntriesResponse == "AppendEntriesResponse_OF_MESSAGE_TYPE"

----

VARIABLES
    \* @type: MESSAGE -> Int;
    messages,

    \* @type: Set(ELECTION);
    elections

VARIABLES
    \* @type: SERVER -> Int;
    currentTerm,

    \* @type: SERVER -> STATE;
    state,

    \* @type: SERVER -> Set(SERVER);
    votedFor

VARIABLES
    \* @type: SERVER -> Seq(LOG_ITEM);
    log,

    \* @type: SERVER -> Int;
    commitIndex,

    \* @type: Int;
    valueRequestedByClient

VARIABLES
    \* @type: SERVER -> Set(SERVER);
    votesResponded,

    \* @type: SERVER -> Set(SERVER);
    votesGranted,

    \* @type: SERVER -> SERVER -> Seq(LOG_ITEM);
    voterLog

VARIABLES
    \* @type: SERVER -> SERVER -> Int;
    nextIndex,

    \* @type: SERVER -> SERVER -> Int;
    matchIndex

----

INSTANCE Raft

\* Invariant: Multiple leaders are not in a term.
\* @type: Bool;
ElectionSafety ==
    \A i,j \in Server : i /= j /\ currentTerm[i] = currentTerm[j] => state[i] /= Leader \/ state[j] /= Leader

====
