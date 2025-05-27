---- MODULE Raft ----
\* This is the formal specification for the Raft consensus algorithm.
\*
\* Copyright 2014 Diego Ongaro.
\* This work is licensed under the Creative Commons Attribution-4.0
\* International License https://creativecommons.org/licenses/by/4.0/
\* Source: https://github.com/ongardie/raft.tla
\*
\* Copyright 2022 Yuya Shiratori.
\* This document includes some adaptions by Yuya Shiratori.
\*
\* Changes:
\*   - Change the format
\*   - Annotate types for Apalache
\*   - Change the codomain of the variable `votedFor` from `Server \cup { Nil }` to `Set(SERVER)`
\*   - Use `clientRequest` instead of `v \in Value` (thanks to @jinlmsft)
\*   - Remove allLogs variable
\*   - ... plus refactoring
\*

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    \* The set of server IDs.
    \* @type: Set(SERVER);
    Server,

    \* Maximum request count from clients.
    \* @type: Int;
    MaxClientRequests,

    \* Maximum log length.
    \* @type: Int;
    MaxLogLength

CONSTANTS
    \* Server states.
    \* @type: STATE;
    Follower,
    \* @type: STATE;
    Candidate,
    \* @type: STATE;
    Leader

CONSTANTS
    \* Message types:
    \* @type: MESSAGE_TYPE;
    RequestVoteRequest,
    \* @type: MESSAGE_TYPE;
    RequestVoteResponse,
    \* @type: MESSAGE_TYPE;
    AppendEntriesRequest,
    \* @type: MESSAGE_TYPE;
    AppendEntriesResponse

----
\* Global variables

\* The type representing both requests and responses sent from a server.
\* @typeAlias: MESSAGE = [mtype: MESSAGE_TYPE, mterm: Int, mlastLogIndex: Int,
\*     mlastLogTerm: Int, mvoteGranted: Bool, mlog: Seq(LOG_ITEM),
\*     mprevLogIndex: Int, mprevLogTerm: Int, mentries: Seq(LOG_ITEM),
\*     mcommitIndex: Int, msuccess: Bool, mmatchIndex: Int,
\*     msource: SERVER, mdest: SERVER];
MSGTypeAliases == TRUE

\* The type representing a log item.
\* @typeAlias: LOG_ITEM = [term: Int, value: Int];
LITypeAliases == TRUE

\* The type representing a history of election.
\* @typeAlias: ELECTION = [eterm: Int, eleader: SERVER, elog: Seq(LOG_ITEM),
\*     evotes: Set(SERVER), evoterLog: SERVER -> Seq(LOG_ITEM)];
ELETypeAliases == TRUE

VARIABLES
    \* A bag of records representing requests and responses sent from one server
    \* to another.
    \* @type: MESSAGE -> Int;
    messages,

    \* A history variable used in the proof. This would not be present in an
    \* implementation.
    \* Keeps track of successful elections, including the initial logs of the
    \* leader and voters' logs. Set of functions containing various things about
    \* successful elections (see BecomeLeader).
    \* @type: Set(ELECTION);
    elections

----
\* The following variables are all per server.

VARIABLES
    \* The server's term.
    \* @type: SERVER -> Int;
    currentTerm,

    \* The server's state (Follower, Candidate, or Leader).
    \* @type: SERVER -> STATE;
    state,

    \* The candidate the server voted for in its current term.
    \* If it hasn't voted for any, the value is empty.
    \* @type: SERVER -> Set(SERVER);
    votedFor

serverVars == <<currentTerm, state, votedFor>>

VARIABLES
    \* A sequence of log entries. The index into this sequence is the index of the
    \* log entry. Unfortunately, the Sequence module defines Head(s) as the entry
    \* with index 1, so be careful not to use that!
    \* @type: SERVER -> Seq(LOG_ITEM);
    log,

    \* The index of the latest entry in the log the state machine may apply.
    \* @type: SERVER -> Int;
    commitIndex,

    \* A value which clients request.
    \* @type: Int;
    valueRequestedByClient

logVars == <<log, commitIndex, valueRequestedByClient>>

\* The following variables are used only on candidates:
VARIABLES
    \* The set of servers from which the candidate has received a RequestVote
    \* response in its currentTerm.
    \* @type: SERVER -> Set(SERVER);
    votesResponded,

    \* The set of servers from which the candidate has received a vote in its
    \* currentTerm.
    \* @type: SERVER -> Set(SERVER);
    votesGranted,

    \* A history variable used in the proof. This would not be present in an
    \* implementation.
    \* @type: SERVER -> SERVER -> Seq(LOG_ITEM);
    voterLog

candidateVars == <<votesResponded, votesGranted, voterLog>>

\* The following variables are used only on leaders:
VARIABLES
    \* The next entry to send to each follower.
    \* @type: SERVER -> SERVER -> Int;
    nextIndex,

    \* The latest entry that each follower has acknowledged is the same as the
    \* leader's. This is used to calculate commitIndex on the leader.
    \* @type: SERVER -> SERVER -> Int;
    matchIndex

leaderVars == <<nextIndex, matchIndex, elections>>

----

\* All variables; used for stuttering (asserting state hasn't changed).
vars == <<messages, serverVars, candidateVars, leaderVars, logVars>>

----
\* Helpers

\* The set of all quorums. This just calculates simple majorities, but the only
\* important property is that every quorum overlaps with every other.
\* @type: Set(Set(SERVER));
Quorum == {i \in SUBSET Server : Cardinality(i) * 2 > Cardinality(Server)}

\* The term of the last entry in a log, or 0 if the log is empty.
\* @type: (Seq(LOG_ITEM)) => Int;
LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* Helper for Send and Reply. Given a message m and bag of messages, return a
\* new bag of messages with one more m in it.
\* @type: (MESSAGE, MESSAGE -> Int) => MESSAGE -> Int;
AppendMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = IF msgs[m] < 2 THEN msgs[m] + 1 ELSE 2]
    ELSE
        msgs @@ (m :> 1)

\* Helper for Discard and Reply. Given a message m and bag of messages, return
\* a new bag of messages with one less m in it.
\* @type: (MESSAGE, MESSAGE -> Int) => MESSAGE -> Int;
DropMessage(m, msgs) ==
    IF m \in DOMAIN msgs THEN
        [msgs EXCEPT ![m] = IF msgs[m] > 0 THEN msgs[m] - 1 ELSE 0]
    ELSE
        msgs

\* Messages in a bag.
\* @type: (MESSAGE -> Int) => Set(MESSAGE);
MessagesInBag(msgs) == {m \in DOMAIN msgs : msgs[m] > 0}

\* Messages whose multiplicity is one in a bag.
\* @type: (MESSAGE -> Int) => Set(MESSAGE);
SingleMessages(msgs) == {m \in DOMAIN msgs : msgs[m] = 1}

\* Add a message to the bag of messages.
\* @type: (MESSAGE) => Bool;
Send(m) == messages' = AppendMessage(m, messages)

\* Remove a message from the bag of messages. Used when a server is done
\* processing a message.
\* @type: (MESSAGE) => Bool;
Discard(m) == messages' = DropMessage(m, messages)

\* Combination of Send and Discard
\* @type: (MESSAGE, MESSAGE) => Bool;
Reply(response, request) ==
    messages' = DropMessage(request, AppendMessage(response, messages))

\* Return the minimum value from a set, or undefined if the set is empty.
\* @type: (Set(Int)) => Int;
Min(s) == CHOOSE x \in s : \A y \in s : x <= y

\* Return the maximum value from a set, or undefined if the set is empty.
\* @type: (Set(Int)) => Int;
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

----
\* Define initial values for all variables

\* @type: Bool;
InitHistoryVars == /\ elections = {}
                   /\ voterLog  = [i \in Server |-> [j \in {} |-> <<>>]]

\* @type: Bool;
InitServerVars == /\ currentTerm = [i \in Server |-> 1]
                  /\ state       = [i \in Server |-> Follower]
                  /\ votedFor    = [i \in Server |-> {}]

\* @type: Bool;
InitCandidateVars == /\ votesResponded = [i \in Server |-> {}]
                     /\ votesGranted   = [i \in Server |-> {}]

\* The values nextIndex[i][i] and matchIndex[i][i] are never read, since the
\* leader does not send itself messages. It's still easier to include these
\* in the functions.
\* @type: Bool;
InitLeaderVars == /\ nextIndex  = [i \in Server |-> [j \in Server |-> 1]]
                  /\ matchIndex = [i \in Server |-> [j \in Server |-> 0]]

\* @type: Bool;
InitLogVars == /\ log                    = [i \in Server |-> <<>>]
               /\ commitIndex            = [i \in Server |-> 0]
               /\ valueRequestedByClient = 1

\* @type: Bool;
Init == /\ messages = [m \in {} |-> 0]
        /\ InitHistoryVars
        /\ InitServerVars
        /\ InitCandidateVars
        /\ InitLeaderVars
        /\ InitLogVars

----
\* Define state transitions

\* Server i restarts from stable storage.
\* It loses everything but its currentTerm, votedFor, and log.
\* @type: (SERVER) => Bool;
Restart(i) ==
    /\ state'          = [state EXCEPT ![i] = Follower]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Server |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ commitIndex'    = [commitIndex EXCEPT ![i] = 0]
    /\ UNCHANGED <<messages, currentTerm, votedFor, log, elections, valueRequestedByClient>>

\* Server i times out and starts a new election.
\* @type: (SERVER) => Bool;
Timeout(i) == /\ state[i] \in {Follower, Candidate}
              /\ state'          = [state EXCEPT ![i] = Candidate]
              /\ currentTerm'    = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
              \* Most implementations would probably just set the local vote
              \* atomically, but messaging localhost for it is weaker.
              /\ votedFor'       = [votedFor EXCEPT ![i] = {}]
              /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
              /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
              /\ voterLog'       = [voterLog EXCEPT ![i] = [j \in {} |-> <<>>]]
              /\ UNCHANGED <<messages, leaderVars, logVars>>

\* @type: (SERVER, SERVER) => Bool;
SendRequestVote(src, dest) ==
    Send([mtype         |-> RequestVoteRequest,
          mterm         |-> currentTerm[src],
          mlastLogIndex |-> Len(log[src]),
          mlastLogTerm  |-> LastTerm(log[src]),
          msource       |-> src,
          mdest         |-> dest])

\* Candidate i sends j a RequestVote request.
\* @type: (SERVER, SERVER) => Bool;
RequestVote(i, j) ==
    /\ state[i] = Candidate
    /\ j \notin votesResponded[i]
    /\ SendRequestVote(i, j)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* @type: (SERVER, SERVER) => Bool;
SendAppendEntries(src, dest) ==
    LET prevLogIndex == nextIndex[src][dest] - 1
        prevLogTerm  == IF prevLogIndex > 0 THEN
                            log[src][prevLogIndex].term
                        ELSE
                            0
        \* Send up to 1 entry, constrained by the end of the log.
        lastEntry    == Min({Len(log[src]), nextIndex[src][dest]})
        entries      == SubSeq(log[src], nextIndex[src][dest], lastEntry)
    IN Send([mtype         |-> AppendEntriesRequest,
             mterm         |-> currentTerm[src],
             mprevLogIndex |-> prevLogIndex,
             mprevLogTerm  |-> prevLogTerm,
             mentries      |-> entries,
             \* mlog is used as a history variable for the proof.
             \* It would not exist in a real implementation.
             mlog          |-> log[src],
             mcommitIndex  |-> Min({commitIndex[src], lastEntry}),
             msource       |-> src,
             mdest         |-> dest])

\* Leader i sends j an AppendEntries request containing up to 1 entry.
\* While implementations may want to send more than 1 at a time, this spec uses
\* just 1 because it minimizes atomic regions without loss of generality.
\* @type: (SERVER, SERVER) => Bool;
AppendEntries(i, j) ==
    /\ i /= j
    /\ state[i] = Leader
    /\ SendAppendEntries(i, j)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* Candidate i transitions to leader.
\* @type: (SERVER) => Bool;
BecomeLeader(i) ==
    /\ state[i] = Candidate
    /\ votesGranted[i] \in Quorum
    /\ state'      = [state EXCEPT ![i] = Leader]
    /\ nextIndex'  = [nextIndex EXCEPT ![i] = [j \in Server |-> Len(log[i]) + 1]]
    /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in Server |-> 0]]
    /\ elections'  = elections \cup
                        {[eterm     |-> currentTerm[i],
                          eleader   |-> i,
                          elog      |-> log[i],
                          evotes    |-> votesGranted[i],
                          evoterLog |-> voterLog[i]]}
    /\ UNCHANGED <<messages, currentTerm, votedFor, candidateVars, logVars>>

\* Leader i receives a client request to add v to the log.
\* @type: (SERVER) => Bool;
ClientRequest(i) ==
    /\ state[i] = Leader
    /\ valueRequestedByClient < MaxClientRequests
    /\ Len(log[i]) < MaxLogLength
    /\ LET entry  == [term |-> currentTerm[i], value |-> valueRequestedByClient]
           newLog == Append(log[i], entry)
       IN /\ log'                    = [log EXCEPT ![i] = newLog]
          /\ valueRequestedByClient' = valueRequestedByClient + 1
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, commitIndex>>

\* Leader i advances its commitIndex.
\* This is done as a separate step from handling AppendEntries responses,
\* in part to minimize atomic regions, and in part so that leaders of
\* single-server clusters are able to mark entries committed.
\* @type: (SERVER) => Bool;
AdvanceCommitIndex(i) ==
    /\ state[i] = Leader
    /\ LET \* The set of servers that agree up through index.
           Agree(index) == {i} \cup {k \in Server : matchIndex[i][k] >= index}

           \* The maximum indices for which a quorum agrees.
           agreeIndices == {index \in 1..MaxLogLength :
                                /\ index <= Len(log[i])
                                /\ Agree(index) \in Quorum}

           \* New value for commitIndex'[i].
           newCommitIndex ==
               IF /\ agreeIndices /= {}
                  /\ log[i][Max(agreeIndices)].term = currentTerm[i]
               THEN
                   Max(agreeIndices)
               ELSE
                   commitIndex[i]
       IN commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
    /\ UNCHANGED <<messages, serverVars, candidateVars, leaderVars, log, valueRequestedByClient>>

----
\* Message handlers
\* i = recipient, j = sender, m = message

\* @type: (SERVER, SERVER, MESSAGE, Bool) => Bool;
ReplyRequestVote(src, dest, msg, grant) ==
    Reply([mtype        |-> RequestVoteResponse,
           mterm        |-> currentTerm[src],
           mvoteGranted |-> grant,
           mlog         |-> log[src],
           msource      |-> src,
           mdest        |-> dest],
           msg)

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
\* @type: (SERVER, SERVER, MESSAGE) => Bool;
HandleRequestVoteRequest(i, j, m) ==
    LET logOk ==
            \* The voter i agree with the vote when the
            \* candidate's log is up-to-date for the voter;
            \* see Section 5.4.1.
            \/ m.mlastLogTerm > LastTerm(log[i])
            \/ /\ m.mlastLogTerm = LastTerm(log[i])
               /\ m.mlastLogIndex >= Len(log[i])
        grant == /\ m.mterm = currentTerm[i]
                 /\ logOk
                 \* The first-come-first-served basis
                 /\ \A k \in votedFor[i] : k = j
    IN \* When m.mterm > currentTerm[i], first update the voter's term
       /\ m.mterm <= currentTerm[i]
       /\ \/ grant  /\ votedFor' = [votedFor EXCEPT ![i] = votedFor[i] \cup {j}]
          \/ ~grant /\ UNCHANGED votedFor
       /\ ReplyRequestVote(i, j, m, grant)
       /\ UNCHANGED <<state, currentTerm, candidateVars, leaderVars, logVars>>

\* Server i receives a RequestVote response from server j with
\* m.mterm = currrentTerm[i].
\* @type: (SERVER, SERVER, MESSAGE) => Bool;
HandleRequestVoteResponse(i, j, m) ==
    \* This tallies votes even when the current state is not Candidate, but
    \* they won't be looked at, so it doesn't matter.
    /\ m.mterm = currentTerm[i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] =
                              votesResponded[i] \cup {j}]
    /\ \/ /\ m.mvoteGranted
          /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                  votesGranted[i] \cup {j}]
          /\ voterLog' = [voterLog EXCEPT ![i] =
                              voterLog[i] @@ (j :> m.mlog)]
       \/ /\ ~m.mvoteGranted
          /\ UNCHANGED <<votesGranted, voterLog>>
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, leaderVars, logVars>>

\* @type: (SERVER, SERVER, MESSAGE) => Bool;
ReplyAppendEntriesAsReject(src, dest, msg) ==
    Reply([mtype       |-> AppendEntriesResponse,
           mterm       |-> currentTerm[src],
           msuccess    |-> FALSE,
           mmatchIndex |-> 0,
           msource     |-> src,
           mdest       |-> dest],
           msg)

\* @type: (SERVER, SERVER, MESSAGE) => Bool;
ReplyAppendEntriesAsDone(src, dest, msg) ==
    Reply([mtype       |-> AppendEntriesResponse,
           mterm       |-> currentTerm[src],
           msuccess    |-> TRUE,
           mmatchIndex |-> msg.mprevLogIndex + Len(msg.mentries),
           msource     |-> src,
           mdest       |-> dest],
           msg)

\* Server i receives an AppendEntries request from server j with
\* m.mterm <= currentTerm[i]. This just handles m.entries of length 0 or 1, but
\* implementations could safely accept more by treating them the same as
\* multiple independent requests of 1 entry.
\* @type: (SERVER, SERVER, MESSAGE) => Bool;
HandleAppendEntriesRequest(i, j, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[i])
                    /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
    IN /\ m.mterm <= currentTerm[i]
       /\ \/ \* reject request
             /\ \/ m.mterm < currentTerm[i]
                \/ /\ m.mterm  = currentTerm[i]
                   /\ state[i] = Follower
                   /\ ~logOk
             /\ ReplyAppendEntriesAsReject(i, j, m)
             /\ UNCHANGED <<serverVars, logVars>>
          \/ \* return to follower state
             /\ m.mterm  = currentTerm[i]
             /\ state[i] = Candidate
             /\ state' = [state EXCEPT ![i] = Follower]
             /\ UNCHANGED <<currentTerm, votedFor, logVars, messages>>
          \/ \* accept requests
             /\ m.mterm  = currentTerm[i]
             /\ state[i] = Follower
             /\ logOk
             /\ LET index == m.mprevLogIndex + 1
                IN \/ \* already done with request
                      /\ \/ m.mentries = <<>>
                         \/ /\ m.mentries /= <<>>
                            /\ Len(log[i]) >= index
                            /\ log[i][index].term = m.mentries[1].term
                         \* This could make out commitIndex decrease (for
                         \* example if we process an old, duplicated request),
                         \* but that doesn't really affect anything.
                      /\ commitIndex' = [commitIndex EXCEPT ![i] = m.mcommitIndex]
                      /\ ReplyAppendEntriesAsDone(i, j, m)
                      /\ UNCHANGED log
                   \/ \* conflict: remove 1 entry
                      /\ m.mentries /= <<>>
                      /\ Len(log[i]) >= index
                      /\ log[i][index].term /= m.mentries[1].term
                      /\ LET new == SubSeq(log[i], 1, Len(log[i]) - 1)
                         IN log' = [log EXCEPT ![i] = new]
                      /\ UNCHANGED <<commitIndex, messages>>
                   \/ \* no conflict: append entry
                      /\ m.mentries /= <<>>
                      /\ Len(log[i]) = m.mprevLogIndex
                      /\ log' = [log EXCEPT ![i] = Append(log[i], m.mentries[1])]
                      /\ UNCHANGED <<commitIndex, messages>>
             /\ UNCHANGED <<serverVars, valueRequestedByClient>>
       /\ UNCHANGED <<candidateVars, leaderVars>>

\* Server i receives an AppendEntries response from server j with
\* m.mterm = currentTerm[i].
\* @type: (SERVER, SERVER, MESSAGE) => Bool;
HandleAppendEntriesResponse(i, j, m) ==
    /\ m.mterm = currentTerm[i]
    /\ \/ /\ m.msuccess \* successful
          /\ nextIndex'  = [nextIndex EXCEPT ![i][j] = m.mmatchIndex + 1]
          /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
       \/ /\ ~m.msuccess \* not successful
          /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max({nextIndex[i][j] - 1, 1})]
          /\ UNCHANGED matchIndex
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, logVars, elections>>

\* Any RPC with a newer term causes the recipient to advance its term first.
\* @type: (SERVER, SERVER, MESSAGE) => Bool;
UpdateTerm(i, j, m) ==
    /\ m.mterm > currentTerm[i]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
    /\ state'       = [state EXCEPT ![i] = Follower]
    /\ votedFor'    = [votedFor EXCEPT ![i] = {}]
       \* messages is unchanged so m can be processed further.
    /\ UNCHANGED <<messages, candidateVars, leaderVars, logVars>>

\* Responses with stale terms are ignored.
\* @type: (SERVER, SERVER, MESSAGE) => Bool;
DropStaleResponse(i, j, m) ==
    /\ m.mterm < currentTerm[i]
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* Receive a message.
\* @type: (MESSAGE) => Bool;
Receive(m) ==
    LET i == m.mdest
        j == m.msource
    IN \* Any RPC with a newer term causes the recipient to advance
       \* its term first. Responses with stale terms are ignored.
       \/ UpdateTerm(i, j, m)
       \/ /\ m.mtype = RequestVoteRequest
          /\ HandleRequestVoteRequest(i, j, m)
       \/ /\ m.mtype = RequestVoteResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleRequestVoteResponse(i, j, m)
       \/ /\ m.mtype = AppendEntriesRequest
          /\ HandleAppendEntriesRequest(i, j, m)
       \/ /\ m.mtype = AppendEntriesResponse
          /\ \/ DropStaleResponse(i, j, m)
             \/ HandleAppendEntriesResponse(i, j, m)

\* End of message handlers.
----
\* Network state transitions

\* The network duplicates a message
\* @type: (MESSAGE) => Bool;
DuplicateMessageByNetwork(m) ==
    /\ Send(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

\* The network drops a message
\* @type: (MESSAGE) => Bool;
DropMessageByNetwork(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars, logVars>>

----
\* Defines how the variables may transition.
\* @type: Bool;
Next == \/ \E i \in Server : Restart(i)
        \/ \E i \in Server : Timeout(i)
        \/ \E i,j \in Server : RequestVote(i, j)
        \/ \E i \in Server : BecomeLeader(i)
        \/ \E i \in Server : ClientRequest(i)
        \/ \E i \in Server : AdvanceCommitIndex(i)
        \/ \E i,j \in Server : AppendEntries(i, j)
        \/ \E m \in MessagesInBag(messages) : Receive(m)
        \/ \E m \in SingleMessages(messages) : DuplicateMessageByNetwork(m)
        \/ \E m \in MessagesInBag(messages) : DropMessageByNetwork(m)

\* The specification must start with the initial state and transition according
\* to Next.
\* @type: Bool;
Spec == Init /\ [][Next]_vars

====
