--------------------------- MODULE Raft ---------------------------

EXTENDS Integers, FiniteSets, Sequences, TLC

\* Constants definition
CONSTANT Servers

CONSTANT VoteReq, VoteResp, AppendReq, AppendResp

CONSTANT None

CONSTANT MaxTerm, MaxLogSize

CONSTANT Follower, Candidate, Leader

ASSUME /\ MaxTerm \in Nat
       /\ Servers # {}

\* Variables definition
VARIABLE votedFor

VARIABLE currentTerm

VARIABLE role

VARIABLE msgs

\* transient state variables
VARIABLE matchIndex

VARIABLE nextIndex

VARIABLE commitIndex

VARIABLE logs

Indexes == <<matchIndex, nextIndex, commitIndex>>

\* helpers
SendMsg(m) == msgs' = msgs \cup {m}

Min(a, b) == IF a < b THEN a ELSE b

Max(a, b) == IF a > b THEN a ELSE b

FindMedian(F) ==
  LET
    RECURSIVE F2S(_)
    F2S(S) ==
      IF Cardinality(S) = 0 THEN <<>>
                            ELSE
                              LET
                                m == CHOOSE u \in S: \A v \in S: F[u] <= F[v]
                              IN
                                F2S(S\{m}) \o <<F[m]>>

    mlist == F2S(DOMAIN F)
    pos == Len(mlist) \div 2 + 1
    \* introduce mistack
    \* pos == Len(mlist) \div 2
  IN
    mlist[pos]

\*HasAllCommitedLog(l, f) == 
\*  LET
\*    lsz == Len(logs[l])
\*    domain == DOMAIN currentTerm
\*    x == CHOOSE u \in domain: \A v \in domain: currentTerm[u] >= currentTerm[v]
\*    maxTerm == currentTerm[x]
\*  IN
\*    IF currentTerm[l] = maxTerm THEN
\*      /\ lsz >= commitIndex[f]
\*      /\ SubSeq(logs[l], 1, commitIndex[f]) = SubSeq(logs[f], 1, commitIndex[f])
\*    ELSE
\*      TRUE
\*
\*LeaderCompleteness(s) == \A f \in Servers\{s}: HasAllCommitedLog(s, f)

\* raft spec
Init == /\ votedFor = [s \in Servers |-> None ]
        /\ currentTerm = [ s \in Servers |-> 0 ]
        /\ role = [ s \in Servers |-> Follower ]
        /\ logs = [ s \in Servers |-> <<[term |-> 0, val |-> None]>> ]
        /\ matchIndex = [ s \in Servers |-> [ t \in Servers |-> 1 ] ]
        /\ nextIndex = [ s \in Servers |-> [ t \in Servers |-> 2 ] ]
        /\ commitIndex = [ s \in Servers |-> 1 ]
        /\ msgs = {}

BecomeCandidate(s) == /\ currentTerm[s] + 1 <= MaxTerm
                      /\ role[s] = Follower
                      /\ currentTerm' = [ currentTerm EXCEPT ![s] = currentTerm[s] + 1 ]
                      /\ role' = [ role EXCEPT ![s] = Candidate ]
                      /\ votedFor' = [ votedFor EXCEPT ![s] = s ]
                      /\ UNCHANGED <<msgs, logs, Indexes>>

RequestVote(s) == /\ role[s] = Candidate
                  /\ \E dst \in Servers\{s}:
                       LET
                         lastLogIndex == Len(logs[s])
                         m == [
                           dst |-> dst,
                           src |-> s,
                           term |-> currentTerm[s],
                           type |-> VoteReq,
                           lastLogIndex |-> lastLogIndex,
                           lastLogTerm |-> logs[s][lastLogIndex].term]
                       IN
                         /\ m \notin msgs
                         /\ SendMsg(m)
                         /\ UNCHANGED <<votedFor, currentTerm, role, logs, Indexes>>

ResponseVote(s) == /\ role[s] = Follower
                   /\ \E m \in msgs:
                        /\ m.dst = s
                        /\ m.type = VoteReq
                        /\ m.term = currentTerm[s]
                        /\ \/ votedFor[s] = None
                           \/ votedFor[s] = m.src
                        /\ LET
                             lastLogIndex == Len(logs[s])
                             lastLogTerm == logs[s][lastLogIndex].term
                           IN
                             \/ m.lastLogTerm > lastLogTerm
                             \/ /\ m.lastLogTerm = lastLogTerm
                                /\ m.lastLogIndex >= lastLogIndex
                        /\ LET
                             gm == [ dst |-> m.src, src |-> s, term |-> m.term, type |-> VoteResp ]
                           IN
                             /\ gm \notin msgs
                             /\ SendMsg(gm)
                             /\ votedFor' = [ votedFor EXCEPT ![s] = m.src ]
                             /\ UNCHANGED <<currentTerm, role, logs, Indexes>>

LeaderHasAllCommittedEntries(s) ==
  ~ \E p \in Servers\{s}:
      /\ currentTerm[p] <= currentTerm[s]
      /\ \/ commitIndex[p] > Len(logs[s])
         \/ /\ commitIndex[p] <= Len(logs[s])
            /\ \E index \in (1..commitIndex[p]): logs[p][index] # logs[s][index]
  

BecomeLeader(s) == /\ role[s] = Candidate
                   /\ LET
                        resps == {m \in msgs : /\ m.dst = s
                                               /\ m.term = currentTerm[s]
                                               /\ m.type = VoteResp }
                      IN
                        /\ (Cardinality(resps) + 1) * 2 > Cardinality(Servers)
                        /\ Assert(LeaderHasAllCommittedEntries(s), {s, resps})
                        /\ role' = [ role EXCEPT ![s] = Leader ]
                        /\ matchIndex' = [ matchIndex EXCEPT ![s] = [ u \in Servers |->  IF u # s THEN 1 ELSE Len(logs[s]) ] ]
                        /\ nextIndex' = [ nextIndex EXCEPT ![s] = [ u \in Servers |-> Len(logs[s])+1 ] ]
                        \* /\ Print(resps, TRUE)
                        \* /\ Print({role', currentTerm, votedFor}, TRUE)
                        /\ UNCHANGED <<currentTerm, votedFor, msgs, logs, commitIndex>>
                        \* /\ Print([IsLeader |-> s, term |-> currentTerm[s]], TRUE)

FollowerUpdateTerm(s) == /\ role[s] = Follower
                         /\ \E m \in msgs:
                              /\ m.term > currentTerm[s]
                              /\ m.dst = s
                              /\ currentTerm' = [ currentTerm EXCEPT ![s] = m.term ]
                              /\ UNCHANGED <<votedFor, msgs, role, logs, Indexes>>

CandateToFollower(s) == /\ role[s] = Candidate
                        /\ \E m \in msgs:
                             \/ /\ m.term > currentTerm[s]
                                /\ m.dst = s
                                /\ currentTerm' = [ currentTerm EXCEPT ![s] = m.term ]
                                /\ role' = [ role EXCEPT ![s] = Follower ]
                                /\ votedFor' = [ votedFor EXCEPT ![s] = None ]
                                /\ UNCHANGED <<msgs, logs, Indexes>>
                             \/ /\ m.term = currentTerm[s]
                                /\ m.dst = s
                                /\ m.type = AppendReq
                                /\ role' = [ role EXCEPT ![s] = Follower ]
                                /\ UNCHANGED <<votedFor, currentTerm, msgs, logs, Indexes>>

LeaderToFollower(s) == /\ role[s] = Leader
                       /\ \E m \in msgs:
                            \* /\ Print(m, TRUE)
                            /\ m.term > currentTerm[s]
                            /\ m.dst = s
                            /\ currentTerm' = [ currentTerm EXCEPT ![s] = m.term ]
                            /\ role' = [ role EXCEPT ![s] = Follower ]
                            /\ votedFor' = [ votedFor EXCEPT ![s] = None ]
                            /\ UNCHANGED <<msgs, logs, Indexes>>

BecomeFollower(s) == \/ FollowerUpdateTerm(s)
                     \/ CandateToFollower(s)
                     \/ LeaderToFollower(s)

ClientReq(s) == /\ role[s] = Leader
                /\ Len(logs[s]) < MaxLogSize
                /\ logs' = [ logs EXCEPT ![s] = Append(logs[s], [ term |-> currentTerm[s], val |-> None ]) ]
                /\ matchIndex' = [ matchIndex EXCEPT ![s][s] = Len(logs[s]) + 1 ]
                /\ UNCHANGED <<currentTerm, votedFor, msgs, role, commitIndex, nextIndex>>

LeaderAppendEntry(s) ==
  /\ role[s] = Leader
  /\ \E dst \in Servers:
       /\ dst # s
       /\ nextIndex[s][dst] <= Len(logs[s]) + 1
       /\ LET
            prevLogIndex == nextIndex[s][dst] - 1
            prevLogTerm == logs[s][prevLogIndex].term
            \* entries == <<>> if nextIndex[s][dst] > Len(logs[s])
            entries == SubSeq(logs[s], nextIndex[s][dst], Len(logs[s]))
            m == [
              type |-> AppendReq,
              dst |-> dst,
              src |-> s,
              prevLogIndex |-> prevLogIndex,
              prevLogTerm |-> prevLogTerm,
              term |-> currentTerm[s],
              entries |-> entries,
              leaderCommit |-> commitIndex[s]
            ] 
          IN
            /\ m \notin msgs
            /\ SendMsg(m)
            /\ UNCHANGED <<Indexes, currentTerm, votedFor, role, logs>>

IsLogMatch(s, m) ==
  /\ m.prevLogIndex <= Len(logs[s]) 
  /\ m.prevLogTerm = logs[s][m.prevLogIndex].term

FollowerAppendEntry(s) == 
  /\ role[s] = Follower
  /\ \E m \in msgs:
       /\ m.dst = s
       /\ m.term = currentTerm[s]
       /\ m.type = AppendReq
       \* /\ Assert(m.prevLogIndex >= commitIndex[s], "illegal log match state")
       /\ IF IsLogMatch(s, m) THEN
            LET
              resp == [
                type |-> AppendResp,
                dst |-> m.src,
                src |-> s,
                prevLogIndex |-> m.prevLogIndex + Len(m.entries),
                succ |-> TRUE,
                term |-> m.term
              ]
              newLog == SubSeq(logs[s], 1, m.prevLogIndex) \o m.entries
              appendNew == Len(newLog) > Len(logs[s])
              truncated == /\ Len(newLog) <= Len(logs[s])
                           /\ newLog # SubSeq(logs[s], 1, Len(newLog))
              updateLog == appendNew \/ truncated
              newCommitIndex == Max(commitIndex[s], Min(m.leaderCommit, Len(newLog)))
            IN
              /\ \/ resp \notin msgs
                 \/ newCommitIndex > commitIndex[s]
              /\ commitIndex' = [ commitIndex EXCEPT ![s] = newCommitIndex ]
              /\ IF updateLog THEN
                   /\ SendMsg(resp)
                   /\ logs' = [ logs EXCEPT ![s] = newLog ]
                   \* /\ Print([ msg |-> m, logs |-> logs[s], entries |-> m.entries, newLog |-> newLog ], TRUE)
                   /\ UNCHANGED <<nextIndex, matchIndex, currentTerm, votedFor, role>>
                 ELSE
                   /\ SendMsg(resp)
                   /\ UNCHANGED <<nextIndex, matchIndex, currentTerm, votedFor, role, logs>>
          ELSE
            LET
              resp == [
                type |-> AppendResp,
                dst |-> m.src,
                src |-> s,
                prevLogIndex |-> m.prevLogIndex - 1,
                succ |-> FALSE,
                term |-> m.term
              ]
            IN
              /\ resp \notin msgs
              /\ SendMsg(resp)
              /\ UNCHANGED <<Indexes, currentTerm, votedFor, role, logs>>

\* leader handle append response
HandleAppendResp(s) ==
  /\ role[s] = Leader
  /\ \E m \in msgs:
    /\ m.type = AppendResp
    /\ m.dst = s
    /\ m.term = currentTerm[s]
    /\ IF m.succ THEN
         /\ matchIndex[s][m.src] < m.prevLogIndex
         /\ matchIndex' = [ matchIndex EXCEPT ![s][m.src] = m.prevLogIndex ]
         /\ nextIndex' = [ nextIndex EXCEPT ![s][m.src] = m.prevLogIndex + 1 ]
         \* TODO commit entry if possible
         /\ UNCHANGED <<currentTerm, votedFor, role, msgs, commitIndex, logs>>
       ELSE
         \* enabling condition
         /\ m.prevLogIndex + 2 = nextIndex[s][m.src]
         /\ m.prevLogIndex >= matchIndex[s][m.src]
         /\ nextIndex[s][m.src] # m.prevLogIndex + 1
         \* /\ Assert(m.prevLogIndex + 1 > matchIndex[s][m.src], {s, m, matchIndex[s], nextIndex[s]})
         /\ nextIndex' = [ nextIndex EXCEPT ![s][m.src] = m.prevLogIndex + 1 ]
         /\ UNCHANGED <<currentTerm, votedFor, role, msgs, commitIndex, matchIndex, logs>>

LeaderCanCommit(s) ==
  /\ role[s] = Leader
  /\ LET
       median == FindMedian(matchIndex[s])
     IN
       /\ median > commitIndex[s]
       \* /\ Print({s, currentTerm[s], median}, TRUE)
       /\ commitIndex' = [ commitIndex EXCEPT ![s] = median ]
       /\ UNCHANGED <<currentTerm, votedFor, role, msgs, logs, matchIndex, nextIndex>>

Restart(s) ==
  /\ role[s] = Leader
  /\ role' = [ role EXCEPT ![s] = Follower ]
  /\ UNCHANGED << votedFor, currentTerm, msgs, matchIndex, nextIndex, commitIndex, logs >>

Next == \E s \in Servers:
          \/ BecomeCandidate(s)
          \/ BecomeFollower(s)
          \/ RequestVote(s)
          \/ ResponseVote(s)
          \/ BecomeLeader(s)
          \/ ClientReq(s)
          \/ LeaderAppendEntry(s)
          \/ FollowerAppendEntry(s)
          \/ HandleAppendResp(s)
          \/ LeaderCanCommit(s)
          \/ Restart(s)

\* Invariants
\* for debug
RaftCanCommt == \E s \in Servers: commitIndex[s] > 1

FollowerCanCommit ==
  \E s \in Servers:
    /\ role[s] = Follower
    /\ commitIndex[s] > 1
    
CommitAll == \A s \in Servers: commitIndex[s] > 2

NoSplitVote == ~ \E s1, s2 \in Servers:
                     /\ s1 # s2
                     /\ currentTerm[s1] = currentTerm[s2]
                     /\ role[s1] = Leader
                     /\ role[s2] = Leader
                     \* /\ Print({currentTerm, role, votedFor}, TRUE)

NoAllCommit ==
  \E s1, s2, s3 \in Servers:
    /\ s1 # s2
    /\ s2 # s3
    /\ role[s1] = Leader
    /\ role[s2] = Follower
    /\ role[s3] = Follower
    /\ currentTerm[s1] = currentTerm[s3]
    /\ commitIndex[s1] = 2
    /\ commitIndex[s2] = 2
    /\ commitIndex[s3] = 1
    /\ matchIndex[s1][s2] = 2
    /\ matchIndex[s1][s3] = 2
    /\ \E m \in msgs:
         /\ m.dst = s3
         /\ m.src = s1
         /\ m.term = currentTerm[s3]
         /\ m.type = AppendReq
         /\ m.prevLogIndex = 1
    /\ \E m \in msgs:
         /\ m.dst = s1
         /\ m.src = s3
         /\ m.term = currentTerm[s3]
         /\ m.type = AppendResp
         /\ m.prevLogIndex = 1
         /\ m.succ = TRUE
    /\ \E m \in msgs:
         /\ m.dst = s3
         /\ m.src = s1
         /\ m.type = AppendReq
         /\ m.prevLogIndex = 2

Inv == TRUE \* ~CommitAll

=============================================================================
\* Modification History
\* Last modified Tue Jan 03 21:15:28 CST 2023 by wenlinwu
\* Created Wed Dec 14 10:07:36 CST 2022 by wenlinwu

