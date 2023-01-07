-------------------------------- MODULE Raft --------------------------------

EXTENDS Integers, FiniteSets, Sequences, TLC

\* Constants definition
CONSTANT Servers

CONSTANT VoteReq, VoteResp, AppendReq, AppendResp

CONSTANT None

CONSTANT MaxElection, MaxLogSize

CONSTANT Follower, Candidate, Leader

ASSUME /\ MaxElection \in Nat
       /\ Servers # {}

symmServers == Permutations(Servers)

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

\* ausialary variable
VARIABLE electionCount

MajoritySize == Cardinality(Servers) \div 2 + 1

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
Init == 
  /\ votedFor = [s \in Servers |-> None ]
  /\ currentTerm = [ s \in Servers |-> 0 ]
  /\ role = [ s \in Servers |-> Follower ]
  /\ logs = [ s \in Servers |-> <<[term |-> 0, val |-> None]>> ]
  /\ matchIndex = [ s \in Servers |-> [ t \in Servers |-> 1 ] ]
  /\ nextIndex = [ s \in Servers |-> [ t \in Servers |-> 2 ] ]
  /\ commitIndex = [ s \in Servers |-> 1 ]
  /\ electionCount = 0
  /\ msgs = {}

BecomeCandidate(s) == 
  /\ electionCount < MaxElection
  /\ role[s] = Follower
  /\ electionCount' = electionCount + 1
  /\ currentTerm' = [ currentTerm EXCEPT ![s] = currentTerm[s] + 1 ]
  /\ role' = [ role EXCEPT ![s] = Candidate ]
  /\ votedFor' = [ votedFor EXCEPT ![s] = s ]
  /\ LET
       lastLogIndex == Len(logs[s])
	   lastLogTerm == logs[s][lastLogIndex].term
       voteReqs == {
         [                                                                       
           dst |-> p,
           src |-> s,
           term |-> currentTerm[s] + 1,
           type |-> VoteReq,
           lastLogIndex |-> lastLogIndex,
           lastLogTerm |-> logs[s][lastLogIndex].term
         ] : p \in Servers\{s}
	   }
     IN
       \* cast votes in one shot
       /\ msgs' = msgs \union voteReqs
       /\ UNCHANGED <<logs, Indexes>>

ResponseVote(s) == 
  /\ role[s] = Follower
  /\ \E m \in msgs:                                                                                  
       /\ m.dst = s                                                                                  
       /\ m.type = VoteReq                                                                           
       /\ m.term = currentTerm[s]                                                                    
	   \* /\ Print({m, votedFor[s]}, TRUE)
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
            \* /\ Print({gm}, TRUE)
            /\ SendMsg(gm)                                                                           
            /\ votedFor' = [ votedFor EXCEPT ![s] = m.src ]                                          
            /\ UNCHANGED <<currentTerm, role, logs, Indexes, electionCount>>


BecomeLeader(s) ==
  /\ role[s] = Candidate
  /\ LET
       resps == {m \in msgs : /\ m.dst = s
                              /\ m.term = currentTerm[s]
                              /\ m.type = VoteResp }
     IN
       /\ Cardinality(resps) + 1 >= MajoritySize
       \* /\ Assert(LeaderHasAllCommittedEntries(s), {s, resps})
       /\ role' = [ role EXCEPT ![s] = Leader ]
       /\ matchIndex' = [ matchIndex EXCEPT ![s] = [ u \in Servers |->  IF u # s THEN 1 ELSE Len(logs[s]) ] ]
       /\ nextIndex' = [ nextIndex EXCEPT ![s] = [ u \in Servers |-> Len(logs[s])+1 ] ]
       \* /\ Print(resps, TRUE)
       \* /\ Print({role', currentTerm, votedFor}, TRUE)
       /\ UNCHANGED <<currentTerm, votedFor, msgs, logs, commitIndex, electionCount>>
       \* /\ Print([IsLeader |-> s, term |-> currentTerm[s]], TRUE)

FollowerUpdateTerm(s) ==
  /\ role[s] = Follower
  /\ \E m \in msgs:
       /\ m.term > currentTerm[s]
       /\ m.dst = s
       /\ currentTerm' = [ currentTerm EXCEPT ![s] = m.term ]
       /\ UNCHANGED <<votedFor, msgs, role, logs, Indexes, electionCount>>

CandidateToFollower(s) ==
  /\ role[s] = Candidate
  /\ \E m \in msgs:
       \/ /\ m.term > currentTerm[s]
          /\ m.dst = s
          /\ currentTerm' = [ currentTerm EXCEPT ![s] = m.term ]
          /\ role' = [ role EXCEPT ![s] = Follower ]
          /\ votedFor' = [ votedFor EXCEPT ![s] = None ]
          /\ UNCHANGED <<msgs, logs, Indexes, electionCount>>
       \/ /\ m.term = currentTerm[s]
          /\ m.dst = s
          /\ m.type = AppendReq
          /\ role' = [ role EXCEPT ![s] = Follower ]
          /\ UNCHANGED <<votedFor, currentTerm, msgs, logs, Indexes, electionCount>>

LeaderToFollower(s) ==
  /\ role[s] = Leader
  /\ \E m \in msgs:
       \* /\ Print(m, TRUE)
       /\ m.term > currentTerm[s]
       /\ m.dst = s
       /\ currentTerm' = [ currentTerm EXCEPT ![s] = m.term ]
       /\ role' = [ role EXCEPT ![s] = Follower ]
       /\ votedFor' = [ votedFor EXCEPT ![s] = None ]
       /\ UNCHANGED <<msgs, logs, Indexes, electionCount>>

\* FIXME
BecomeFollower(s) == 
  \/ FollowerUpdateTerm(s)
  \/ CandidateToFollower(s)
  \/ LeaderToFollower(s)

ClientReq(s) ==
  /\ role[s] = Leader
  /\ Len(logs[s]) < MaxLogSize
  /\ logs' = [ logs EXCEPT ![s] = Append(logs[s], [ term |-> currentTerm[s], val |-> None ]) ]
  /\ matchIndex' = [ matchIndex EXCEPT ![s][s] = Len(logs[s]) + 1 ]
  /\ UNCHANGED <<currentTerm, votedFor, msgs, role, commitIndex, nextIndex, electionCount>>

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
            /\ UNCHANGED <<Indexes, currentTerm, votedFor, role, logs, electionCount>>

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
                   /\ UNCHANGED <<nextIndex, matchIndex, currentTerm, votedFor, role, electionCount>>
                 ELSE
                   /\ SendMsg(resp)
                   /\ UNCHANGED <<nextIndex, matchIndex, currentTerm, votedFor, role, logs, electionCount>>
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
              /\ UNCHANGED <<Indexes, currentTerm, votedFor, role, logs, electionCount>>

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
         /\ UNCHANGED <<currentTerm, votedFor, role, msgs, commitIndex, logs, electionCount>>
       ELSE
         \* enabling condition
         /\ m.prevLogIndex + 2 = nextIndex[s][m.src]
         /\ m.prevLogIndex >= matchIndex[s][m.src]
         /\ nextIndex[s][m.src] # m.prevLogIndex + 1
         \* /\ Assert(m.prevLogIndex + 1 > matchIndex[s][m.src], {s, m, matchIndex[s], nextIndex[s]})
         /\ nextIndex' = [ nextIndex EXCEPT ![s][m.src] = m.prevLogIndex + 1 ]
         /\ UNCHANGED <<currentTerm, votedFor, role, msgs, commitIndex, matchIndex, logs, electionCount>>

LeaderCanCommit(s) ==
  /\ role[s] = Leader
  /\ LET
       median == FindMedian(matchIndex[s])
     IN
       /\ median > commitIndex[s]
       \* /\ Print({s, currentTerm[s], median}, TRUE)
       /\ commitIndex' = [ commitIndex EXCEPT ![s] = median ]
       /\ UNCHANGED <<currentTerm, votedFor, role, msgs, logs, matchIndex, nextIndex, electionCount>>

Restart(s) ==
  /\ role[s] = Leader
  /\ role' = [ role EXCEPT ![s] = Follower ]
  /\ UNCHANGED << votedFor, currentTerm, msgs, matchIndex, nextIndex, commitIndex, logs, electionCount>>

Next ==
  \E s \in Servers:
    \/ BecomeCandidate(s)            
    \/ BecomeFollower(s)             
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

\* all server commit one entry
CommitAll == \A s \in Servers: commitIndex[s] > 1

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

ExistLeaderAndCandidate ==
  /\ \E s1, s2 \in Servers:
       /\ s1 # s2
	   /\ role[s1] = Leader
	   /\ role[s2] = Candidate

\* leader completeness
(*
LeaderHasAllCommittedEntries ==
  LET
    leaderSet == { l \in Servers: /\ role[l] = Leader
	                           /\ \A p \in Servers\{l}: currentTerm[l] >= currentTerm[p] }
    leader == IF Cardinality(leaderSet) == 1 THEN CHOOSE s \in leaderSet: TRUE ELSE NONE
  IN

  \E l \in Servers:
    /\ role[l] = Leader
	/\ ~\E p \in Servers\{s}:
	     /\ currentTerm[p] > currentTerm[l]
	/\ 
  ~ \E p \in Servers\{s}:
      /\ currentTerm[p] <= currentTerm[s]
      /\ \/ commitIndex[p] > Len(logs[s])
         \/ /\ commitIndex[p] <= Len(logs[s])
            /\ \E index \in (1..commitIndex[p]): logs[p][index] # logs[s][index]
*)

Inv ==
  /\ TRUE
  \* /\ NoSplitVote
  \* /\ ~ CommitAll
  \* /\ ~ ExistLeaderAndCandidate

=============================================================================
\* Modification History
\* Last modified Sat Jan 07 11:39:28 CST 2023 by wenlinwu
\* Created Sat Jan 07 09:20:39 CST 2023 by wenlinwu
