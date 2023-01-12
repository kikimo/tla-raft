-------------------------------- MODULE Raft --------------------------------

EXTENDS Integers, FiniteSets, Sequences, TLC

\* Constants definition
CONSTANT Servers

CONSTANT VoteReq, VoteResp, AppendReq, AppendResp

CONSTANT None

CONSTANT MaxElection, MaxRestart

CONSTANT Follower, Candidate, Leader

CONSTANT Vals

ASSUME /\ MaxElection \in Nat
       /\ Servers # {}

symmServers == Permutations(Servers)

\* Variables definition

\* persistent variable
VARIABLE votedFor, currentTerm, logs

\* transient state variables
VARIABLE matchIndex, nextIndex, commitIndex, msgs, role

Indexes == <<matchIndex, nextIndex, commitIndex>>

\* auxialary variable
VARIABLE electionCount, restartCount, pendingResponse, valSent

AuxVars == <<electionCount, restartCount, pendingResponse, valSent>>

view == <<votedFor, currentTerm, logs, matchIndex, nextIndex, commitIndex, msgs, role>>

\* helpers
MajoritySize == Cardinality(Servers) \div 2 + 1

SendMsg(m) == msgs' = msgs \cup {m}

SendMultiMsgs(mset) == msgs' = msgs \cup mset

Min(a, b) == IF a < b THEN a ELSE b

Max(a, b) == IF a > b THEN a ELSE b

\* TODO: delete me later
\*FindMedian(F) ==
\*  LET
\*    RECURSIVE F2S(_)
\*    F2S(S) ==
\*      IF Cardinality(S) = 0 THEN <<>>
\*                            ELSE
\*                              LET
\*                                m == CHOOSE u \in S: \A v \in S: F[u] <= F[v]
\*                              IN
\*                                F2S(S\{m}) \o <<F[m]>>
\*
\*    mlist == F2S(DOMAIN F)
\*    pos == Len(mlist) \div 2 + 1
\*    \* introduce mistack
\*    \* pos == Len(mlist) \div 2
\*  IN
\*    mlist[pos]

Median(F) ==
  LET
    mset == { s \in DOMAIN F : Cardinality({ p \in DOMAIN F : F[p] <= F[s] }) >= MajoritySize }
    median == CHOOSE s \in mset: (\A p \in mset: F[p] >= F[s])
  IN
    F[median]

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
  /\ restartCount = 0
  /\ msgs = {}
  /\ pendingResponse = [ s \in Servers |-> [ p \in Servers |-> FALSE ]]
  /\ valSent = [ v \in Vals |-> None ]

BecomeCandidate(s) == 
  /\ electionCount < MaxElection
  /\ role[s] \in { Follower, Candidate }
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
           lastLogTerm |-> lastLogTerm
         ] : p \in Servers\{s}
	   }
     IN
       \* broadcast votes in one shot
       /\ SendMultiMsgs(voteReqs)
       /\ UNCHANGED << logs, Indexes, restartCount, pendingResponse, valSent >>

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
            grantVote == [ dst |-> m.src, src |-> s, term |-> m.term, type |-> VoteResp ]
          IN
            /\ grantVote \notin msgs
            \* /\ Print({gm}, TRUE)
            /\ SendMsg(grantVote)
            /\ votedFor' = [ votedFor EXCEPT ![s] = m.src ]
            /\ UNCHANGED << currentTerm, role, logs, Indexes, AuxVars >>

BecomeLeader(s) ==
  /\ role[s] = Candidate
  /\ LET
       resps == {m \in msgs : /\ m.dst = s
                              /\ m.term = currentTerm[s]
                              /\ m.type = VoteResp }
     IN
       /\ Cardinality(resps) + 1 >= MajoritySize \* plus an extra vote for candidate itself
       \* /\ Assert(LeaderHasAllCommittedEntries(s), {s, resps})
       /\ role' = [ role EXCEPT ![s] = Leader ]
       /\ matchIndex' = [ matchIndex EXCEPT ![s] = [ u \in Servers |->  IF u # s THEN 1 ELSE Len(logs[s]) ] ]
       /\ nextIndex' = [ nextIndex EXCEPT ![s] = [ u \in Servers |-> Len(logs[s])+1 ] ]
       /\ pendingResponse' = [ pendingResponse EXCEPT ![s] = [ p \in Servers |-> FALSE ] ]
       \* /\ Print(resps, TRUE)
       \* /\ Print({role', currentTerm, votedFor}, TRUE)
       /\ UNCHANGED <<currentTerm, votedFor, msgs, logs, commitIndex, electionCount, restartCount, valSent>>
       \* /\ Print([IsLeader |-> s, term |-> currentTerm[s]], TRUE)

UpdateTerm(s) ==
  \E m \in msgs:
    /\ m.dst = s
    /\ \/ /\ m.term > currentTerm[s]
          /\ role' = [ role EXCEPT ![s] = Follower ]
          /\ currentTerm' = [ currentTerm EXCEPT ![s] = m.term ]
          /\ votedFor' = [ votedFor EXCEPT ![s] = None ]
          /\ UNCHANGED << msgs, logs, Indexes, AuxVars >>
       \/ /\ m.term = currentTerm[s]
          /\ m.type = AppendReq
          /\ Assert(role[s] # Leader, "split brain")
          /\ role[s] = Candidate
          /\ role' = [ role EXCEPT ![s] = Follower ]
          /\ UNCHANGED << currentTerm, votedFor, msgs, logs, Indexes, AuxVars >>

\* TODO: delete me later
FollowerUpdateTerm(s) ==
  /\ role[s] = Follower
  /\ \E m \in msgs:
       /\ m.term > currentTerm[s]
       /\ m.dst = s
       /\ currentTerm' = [ currentTerm EXCEPT ![s] = m.term ]
       /\ UNCHANGED << votedFor, msgs, role, logs, Indexes, AuxVars >>

\* TODO: delete me later
CandidateToFollower(s) ==
  /\ role[s] = Candidate
  /\ \E m \in msgs:
       \/ /\ m.term > currentTerm[s]
          /\ m.dst = s
          /\ currentTerm' = [ currentTerm EXCEPT ![s] = m.term ]
          /\ role' = [ role EXCEPT ![s] = Follower ]
          /\ votedFor' = [ votedFor EXCEPT ![s] = None ]
          /\ UNCHANGED << msgs, logs, Indexes, AuxVars >>
       \/ /\ m.term = currentTerm[s]
          /\ m.dst = s
          /\ m.type = AppendReq
          /\ role' = [ role EXCEPT ![s] = Follower ]
          /\ UNCHANGED << votedFor, currentTerm, msgs, logs, Indexes, AuxVars >>

\* TODO: delete me later
LeaderToFollower(s) ==
  /\ role[s] = Leader
  /\ \E m \in msgs:
       \* /\ Print(m, TRUE)
       /\ m.term > currentTerm[s]
       /\ m.dst = s
       /\ currentTerm' = [ currentTerm EXCEPT ![s] = m.term ]
       /\ role' = [ role EXCEPT ![s] = Follower ]
       /\ votedFor' = [ votedFor EXCEPT ![s] = None ]
       /\ UNCHANGED << msgs, logs, Indexes, AuxVars >>

\* TODO: delete me later
BecomeFollower(s) ==
  \/ FollowerUpdateTerm(s)
  \/ CandidateToFollower(s)
  \/ LeaderToFollower(s)

ClientReq(s) ==
  /\ role[s] = Leader
  /\ \E v \in Vals:
       /\ valSent[v] = None
       /\ valSent' = [ valSent EXCEPT ![v] = FALSE ]
       /\ logs' = [ logs EXCEPT ![s] = Append(logs[s], [ term |-> currentTerm[s], val |-> v ]) ]
       /\ matchIndex' = [ matchIndex EXCEPT ![s][s] = Len(logs[s]) + 1 ]
       /\ UNCHANGED << currentTerm, votedFor, msgs, role, commitIndex, nextIndex, electionCount, restartCount, pendingResponse >>

LeaderAppendEntry(s) ==
  /\ role[s] = Leader
  /\ \E dst \in Servers\{s}:
       /\ nextIndex[s][dst] <= Len(logs[s]) + 1
       /\ pendingResponse[s][dst] = FALSE
       /\ LET
            prevLogIndex == nextIndex[s][dst] - 1
            prevLogTerm == logs[s][prevLogIndex].term
            \* entries == <<>> if nextIndex[s][dst] > Len(logs[s])
            \* TODO: limit to only one entry per request
            entries == SubSeq(logs[s], nextIndex[s][dst], Len(logs[s]))
            appendEntries == IF Len(entries) > 0 THEN << Head(entries) >> ELSE <<>>
            m == [
              type |-> AppendReq,
              dst |-> dst,
              src |-> s,
              prevLogIndex |-> prevLogIndex,
              prevLogTerm |-> prevLogTerm,
              term |-> currentTerm[s],
              entries |-> appendEntries,
              leaderCommit |-> commitIndex[s]
            ]
          IN
            /\ m \notin msgs
            /\ pendingResponse' = [ pendingResponse EXCEPT ![s][dst] = TRUE ]
            \* /\ Print([appendReq |-> m], TRUE)
            /\ SendMsg(m)
            /\ UNCHANGED << Indexes, currentTerm, votedFor, role, logs, electionCount, restartCount, valSent >>

LogMatch(s, m) ==
  /\ m.prevLogIndex <= Len(logs[s])
  /\ m.prevLogTerm = logs[s][m.prevLogIndex].term

FollowerAcceptEntry(s) ==
  /\ role[s] = Follower
  /\ \E m \in msgs:
       /\ m.dst = s
       /\ m.term = currentTerm[s]
       /\ m.type = AppendReq
       /\ LogMatch(s, m) 
       /\ LET
            accResp == [
              type |-> AppendResp,
              dst |-> m.src,
              src |-> s,
              prevLogIndex |-> m.prevLogIndex + Len(m.entries),
              succ |-> TRUE,
              term |-> m.term
            ]
            newLog == SubSeq(logs[s], 1, m.prevLogIndex) \o m.entries
            appendNew == Len(newLog) > Len(logs[s])
            truncated == Len(newLog) <= Len(logs[s]) /\ newLog # SubSeq(logs[s], 1, Len(newLog))
            newCommitIndex == Max(commitIndex[s], Min(m.leaderCommit, Len(newLog)))
            updatedLog == IF truncated \/ appendNew THEN newLog ELSE logs[s]
          IN
            /\ SendMsg(accResp)
            /\ commitIndex' = [ commitIndex EXCEPT ![s] = newCommitIndex ]
            /\ logs' = [ logs EXCEPT ![s] = updatedLog ]
            /\ UNCHANGED << currentTerm, votedFor, role, matchIndex, nextIndex, AuxVars >>

FollowerRejectEntry(s) ==
  /\ role[s] = Follower
  /\ \E m \in msgs:
       /\ m.dst = s
       /\ m.term = currentTerm[s]
       /\ m.type = AppendReq
       /\ ~ LogMatch(s, m)
       /\ LET
            rejectResp == [
              type |-> AppendResp,
              dst |-> m.src,
              src |-> s,
              prevLogIndex |-> m.prevLogIndex,
              succ |-> FALSE,
              term |-> m.term
            ]
          IN
            /\ rejectResp \notin msgs
            /\ SendMsg(rejectResp)
            /\ UNCHANGED << Indexes, AuxVars, currentTerm, votedFor, logs, role >>

FollowerAppendEntry(s) ==
  /\ role[s] = Follower
  /\ \E m \in msgs:
       /\ m.dst = s
       /\ m.term = currentTerm[s]
       /\ m.type = AppendReq
       \* /\ Assert(m.prevLogIndex >= commitIndex[s], "illegal log match state")
       /\ IF LogMatch(s, m) THEN
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
                   /\ UNCHANGED << nextIndex, matchIndex, currentTerm, votedFor, role, electionCount, restartCount, pendingResponse >>
                 ELSE
                   /\ SendMsg(resp)
                   /\ UNCHANGED <<nextIndex, matchIndex, currentTerm, votedFor, role, logs, electionCount, restartCount, pendingResponse>>
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
              /\ UNCHANGED << Indexes, currentTerm, votedFor, role, logs, electionCount, restartCount, pendingResponse >>

\* leader handle append response
HandleAppendResp(s) ==
  /\ role[s] = Leader
  /\ \E m \in msgs:
    /\ m.type = AppendResp
    /\ m.dst = s
    /\ m.term = currentTerm[s]
    /\ pendingResponse[s][m.src] = TRUE
    /\ IF m.succ THEN
         \* (m.succ = TRUE) => (m.prevLogIndex = matchingIndex[s][m.src])
         /\ matchIndex[s][m.src] < m.prevLogIndex
         /\ matchIndex' = [ matchIndex EXCEPT ![s][m.src] = m.prevLogIndex ]
         /\ nextIndex' = [ nextIndex EXCEPT ![s][m.src] = m.prevLogIndex + 1 ]
         /\ pendingResponse' = [ pendingResponse EXCEPT ![s][m.src] = FALSE ]
         \* TODO commit entry if possible
         /\ UNCHANGED << currentTerm, votedFor, role, msgs, commitIndex, logs, electionCount, restartCount, valSent >>
       ELSE
         \* enabling condition
         /\ m.prevLogIndex + 1 = nextIndex[s][m.src]
         /\ m.prevLogIndex > matchIndex[s][m.src]
         \* /\ Assert(m.prevLogIndex > matchIndex[s][m.src], [msg |-> "disagree on matching index", appendResp |-> m])
         /\ pendingResponse' = [ pendingResponse EXCEPT ![s][m.src] = FALSE ]
         /\ nextIndex' = [ nextIndex EXCEPT ![s][m.src] = m.prevLogIndex ]
         /\ UNCHANGED << currentTerm, votedFor, role, msgs, commitIndex, matchIndex, logs, electionCount, restartCount, valSent >>

LeaderCanCommit(s) ==
  /\ role[s] = Leader
  /\ LET
       \* median == FindMedian(matchIndex[s])
       median == Median(matchIndex[s])
     IN
       /\ median > commitIndex[s]
       \* /\ Print({s, currentTerm[s], median}, TRUE)
       /\ commitIndex' = [ commitIndex EXCEPT ![s] = median ]
       /\ UNCHANGED << currentTerm, votedFor, role, msgs, logs, matchIndex, nextIndex, electionCount, restartCount, pendingResponse, valSent >>

Restart(s) ==
  /\ role[s] = Leader
  /\ restartCount < MaxRestart
  /\ restartCount' = restartCount + 1
  /\ role' = [ role EXCEPT ![s] = Follower ]
  /\ UNCHANGED << votedFor, currentTerm, msgs, matchIndex, nextIndex, commitIndex, logs, electionCount, pendingResponse, valSent >>

Next ==
  \E s \in Servers:
    \/ BecomeCandidate(s)            
    \/ UpdateTerm(s)  
    \* \/ BecomeFollower(s)           
    \/ ResponseVote(s)               
    \/ BecomeLeader(s)               
    \/ ClientReq(s)                  
    \/ LeaderAppendEntry(s)          
    \* \/ FollowerAppendEntry(s)
    \/ FollowerAcceptEntry(s)
    \/ FollowerRejectEntry(s)      
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
CommitAll == \A s \in Servers: commitIndex[s] = 3

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

LeaderHasAllCommittedEntries ==
  \/ ~\E p \in Servers: role[p] = Leader
  \/ \E l \in Servers:
       /\ role[l] = Leader
	   /\ ~\E p \in Servers\{l}:
            /\ currentTerm[p] <= currentTerm[l]
            /\ \/ commitIndex[p] > Len(logs[l])
               \/ /\ commitIndex[p] <= Len(logs[l])
                  /\ \E index \in (1..commitIndex[p]): logs[p][index] # logs[l][index]


Inv ==
  LeaderHasAllCommittedEntries
  \* /\ TRUE
  \* /\ NoSplitVote
  \* /\ ~ CommitAll
  \* /\ ~ ExistLeaderAndCandidate

=============================================================================
\* Modification History
\* Last modified Wed Jan 11 09:42:33 CST 2023 by wenlinwu
\* Created Sat Jan 07 09:20:39 CST 2023 by wenlinwu

