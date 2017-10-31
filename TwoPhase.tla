------------------------------ MODULE TwoPhase ------------------------------

CONSTANT RM

VARIABLES rmState, tmState, tmPrepared, msgs

Messages == [type: {"Prepared"}, rm: RM] \union [type: {"Commit", "Abort"}]

TPTypeOK == 
    /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
    /\ tmState \in {"init", "committed", "aborted"}
    /\ tmPrepared \subseteq RM
    /\ msgs \subseteq Messages
            
TPInit == 
    /\ rmState = [r \in RM |-> "working"]
    /\ tmState = "init"
    /\ tmPrepared = {}
    /\ msgs = {}
        
TMRcvPrepared(r) == 
    /\ tmState = "init"
    /\ [type |-> "Prepared", rm |-> r] \in msgs
    /\ tmPrepared' = tmPrepared \union {r}
    /\ UNCHANGED <<rmState, tmState, msgs>>
    
TMCommit ==
    /\ tmState = "init"
    /\ tmPrepared = RM
    /\ tmState' = "committed"
    /\ msgs' = msgs \union {[type |-> "Commit"]}
    /\ UNCHANGED <<rmState, tmPrepared>>

TMAbort ==
    /\ tmState = "init"
    /\ tmPrepared = RM
    /\ tmState' = "aborted"
    /\ msgs' = msgs \union {[type |-> "Abort"]}
    /\ UNCHANGED <<rmState, tmPrepared>>
    
RMPrepare(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
    /\ msgs' = msgs \union {[type |-> "Prepared", rm |-> r]}
    /\ UNCHANGED <<tmState, tmPrepared>>
    
RMChooseToAbort(r) ==
    /\ rmState[r] = "working"
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs>>
    
RMRcvCommitMsg(r) ==
    /\ [type |-> "Commit"] \in msgs
    /\ rmState' = [rmState EXCEPT ![r] = "committed"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs>>
    
RMRcvAbortMsg(r) ==
    /\ [type |-> "Abort"] \in msgs
    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
    /\ UNCHANGED <<tmState, tmPrepared, msgs>>    
    
TPNext ==
    \/ TMCommit \/ TMAbort
    \/ \E r \in RM:
        TMRcvPrepared(r) \/ RMPrepare(r) \/ RMChooseToAbort(r)
            \/ RMRcvCommitMsg(r) \/ RMRcvAbortMsg(r)
    
=============================================================================
\* Modification History
\* Last modified Tue Oct 31 08:14:23 CST 2017 by tangliu
\* Created Thu Oct 26 22:00:18 CST 2017 by tangliu
