------------------------------ MODULE TCommit ------------------------------

CONSTANTS RM

VARIABLES rmState, v

TCTypeOK == rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCInit == rmState = [r \in RM |-> "working"]
          
Prepare(rm) == /\ rmState[rm] = "working"
               /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
               
canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}

notCommitted == \A rm \in RM : rmState[rm] /= "committed"
               
Decide(rm) == \/ /\ rmState[rm] = "prepared"
                 /\ canCommit
                 /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
              \/ /\ rmState[rm] \in {"working", "prepared"}
                 /\ notCommitted
                 /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]

TCNext == \E rm \in RM :  Prepare(rm) \/ Decide(rm)

TCConsistent == \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                                       /\ rmState[rm2] = "committed"

=============================================================================
\* Modification History
\* Last modified Wed Oct 25 22:29:01 CST 2017 by tangliu
\* Created Wed Oct 25 09:45:19 CST 2017 by tangliu
