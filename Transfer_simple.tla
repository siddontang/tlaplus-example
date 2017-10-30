-------------------------- MODULE Transfer_simple --------------------------

EXTENDS Naturals, TLC

(* --algorithm Transfer_simple {
    variables alice_account = 10, bob_account = 10, money = 5;
    {
        A: alice_account := alice_account - money;
        B: bob_account := bob_account + money;
    } 
}*)
\* BEGIN TRANSLATION
VARIABLES alice_account, bob_account, money, pc

vars == << alice_account, bob_account, money, pc >>

Init == (* Global variables *)
        /\ alice_account = 10
        /\ bob_account = 10
        /\ money = 5
        /\ pc = "A"

A == /\ pc = "A"
     /\ alice_account' = alice_account - money
     /\ pc' = "B"
     /\ UNCHANGED << bob_account, money >>

B == /\ pc = "B"
     /\ bob_account' = bob_account + money
     /\ pc' = "Done"
     /\ UNCHANGED << alice_account, money >>

Next == A \/ B
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Mon Oct 16 15:11:17 CST 2017 by tangliu
\* Created Mon Oct 16 15:09:08 CST 2017 by tangliu
