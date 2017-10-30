-------------------------- MODULE Transfer_atomic --------------------------

EXTENDS Naturals, TLC

(* --algorithm Transfer_atomic {
variables alice_account = 10, bob_account = 10, money \in 1..20, account_total = alice_account + bob_account;  
{
    Transfer: if (alice_account >= money) {
        A: alice_account := alice_account - money;
           bob_account := bob_account + money;
    };
    C: assert alice_account >= 0;
} 
}*)
\* BEGIN TRANSLATION
VARIABLES alice_account, bob_account, money, account_total, pc

vars == << alice_account, bob_account, money, account_total, pc >>

Init == (* Global variables *)
        /\ alice_account = 10
        /\ bob_account = 10
        /\ money \in 1..20
        /\ account_total = alice_account + bob_account
        /\ pc = "Transfer"

Transfer == /\ pc = "Transfer"
            /\ IF alice_account >= money
                  THEN /\ pc' = "A"
                  ELSE /\ pc' = "C"
            /\ UNCHANGED << alice_account, bob_account, money, account_total >>

A == /\ pc = "A"
     /\ alice_account' = alice_account - money
     /\ bob_account' = bob_account + money
     /\ pc' = "C"
     /\ UNCHANGED << money, account_total >>

C == /\ pc = "C"
     /\ Assert(alice_account >= 0, 
               "Failure of assertion at line 12, column 8.")
     /\ pc' = "Done"
     /\ UNCHANGED << alice_account, bob_account, money, account_total >>

Next == Transfer \/ A \/ C
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

MoneyInvariant == alice_account + bob_account = account_total

=============================================================================
\* Modification History
\* Last modified Mon Oct 16 15:37:47 CST 2017 by tangliu
\* Created Mon Oct 16 15:36:23 CST 2017 by tangliu
