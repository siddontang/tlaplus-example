------------------------ MODULE Transfer_invariants ------------------------

EXTENDS Naturals, TLC

(* --algorithm Transfer_invariants {
variables alice_account = 10, bob_account = 10, money \in 1..20, account_total = alice_account + bob_account;  
{
    Transfer: if (alice_account >= money) {
        A: alice_account := alice_account - money;
        B: bob_account := bob_account + money;
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
     /\ pc' = "B"
     /\ UNCHANGED << bob_account, money, account_total >>

B == /\ pc = "B"
     /\ bob_account' = bob_account + money
     /\ pc' = "C"
     /\ UNCHANGED << alice_account, money, account_total >>

C == /\ pc = "C"
     /\ Assert(alice_account >= 0, 
               "Failure of assertion at line 12, column 8.")
     /\ pc' = "Done"
     /\ UNCHANGED << alice_account, bob_account, money, account_total >>

Next == Transfer \/ A \/ B \/ C
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

MoneyInvariant == alice_account + bob_account = account_total

=============================================================================
\* Modification History
\* Last modified Mon Oct 16 15:32:26 CST 2017 by tangliu
\* Created Mon Oct 16 15:21:21 CST 2017 by tangliu
