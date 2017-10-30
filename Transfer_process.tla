-------------------------- MODULE Transfer_process --------------------------

EXTENDS Naturals, TLC

(* --algorithm Transfer_process {
variables alice_account = 10, bob_account = 10, account_total = alice_account + bob_account;  

process (Transfer \in 1..2)

variable money \in 1..20, 
{
Transfer: if (alice_account >= money) {
    A: alice_account := alice_account - money;
       bob_account := bob_account + money;
};
C: assert alice_account >= 0;

}
}*)
\* BEGIN TRANSLATION
\* Label Transfer of process Transfer at line 12 col 11 changed to Transfer_
VARIABLES alice_account, bob_account, account_total, pc, money

vars == << alice_account, bob_account, account_total, pc, money >>

ProcSet == (1..2)

Init == (* Global variables *)
        /\ alice_account = 10
        /\ bob_account = 10
        /\ account_total = alice_account + bob_account
        (* Process Transfer *)
        /\ money \in [1..2 -> 1..20]
        /\ pc = [self \in ProcSet |-> "Transfer_"]

Transfer_(self) == /\ pc[self] = "Transfer_"
                   /\ IF alice_account >= money[self]
                         THEN /\ pc' = [pc EXCEPT ![self] = "A"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "C"]
                   /\ UNCHANGED << alice_account, bob_account, account_total, 
                                   money >>

A(self) == /\ pc[self] = "A"
           /\ alice_account' = alice_account - money[self]
           /\ bob_account' = bob_account + money[self]
           /\ pc' = [pc EXCEPT ![self] = "C"]
           /\ UNCHANGED << account_total, money >>

C(self) == /\ pc[self] = "C"
           /\ Assert(alice_account >= 0, 
                     "Failure of assertion at line 16, column 4.")
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ UNCHANGED << alice_account, bob_account, account_total, money >>

Transfer(self) == Transfer_(self) \/ A(self) \/ C(self)

Next == (\E self \in 1..2: Transfer(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

MoneyInvariant == alice_account + bob_account = account_total

=============================================================================
\* Modification History
\* Last modified Mon Oct 16 16:08:48 CST 2017 by tangliu
\* Created Mon Oct 16 15:39:36 CST 2017 by tangliu
