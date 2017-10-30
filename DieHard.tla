------------------------------ MODULE DieHard ------------------------------

EXTENDS Integers

VARIABLES big, small

Init == 
    /\ big = 0
    /\ small = 0
       
        
FillSmall == 
    /\ small' = 3
    /\ big' = big

FillBig == 
    /\ big' = 3
    /\ small' = small

EmptySmall == 
    /\ small' = 0
    /\ big' = big

EmptyBig == 
    /\ big' = 0
    /\ small' = small

\*SmallToBig == \/ /\ small + big > 5
\*                 /\ big' = 5
\*                 /\ small' = small - (5 - big)
\*              \/ /\ small + big <= 5
\*                 /\ big' = big + small
\*                 /\ small' = 0
\*
\*BigToSmall == \/ /\ small + big > 3
\*                 /\ small' = 3
\*                 /\ big' = big - (3 - small)
\*              \/ /\ small + big <= 3
\*                 /\ big' = 0
\*                 /\ small' = small + big

Min(m, n) == IF m < n THEN m ELSE n

\*SmallToBig == /\ big' = Min(big + small, 5)
\*              /\ small' = small - (big' - big)
\*              
\*BigToSmall == /\ small' = Min(big + small, 3)
\*              /\ big' = big - (small' - small)

SmallToBig == 
LET poured == Min(big + small, 5) - big
IN 
    /\ big' = big + poured
    /\ small' = small - poured
   
BigToSmall == 
LET poured == Min(big + small, 3) - small
IN 
    /\ big' = big - poured
    /\ small' = small + poured
   
   

Next == 
    \/ FillSmall
    \/ FillBig
    \/ EmptySmall
    \/ EmptyBig
    \/ SmallToBig
    \/ BigToSmall
                      
TypeOK == 
    /\ big \in 0..5
    /\ small \in 0..3
          
NotSolved == big /= 4

=============================================================================
\* Modification History
\* Last modified Mon Oct 30 13:59:54 CST 2017 by tangliu
\* Created Mon Oct 23 13:21:58 CST 2017 by tangliu
