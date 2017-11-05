----------------------------- MODULE Percolator -----------------------------

EXTENDS Integers, Sequences, Bags, TLC

\* The set of transaction keys 
CONSTANTS KEY

\* The set of client to execute a transaction
CONSTANTS CLIENT

\* ts is the timestamp for transaction. It is increased monotonically so
\* every transaction must have a unique start and commit ts.
VARIABLES ts

\* $clientState[c] is the state of client
VARIABLES clientState

\* $clientTS[c] is a record of [start: ts, commit: ts]
VARIABLES clientTS

\* $clientKeys[c] is a record of [primary: key, second: {key}]
VARIABLES clientKey

\* $keyLock[k] is the lock of key. It is a record of a start ts and a primary key.
\* If the primary key is not an empty set, the lock is a secondary key lock, otherwise, it is 
\* a primary key lock.
VARIABLES keyLock

\* $keyWrite[k] is a sequence of committed version of the key.
VARIABLES keyWrite

\* $keyData[k] is the set of multi-version data timestamp of the key. 
VARIABLES keyData

keyVars == <<keyLock, keyWrite, keyData>>

EmptyLock ==[start |-> 0, primary |-> ""]

Init == 
    /\ ts = 0
    /\ clientState = [c \in CLIENT |-> "init"]
    /\ clientTS = [c \in CLIENT |-> [start |-> 0, commit |-> 0]]
    /\ clientKey = [c \in CLIENT |-> [primary |-> "", second |-> {}]]
    /\ keyLock = [k \in KEY |-> EmptyLock]
    /\ keyWrite = [k \in KEY |-> <<>>]
    /\ keyData = [k \in KEY |-> {}]
    
TypeOK ==
    /\ ts \in Nat
    /\ clientState \in [CLIENT -> {"init", "working", "prewriting", "committing", "aborted", "committed"}]
    
\* Selects a primary key from KEY, and use others as the secondary keys.
GenKey ==     
    LET
        \* TODO: How to select a primary key randomly?
        primary == CHOOSE k \in KEY: TRUE
    IN
        [primary |-> primary, second |-> KEY \ {primary}]

\* Starts a transaction in one client.
Start(c) == 
    /\ clientState[c] = "init"
    /\ clientState' = [clientState EXCEPT ![c] = "working"]
    /\ ts' = ts + 1
    /\ clientTS' = [clientTS EXCEPT ![c] = [start |-> ts', commit |-> 0]]
    /\ clientKey' = [clientKey EXCEPT ![c] = GenKey]
    /\ UNCHANGED<<keyVars>>   
    
\* Find write with start ts.
FindWriteWithStart(k, t) ==
    LET select(w) == w.start = t
    IN  SelectSeq(keyWrite[k], select)            
        

\* Returns TRUE when any key is not locked.
CanPrewrite(c) == 
    LET
        primary == clientKey[c].primary
        second == clientKey[c].second
    IN
        /\ keyLock[primary] = EmptyLock
        /\ \A k \in second : 
            /\ keyLock[k] = EmptyLock        
                        
\* Returns TRUE if the client can clean up the lock
CanCleanupLock(startTS, k) == 
    /\ keyLock[k] /= EmptyLock
    /\ keyLock[k].start < startTS \* Can clean up any previous lock  
    /\ \/ keyLock[k].primary = ""
       \* If the primary key of the second lock key is empty, 
       \* we can clean up the second lock key
       \/ keyLock[keyLock[k].primary] = EmptyLock

CanCleanup(c) ==
    LET
        startTS == clientTS[c].start 
        primary == clientKey[c].primary
        second == clientKey[c].second  
    IN
        /\ CanCleanupLock(startTS, primary)
        /\ \A k \in second :
            /\ CanCleanupLock(startTS, k)

\* Returns the information which we need to clean up the lock.
GetCleanupInfo(oldLock, k, c) ==
    LET
        startTS == clientTS[c].start 
        primary == clientKey[c].primary
        second == clientKey[c].second  
    IN
    IF
        /\ k = primary \/ k \in second 
        /\ oldLock.start /= 0
        /\ oldLock.start < startTS \* Can clean up any previous lock  
    THEN
        IF oldLock.primary /= "" 
        THEN 
            \* The lock is a primary key lock.
            <<EmptyLock>>
        ELSE
            LET 
                lockTS == oldLock.start
                w == FindWriteWithStart(oldLock.primary, lockTS)
            IN
                \* If the associated primary lock is clean up, we must find the write for the primary key
                \* and then append to the write of the second key
                IF keyLock[oldLock.primary].start = 0 
                THEN
                    <<EmptyLock, w[1]>>
                ELSE <<>>        
    ELSE
        <<>>
        
CleanupLock(oldLock, k, infos) ==
    IF infos[k] /= <<>>
    THEN
        infos[k][1]
    ELSE
        oldLock
        
CleanupWrite(oldWrite, k, infos) ==
    IF Len(infos[k]) = 2
    THEN
        Append(oldWrite, infos[k][2])
    ELSE
        oldWrite
                
Cleanup(c) ==
    LET
        infos == [k \in DOMAIN keyLock |-> GetCleanupInfo(keyLock[k], k, c)]
    IN
    /\ keyLock' = [k \in DOMAIN keyLock |-> CleanupLock(keyLock[k], k, infos)]
    /\ keyWrite' = [k \in DOMAIN keyWrite |-> CleanupWrite(keyWrite[k], k, infos)]
    
              
\* Get checks whether the key is already locked, if the key is locked, 
\* The transaction will abort or try to clean up the lock then restart.        
Get(c) ==
    /\ clientState[c] = "working"
    /\ 
        IF CanPrewrite(c)    
        THEN
            /\ clientState' = [clientState EXCEPT ![c] = "prewriting"]
            /\ UNCHANGED <<keyWrite, keyLock>>
        ELSE             
            IF CanCleanup(c)
            THEN
                \* If we clean up any old lock, we can retry running next time
                 /\ Cleanup(c)
                 /\ UNCHANGED <<ts, clientState>>
            ELSE  
                /\ clientState' = [clientState EXCEPT ![c] = "aborted"]
                /\ UNCHANGED <<ts, keyWrite, keyLock>>
    /\ UNCHANGED <<ts, keyData, clientTS, clientKey>>
    
CanLockKey(c, k, primary) ==    
    LET
        startTS == clientTS[c].start
        writes == {w \in DOMAIN keyWrite[k] : keyWrite[k][w].commit >= startTS}
    IN
        \* No any transaction locks the key
        /\ keyLock[k] = EmptyLock 
        \* No any newer write
        /\ writes = {} 
       
\* CanLock returns whether the transaction can lock all keys    
CanLock(c) ==
    LET
        primary == clientKey[c].primary
        second == clientKey[c].second  
    IN
        /\ CanLockKey(c, primary, "")
        /\ \A k \in second :
           /\ CanLockKey(c, k, primary)

LockKey(oldLock, k, c) ==
    LET
        primary == clientKey[c].primary
        second == clientKey[c].second  
        startTS == clientTS[c].start
    IN
        IF k = primary 
        THEN
            [start |-> startTS, primary |-> ""]
        ELSE
            IF k \in second 
            THEN
                [start |-> startTS, primary |-> primary]
            ELSE
                oldLock
    
CommitData(data, k, c) ==
    LET
        primary == clientKey[c].primary
        second == clientKey[c].second  
        startTS == clientTS[c].start
    IN
        IF k = primary \/ k \in second 
        THEN
            data \UNION {startTS}
        ELSE
            data
            

Lock(c) == 
    /\ keyLock' = [k \in DOMAIN keyLock |-> LockKey(keyLock[k], k, c)]
    /\ keyData' = [k \in DOMAIN keyData |-> CommitData(keyData[k], k, c)]

Prewrite(c) ==
    /\ clientState[c] = "prewriting"
    /\ 
        IF CanLock(c)
        THEN
            /\ Lock(c)
            /\ ts' = ts + 1
            /\ clientTS' = [clientTS EXCEPT ![c] = [@ EXCEPT !.commit = ts']]
            /\ clientState' = [clientState EXCEPT ![c] = "committing"]
        ELSE           
            /\ clientState' = [clientState EXCEPT ![c] = "aborted"]
            /\ UNCHANGED <<ts, clientTS, clientKey, keyLock, keyData>>
    /\ UNCHANGED<<keyWrite, clientKey>>

CommitPrimary(c) ==
    LET 
        startTS == clientTS[c].start
        commitTS == clientTS[c].commit    
        primary == clientKey[c].primary
        w == [start |-> startTS, commit |-> commitTS]
    IN
        /\ keyLock[primary].start = startTS 
        /\ keyWrite' = [keyWrite EXCEPT ![primary] = Append(@, w)]
        /\ keyLock' = [keyLock EXCEPT ![primary] = EmptyLock]

Commit(c) == 
    /\ clientState[c] = "committing"
    /\ 
        LET
            startTS == clientTS[c].start
            commitTS == clientTS[c].commit    
            primary == clientKey[c].primary
            w == [start |-> startTS, commit |-> commitTS]
        IN
            IF 
                keyLock[primary].start = startTS
            THEN
                /\ keyWrite' = [keyWrite EXCEPT ![primary] = Append(@, w)]
                /\ keyLock' = [keyLock EXCEPT ![primary] = [start |-> 0, primary |-> ""]]
                /\ clientState' = [clientState EXCEPT ![c] = "committed"]
                \* If we commit primary successfully, we can think the transaction is committed
                \* TODO: use async message to commit second keys
            ELSE
                /\ clientState' = [clientState EXCEPT ![c] = "aborted"]
                /\ UNCHANGED<<keyLock, keyWrite>>
    /\ UNCHANGED<<ts, keyData, clientTS, clientKey>>
            
            
Next == 
    \E c \in CLIENT : 
        Start(c) \/ Get(c) \/ Prewrite(c) \/ Commit(c)

CheckWriteOrder(w1, w2) ==
    /\ w1.commit < w2.commit
    /\ w1.start < w2.start
    /\ w1.start < w1.commit

\* The committed ts of the key must be in order.
WriteConsistency ==
    \A k \in KEY :
        IF Len(keyWrite[k]) > 1 
        THEN
            LET
                newWrite == [n \in 1..Len(keyWrite[k]) - 1 |-> CheckWriteOrder(keyWrite[k][n], keyWrite[k][n + 1])]
            IN
                ~ FALSE \in newWrite
        ELSE
            IF Len(keyWrite[k]) = 1 
            THEN
                keyWrite[k][1].start < keyWrite[k][1].commit
            ELSE
                TRUE    

\* Find write with commit ts.
FindWriteWithCommit(k, t) ==
    LET select(w) == w.commit = t
    IN  SelectSeq(keyWrite[k], select)            
             
CommittedConsistency == 
    \A c \in CLIENT :
    LET 
        startTS == clientTS[c].start
        commitTS == clientTS[c].commit
        primary == clientKey[c].primary
        second == clientKey[c].second
        w == [start |-> startTS, commit |-> commitTS]
    IN  
        \/ /\ clientState[c] = "committed"
           \* The primary key lock must be empty or locked by a newer transaction.
           /\ \/ keyLock[primary] = EmptyLock 
              \/ keyLock[primary].start > commitTS
           /\ FindWriteWithCommit(primary, commitTS) = <<w>>
           /\ {startTS} \in keyData[primary]
           /\ \A k \in second :
              \* The second key lock can be empty or not.
              /\ \/ /\ keyLock[k] = EmptyLock
                    /\ FindWriteWithCommit(k, commitTS) = <<w>>
                 \/ keyLock[k].start = startTS
                    /\ FindWriteWithCommit(k, commitTS) = <<>>
                    /\ 
                        IF Len(keyWrite[k]) > 0 
                        THEN
                            keyWrite[k][Len(keyWrite[k])].commit < startTS
                        ELSE
                            TRUE
              /\ {startTS} \in keyData[k]
        \/ TRUE
        
=============================================================================
\* Modification History
\* Last modified Sun Nov 05 21:26:26 CST 2017 by tangliu
\* Created Sat Nov 04 09:40:10 CST 2017 by tangliu
