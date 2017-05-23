-------------------- MODULE textbookSnapshotIsolation -------------------

(* A TLA+ specification of textbook snapshot isolation, as described in section 4.2 of 

       "A Critique of ANSI SQL Isolation Levels"  
       http://research.microsoft.com/apps/pubs/default.aspx?id=69541

   This version includes the use of exclusive locks to implement 
   the 'First Committer Wins' rule (actually the 'First Updater Wins' rule)
   
   This specification includes various correctness properties, which can be 
   checked by the TLC model checker for all possible sequences of operations 
   by a small number of transactions (e.g. 3 or 4) over a small number of 
   keys (e.g. 2 or 3)
   
   We include a test for serializability, which TLC can use to show that 
   textbook snapshot isolation is NOT serializable, as it allows anomalies 
   such as write-skew.
   
   Instructions for testing the specification are below.  

   We also show how to use TLC to find 'interesting executions' of the algorithm,
   e.g. the one described in:

       "A Read-Only Transaction Anomaly Under Snapshot Isolation" 
       http://www.cs.umb.edu/~poneil/ROAnom.pdf
 *)

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS TxnId, Key
NoLock == CHOOSE x : x \notin (Key \union TxnId)         

(* To check properties of this specification via the TLA toolbox:

 1. In the "TLC Model Checker" menu, create new model
    to specify the values of the "CONSTANTS" defined above.
    See instructions below. 
    
 2. Run TLC, with same number of threads as you have cores.

Configuring the TLC Model Checker    (release v1.4.0 or later)

  "Model Overview" ... "What is the model?" 
  
    Key   <-   {K1,K2}            
        Click 'Set of model values'
        Click 'Symmetry set'         ... click 'Next'
        Click 'Leave untyped'        ... click 'Finish'
        
    TxnId <-   {T1,T2,T3,T4}
        As above, click 'Set of model values', 'Symmetry set', and 'Leave untyped'.
         
  "Model Overview" ... "What is the behavior spec?" ... 
  
    Spec
    
  "How to run TLC"
  
    Maximum JVM heap size in MB:    I tested with 1500, but smaller may be fine
    Number of worker threads:       Use the number of cpu cores on your machine
           
  "Model Overview" ... "What to check?"
  
    - Ensure that the "Deadlock" box is checked
    
    - For "Invariants",  add one or more of the following:  
      
      Should NEVER be violated
    
          Check basic model correctness:
          
            TypeInv
            WellFormedTransactionsInHistory(history)
            CorrectnessOfHoldingXLocks
            CorrectnessOfWaitingForXLock
            
          Check the semantics of Snapshot Isolation are met:
          
            CorrectReadView
            FirstCommitterWins
            
          Check that Cahill's formulation of the serializability condition (and our encoding of it in TLA+) 
          is equivalent to our encoding of Bernstein's formulation of the same condition, 
          in all reachable states.  
          This should be true even for states that are not serializable.  I.e. if one check returns false, 
          then the other should also.
                 
            CahillSerializable(history) = BernsteinSerializable(history)

      EXPECTED to be violated:
      
          We know that Snapshot Isolation is not serializable.          
     
            CahillSerializable(history)

          We can use TLC to find "interesting execution histories".
          This helps increase confidence that the specification allows all 
          the behaviors that we want it to allow -- i.e. is not unintentionally over-constrained.
          To do so, we check an invariant of the form "the interesting condition is NOT true".
          TLC will therefore report an invariant-violation for the first state 
          it finds in which the interesting condition is true.
          Examples:   

            ~ (AtLeastNTxnsHaveCommitted(3) /\ AtLeastNTxnsHaveRead(2) /\ AtLeastNTxnsHaveWritten(2))
            ~ AtLeastNTxnsAreWaitingForLocks(2) 
            ~ AtLeastNTxnsAbortedDueToReason(1, "forced by First Committer Wins")
            ~ AtLeastNTxnsAbortedDueToReason(1, "forced by deadlock-prevention")
 *)

VARIABLES  history,            (* Global linear history of all transaction operations *) 
           holdingXLocks,      (* Abstraction of a lock-manager *)
           waitingForXLock

allvars == <<history, holdingXLocks, waitingForXLock>>

(* 
 * Types of variables (the sets of allowed values)
 *)

(*
 * Elements in the global history of transaction operations.
 * We maintain the familiar linear "operation history" in a form easily readable by humans.
 * Also, our formulation of correctness properties examines this history.
 * Finally, we use this history to abstract-away some uninteresting details of the 
 * algorithm for snapshot isolation (see later). 
 *)
 
AbortReasons   == {"voluntary",   (* the 'reason' for an abort is only used for debugging the spec in TLC *) 
                   "forced by First Committer Wins", 
                   "forced by deadlock-prevention"}

BeginEventsT   == [op : {"begin"},  txnid : TxnId] 
AbortEventsT   == [op : {"abort"},  txnid : TxnId, reason : AbortReasons] 
CommitEventsT  == [op : {"commit"}, txnid : TxnId] 
ReadEventsT    == [op : {"read"},   txnid : TxnId, key : Key, ver : TxnId]
WriteEventsT   == [op : {"write"},  txnid : TxnId, key : Key]
EventsT        == BeginEventsT \union ReadEventsT \union WriteEventsT \union CommitEventsT \union AbortEventsT 

(* TLA+ is not statically typed.  
   It's wise to define a 'type invariant', and have TLC check it. 
 *)
TypeInv ==  /\ history         \in Seq(EventsT)
               (* A transaction may hold indepedent exclusive locks on any number of keys *)
            /\ holdingXLocks   \in [TxnId -> SUBSET Key]
               (* A transaction can be waiting for at most one exclusive lock *) 
            /\ waitingForXLock \in [TxnId -> Key \union {NoLock}]


(* Generic TLA+ utilities 
 *)
Range(f) == {f[x] : x \in DOMAIN f}


(* Utilities on for history of operations.  
   These take the history as a parameter (rather than working on the current global history),
   so we can use them to examine prefixes or filtered views of the global history.

   A note on the abstraction-level of this specification:
   An implementation of snapshot isolation needs to keep track of various metadata 
   about transactions, e.g. to decide which version of a key should be 
   read by a transaction, and whether a transaction must 
   be aborted due to the First Committer Wins rule, etc.
   For the purposes of this specification we are not interested in the details of 
   those mechanisms, so we choose to abstract them heavily.  We achieve the abstraction 
   by allowing transactions to directly examine the global history of events.
   (It it is possible that a real implementation could do the same, although that 
   is unlikely to be an efficient solution in practice.)
   The abstraction is done via the following operators: 
      
        - CommittedTxns, AbortedTxns and therefore FinalizedTxns
        - KeysThatTxnHasDoneOperationOn
        - VersionThatWouldBeReadBy   (uses CommittedWriteHistoryOfKey)
        - WritersCommittedToKeySinceTxnBegan
        - VersionIDsOfKeyNewerThanReadByTxn
   
   There is one mechanism that cannot be abstracted by the conventional type of global linear operation history 
   -- we need state to record when a transaction is blocked waiting for a lock to be released.
   We therefore introduce the 'waitingForXLock' variable to model that mechanism.
    
   To demonstrate that the level of abstraction is a free choice, we choose to 
   also introduce a variable 'holdingXLocks', to model which exclusive locks are currently held by each transaction.
   i.e. The combination of 'waitingForXLock' and 'holdingXLocks' (plus the code that detects and prevents deadlocks) 
   gives an abstract representation of a lock manager.
   However, the variable 'holdingXLocks' is not actually necessary, as the same information can 
   be obtained by examining the global operation history to see which keys a transaction has written to.
   An earlier version of this specification did exactly that.
   The correctness predicate 'CorrectnessOfHoldingXLocks' checks that in every state, 
   holdingXLocks is consistent with the global operation history.   
 *) 


(* We model an execution history as a TLA finite-length Sequence of events.
   A TLA Sequence is a function [1..N |-> element].
   As our events don't store a unique timestamp or serial number, converting a history 
   to a set of events would lose track of events that differ only by position 
   in history -- e.g. multiple reads or writes of a particular key by the same transaction. 
   For simplicitly, Phil Bernstein's book chooses to forbid such operations, and we do the same
   (via enabling conditions on actions in the model). 
   So it is actually safe to select (into a set) events which meet some criteria.
 *)
SelectEvents(h, Test(_)) == {e \in Range(h): Test(e)}

(* Operators that classify transactions, as of the 'end' of a given global operation history. 

   Currently we just deduce the classification of a transaction from the global history of operations.
   A real implementation would obviously have internal state for this. 
*)
ActiveOrFinalizedTxns(h) == {e.txnid : e \in Range(h)}        (* all transactions apart from those that have not yet started *)
NotYetStartedTxns(h)     == TxnId \ ActiveOrFinalizedTxns(h)
CommittedTxns(h)         == {e.txnid : e \in SelectEvents(h, LAMBDA e : e.op \in {"commit"})}
AbortedTxns(h)           == {e.txnid : e \in SelectEvents(h, LAMBDA e : e.op \in {"abort"})}
FinalizedTxns(h)         == CommittedTxns(h) \union AbortedTxns(h)
ActiveTxns(h)            == ActiveOrFinalizedTxns(h) \ FinalizedTxns(h)

(* We define the 'start time' of a transation as the position (index) 
   of its operation in the specified history.
   Obviously it is not valid to compare 'start times' that were obtained from 
   different histories (e.g. different filtered views of the global history). 
   We mostly use this for finding the end of an interesting prefix of the global history. 
 *)
StartTime(h, txn) == CHOOSE pos \in 1 .. Len(h) : h[pos] = [op |-> "begin", txnid |-> txn]

KeysThatTxnHasDoneOperationOn(h, txn, operation) == 
    LET txn_ops == SelectEvents(h, LAMBDA e : e.txnid = txn  /\  e.op = operation) 
    IN {e.key : e \in txn_ops}

(* The sequence of committed operations in h. i.e. All operations by aborted or non-finalized transactions are removed *)
CommittedWriteHistoryOfKey(h, key) ==
    SelectSeq(h,
              LAMBDA e : /\ e.op = "write" 
                         /\ e.key = key
                         /\ e.txnid \in CommittedTxns(h))

(* The set of transactions that txn has read from in history h *)
TxnsReadFrom(h, txn) == {op.ver : op \in Range(SelectSeq(h, 
                                                         LAMBDA e : /\ e.op = "read" 
                                                                    /\ e.txnid = txn))}
(* Returns a set of of <<Key, Ver>> *) 
KeyVersionsReadByTxn(h, txn) ==
    {<<op.key, op.ver>> : op \in Range(SelectSeq(h, 
                                                 LAMBDA e : /\ e.op = "read" 
                                                            /\ e.txnid = txn))}

(* Returns -1 if op is not in history.  Otherwise returns an integer in 1..Len(h) *)
IndexOfOpInHistory(h, op) == 
    IF op \in Range(h) THEN CHOOSE i \in 1..Len(h) : h[i] = op
                       ELSE -1


(* 
 * Helpers for actions; these are hard-wired to use the spec variables 
 * current database history, holdingXLocks, and waitingForXlock.
 * i.e. They don't work on prefixes of the database history.  
 *)

KeysCurrentlyXLockedByActiveTxn(txn) == holdingXLocks[txn]

KeysCurrentlyXLockedByAnyTxn == UNION Range(holdingXLocks) 

StartedAndCanDoPublicOperation(txn) ==
       (* Started and not yet finalized *)
    /\ txn \in ActiveTxns(history)
       (* If txn was waiting for a lock (because it is attempting to write to some key) 
          then it cannot choose to commit, abort, read or write. 
          But note that  *internal* actions may choose to forcibly abort it, or may grant 
          the lock and allow the suspended write to proceed. 
       *)
    /\ waitingForXLock[txn] = NoLock    


WritersCommittedToKeySinceTxnBegan(txn, key) ==
    (* Note: the write to key might have happened before txn started,  
       even if the writer committed after txn started. 
     *)
    LET hSinceTxnBegan == SubSeq(history, StartTime(history, txn), Len(history))
        cSinceTxnBegan == CommittedTxns(hSinceTxnBegan) 
    IN  
        {t \in cSinceTxnBegan : key \in KeysThatTxnHasDoneOperationOn(history, t, "write")}  


(* Returns a set with one version id (txn id)
   or      an empty set, if there was no committed version before txn began,
*) 
LatestCommittedVersionOfKeyWhenTxnBegan(txn, key) ==
    (* Because of the FirstCommitterWins Rule, the latest write in the 
       committed write history of the key is that latest version. 
    *)
    LET hBeforeTxnBegan == SubSeq(history, 1, StartTime(history, txn))
        cwhkbtb         == CommittedWriteHistoryOfKey(hBeforeTxnBegan, key)                       
    IN  
        (* The latest committed write is the last in the sequence. *)
        IF Len(cwhkbtb) = 0 THEN {} 
                            ELSE {cwhkbtb[Len(cwhkbtb)].txnid}
    
(* Evaluates to a set containing one TxnId, or an empty set if there 
   are no versions of key that can be read by txn 
 *) 
VersionThatWouldBeReadBy(txn, key) ==
    IF key \in KeysCurrentlyXLockedByActiveTxn(txn) THEN
        (* txn reads the (uncommitted) version that it wrote itself.
           Note: There can be only one such committed version, as this spec
           artificially constrains transactions to do at most one write of  
           a particular key - i.e. Bernstein's standard simplification. 
        *) 
        {txn}         
    ELSE  
        (* Txn reads the version that was written by the latest transaction 
           to commit before txn began. 
        *)
        LatestCommittedVersionOfKeyWhenTxnBegan(txn, key)
    


(*
 * Public actions.  This is the public interface of the system.  
 *)

Begin(txn) == 
    /\ txn \notin ActiveOrFinalizedTxns(history)
    /\ history' = Append(history, [op |-> "begin", txnid |-> txn]) 
    /\ UNCHANGED <<holdingXLocks, waitingForXLock>>


Commit(txn) == 
    /\ StartedAndCanDoPublicOperation(txn)
    (* Txn is the winner of FirstCommiterWins rule for any writes it is doing.
       So if there are other transactions that are currently waiting for any xlock 
       that is held by txn, then we must abort those transactions.
     *)
    /\ LET  XLocksHeldByCommittingTxn == 
                KeysCurrentlyXLockedByActiveTxn(txn)
                 
            LoserTxns == 
                {blockedTxn \in TxnId : waitingForXLock[blockedTxn] \in XLocksHeldByCommittingTxn}
                 
            AbortOpSeq(Txns) ==
                LET RECURSIVE BuildAbortOpSeq(_)
                    BuildAbortOpSeq(RemainingTxns) == 
                        IF RemainingTxns = {} THEN 
                            <<>>  
                        ELSE 
                            LET t == CHOOSE t \in RemainingTxns : TRUE
                            IN     <<[op |-> "abort", txnid |-> t, reason |-> "forced by First Committer Wins"]>> 
                                \o BuildAbortOpSeq(RemainingTxns \ {t})
                IN  
                    BuildAbortOpSeq(Txns)
       IN   
          /\ history' = Append(history, [op |-> "commit", txnid |-> txn]) \o AbortOpSeq(LoserTxns)
          /\ holdingXLocks'   = [t \in TxnId |-> IF t \in {txn} \union LoserTxns 
                                                 THEN {}              (* drop locks held by transactions that have just committed or aborted *)
                                                 ELSE holdingXLocks[t]]
          /\ waitingForXLock' = [t \in TxnId |-> IF t \in LoserTxns 
                                                 THEN NoLock          (* aborted transactions cannot now be waiting for a lock *) 
                                                 ELSE waitingForXLock[t]]

    
ChooseToAbort(txn) == 
    /\ StartedAndCanDoPublicOperation(txn)
    /\ history'       = Append(history, [op |-> "abort", txnid |-> txn, reason |-> "voluntary"])
    /\ holdingXLocks' = [holdingXLocks EXCEPT ![txn] = {}]  (* drop any locks held by the txn that is aborting *)
    /\ UNCHANGED <<waitingForXLock>>  (* txn can't be waiting for any locks, because StartedAndCanDoPublicOperation(txn) is true *)  
                     

Read(txn, key) == 
    /\ StartedAndCanDoPublicOperation(txn)
    /\ key \notin KeysThatTxnHasDoneOperationOn(history, txn, "read")   (* Bernstein's simplification: no txn reads the same key more than once *)
    /\ LET readVerSet == VersionThatWouldBeReadBy(txn, key) 
       IN
         /\ readVerSet /= {} (* still part of the 'enabling condition' for this action
                                -- we can only read if there is a version of this key that can be read, 
                                   i.e. we don't model attempts to read keys that have not yet been created. 
                              *)
        /\ history' = Append(history, [op |-> "read", txnid |-> txn, 
                                       key |-> key, ver |-> CHOOSE ver \in readVerSet : TRUE])
        /\ UNCHANGED <<holdingXLocks, waitingForXLock>>


(* The Write action requires some helpers, and TLA+ requires that operators are declared before use,
 * so helpers come first.
 *) 

HelperWriteCanAcquireXLock(txn, key) ==
    /\ history'         = Append(history, [op |-> "write", txnid |-> txn, key |-> key])
    /\ holdingXLocks'   = [holdingXLocks EXCEPT ![txn] = @ \union {key}]  (* txn acquires lock on key *)
    /\ waitingForXLock' = [waitingForXLock EXCEPT ![txn] = NoLock]


HelperWriteConflictsWithXLock(txn, key) ==
    (* Some other transaction is holding the xlock on this key
       (In the current model txn itself cannot be holding the xlock 
       as the current model doesn't allow a transaction to write to the 
       same key twice.)
       To write to this key, we must acquire the xlock.
       But if waiting for the xlock would cause a deadlock
       then we must abort one of the transactions involved in the cycle. 
       If we choose to abort a transaction other than txn itself, 
       then txn can start waiting for the lock it wants. 
     *)
    LET activeTxns == ActiveTxns(history)

        xlockIsHeldBy == 
            [k \in Key |->
                LET holder == {t \in activeTxns : k \in KeysCurrentlyXLockedByActiveTxn(t)}
                IN  IF holder /= {} THEN CHOOSE t \in holder : TRUE
                                    ELSE NoLock]

        proposedWaitingForXLock == [waitingForXLock EXCEPT ![txn] = key] 

        newWaitingForXLockHeldByEdges == 
            {<<from, to>> \in activeTxns \X activeTxns :
                \E k \in Key :  /\ proposedWaitingForXLock[from] = k
                                /\ xlockIsHeldBy[k]              = to}

        pathThatCyclesFromTxnToTxn ==
            (* We do eager deadlock-prevention, so we simply forbid the the creation 
               of any cycle in the actual (accepted) waiting-for-locks graph. 
               Therefore the only possible cycle in the *proposed* waiting-for-locks  
               graph would be created by the sole new edge; i.e. txn wanting to acquire   
               the xlock for key.  Therefore the only possible cycle begins with txn   
               and loops back through txn.  So we only consider txn as the start point  
               of the search, and we don't have to worry about cycles between 
               groups of nodes that don't include txn.
               
               Also, there can be at most one cycle. If there were more than one cycle 
               then some node (inc. txn) must have more than one outgoing edge. But it is impossible for any 
               node to have more than one outgoing edge, as outgoing edges can only be caused by a transaction  
               waiting for an Xlock.  A transaction can only be waiting for at most one lock 
               at any point in time (and any particular XLock can only be held by at most one other transaction).
               Therefore there is at most one outgoing edge from each transaction.
               So we only need to look for any one cycle; i.e. we don't need to find the set of all cycles.
               So we don't need to do backtracking; if we hit a dead-end then we are done.  
               Note: We can't use the generic Graphs module in 'Specifying Systems' as 
               TLC can't enumerate the infinite set-comprehension in the definition of Path(G).
               
               TODO: could just use FindAllNodesInAnyCycle(_) for this (it's defined later). 
             *)
            LET RECURSIVE extendPath(_)
                (* Returns a set of Seq(TxnId) with at most one member.  
                   Any member will begin with txn and end with a different transaction 
                   that would loop back to txn if we continued to follow the cycle. 
                 *)  
                extendPath(currPath) ==
                    LET from == currPath[Len(currPath)]
                        outgoingEdges == {<<e_from, e_to>> \in newWaitingForXLockHeldByEdges : e_from = from} 
                    IN  IF outgoingEdges = {} 
                        THEN {}             (* Done: the first dead-end we hit implies there is no cycle. *)
                        ELSE LET edge == CHOOSE <<e_from, e_to>> \in outgoingEdges : TRUE 
                             IN  IF edge[2] = txn THEN {currPath}  (* Done: This path does loop back to txn. *) 
                                                  ELSE extendPath(Append(currPath, edge[2]))
            IN extendPath(<<txn>>)
    IN
        IF pathThatCyclesFromTxnToTxn = {} THEN
              (* Here, txn won't cause a deadlock when it starts waiting for k's xlock, 
                 so it starts waiting without further ado.
               *)
            /\ waitingForXLock' = [waitingForXLock EXCEPT ![txn] = key] 
            /\ UNCHANGED <<history, holdingXLocks>>
        ELSE
            (* If txn starts waiting for xlock for k, then it will cause a deadlock.
               Pick a transaction to abort, that will prevent the potential cycle in the graph.  
               We make this a non-deterministic choice from all transactions involved in the 
               potential cycle, so we model-check all possible choices.  
               i.e. We don't enshrine a particular abort policy (e.g. minimum write locks).
             *)
            \E to_abort \in Range(CHOOSE anyPathSeq \in pathThatCyclesFromTxnToTxn : TRUE) :
                /\ history' = Append(history, [op |-> "abort", txnid |-> to_abort, reason |-> "forced by deadlock-prevention"])
                /\ IF to_abort = txn THEN
                    (* We've decided to avoid deadlock by aborting the current transation.
                     *)
                    /\ holdingXLocks' = [holdingXLocks EXCEPT ![txn] = {}]  (* drop any locks held by the txn that is aborting *)
                    /\ UNCHANGED <<waitingForXLock>>  (* txn can't be waiting for any locks, because StartedAndCanDoPublicOperation(txn) is true *)  
                   ELSE
                    (* We've decided to avoid deadlock by aboring a transaction other than txn.
                       We alter waitingForXLock so that txn starts waiting for the lock it wants, 
                       and the to_abort transaction is nolonger waiting for any locks, or holding 
                       any locks (because it's been aborted).
                       
                       Note: the abort is not guaranteed to release the xlock 
                       that txn wants.  (The abort just guarantees that when txn 
                       starts waiting for the xlock, that action won't create a cycle in the 
                       waiting-for-locks graph.)
                       
                       Also we *don't* check to see if the abort has released the 
                       xlock that txn wants (to grant the xlock immediately to txn).
                       There might be other transactions waiting for the xlock
                       and we don't want to starve them.  We want to model-check 
                       all possible combinations of acquisition. 
                     *)
                    /\ holdingXLocks'   = [holdingXLocks EXCEPT ![to_abort] = {}]       (* to_abort may have been holding locks *)
                    /\ waitingForXLock' = [waitingForXLock EXCEPT ![txn]      = key, 
                                                                  ![to_abort] = NoLock] (* to_abort may have been waiting for a lock *)


StartWriteMayBlock(txn, key) == 
    /\ StartedAndCanDoPublicOperation(txn)
    /\ key \notin KeysCurrentlyXLockedByActiveTxn(txn)  (* Bernstein's simplification *)
    (* Part of First Commiter Wins rule: if txn attempts to write to a key that has 
       been modified and committed since txn began, then txn cannot possibly 
       commit, so we might as well abort txn now.
       Alternative: we could just fail the individual write, and allow the transaction
       to proceed.  We could model that by including the FCW check in the 
       enabling-condition, so that Alloy doesn't even attempt to generate behaviors 
       that attempt to violate the FCW rule in that way.   
       I choose to not do that, as we would not be modelling the application's choice 
       of how to handle the failed write.  In the vast majority of cases the transaction 
       won't have any realistic alternative than abort, so we simply model the abort.
     *)
    /\ IF WritersCommittedToKeySinceTxnBegan(txn, key) /= {} THEN
        (* Abort txn because it lost the First Updater Wins rule. *)
        /\ history'       = Append(history, [op |-> "abort", txnid |-> txn, reason |-> "forced by First Committer Wins"])
        /\ holdingXLocks' = [holdingXLocks EXCEPT ![txn] = {}]  (* txn may have been holding locks *)
        /\ UNCHANGED <<waitingForXLock>>  (* txn cannot have been waiting for a lock, as StartedAndCanDoPublicOperation(txn) is true *)  
       ELSE
        IF key \in KeysCurrentlyXLockedByAnyTxn THEN
            (* txn needs to wait for some other transaction to release the lock on key. *)
            HelperWriteConflictsWithXLock(txn, key)
        ELSE
            (* No-one is holding key's lock, so txn can lock it immediately. *)
            HelperWriteCanAcquireXLock(txn, key)

            
(* 
 * Internal actions, not part of the public interface of the system.  
 *)

(* If txn is blocked waiting for a lock on some key, 
   it may proceed when that key is nolonger locked.
   (Note: txn might be forcibly aborted while it is waiting,
   before it ever gets here.)
 *)
FinishBlockedWrite(txn) ==
    /\ waitingForXLock[txn] /= NoLock
    /\ LET key == waitingForXLock[txn] 
       IN  /\ key \notin KeysCurrentlyXLockedByAnyTxn
           /\ HelperWriteCanAcquireXLock(txn, key)

(* 
 * End of actions.
 *)


(* 
 * Constraint on possible initial states 
 *)
Init == /\ history         = <<>>
        /\ holdingXLocks   = [txn \in TxnId |-> {}] 
        /\ waitingForXLock = [txn \in TxnId |-> NoLock]


(* We legitimately terminate if all transactions have either 
   committed or aborted.  At all times when that is not the 
   case then the Next-state action should make progress.
   So for liveness we simply assert weak-fairness of Next.
   If we don't explicitly model termination like this then 
   TLC reports a 'deadlock error' for such terminations.
   (That is 'deadlock' in the TLA sense, which means that 
   ENABLED(Next) is false so the system cannot make any more 
   state transitions.  That has almost nothing to do with 
   transactional deadlock. We _do_ want to model and check,
   transactional deadlock because our algorithm has to handle it.
   If there was a bug in our algorithm for preventing/resolving 
   transaction deadlock, then that should be detected by TLC 
   as a TLA deadlock (inability for the system to make progress).
   But other kinds of algorithm bugs or modelling errors could 
   also cause TLA-type deadlock.
 *)
LegitimateTermination ==  FinalizedTxns(history) = TxnId

             
(* 
 * The Next-state action.  
 * This says that in every state, some transaction can perform one of the named actions.
 * or, we have reached the LegitimateTermination condition (all transactions have committed or aborted)
 *)
Next == \/ \E txn \in TxnId :

               (* Public actions *) 
            \/ Begin(txn)
            \/ Commit(txn)
            \/ ChooseToAbort(txn) (* as contrasted with being forced to abort by FCW rule or deadlock prevention *)
            \/ \E key \in Key : 
                \/ Read(txn, key)
                \/ StartWriteMayBlock(txn, key)
                
               (* Internal actions *)
            \/ FinishBlockedWrite(txn)
            
           (* The following disjunct allows infinite 'stuttering steps' (no change in state)
              once legitimate termination has been reached (all transactions have committed or aborted).  
              This allows TLC to distinguish between legitimate termination 
              vs. inability to make progress due to some bug in the algorithm or TLA+ code.
              An example of such a bug in the algorithm would be failure to detect 
              and prevent transaction deadlock (a cycle in the graph of waiting-for-held-locks).
              We want legitimate termination to be treated as a legal state, despite being 
              a dead-end in the graph of states that TLC is exploring.  In particular, we want 
              TLC to continue model-checking via any other other unexplored states left in its queue. 
              But inability to progress for any other reason should cause TLC to 
              halt and report an error ('deadlock') in that behavior. 
            *)
        \/ (LegitimateTermination /\ UNCHANGED allvars) 


(* The formula for the whole specification.  
   
   The assertion of weak fairness on the Next-state action says that 
   if Next is continuously enabled then infinitely many Next steps 
   occur.  i.e. The system must take another step if Next is enabled.
 *) 
Spec == Init  /\  [][Next]_allvars  /\  WF_allvars(Next)           


(*
 * Correctness properties of the algorithm, 
 * and of the specification (encoding of the algorithm in TLA+)
 *
 * Most properties are specified as being invariants (true in every reachable state).
 * In TLA+ we can write that a property is an invariant by declaring that 
 * it is a theorem that the specification formula implies that the property is always true.
 *) 
                    
THEOREM Spec => []TypeInv

(* Liveness (progress) properties are written in temporal logic. 
 * e.g. We assert that Spec implies that eventually, all transactions commit or abort.
 *)
THEOREM Spec => <>LegitimateTermination   

(* There are further correctness properties below.  I haven't bothered declaring 
 * them as theorems because we have to manually enter them into the "What to check?"
 * part of the "TLC Model Checker" configuration anyway.   Declaring them as theorems 
 * doesn't seem to affect that.
 *)


(*
 * Helpers for correctness properties
 *)
  
(* Returns an set containing all elements that participate in any cycle (i.e. union of all cycles),
           or an empty set if no cycle is found.
   TODO: this is stronger than necessary for our current use-case; 
   we only need to know if there is a cycle, not all of the nodes in all cycles. 
 *) 
FindAllNodesInAnyCycle(edges) ==

    LET RECURSIVE findCycleNodes(_, _)   (* startNode, visitedSet *)
        (* Returns a set containing all elements of some cycle starting at startNode,
           or an empty set if no cycle is found. 
         *)
        findCycleNodes(node, visitedSet) ==
            IF node \in visitedSet THEN
                {node}  (* found a cycle, which includes node *)
            ELSE
                LET newVisited == visitedSet \union {node}
                    neighbors == {to : <<from, to>> \in 
                                           {<<from, to>> \in edges : from = node}}
                IN  (* Explore neighbors *)
                    UNION {findCycleNodes(neighbor, newVisited) : neighbor \in neighbors}
                    
        startPoints == {from : <<from, to>> \in edges}  (* All nodes with an outgoing edge *)
    IN 
        UNION {findCycleNodes(node, {}) : node \in startPoints}
       
IsCycle(edges) == FindAllNodesInAnyCycle(edges) /= {}

(* It's easy to write unit tests for helper operators,
   and have TLC check them: 
      - in "What is the behavior spec?", choose "No Behavior Spec" 
      - In "Evaluate Constant Expression", enter  UnitTests_FindAllNodesInAnyCycle
   Example:  
 *)
UnitTests_FindAllNodesInAnyCycle ==
    /\ FindAllNodesInAnyCycle({})                                                       = {}
    /\ FindAllNodesInAnyCycle({<<"a", "b">>})                                           = {}
    /\ FindAllNodesInAnyCycle({<<"a", "b">>, <<"b", "c">>, <<"c", "d">>})               = {}                   (* no cycle, more nodes *)
    /\ FindAllNodesInAnyCycle({<<"a", "a">>})                                           = {"a"}                (* cycle of length 1 *)
    /\ FindAllNodesInAnyCycle({<<"a", "b">>, <<"b", "a">>})                             = {"a", "b"}           (* cycle of length 2 *)
    /\ FindAllNodesInAnyCycle({<<"a", "b">>, <<"b", "c">>, <<"c", "d">>, <<"d", "a">>}) = {"a", "b", "c", "d"} (* cycle of length 3 *)
    /\ FindAllNodesInAnyCycle({<<"a", "a">>, <<"b", "b">>})                             = {"a", "b"}           (* multiple disjoint cycles of length 1*)
    /\ FindAllNodesInAnyCycle({<<"a", "d">>, <<"d", "b">>, <<"c", "d">>, <<"d", "c">>}) = {"d", "c"}           (* cycles plus some nodes not in any cycle but which join to a cycle *)
    /\ FindAllNodesInAnyCycle({<<"a", "b">>, <<"b", "a">>, <<"c", "c">>, <<"d", "c">>}) = {"a", "b", "c"}      (* multiple disjoint cycles including length > 1 *)

(* Sidebar
   Another way to test for a cycle in a graph is by computing the transitive closure of 
   the graph (as done in the Alloy version of this spec).

   Here are a couple of different definitions of Transitive Closure that TLC can evaluate 
   fairly efficiently.  I've verified that these are equivalent for relations up to 1..5 \X 1..5 
   
        (* "If R is a relation--that is a set of ordered pairs--let its support be
            the set of all elements that appear in those pairs." 
         *)
        Support(R) == {r[1] : r \in R} \cup {r[2] : r \in R}
     
        TC_SelfJoin(R) == 
            LET S   == Support(R)
                SS  == S \X S
                RECURSIVE selfJoin(_)
                    selfJoin(r1) == 
                        LET missingJoinTuples(left,right) == 
                                {<<x, z>> \in SS : 
                                    /\ <<x, z>> \notin left
                                    /\ <<x, z>> \notin right
                                    /\ \E y \in S : <<x, y>> \in left /\ <<y, z>> \in right}
                                mjt == missingJoinTuples(r1, r1)
                             IN 
                                IF mjt = {} THEN r1   (* have reached least fixpoint, so this must be transitive closure *)
                                            ELSE LET bigger == r1 \union mjt 
                                                 IN  bigger \union selfJoin(bigger)
            IN selfJoin(R)
        
        (* This definition is based on a suggestion by Leslie Lamport *)
        TC_ExtendPath(R) ==
            LET S  == Support(R)
                SS == S \X S
                C[PathLen \in Nat] == 
                    IF PathLen = 0 THEN R
                    ELSE
                        LET TCShorterPaths == C[PathLen - 1]
                        IN {<<x, z>> \in SS :
                               \E y \in S : /\ <<x, y>> \in TCShorterPaths
                                            /\ <<y, z>> \in TCShorterPaths}
                           \union  TCShorterPaths
            IN (* Allowing paths of length Cardinality(S) + 1 allows for paths that are cycles *)
               C[Cardinality(S)]
 *)


(* Returns true iff both t1 and t2 start and their lifetimes overlap. *)
AreConcurrent(h, t1, t2) ==
    LET iT1b  == IndexOfOpInHistory(h, [op |-> "begin", txnid |-> t1])
        iT1c  == IndexOfOpInHistory(h, [op |-> "commit", txnid |-> t1])
        iT2b  == IndexOfOpInHistory(h, [op |-> "begin", txnid |-> t2])
        iT2c  == IndexOfOpInHistory(h, [op |-> "commit", txnid |-> t2])
    IN
        /\  iT1b /= -1              (* t1 started *)
        /\  iT1b /= -1              (* t2 started *)
        /\  IF iT1b < iT2b THEN
                \/  iT1c = -1       (* t1 never finished *)
                \/  iT1c > iT2b     (* or t1 finished after t2 started *)
            ELSE 
                \/  iT2c = -1       (* t2 never finished *)
                \/  iT2c > iT1b     (* or t2 finished after t2 started *)
    

(*
 * Correctness properties
 *)

WellFormedTransactionsInHistory(h) ==

    /\ h \in Seq(EventsT)    (* The relevant part of TypeInv *)
    /\ \A txn \in TxnId :
        LET th == SelectSeq(h, LAMBDA e : e.txnid = txn)  (* just the history for this transaction *) 
        IN    
              (* If a txn has any operations, the first, and only the first, must be begin.
               *)
           /\ LET idxsB == {i \in 1..Len(th) : th[i] = [op |-> "begin", txnid |-> txn]}
              IN IF Len(th) = 0 THEN idxsB = {} 
                                ELSE idxsB = {1}

              (* A txn may have at most one commit or abort operation, 
                 and if present it must be the last for that txn. 
               *) 
           /\ LET idxsF == {i \in 1..Len(th) : \/ th[i] = [op |-> "commit", txnid |-> txn]
                                               \/ \E r \in AbortReasons : 
                                                    th[i] = [op |-> "abort", txnid |-> txn, reason |-> r]}
              IN idxsF = {}  \/  idxsF = {Len(th)}

              (* "Bernstein's simplification" 
                 We choose to restrict the specification to histories in which 
                 each transactions is allowed at most one read and one write to each key.  
                 (N.B. There aren't any other restrictions on reads or writes.  
                 E.g. A transaction may read and/or write to more than one key,  
                 and if it both reads and writes to a key, then the read and write may be in either order.)
               *)  
           /\ \A key \in Key : 
                  /\ LET idxsWK == {i \in 1..Len(th) : th[i] = [op |-> "write", txnid |-> txn, key |-> key]}
                     IN Cardinality(idxsWK) =< 1
                  /\ LET idxsRK == {i \in 1..Len(th) : 
                                        \E ver \in TxnId : 
                                            th[i] = [op |-> "read", txnid |-> txn, key |-> key, ver |-> ver]}
                     IN Cardinality(idxsRK) =< 1


(* It's easy to do unit-tests of correctness conditions: 
 *)
UnitTest_WellFormedTransactionsInHistory ==
         (* must begin *)
    /\   WellFormedTransactionsInHistory(<<[op |-> "begin", txnid |-> "T_1"]>>)
         (* just begin & commit *)
    /\   WellFormedTransactionsInHistory(<<[op |-> "begin", txnid |-> "T_1"], [op |-> "commit", txnid |-> "T_1"]>>)
         (* begin, readX, writeY, commit *)
    /\   WellFormedTransactionsInHistory(<<[op |-> "begin", txnid |-> "T_1"], [op |-> "read", txnid |-> "T_1", key |-> "K_X", ver |-> "T_2"], [op |-> "write", txnid |-> "T_1", key |-> "K_Y"], [op |-> "commit", txnid |-> "T_1"]>>)
         (* begin, readX, writeX, abort *)
    /\   WellFormedTransactionsInHistory(<<[op |-> "begin", txnid |-> "T_1"], [op |-> "read", txnid |-> "T_1", key |-> "K_X", ver |-> "T_2"], [op |-> "write", txnid |-> "T_1", key |-> "K_X"], [op |-> "abort", txnid |-> "T_1", reason |-> "voluntary"]>>)
    (* Negative tests *)
         (* begin out of place *)
    /\ ~ WellFormedTransactionsInHistory(<<[op |-> "write", txnid |-> "T_1", key |-> "K_X"], [op |-> "begin", txnid |-> "T_1"]>>)
         (* multiple begin *)
    /\ ~ WellFormedTransactionsInHistory(<<[op |-> "begin", txnid |-> "T_1"], [op |-> "begin", txnid |-> "T_1"], [op |-> "write", txnid |-> "T_1", key |-> "K_X"]>>)
         (* commit out of place (after a begin of a different transaction) *)
    /\ ~ WellFormedTransactionsInHistory(<<[op |-> "begin", txnid |-> "T_1"], [op |-> "commit", txnid |-> "T_1"], [op |-> "write", txnid |-> "T_1", key |-> "K_X"]>>)
         (* abort out of place *)
    /\ ~ WellFormedTransactionsInHistory(<<[op |-> "begin", txnid |-> "T_1"], [op |-> "abort", txnid |-> "T_1", reason |-> "voluntary"], [op |-> "write", txnid |-> "T_1", key |-> "K_X"]>>)
         (* Violation of Bernstein's simplification: multiple writes to same key *)
    /\ ~ WellFormedTransactionsInHistory(<<[op |-> "begin", txnid |-> "T_1"], [op |-> "write", txnid |-> "T_1", key |-> "K_X"], [op |-> "write", txnid |-> "T_1", key |-> "K_X"]>>)
         (* Violation of Bernstein's simplification: multiple reads of same key *)
    /\ ~ WellFormedTransactionsInHistory(<<[op |-> "begin", txnid |-> "T_1"], [op |-> "read", txnid |-> "T_1", key |-> "K_X", ver |-> "T_2"], [op |-> "read", txnid |-> "T_1", key |-> "K_X", ver |-> "T_2"]>>)


(* 
 * Semantics of snapshot isolation. 
 *)

(* Snapshot isolation has precisely defined semantics for what versions of keys 
   a transaction is allowed to read.
 *)
CorrectReadView ==

    \A txn \in TxnId :
        LET itxnb == IndexOfOpInHistory(history, [op |-> "begin", txnid |-> txn])
        IN 
            (* only committed reads: 
               all transactions that txn read from (excluding itself) must have committed *before* txn started 
             *)
            /\ \A read_from \in TxnsReadFrom(history, txn) \ {txn} :
                 LET irfc == IndexOfOpInHistory(history, [op |-> "commit", txnid |-> read_from])
                 IN
                    /\ irfc /= -1    (* read_from has committed *)
                    /\ irfc < itxnb  (* read_from committed before txn began, so txn sees any writes by read_from *)

            (* only up-to-date reads: 
               for each key-version read by txn, there must be no committed writes between 
               the write of that version of the key, and the start time of txn (when it chose its read-view).
               (This also holds for the case where txn reads a version that it wrote itself.)
             *)
            /\ \A <<key, ver>> \in KeyVersionsReadByTxn(history, txn) : 
                  LET iwkv  
                        == IndexOfOpInHistory(history, [op |-> "write", txnid |-> ver, key |-> key])  (* we know this is not -1 *)
                        
                      history_between_write_and_txn_began 
                        == SubSeq(history, iwkv + 1, itxnb)
                        
                      committed_txns_when_txn_began 
                        == CommittedTxns(SubSeq(history, 1, itxnb))
                        
                      committed_writes_to_key_between_write_that_txn_read_and_when_txn_began 
                        == SelectEvents(history_between_write_and_txn_began, 
                                        LAMBDA e : /\ e.op = "write" 
                                                   /\ e.key = key
                                                   /\ e.txnid \in committed_txns_when_txn_began)
                  IN 
                     {} = committed_writes_to_key_between_write_that_txn_read_and_when_txn_began

            (* For all keys that were both written and read by txn, 
                 - if the read occured before the write, then txn read the latest committed version at the time that txn began
                 - if the read occured after the write, then txn read the version it wrote itself
               (We assume that we have correctly implemented Bernstein's simplification, checked elsewhere, 
                that a transaction can do at most one read and at most one write to each key.)
             *)       
            /\ LET read_key_ver == KeyVersionsReadByTxn(history, txn)
                   written_key  == KeysThatTxnHasDoneOperationOn(history, txn, "write")
                   key_ver_of_keys_that_txn_also_wrote
                        == {<<key, ver>> \in read_key_ver : key \in written_key}
               IN
                   /\ \A <<key, ver>> \in key_ver_of_keys_that_txn_also_wrote :
                        LET iw == IndexOfOpInHistory(history, [op |-> "write", txnid |-> txn, key |-> key])
                            ir == IndexOfOpInHistory(history, [op |-> "read",  txnid |-> txn, key |-> key, ver |-> ver])
                        IN
                            IF ir < iw THEN {ver} = LatestCommittedVersionOfKeyWhenTxnBegan(txn, key) (* returns a set *) 
                                       ELSE  ver  = txn


FirstCommitterWins ==
    (* There are no committed transactions that were concurrent, and whose write-sets (keys) intersect. *) 
    ~ \E t1, t2 \in CommittedTxns(history) :  
        /\ t1 /= t2
        /\ AreConcurrent(history, t1, t2)
        /\             KeysThatTxnHasDoneOperationOn(history, t1, "write") 
            \intersect KeysThatTxnHasDoneOperationOn(history, t2, "write")
                /= {}

(* NoDeadlock ==
    Absence of deadlock is tested automatically by TLC (unless we disable that test).
    The LegitimateTermination condition, plus the weak-fairness of Next action, mean 
    that TLC correctly does not report deadlock when a behavior cannot be extended because 
    all transactions have been committed or aborted. 
    But in all other cases where TLC finds that ENABLED(Next) is false, it will report a deadlock. 
 *)

SemanticsOfSnapshotIsolation ==
    /\ CorrectReadView
    /\ FirstCommitterWins
    (* /\ NoDeadlock *)       (* implicitly tested by TLC, see definition of Next *)


(* Some cross-checks that the TLA+ code is correct. 
   These have nothing to do with checking the algorithm, only it's encoding in TLA+.
    
   E.g. We wish to check that we are correctly abstracting the lock manager, 
   and not losing or acquiring locks by accident.  Such bugs might prevent execution histories 
   that could reveal bugs in the actual algorithm.   
 *)

CorrectnessOfHoldingXLocks == 
    (* At any time, an XLOCK can be held by at most one transaction *)
    /\ \A k \in Key : Cardinality({t \in TxnId : k \in holdingXLocks[t]}) <= 1 
    
    (* We can deduce from the write/commit/abort history of a transaction 
       which XLOCKS it must hold at any point in time.
       Specifically a lock is held from the write of a key (not before) 
       until the transaction is finalized (not after).
       Check that holdingXLOCK is equivalent to the locks implied by history.
       e.g. This checks that holdingXLOCKs does not accidentally lose entries. 
     *)
    /\ LET active == ActiveTxns(history) 
       IN \A t \in TxnId : 
            IF t \in active THEN holdingXLocks[t] = KeysThatTxnHasDoneOperationOn(history, t, "write")
                            ELSE holdingXLocks[t] = {}

    (* For all transactions that claim to be holding an XLOCK, the transaction must be active.
       (This is checked by the equivalence to the locks implied by the write/commit/abort history.) 
     *)
    /\ \A t \in TxnId : holdingXLocks[t] /= {} => t \in ActiveTxns(history) 


CorrectnessOfWaitingForXLock ==
    (* A transaction can only be waiting for one xlock at any point in time 
       This is checked by TypeInv, as Range(waitingForXLOCK) is key, not SUBSET key.
     *)

    (* Only active transactions can be waiting for an XLOCK *)    
    /\ \A t \in TxnId : waitingForXLock[t] /= NoLock => t \in ActiveTxns(history) 


(* Serializability 

   As the tests for serializability are complex, we reduce the risk of an error by 
   including two different formulations (by Cahill and Bernstein).  
   We can check an invariant that says that these are equivalent in all states.
 *)  

(*
  From Michael Cahill's PhD thesis:
  
  Verifying that a history is conflict serializable is equivalent to showing that a particular graph is free of
  cycles. The graph that must be cycle-free contains a node for each transaction in the history, and an edge
  between each pair of conflicting transactions. Transactions T1 and T2 are said to conflict (or equivalently,
  to have a dependency) whenever they perform operations whose results reveal something about the order
  of the transactions; in particular when T1 performs an operation, and later T2 performs a conflicting
  operation. Operations O1 and O2 are said to conflict if swapping the order of their execution would
  produce different results (either a query producing a different answer, or updates producing different
  database state). A cycle in this graph implies that there is a set of transactions that cannot be executed
  serially in some order that gives the same results as in the original history.
  
  This is formalized in Theorem 1, which models each transaction as a log of operations, which is a
  list of read or write operations on named data items. The execution history is then an interleaving
  of the different logs; each log is a subsequence of the execution history involving the ops of a single
  transaction.
  
      Theorem 1 (Conflict serializability, (Stearns et al., 1976)). Let T = {T1 .. Tm} be a set of transactions
  and let E be an execution of these transactions modeled by logs {L1, .. Lm}. E is serializable
  if there exists a total ordering of T such that for each pair of conflicting operations Oi and Oj from
  distinct transactions Ti, and Tj (respectively), Oi precedes Oj in any log L1,...Lm if and only if Ti
  precedes Tj in the total ordering.
  
  ...
  
  With snapshot isolation, the definitions of the serialization graph become much simpler, as versions of
  an item x are ordered according to the temporal sequence of the [commits of the] transactions that created 
  those versions (note that First-Committer-Wins ensures that among two transactions that produce 
  versions of x, one will commit before the other starts). 
  
  In the MVSG, we put an edge from one committed transaction T1
  to another committed transaction T2 in the following situations:
  
   - T1 produces a version of x, and T2 produces a later version of x (this is a ww-dependency);
   - T1 produces a version of x, and T2 reads this (or a later) version of x (this is a wr-dependency);
   - T1 reads a version of x, and T2 produces a later version of x (this is a rw-dependency, also
          known as an anti-dependency, and is the only case where T1 and T2 can run concurrently).
 *)
CahillMVSG(h) ==
    (* We only consider operations by transactions that have committed in h, 
       i.e. not operations done by transactions that have already aborted, or have not yet committed. 
     *)
    LET ct == CommittedTxns(h)
        ch == SelectSeq(h, LAMBDA e : e.txnid \in CommittedTxns(h))
    IN
        (* The following set comprehension is SPECIFIC TO SNAPSHOT ISOLATION, 
           because it 'knows' that snapshot isolation guarantees certain properties.
           We check correctness of snapshot isolation elsewhere (e.g. First Committer Wins rule).
           This predicate does not test the correctness of snapshot isolation.
           Here we assume that we have correctly implemented snapshot isolation, and then test 
           the correctness of Cahill's algorithm (extension to snapshot isolation)
           that restricts snapshot isolation to only producing serializable execution histories.
           The properties we assume of snapshot isolation are:
             a. First Committer Wins: 
                 Two committed transactions that both wrote to at least one common key 
                 cannot be concurrent.  
                 Therefore, 
                    - the version-order of a key is the commit-order of the transactions that wrote to that key.
                    - the version-order of a key is also the write-order (as writers cannot be concurrent, 
                      so writes cannot be logically re-ordered when constructing a serializable ordering).
             b. Consistent Read-view: 
                  If T2 reads a version that T1 wrote (or a 'later' version in the version order of that key), 
                  then T2 must have started after T1 committed.  
         *)    
        {<<T1, T2>> \in ct \X ct :
               (* ... from one committed transaction T1 to another [distinct] committed transaction T2 *) 
               T1 /= T2
            /\ \E x \in Key :
                LET iT1w == IndexOfOpInHistory(ch, [op |-> "write",  txnid |-> T1, key |-> x])
                    iT2w == IndexOfOpInHistory(ch, [op |-> "write",  txnid |-> T2, key |-> x])
                IN      (* T1 produces a version of x, and T2 produces a later version of x 
                           (this is a 'ww-dependency') *)
                        /\ iT1w /= -1   (* T1 wrote to x *) 
                        /\ iT2w /= -1   (* T2 wrote to x *)   
                        /\ iT1w < iT2w  (* T1 committed before T2, which for snapshot isolation means that 
                                           T1's write is before T2's write in the version order for x. 
                                           Note that the First Committer Wins rule guarantees that T1 and T2 
                                           were not concurrent. 
                                         *)
                    \/  
                        (* T1 produces a version of x, and T2 reads this (or a later) version of x 
                           (this is a 'wr-dependency').
                         *)
                        LET iT1c == IndexOfOpInHistory(ch, [op |-> "commit", txnid |-> T1])
                            iT2b == IndexOfOpInHistory(ch, [op |-> "begin", txnid |-> T2])
                        IN  
                            /\ iT1w /= -1                                            (* T1 wrote to x *)    
                            /\ x \in KeysThatTxnHasDoneOperationOn(ch, T2, "read")   (* T2 read some version of x *)
                            /\ iT1c < iT2b                                           (* T1 committed before T2 began, so T2 sees any writes by T1 *) 
                    \/  
                        (* T1 reads a version of x, and T2 produces a later version of x 
                           (this is a 'rw-dependency, also' known as an anti-dependency, 
                           and is the only case where T1 and T2 can run concurrently).
                         *)
                        LET iT1b == IndexOfOpInHistory(ch, [op |-> "begin", txnid |-> T1])
                            iT2c == IndexOfOpInHistory(ch, [op |-> "commit", txnid |-> T2])
                        IN 
                            /\ x \in KeysThatTxnHasDoneOperationOn(h, T1, "read")  (* T1 read some version of x *)
                            /\ iT2w /= -1                                          (* T2 wrote to x *)
                            /\ iT1b < iT2c                                         (* T1 (reader) begins before T2 (writer) commits, so T1's read view does not include T2, so T1 reads an earlier version of x than is written by T2 *)
        }
        
(* For serializability, the property must hold for every committed prefix of the actual history.
   We ensure that by checking that it is an invariant -- i.e. true in every state 
 *)
CahillSerializable(h) ==  ~ IsCycle(CahillMVSG(h))


(*
  From Phil Bernstein's book: http://research.microsoft.com/en-us/people/philbe/ccontrol.aspx 
 
  This is the correctness condition from p152 (chapter 5 section 5.2):
 
       Theorem 5.4: An MV history H is 1SR iff there exists a version order, <<, 
       such that MVSG(H, <<) is acyclic.
 
  'version order' is defined as:   
 
  From p151
   Given an MV history H and a data item [key] x, a version order, <, for x in H is
   a total order of versions of x in H. 
   A version order, <<, for H is the union of the version orders for all data items. 
 
  The version order is defined (for MVTO) as:
 
  From p152
   Given an MV history H and a version order, <<, the multiversion serialization
   graph for H and <<, MVSG(H, <<), is SG(H) with the following version
   order edges added: for each rk[xj] and wi[xi] in C(H) where i, j, and k are
   distinct, if xi << xj then include Ti -> Tj, otherwise include Tk -> Ti. 
   Recall that the nodes of SG(H) and, therefore, of MVSG(H, <<) are the 
   committed transactions in H.
   (Note that there is no version order edge if j = k, that is, if a transaction reads 
   from itself.)
 
  SG(H) is defined as follows:
 
  From p149:
   The serialization graph for an MV history is defined as for a 1V history.
 
  From p32  (section 2.3, serializability theory for monoversion histories)    
   The serialization graph (SG) for H, denoted SG(H), is a directed
   graph whose nodes are the transactions in T that are committed in H and
   whose edges are all Ti -> Tj (i /= j) such that one of Ti's operations precedes
   and conflicts with one of Tj's operations in H.
 
  Continuing p149
   But since only one kind of conflict is possible in an MV history, SGs are quite
   simple. Let H be an MV history. SG(H) has nodes for the committed transaction
   in H and edges Ti -> Tj (i /= j) whenever for some key x, Tj reads x from Ti.
   That is, Ti -> Tj is present iff for some x, rj[xi] (i /= j) is an operation of C(H).
 
  From p30
   Given a history H, the committed projection of H, denoted C(H), is the history 
   obtained from H by deleting all operations that do not belong to transactions 
   committed in H.  Note that C(H) is a complete history over the set of committed 
   transactions in H. If H represents an execution at some point in time, C(H) is the 
   only part of the execution we can count on, since active transactions can be 
   aborted at any time, for instance, in the event of a system failure.
 *)

(* SG(H)
   "Ti -> Tj is present iff for some x, rj[xi] (i /= j) is an operation of C(H).
 *)
BernsteinSG(h) ==

    LET ct == CommittedTxns(h)
        ch == SelectSeq(h, LAMBDA e : e.txnid \in CommittedTxns(h))
    IN
        {<<writer_txn, reader_txn>> \in ct \X ct :
            /\ reader_txn /= writer_txn                     (* distinct *)
            /\ writer_txn \in TxnsReadFrom(h, reader_txn)   (* reader_txn read from writer_txn *)
        }

(* "for each rk[xj] and wi[xi] in C(H) where i, j, and k are distinct, 
     if xi << xj then include Ti -> Tj, 
            otherwise include Tk -> Ti." 
 *)
BernsteinVersionOrderEdges(h) ==

    LET ct == CommittedTxns(h)
        ch == SelectSeq(h, LAMBDA e : e.txnid \in CommittedTxns(h))
    IN
        {<<Ti, Tj>> \in ct \X ct :
           /\ Ti /= Tj                                (* Ti and Tj are distinct committed transactions *)
           /\ \E Tk \in ct : 
               /\ Tk /= Ti                            (* Tk is a committed transaction distinct from Ti and Tj *)
               /\ Tk /= Tj
               /\ \E x \in Key :
                   /\ -1 /= IndexOfOpInHistory(ch, [op |-> "read", txnid |-> Tk, key |-> x, ver |-> Tj]) (* rk[xj] is in C(H) *)
                   /\ LET idx_xi == IndexOfOpInHistory(ch, [op |-> "write", key |-> x, txnid |-> Ti])
                          idx_xj == IndexOfOpInHistory(ch, [op |-> "write", key |-> x, txnid |-> Tj])
                      IN
                          /\ -1 /= idx_xi         (* xi exists in C(H) *)
                          /\ -1 /= idx_xj         (* xj exists in C(H) *)
                          /\ (idx_xi < idx_xj)    (* xi << xj. It is valid to compare these indexes, as they come from the same history (ch) *)
         }
      \union   
        {<<Tk, Ti>> \in ct \X ct :
           /\ Tk /= Ti                                (* Tk and Ti are distinct *)
           /\ \E Tj \in ct :
               /\ Tj /= Tk                            (* Tj is distinct from Ti and Tj *)
               /\ Tj /= Ti
               /\ \E x \in Key :
                   /\ -1 /= IndexOfOpInHistory(ch, [op |-> "read", txnid |-> Tk, key |-> x, ver |-> Tj]) (* rk[xj] is in C(H) *)
                   /\ LET idx_xi == IndexOfOpInHistory(ch, [op |-> "write", key |-> x, txnid |-> Ti])
                          idx_xj == IndexOfOpInHistory(ch, [op |-> "write", key |-> x, txnid |-> Tj])
                      IN
                          /\ -1 /= idx_xi         (* xi exists in C(H) *)
                          /\ -1 /= idx_xj         (* xj exists in C(H) *)
                          /\ ~ (idx_xi < idx_xj)  (* NOT xi << xj. It is valid to compare these indexes, as they come from the same history (ch) *)
         }
 
BernsteinMVSG(h) ==  BernsteinSG(h) \union BernsteinVersionOrderEdges(h)

BernsteinSerializable(h) ==  ~ IsCycle(BernsteinMVSG(h))



(* Predicates used solely to force TLC to find interesting histories, for understanding 
   and debugging the algorithm and model.
   For this, we use TLC's ability to check that a predicate is invariant (true in every state).
   TLC reports the first state it finds in which the invariant is false. 
   So to find an example of a particular interesting condition,  
   we tell TLC to check an invariant of the form 'not MyInterestingCondition', 
   and so find an instance of MyInterestingCondition.
   So when telling TLC to 'check' these, remember to prefix with '~'.  Can't really get that 
   wrong as if you forget the '~' TLC will instantly report the invariant violated, 
   as these are usually not true of the initial state. 
 *) 
AtLeastNTxnsHaveWritten(N)        ==  Cardinality({txn \in TxnId : KeysThatTxnHasDoneOperationOn(history, txn, "write") /= {}}) >= N
AtLeastNTxnsHaveRead(N)           ==  Cardinality({txn \in TxnId : KeysThatTxnHasDoneOperationOn(history, txn, "read") /= {}}) >= N
AtLeastNTxnsHaveCommitted(N)      ==  Cardinality(CommittedTxns(history)) >= N
AtLeastNTxnsAreWaitingForLocks(N) ==  Cardinality({txn \in TxnId : waitingForXLock[txn] /= NoLock}) >= N
AtLeastNTxnsAbortedDueToReason(N, Reason) ==  
    LET TxnsAbortedDueToReason == {e.txnid : e \in SelectEvents(history, 
                                                                LAMBDA e : e.op = "abort" /\ e.reason = Reason)}
    IN Cardinality(TxnsAbortedDueToReason) >= N


(* An interesting case: find the 'read-only anomaly' reported in
     "A Read-Only Transaction Anomaly Under Snapshot Isolation" 
     [Alan Fekete, Elizabeth O'Neil, and Patrick O'Neil]
     http://www.cs.umb.edu/~poneil/ROAnom.pdf
     
   Find the anomalous history by checking this 'invariant' 
   
      ~ ReadOnlyAnomaly(history)
      
   If that invariant is violated then a read-only anomaly has been found.
   The unit test below confirms that the above invariant will indeed be violated 
   by the history in Fekete's paper.   
   However, at the time of writing (September 2011), TLC fails to find the anomaly  
   because of an apparent bug -- TLC stops searching if its Queue Size 
   grows larger than 2^31 states.  
   From manual experiments, I found that TLC does find the history up to the 
   last 4 states, before hitting this limit.  
   I filed this bug report: http://bugzilla.tlaplus.net/show_bug.cgi?id=205
*)

(* Helper, returns <<keysRead, keysWritten>> *)
KeysReadAndWrittenByTxn(h, txn) ==
    <<SelectEvents(h, LAMBDA e : /\ e.txnid = txn
                                 /\ e.op = "read"),
      SelectEvents(h, LAMBDA e : /\ e.txnid = txn
                                 /\ e.op = "write") 
    >>

HistoryWithoutTxn(h, txn) ==
    SelectSeq(h, LAMBDA e : /\ e.txnid /= txn)

ReadOnlyAnomaly(h) ==
        (* current history is not serializable *) 
    /\  ~ CahillSerializable(h)
        (* and there is a transaction that does some reads and zero writes,
           and when that transaction is entirely removed from the history, 
               the resulting history is serializable. *)   
    /\ \E txn \in TxnId :
            LET keysReadWritten == KeysReadAndWrittenByTxn(h, txn)
            IN  
                /\ Cardinality(keysReadWritten[1]) > 0
                /\ Cardinality(keysReadWritten[2]) = 0
                /\ CahillSerializable(HistoryWithoutTxn(h, txn))

(* Unit test for ReadOnlyAnomaly.
   This is an encoding of the example history from Fekete's paper:
   
    R2(X0,0) R2(Y0,0) R1(Y0,0) W1(Y1,20) C1 R3(X0,0) R3(Y1,20) C3 W2(X2,-11) C2
*)
UnitTests_ReadOnlyAnomaly ==

    LET h == <<
    (* preamble: create keys that are used later *)
    [op |-> "begin",  txnid |-> "T_0"], 
    [op |-> "write",  txnid |-> "T_0", key |-> "K_X"], 
    [op |-> "write",  txnid |-> "T_0", key |-> "K_Y"], 
    [op |-> "commit", txnid |-> "T_0"],
    
    (* the history from the paper *) 
                     [op |-> "begin",  txnid |-> "T_2"], 
    (* R2(X0,0)   *) [op |-> "read",   txnid |-> "T_2", key |-> "K_X", ver |-> "T_0"], 
    (* R2(Y0,0)   *) [op |-> "read",   txnid |-> "T_2", key |-> "K_Y", ver |-> "T_0"],
                      
                     [op |-> "begin",  txnid |-> "T_1"], 
    (* R1(Y0,0)   *) [op |-> "write",  txnid |-> "T_1", key |-> "K_Y"], 
    (* W1(Y1,20)  *) [op |-> "write",  txnid |-> "T_1", key |-> "K_Y"],
    (* C1         *) [op |-> "commit", txnid |-> "T_1"],
     
                     [op |-> "begin",  txnid |-> "T_3"], 
    (* R3(X0,0)   *) [op |-> "read",   txnid |-> "T_3", key |-> "K_X", ver |-> "T_0"], 
    (* R3(Y1,20)  *) [op |-> "read",   txnid |-> "T_3", key |-> "K_Y", ver |-> "T_1"], 
    (* C3         *) [op |-> "commit", txnid |-> "T_3"],
                      
    (* W2(X2,-11) *) [op |-> "write",  txnid |-> "T_2", key |-> "K_X"], 
    (* C2         *) [op |-> "commit", txnid |-> "T_2"]
    >>
    IN
        ReadOnlyAnomaly(h)
        
(*
As the unit test uses strings to represent transaction identifiers and keys, 
running the test is slightly different the normal way we check this specification.

1. Define a new model with

   Model Overview ... What is the model? 
            Key <- {"K_X", "K_Y"} 
            TxnId <- {"T_0", "T_1", "T_2", "T_3"}
            (both normal assignments)
            
   Advanced Options ... Definition Override :
            NoLock <- (a model value)
            
2. Check "No behavior spec" under "Model Overview" ... "What is the behavior spec?" 

3. Set "Evaluate Constant Expression" to
            UnitTests_ReadOnlyAnomaly

4. Run TLC.  It the output in the "Value" pane should be TRUE .

p.261 of Specifying Systems suggests that this should work (as "Evaluate Constant Expression") 
but the toolbox gives an error about the assume.
 
   ASSUME LET Key == {"K_X", "K_Y"} 
              TxnId == {"T_0", "T_1", "T_2", "T_3"} 
          IN UnitTests_ReadOnlyAnomaly
*)

=============================================================================
\* Modification History
\* Last modified Mon Oct 10 09:21:44 PDT 2011 by cnewcom
\* Created Sun Mar 27 13:01:51 PDT 2011 by cnewcom
