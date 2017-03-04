# tla+rust → <img src="parrot.gif" width="48" height="48" />

Stable stateful systems through modeling, linear types and simulation.

I like to use things that wake me up at 4am as rarely as possible.
Unfortunately, infrastructure vendors don't focus on reliability.
Even if a company gives reliability lip service, it's unlikely that they
use techniques like modeling or simulation to create a rock-solid core.
Let's just build an open-source distributed store that takes correctness
seriously at the local storage, sharding, and distributed transactional layers.

My goal: verify core lock-free and distributed algorithms in use
with [rsdb](http://github.com/spacejam/rsdb) and
[rasputin](http://github.com/disasters/rasputin) with TLA+. Write
an implementation in Rust. Use quickcheck and abstracted RPC/clocks
to simulate partitions and test correctness under failure conditions.

##### table of contents
1. overview of topics covered
  - [x] [intro: specifying concurrent processes with pluscal](#here-we-go-jumping-into-pluscal)
2. lock-free algorithms for efficient local storage
  - [ ] [lock-free ring buffer](#lock-free-ring-buffer)
  - [ ] [lock-free list](#lock-free-liss)
  - [ ] [lock-free stack](#lock-free-stack)
  - [ ] [lock-free radix tree](#lock-free-radix-tree)
  - [ ] [lock-free IO buffer](#lock-free-io-buffer)
  - [ ] [lock-free epoch-based garbage collector](#lock-free-epoch-based-gc)
  - [ ] [lock-free pagecache](#lock-free-pagecache)
  - [ ] [lock-free tree](#lock-free-tree)
3. consensus within a shard
  - [ ] [the harpoon consensus protocol](#harpoon-consensus)
4. sharding operations
  - [ ] [shard splitting](#shard-splitting)
  - [ ] [shard merging] (#shard-merging)
5. distributed transactions
  - [ ] [cross-shard 2PC](#cross-shard-2pc)

## here we go... jumping into pluscal

This is a summary of an example from
[a wonderful primer on TLA+](https://www.learntla.com/introduction/example/)...

The first thing to know is that there are two languages in play: pluscal and TLA.
We test models using `tlc`, which understands most of TLA (not infinite sets, maybe
other stuff). TLA started as a specification language, tlc came along later to
actually test it, and pluscal is a simpler language that can be transpiled into
TLA. Pluscal has two forms, `c` and `p`. They are functionally identical, but
`c` form uses braces and `p` form uses prolog/ruby-esque `begin` and `end`
statements that can be a little easier to spot errors with, in my opinion.

We're writing Pluscal in a TLA comment (block comments are written
with `(* <comment text> *)`), and when we run a translator like `pcal2tla`
it will insert TLA after the comment, in the same file.

```tla
------------------------------- MODULE pcal_intro -------------------------------
EXTENDS Naturals, TLC

(* --algorithm transfer
variables alice_account = 10, bob_account = 10,
          account_total = alice_account + bob_account

process TransProc \in 1..2
  variables money \in 1..20;
begin
  Transfer:
    if alice_account >= money then
      A: alice_account := alice_account - money;
      B: bob_account := bob_account + money;
    end if;
C: assert alice_account >= 0;
end process

end algorithm *)

\* this is a TLA comment. pcal2tla will insert the transpiled TLA here

MoneyInvariant == alice_account + bob_account = account_total

=============================================================================
```

This code specifies 3 global variables, `alice_account`, `bob_account`, `account_total`.
It specifies, using `process <name> \in 1..2` that it will run in two concurrent processes.
Each concurrent process has local state, `money`, which may take any initial value from
1 to 20, inclusive.  It defines steps `Transfer`, `A`, `B` and `C` which are evaluated as
atomic units, although they will be tested against all possible interleavings of execution.
All possible values will be tested.

Let's save the above example as `pcal_intro.tla`, transpile the pluscal comment to TLA,
then run it with tlc! (if you want to name it something else, update the MODULE
specification at the top)

```
pcal2tla pcal_intro.tla
tlc pcal_intro.tla
```

BOOM! This blows up because our transaction code sucks, big time:

```
The first argument of Assert evaluated to FALSE; the second argument was:
"Failure of assertion at line 16, column 4."
Error: The behavior up to this point is:
State 1: <Initial predicate>
/\ bob_account = 10
/\ money = <<1, 10>>
/\ alice_account = 10
/\ pc = <<"Transfer", "Transfer">>
/\ account_total = 20

State 2: <Action line 35, col 19 to line 40, col 42 of module pcal_intro>
/\ bob_account = 10
/\ money = <<1, 10>>
/\ alice_account = 10
/\ pc = <<"A", "Transfer">>
/\ account_total = 20

State 3: <Action line 35, col 19 to line 40, col 42 of module pcal_intro>
/\ bob_account = 10
/\ money = <<1, 10>>
/\ alice_account = 10
/\ pc = <<"A", "A">>
/\ account_total = 20

State 4: <Action line 42, col 12 to line 45, col 63 of module pcal_intro>
/\ bob_account = 10
/\ money = <<1, 10>>
/\ alice_account = 9
/\ pc = <<"B", "A">>
/\ account_total = 20

State 5: <Action line 47, col 12 to line 50, col 65 of module pcal_intro>
/\ bob_account = 11
/\ money = <<1, 10>>
/\ alice_account = 9
/\ pc = <<"C", "A">>
/\ account_total = 20

State 6: <Action line 42, col 12 to line 45, col 63 of module pcal_intro>
/\ bob_account = 11
/\ money = <<1, 10>>
/\ alice_account = -1
/\ pc = <<"C", "B">>
/\ account_total = 20

Error: The error occurred when TLC was evaluating the nested
expressions at the following positions:
0. Line 52, column 15 to line 52, column 28 in pcal_intro
1. Line 53, column 15 to line 54, column 66 in pcal_intro


9097 states generated, 6164 distinct states found, 999 states left on queue.
The depth of the complete state graph search is 7.
```

Looking at the trace that tlc outputs, it shows us how alice's account may become
negative. Because processes 1 and 2 execute the steps sequentially but with
different interleavings, the algorithm will check `alice_account >= money`
before trying to transfer it to bob. By the time one process subtracts the
money from alice, however, the other process may have already done so. We can
specify that these steps and checks happen atomically by changing:

```
  Transfer:
    if alice_account >= money then
      A: alice_account := alice_account - money;
      B: bob_account := bob_account + money;
    end if;
```

to

```
  Transfer:
    if alice_account >= money then
      \* remove the labels A: and B:
      alice_account := alice_account - money;
      bob_account := bob_account + money;
    end if;
```

which means that the entire `Transfer` step is atomic. In reality, maybe this is done
by punting this atomicity requirement to a database transaction. Re-running tlc should
produce no errors now, because both processes atomically check + deduct + add balances
to the bank accounts without violating the assertion.

The invariant, `MoneyInvariant`, at the bottom is not actually being checked yet.
Invariants are specified in TLA, not in the pluscal comment. They can be checked
by creating a `pcal_intro.cfg` file (or replace the one auto-generated by pcal2tla)
with the following content:

```
SPECIFICATION Spec
INVARIANT MoneyInvariant
```

Ok, now let's start verifying some algorithms we'll use for our database!

# lock-free algorithms for efficient local storage

In the interests of achieving a price-performance that is compelling,
we need to make this thing sympathetic to modern hardware. Check out
[Dmitry's wonderful blog](http://www.1024cores.net/home/lock-free-algorithms)
for a fast overview of the important ideas in writing scalable code.

## lock-free ring buffer

The ring buffer is at the heart of several systems in our local storage system.
It serves as the core of our concurrent persistent log IO buffer and the
epoch-based garbage collector for our logical page ID allocator.

## lock-free list
The list allows us to CAS a partial update to a page into a chain, avoiding
the work of rewriting the entire page. To read a page, we traverse its list
until we learn about what we sought. Eventually, we need to compact the list
of partial updates to improve locality, probably around 4-8.

## lock-free stack
The stack allows us to maintain a free list of page identifiers. Our radix
tree needs to be very densely populated to achieve a favorable data to
pointer ratio, and by reusing page identifiers after they are freed, we
are able to keep it dense. Hence this stack. When we free a page, we push
its identifier into this stack for reuse.

## lock-free radix tree
We use a radix tree for maintaining our in-memory mapping from logical
page ID to its list of partial updates. A well-built radix tree can
achieve a .92 total size:data ratio when densely populated and using a
contiguous key range. This is way better than what we get with B+ trees,
which max out between .5-.6. The downside is that with low-density we
get extremely poor data:pointer ratios with a radix tree.

## lock-free IO buffer
We use a ring buffer to hold buffers for writing data onto the disk, along
with associated metadata about where on disk the buffer will end up.
This is fraught with peril. We need to avoid ABA problems in the CAS that
claims a particular buffer, and later relies on a particular log offset.
We also need to avoid creating a stall when all available buffers are
claimed, and a write depends on flushing the end of the buffer before the
beginning is free. Possible ways of avoiding: fail reservation attempts
when the buffer is full of claims, support growing the buffer when necessary.
Bandaid: don't seal entire buffer during commit of reservation.

## lock-free epoch-based GC
The basic idea for epoch-based GC is that in our lock-free structures,
we may end up making certain data inaccessible via a CAS on a node somewhere,
but that doesn't mean that there isn't already some thread that is operating
on it. We use epochs to track when a structure is marked inaccessible, as
well as when threads begin and end operating on shared state. Before
reading or mutating the shared state, a thread "enrolls" in an epoch.
If the thread makes some state inaccessible, it adds it to the
current epoch's free list. The current epoch may be later than the
epoch that the thread initially enrolled in. The state is not dropped
until there are no threads in epochs before or at the epoch where
the state was marked free. When a thread stops reading or mutating
the shared state, it leaves the epoch that it enrolled in.


## lock-free pagecache
Maintains a radix tree mapping from logical page ID to a list of page updates,
terminated by a base page. Uses the epoch-based GC for safely making logical ID's
available in a stack. Facilitates atomic splits and merges of pages.

## lock-free tree
Uses the pagecache to store B+ tree pages.

# consensus within a shard
We use a consensus protocol as the basis of our replication across a shard.
Consensus notes:

1. support OLTP with small replication batch size
1. support batch loading and analytical jobs with large replication batch size
1. for max throughput with a single shard, send disparate 1/N of the batch to
   each other node, and then have them all forward their chunk to everybody else
1. but this adds complexity, and if each node has several shards, we are already
   spreading the IO around, so we can just pick the latency-minimizing simple
   broadcast where the leader sends full batches to all followers.
1. TCP is already a replicated log, hint hint
1. UDP may be nice for receiving acks, but it doesn't work in a surprising number of DCs

## harpoon consensus
Similar to raft, but uses leader leases instead of a paxos register. The paxos
register preemptable election of raft is vulnerable to livelock in the not-unusual
case of a network partition between a leader and another node, which triggers a
dueling candidate situation. Using leases allows us to make progress as long as a
node has connectivity with a majority of its quorum, regardless of interfering nodes.
In addition, a node that cannot reach a leader may subscribe to the replication log
of any other node which has seen more successful log entries.

# sharding operations
Sharding has these ideals:

1. avoid unnecessary data movement (wait some time before replacing a failed node)
2. if multiple nodes fail simultaneously, minimize chances of dataloss ([chainsets](https://github.com/rescrv/HyperDex/blob/8d8ca6781cdfa6b72869c466caa32f076576c43d/coordinator/replica_sets.cc#L71))
3. minimize MTTR when a node fails (lots of shards per machine, reduce membership overlap)

ideals 2 and 3 are someone at tension, but there is a goldilocks zone.

Sharding introduces the question of "who manages the mapping?"
This is sometimes punted to an external consensus-backed system.
We will initially create this by punting the metadata problem to
such a system. Eventually, we will go single-binary with something
like the following:

If we treat shard metadata as just another range, how do we prevent
split brain?

General initialization and key metadata:

1. nodes are configured with a set of "seed nodes" to initially connect to
1. cluster is initialized when some node is explicitly given permission to do so, either
   via argv, env var, conf file or admin REST api request
1. the designated node creates an initial range in an underreplicated state
1. the metadata range contains a mapping from range to current assigned members
1. as this node learns of others via the seeds, it assigns peers to the initial range
1. if the metadata range (or any other range) loses quorum, a particular minority survivor
   can be manually chosen as a seed for fresh replication. the admin api can also trigger
   backup dumps for a range, and restoration of a range from a backup file.
1. nodes each maintain their own monotonic counters, and publish a few basic stats about
   their ranges and utilization using a shared ORSWOT

## shard splitting
Split algorithm:

1. as operations happen in a range, we keep track of the max and min keys,
   and keep a running average for the position between max and min of inserts.
   We then choose a split point around there. If keys are always added to one end,
   the split should occur at the end.
1. record split intent in watched meta range at the desired point
1. record the split intent in the replicated log for the range
1. all members of the replica set split their metadata when they see
   the split intent in their replicated log
1. The half of the split point that contains less density is migrated
   by changing consensus participants one node at a time.
1. once the two halves have a balanced placement, the split intent is removed

## shard merging
Merge algorithm:

1. merge intent written to metadata range
1. the smaller half is to move to the larger's servers
1. this direction is marked at the time of intent, to prevent flapping
1. once the ranges are colocated, in the larger range's replicated log,
   write a merge intent, which causes it to accept keys in the new range
1. write a merge intent into the less frequently accessed range's replicated
   log that causes it to redirect reads and writes to the larger range.
1. update the metadata range to reflect the merge
1. remove handlers and metadata for old range

# distributed transactions
## cross-shard 2PC
Relatively simple lock-free distributed transactions:

1. read all involved data
1. create txn object somewhere
1. CAS all involved data to refer to the txn object
1. CAS the txn object to successful

readers at any point will CAS a txn object to aborted if they encounter an in-progress
txn on something they are reading.

This can be relaxed to just intended writers, but then our isolation level goes from SSI 
to SI and we are vulnerable to write skew.
