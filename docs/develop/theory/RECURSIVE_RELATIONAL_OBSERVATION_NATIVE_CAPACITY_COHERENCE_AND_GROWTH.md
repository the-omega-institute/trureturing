# Native capacity coherence and growth of one continuing source

## 1. Mathematical domain and supplied contracts

**Convention 1.1 (status and scope).** This volume gives ordinary mathematical
definitions and proofs for a sequential constructed-tape instrument. It is
reference input, with no Lean-kernel certification or physical-realization
claim. Merged text is append-only. The fixed source revision for the suppliers
is `a31331d631db225e94b3a650a67498d812228d33`; the acquired-input supplier is
also read at `346647b9c5e41ec76f0ea19d5796323dc813f750`. The new result concerns
an instrument installed with its maintenance authority at its original boot.
It does not install new authority into an arbitrary closed legacy controller.

**Definition 1.2 (original source task).** Let
$\mathcal T=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle$ be the
nonempty ordered binary-tree algebra, retaining brackets and leaf labels.
Let $\lambda$ count leaves and let $\mathcal T_h=\{t:\lambda(t)\le h\}$ for
$h\ge1$. The original substitution is

$$
\rho\alpha=\beta,\qquad \rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle.
$$

The fixed-guard task $F_h$ has source $t\in\mathcal T_h$. ReadE returns the
original Clifford value $E(t)$. TagRead at any finite $L/R$ address returns its
literal alpha, beta, branch or absent reply. Rho, Left($v$), Right($v$), for
every actual nonempty finite context $v$, form the whole candidates
$\rho t,\langle v,t\rangle,\langle t,v\rangle$. They accept exactly when the
candidate has at most $h$ leaves. Acceptance installs that whole candidate;
rejection retains $t$ and exposes no candidate value. Rejection is executed
work with an event, row and successor. Busy second calls and unauthorized
reads/writes are unexecuted `none`. A completed stop, an absent literal reply,
a source reject and a paid archive `no-row` have distinct types.

**Convention 1.3 (reused results and their limits).** The following supplied
facts retain their stated hypotheses. Their proofs are not new claims here.

| Supplier | Reused statement and exact boundary |
| --- | --- |
| [Transport Memory Completion](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md), PR57.D1–D9, L1–L4, T1–T5 | Finite native control, constructed tapes, literal source ingress, whole-candidate guards, source circuits, real Allocate/AppendWord/Promote, metering, immutable archives and record-only verification. The source guard and contiguous source packet in that supplier are fixed at its $H$. Generic allocation is not its original-source growth theorem. |
| [Native Literal Journal Adapter](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_LITERAL_JOURNAL_ADAPTER.md), Definitions 1.1–1.3, 2.1, 3.1–3.2, 4.1–4.4; Theorems 3.3–3.4, 4.5, 5.3, 7.2 | Same-source literal TagRead, pending events versus sealed rows, and the finite capacity-safe Native adapter. Its Open 11.3 explicitly leaves priced cross-capacity source growth and identity correspondence. |
| [Native Acquired Input Frontier and Replay](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ACQUIRED_INPUT_FRONTIER_AND_REPLAY.md), Definitions 2.1–2.6, 3.1–3.4, 6.3; Theorems 4.4 and 6.4 | Actual retained input, source-free deterministic replay with an absolute primitive ordinal, and the complete length-controlled two-stage copy. Its $12k+6$ includes loop tests; $8k+4$ alone does not. Neither expression includes allocation, descriptors or positioning. |
| `D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.lean`, `nativeStep`, `Run`, `actual_register_execution`; its owning Scribe | Actual local/read/rho chronology on one register. There is no capacity, physical-address resolver, installed growth authority or maintenance bill in that abstract interface. |
| `NativeFullSourceProducer.lean`, `sourceControl`, `native_source_producer`; `NativeEffectiveSourceProducer.lean`, `effective_source_producer`; their owning Scribes in the same observer directory | Existing no-update finite-source traversal and effective acquisition. A mathematical selector is not an installed paid evaluator. |
| `NativeSerialEffective.lean`, `OriginalCodeRealization`, `original_code_service_simulation`; its owning Scribe | The given actual evaluator and genuine-state realization equation supply the effective-controller interface. The present instrument still has to store, run and retain that controller. |
| Transport Memory Completion, TMC23.10–23.12 and subsection 30.4 | Compatible infinite-tree semantics and static capacity projection already exist. Static projection is explicitly not guarded-action intertwining. TMC30.3 already supplies the three-leaf missing-window witness. None of these is counted as a new result here. |

**Definition 1.4 (extended task).** Fix an initial $H_0\ge1$ and one paid valid
preparation occurrence $\xi$ with seed $u\in\mathcal T_{H_0}$. Maintain separate
public natural parameters

$$
1\le H_0\le h\le K,\qquad \lambda(t)\le h.
$$

Here $h$ is the semantic guard and $K$ is source-storage reserve. Initially
$h=K=H_0$. The extended task $F^+$ retains all of $F_h$ and adds producer-owned
maintenance operations. Reserve($J$), for $J>K$, appends backing cells and
changes $K$ to $J$, leaving $h,t$ unchanged. Reserve($K$) returns `unchanged`;
$J<K$ returns `maintenance-refusal`. Raise($J$), for $h<J\le K$, changes the
guard to $J$ without changing $t$ or backing cells. Raise($h$) returns
`unchanged`; all other values return `maintenance-refusal`. These are complete
paid operations, not source rejects. They preserve the source-call count $q$,
accepted-modification count $g$ and accepted-rho epoch $e$. A distinct all-event
count $m$ includes maintenance, source events and exposed local/stop markers.
The inherited semantic-event count $j$ includes every source event,
NativeLocal and Halt, including executed rejects, and excludes maintenance.
Thus $q\le j\le m$; none of these is the primitive clock. Journal access,
copying, fences and other service microsteps increment neither $j$ nor $m$.
Successful reservations and strict raises have separate layout and policy
ordinals $r,p$. Every accessible ordinal is a constructed unary word.

Maintenance is admitted only at the serial idle boundary after previous
mandatory row delivery and acknowledgement. All inherited ingress, generation,
source-write, pending-row and partial-copy cuts remain runtime states. The
restriction on maintenance admission removes no original busy cut or original
continuation. No arbitrary-busy-cut migration, concurrency, crash recovery or
interrupt service is included.

The inherited callable journal service is an auxiliary paid memory routine,
with the explicit resident entry and versioned index contracts of §6. It
does not add a semantic source/maintenance event or an external source tag.

## 2. Primitive carrier, material and installation authority

**Definition 2.1 (primitive carrier).** Use exactly PR57.D1's 64 finite tape
ports, fixed finite native control, eight finite symbol latches, ownership
tokens, constructed head marks and receipt meter. The atomic core occurrences
are RD, WR, ML, MR, EX, BF, IN, OUT, TOK and CTL with their supplier meanings.
EX constructs one adjacent cell; WR changes one symbol; IN changes its finite
latch and does not write or move. Each occurrence appends one actual meter
receipt, takes one tick and charges two fee units. No natural, pointer,
interval, table, counter increment or whole seal record is an atomic register.

Tape data cells have the supplier's eight-bit encoding. The fixed symbols
$L,R,0,1,\square,\mathsf{sep},\mathsf{seal},\mathsf F$ are finite symbols.
A record's seal is an actually constructed symbol cell. Metadata bits, unary
fields, field separators, all head marks and all retired data remain physical
parts of the carrier. Primitive atomicity is the declared ideal sequential
atomicity; a finer device must provide its own intermediate-cut refinement.

**Definition 2.2 (ports, latches and finite calling convention).** Ports 0–15
are public producer runtime work: directory 0, twelve word-work ports 1–12,
retained ingress stream 13, complete-row construction 14, generated literal
gate code 15. Port 16 is the producer-private bit arena, containing source
segments and separately allocated circuit work. Ports 17–23 retain the
producer's supplied counters, archives, response blocks and other inherited
private work. Actor/controller 24–31, verifier 32–39, consumer 40–47,
mailboxes 48–55 and meter/readout 56–63 retain PR57's owner partitions.
The inherited service graphs can relocate their scratch roles within their
owner partition by the same Base/Seek discipline; this grants no cross-owner
read. The new directory and twelve word registers use only 0–12.
Within the actor partition, 24 holds its immutable table, 25 its encoded
persistent state/workspace, 26 its acquired seed and earlier acquired data,
and 27 its waiting command/return packet. Maintenance protects these four
ports. Ports 28–31 are actor archive, archive descriptors, checking work and
terminal/output work respectively. Delivery can append to or scan those
four ports while preserving all old payloads and handle meanings. Producer
17 holds block descriptions, 18 the semantic-journal index, 19 unified-row
indices, 20 responses, 21 frozen-prefix work, 22 inherited public-expression
frames, and 23 the counter bank of Definition 6.1. These are boot assignments,
not a later movement of already acquired data.

Port 21 also holds staged public blocks and frozen-prefix work; BuildManifest
constructs its word on one of 1–12 before copying it into a block/row.
These contain public directory material, never source payload.
Verifier 32 is its acquired snapshot/block archive, 33 its native descriptor
stream, 34 its candidate/replica arena, 35 its public prior/program work,
36 receipt construction, 37 target work, 38 enumeration/frame work and 39
checking work. Consumer 40 is its acquired receipt/binding archive, 41 its
native descriptors, 42 initialization/proposal work, 43 task-output blocks,
44 checks, 45 retained binding work, 46 serial output and 47 scratch.
The fixed mailbox routes are producer-to-actor 48, actor-to-producer 49,
producer-to-verifier 50 and verifier-to-consumer 51; 52–55 are unused here.
A mailbox's native descriptor is on its sender's descriptor stream (17, 29
or 33); the receiver's final archive descriptor is on 29, 17, 33 or 41 as
appropriate. All these assignments are part of the paid resident boot.
Descriptor streams on 17,
29 and the corresponding verifier/consumer work ports use the same native
record format of Definition 6.1. The readout service has the supplier's
public meter read head; its arithmetic uses producer public word roles.
No actor or consumer receives a private arena token from a descriptor.

The new word routines use latch 4 for public tests/data and finite control for
one additional read bit or comparison result. Private gate operands/results
use latches 0–3. The input latch is 5 and is untouched until its corresponding
WR. Latches 6–7 are available to inherited output/control routines. In
particular an address seek does not overwrite a saved private operand or the
input latch. A caller of maintenance is suspended at a complete source-service
boundary: its persistent continuation, machine table, workspace, acquired seed
and previous inputs are on actor-owned tapes. Its pending command and return
kind are complete retained blocks, not live shared latches. Maintenance does
not move the protected controller heads or change their bits or owner.
Archive and checking heads can move in the prescribed delivery. Finite runtime
latches and phase do change and remain part of the actual history.

The twelve public word ports are one serial arithmetic workspace, initially
owned by the producer. The installed joint control may lend them to the
actor, verifier or consumer, using **twelve actual TOK occurrences**, one
per port, then one CTL entering that owner's service phase. Return executes
the twelve reverse TOKs and one CTL. These are the existing port tokens,
not a new permission primitive or a free ability to read another owner's
archive. A helper never runs while only part of this finite token transfer
is complete. Those transfer cuts are actual busy states with a unique next
TOK; they are not callable services. Existing word bytes/heads transfer as
constructed public material. All caller words needed afterward are either
among these transferred complete words or staged in their original owned
blocks before reuse. Ports 0 and 13–27 do not join this lending pool.
In particular no private source, producer descriptor bank or protected
actor table/state/seed/command token is lent. A nonproducer owner accesses
only its local descriptor/archive ports and these lent public word roles;
it cannot call producer directory/counter lookup as a local private read.

For a channel the pool starts at the sender. Before receiver allocation,
lend it to that receiver for its own Base/Zero/status/descriptor preparation,
then return it to the sender for stage one. After mailbox seal/read-token
handoff, lend it to the receiver for stage two and receiver checks. Counter,
base and status words survive these transfers at their actual ports. Return
the pool to the sender after copy/check completion, before resuming a sender
routine. A mandatory row parser can run in this receiver phase before the
return; its final row ACK follows that return. At stop lend the pool to the
verifier for its whole replay/receipt construction and to the consumer for
its checks/output; nested channels follow the same rule with their actual
sender as the pool-return owner. No two owners run these routines together.
Thus the eight private ports of a verifier/consumer need hold its archive,
descriptor stream, program/candidate blocks and snapshots, while the twelve
actual lent word ports supply the stated arithmetic/field roles. Every
lending and return is charged and installed at original boot.

A native call is inlined with its fixed return edge, as in PR57.D1. There is no
unbounded native call stack. Twelve word-role names can be permuted among the
twelve work ports by a finite-control CTL; this is a permutation of twelve
fixed ports, not a variable-address pointer. Arithmetic outputs always use a
port distinct from their inputs. A needed repeated operand is copied to a
spare port first. After the result is complete, one such CTL exchanges its role
with the old destination role. Ordinary word/arithmetic routines use at most six operand,
output and temporary word roles at once; directory iteration adds four field
roles and two retained-state roles. More explicitly, ReadState retains five
state words and one current field, with at most two arithmetic temporaries;
Resolve retains its input/remainder/base/length/output and a subtraction
temporary, with at most four caller gate fields; reservation can release
unused $h,p$ roles and retains at most its eight command/state/record fields
plus two arithmetic temporaries; raising retains seven such fields plus two
temporaries; a channel retains its three bases, length, two status addresses
and counter plus at most three construction temporaries. Variable generator
frames and verifier candidates are constructed blocks on their designated
work tapes, loaded a field at a time, not further simultaneously live word
roles. CloseFence's scans/tuple construction use target/count/bound/tick/fee/ref-output
roles and at most four temporary/field roles, at most ten in all; subsequent
staging/descriptor construction releases these roles as in Definition 6.1. Before such a call, reusable
row/state material is staged as complete blocks on 21 with actual native
descriptors on 17, and is reloaded one field at a time. BuildManifest uses
output/expected-count/visited-count/tag/current-field/length and at most two
arithmetic temporaries, at most eight; earlier row fields have already been
written or staged. Reference tuples and compound response/counter fields
are built one component at a time, with those same bounded scans. Staging is
the explicit bit-block graph of Definition 6.2, not an unbounded native
stack or simultaneous collection of word roles. Thus the twelve ports suffice. Old words
on a reused port remain constructed; appending the next word never overwrites
them. Gate execution and directory generation use these work ports in separate
phases, and do not share live word operands across that boundary.

**Definition 2.3 (native graph encoding and expansion).** The native row
encoding is the supplier's

$$
U(q)U(\mathrm{op})U(i)U(j)U(s)U(q_0)U(q_1),\qquad U(n)=1^n0.
$$

Rows are assigned numbers by routine order in this volume, then textual
occurrence order, using the supplier's fixed opcode order. Sequences identify
the first exit with the next entry. A public conditional uses a testing RD or
CTL row with the two stated successors. A public loop connects its body's
last successor to its test row; it adds no invisible back-edge occurrence.
Fixed subroutines are inlined. The finite alternatives over ports, latches,
symbols, finite role permutations and truth tables are expanded literally.
Loops over variable data have actual tape heads and terminal tests. Static
routine calls form the order: primitive word routines, arithmetic, native field/descriptor and bit-frame
codecs, closed readout/staging, directory state/resolution and manifest
serialization, source generation, dispatch, semantic/unified rows and their
finite index/lookup/snapshot readers.
Their call graph has finite depth; inherited public-expression traversal uses
PR57's constructed frame stack. No routine generates its own evaluator.

This specifies a finite native description independent of $H_0,h,K$, request
count and all word lengths. Its exact bit count is the length of this row
encoding after the stated finite expansion. Boot constructs the ordinary
boundaries and installs every native-description/control/token bit through
PR57.D1's literal boot edges, one bit per installation edge, with receipts.
Any fixed finite primitive-control encoding is part of the supplier's $S_0$.
There is no supplied unbounded resident table or preallocated data arena.

**Definition 2.4 (original entrance and acquired continuity).** Boot receives
the public $U(H_0)$, identity $\xi$, prior description and actual controller
table/initial configuration by literal bit ingress/write. Construct
$N_0=2H_0-1$ and $L_0=2N_0=4H_0-2$ by the word arithmetic below. Measure the
actual port-16 base $b_0$ before allocation. Allocate and zero $L_0$ cells with
the inherited masks and work allocations. At that very interval execute the
original $L_0$ private IN; WR; MR source ingress occurrences and the full
PR57 validation circuit. A valid packet enables the initial directory entry;
an invalid packet reaches `invalid-preparation` with no source permission.
There is exactly one private preparation, not an ingress at each capacity.

After the initial directory is sealed, the already supplied no-update producer
may run through the resident TagRead dispatcher, completely materialize the
seed syntax and deliver it to the controller owner. Its internal Stop returns
to the surrounding dispatcher after the paid output/seal/handoff, as in the
acquired-input supplier's entrance. The acquired seed, all completed input
blocks and old archives remain at their original owned intervals throughout
maintenance. Where this entrance is required by a replay theorem, its entire
paid prefix is included. No source identity or handle alone gives the actor
that seed payload. Original guarded clients need not acquire the seed merely
to use Reserve or Raise.

Before that directory seal, boot constructs all six zero counter records of
Definition 6.1, including the inherited fence counter. Immediately after its
seal WR and following MR, boot runs CloseFence(`initial-publication`). It
serializes the initial manifest and that returned fence reference in a sealed
public boot-binding block on 21, with its description on 17. This block,
initialization and prior are copied to the actor before its first use and to
the verifier with its snapshot. This is finite paid boot work. The directory
does not contain its own future publication fence. The initial source and
its original ingress interval remain exactly those above.

## 3. Explicit word, position and field routines

**Definition 3.1 (work-word representation and elementary graphs).** A work
port is an append-only sequence of finite bit words, each followed by one
$\mathsf{sep}$. Its newest completed word is the current value of that finite
port role. Empty words are permitted; unary words are nonempty. No field
descriptor is needed to find the newest word. The following graphs fix all
new positioning and copying used below. Each named arrow is a primitive; its
last row has the stated next routine as successor.

Home and Tail are PR57.D2's boundary-only RD/move loops. Append($d,b$), with
$d$ at R, is EX($d$); WR($d,b$); MR($d$), including for a separator.
Last($d$) executes Tail($d$); ML; ML, then repeatedly RD; on an ordinary bit
ML and repeat, on sep or L execute MR and return. Its precondition is that
at least one complete word exists. It returns at the newest word's first bit,
or its sep if empty. If its newest word has $k$ bits, its cost is exactly
Tail's actual boundary distance cost plus $2k+4$.

New($d$) executes Tail($d$). Finish($d$) appends sep, then Last($d$). A fixed
literal word is New, one Append per literal bit, Finish. Copy($s,d$), for
distinct ports, is Last($s$); New($d$), then RD($s$,4); on sep exit the loop,
otherwise Append($d$,latch4); MR($s$) and repeat; finally Finish($d$).
On a $k$-bit word its copy loop has exactly $5k+1$ occurrences, before Finish.
The terminal test is present even for the empty word. The return has the
source head on sep and destination head at the new word's first bit.

For a native metadata field whose head already points to its first bit,
CopyField uses the identical loop without Last($s$). It stops at that field's
actual sep. SkipField repeatedly RD; on sep MR and return; otherwise MR and
repeat. On $k$ bits it costs $2k+2$. All source heads and destination tails
in these calls are those actual marked cells. No mathematical offset is used
as an unexecuted stopping test.

WriteField($s,d$) is Last($s$), FieldBody($s,d$), Append($d$,sep),
with destination already at R. It writes precisely $w\mathsf{sep}$ for
the complete source word $w$ and returns source on its own sep, destination
at R. ReadField($s,d$) is CopyField($s,d$) followed by **MR($s$)**.
It enters at the first field bit, including at sep for an empty field, and
returns source immediately *after* that sep, destination at its newest
word's first bit. SkipField has this same source exit. These are the shared
metadata writer/reader contracts; CopyField alone deliberately keeps its
on-sep exit. A framed bit payload is decoded by Definition 6.1, never by
applying a sep scanner to its concatenated frames.

Equivalently, FieldBody is just that sep-terminated $5k+1$ loop, entered
with source at its first bit and destination at R, returning with source at
sep and destination at R. CopyField is New(destination), FieldBody, Finish;
Copy additionally positions the source with Last. A native field writer uses WriteField. A bit-row writer uses Frame,
whose payload part calls FieldBody without a separator; it appends its
one physical sep/status only after all frames. Neither is CopyField's
work-word Finish on a mixed stream. UnaryBody copies a complete
$U(a)$ using RD(source); EX(destination); WR(destination,read-bit);
MR(destination); MR(source) for every bit, including its terminal 0. The
RD successor repeats on 1 and returns after those same four remaining
occurrences on 0. Its cost is $5(a+1)$; source returns one cell past the 0
and destination at R. The raw zero-copy calls below mean this graph, with
their explicitly stated source positioning and destination already at R.
All word/field routines may overwrite latch 4; they preserve input latch 5
and private operand/result latches 0–3. Their callers retain no return data
in latch 4 across a positioning call. Each payload RD's bit survives through
its immediately following Append/WR; Finish's later tests may overwrite it.
The channel uses a distinct data latch, as specified in Definition 6.3.

**Definition 3.2 (unary arithmetic graphs).** The following act on actual
newest unary words, with distinct input/output ports. Begin by Last on each
input and New on the output, in that order. Ones($s,d$) is RD($s$,4); on 0
return, on 1 Append($d$,1); MR($s$) and repeat. Its cost is $5a+1$ on the
remaining $a$ ones. A unary output is terminated by Append(0), then Finish.

Add($x,y;z$) executes Ones($x,z$), Ones($y,z$), then that termination.
Sub($x,y;z$), with $y\le x$, repeatedly RD($y$); on 1 RD($x$), require 1,
MR($x$); MR($y$) and repeat; on 0 execute Ones($x,z$), then terminate.
Its body before positioning/Finish uses $4y+1+5(x-y)+1+3$ occurrences.
Compare($x,y$) repeatedly RD($x$), saving its bit in finite control, RD($y$);
if both are 1 perform MR on each and repeat; otherwise return the appropriate
finite-control result less/equal/greater directly from that last RD successor.
Its loop costs $4\min(x,y)+2$, plus its two Last calls. A violated subtraction
precondition returns a distinct public failure edge; lawful callers test it
first. Increment is Add with a constructed literal $U(1)$.

Multiplication is a unary loop over a copied first operand: at each leading 1
append all leading ones of the second operand, resetting it with Last before
that iteration; move the first operand once; on its 0 terminate the output.
The first operand's RD test, all inner terminal tests, every Last, every
Append, the outer MR and the final 0/sep are included. Thus this is an
executable finite recurrence, not a multiplication primitive. Doubling uses
Copy to a second port and Add. In particular $4(J-K)$ is Sub followed by two
such doublings. The constants and every duplicate operand are constructed by
Definition 3.1, including their separators and positioning.

**Definition 3.3 (base, reserve interval and real seek).** Base($a;d$), with
arena $a$ and distinct output work port $d$, executes Home($a$); MR($a$);
New($d$). Repeatedly RD($a$,4); on any non-R symbol Append($d$,1); MR($a$)
and repeat; on R append 0 and Finish($d$). It counts *all* existing ordinary
cells, including delimiters and retired work. If there are $b$ cells its
scan/termination before Finish is $5b+4$. Its boundary tests ignore ordinary
private bit values; they still are actual RD occurrences. The result is the
real $U(b)$ at the newest word on $d$, and the arena head is at R.

Zero($a;k$), with actual $U(k)$, executes Last($k$); Tail($a$), then
RD($k$); on 1 EX($a$); WR($a$,0); MR($a$); MR($k$) and repeat; on 0 exit.
Append one sep to $a$ before return. The zero-fill loop costs $5k+1$; its
following delimiter costs 3. If Base was $b$, exactly the data cells
$[b,b+k)$ are the interval and $b+k$ is its following constructed delimiter.
The interval descriptor consists of actual unary owner, port, base, length,
initialization/mutability bits and construction ordinal copied into the
record that owns it. It is not an atomic allocation result. Standalone
descriptor copies use Definition 3.1 and the native fields/wire-reference distinction in Definition 6.1.

At($a;d$), for actual unary address $U(v)$, executes Last($d$); Home($a$);
MR($a$), then RD($d$); on 1 MR($a$); MR($d$) and repeat; on 0 return at the
arena cell. Its cost is Last($d$) plus $2h_a+3v+3$, where $h_a$ is the actual
initial arena-head distance from L. The addressed cell and the following
delimiter must have been constructed. RD or WR there is an additional
occurrence. All caller address construction and role permutation are separate
displayed calls. None is included a second time in At.

**Definition 3.4 (directory records and finite iteration).** Directory port 0
contains records whose first field is a two-bit tag, followed by the fields
listed below. Each field is a bit word terminated by sep. Each record ends
with a single seal symbol. Concatenation adds no invisible cell.

| Tag | Fields after the tag, in order |
| --- | --- |
| `00`, initial | $\xi,U(H_0),U(b_0),U(L_0),U(16),U(0)$ |
| `01`, reservation | $U(J),U(b),U(d),U(r+1),U(m),U(v),U(f_s)$ |
| `10`, guard raise | $U(J),U(p+1),U(m),U(v),U(f_s)$ |

Here $v$ is the previous complete-directory-record count and $f_s$ is the
already closed start-fence ordinal. The initial final 0 is its construction
ordinal. All record fields are constructed/copies of already actual material.
The representation of $\xi$ is its complete supplied bit string. The record
order, rather than a free pointer register, determines the predecessor. The
native writer alone can append here.

IterateDirectory executes Home(0); MR(0). At each record it reads the two tag
bits with RD; MR per bit, checks its sep with RD; MR, and selects one of the
three finite field counts. Each field is either ReadField into a work role, or SkipField. It checks the seal by RD; MR, then repeats;
at R the testing RD returns. A seal cell is never copied as field data. A
record's tag, field cursor and finite number of remaining fields are finite
control. Record ordinals, if needed, are unary work words incremented by
Definition 3.2 after each seal. No scan bounds itself by the growing meter.
An incomplete tail is ignored by the mathematical committed-prefix relation;
the executable iterator is called only with a complete idle directory or a
previously frozen complete copy. It is never run concurrently with its writer.

WriteRecord executes Tail(0), appends the two literal tag bits and sep, then
for each listed field executes WriteField to directory 0. Its source word
heads end at sep and destination remains at R. Finally EX(0) constructs the
prospective seal cell, WR(0,seal) publishes it, and MR(0) returns to R.
Publication is precisely that one WR, after every field has been written.
The preceding EX, WR and following MR are three distinct runtime cuts. A
partial record grants no source authority. No operation atomically installs
its variable-length fields or writes an unbounded current pointer.
WriteRecord returns at R immediately after MR. A subsequent CloseFence is a
separate CTL-fence/readout graph; neither the seal WR nor this MR is a meter
fence.

**Lemma 3.5 (word/field expansion and termination).** Every lawful invocation
of Definitions 3.1–3.4 has a finite deterministic primitive expansion, including
caller positioning, terminal tests, field delimiters and return edges. At each
unfinished cut it has its specified next occurrence, subject only to a pending
external IN in a caller.

Proof. Home/Tail move toward an existing boundary. Last moves backward across
one finite already completed word and stops at its preceding delimiter or L;
it does not scan newly appended words. Copy and field scans consume a fixed
word/field on a different tape from their destination. Ones and arithmetic
consume fixed finite unary operands. Multiplication has a fixed outer operand
and resets a fixed inner one; it never extends either bound. Base scans a fixed
existing arena before allocation. Zero consumes a distinct already completed
length word. At consumes an already completed address. Directory iteration
consumes a fixed sealed stream and finite field counts. WriteRecord has a fixed
field count and fixed source words, then the three explicitly listed final
occurrences. Role changes are among twelve fixed ports and cost their CTL.
Induction over the finite call nesting proves termination and uniqueness.
Only finitely many EX occurrences can therefore occur. The construction of a
new length or address is part of this induction, not a premise supplying its
bits for free. $\square$

## 4. Stable source addressing and the resident dispatcher

**Definition 4.1 (actual segmented representation).** Put $L(K)=4K-2$.
The initial record and successful reservation records describe an ordered
list of port-16 intervals $(b_a,d_a)$ with $d_a>0$ and
$\sum_a d_a=L(K)$. The first interval is exactly $(b_0,L_0)$ from the original
private ingress. Define, for $0\le i<L(K)$,

$$
\phi_K(i)=b_a+i-\sum_{c<a}d_c
\quad\hbox{when}\quad
\sum_{c<a}d_c\le i<\sum_{c\le a}d_c.
$$

The source invariant says that the bits at these actual cells, in that order,
are preorder tokens of the current $t$, followed by PAD=00 to $2K-1$ tokens.
At a source-write busy cut this is instead the actual raw bit word, without
requiring it to decode to a tree. All physical intervals between source
segments are other actual arena data; none is silently part of the source.

**Definition 4.2 (ReadState and Resolve graphs).** ReadState invokes
IterateDirectory. On the initial record it copies $H_0$ to the current $h,K$
word roles, constructs $U(0)$ for $r,p$ and $U(1)$ for directory count $v$.
It retains the initial base/length only when requested by the caller. On a
reservation it copies $J$ into the current $K$ role and its stored $r+1$ into
the layout role. On a raise it copies $J$ into $h$ and its stored $p+1$ into
the policy role. At every later seal it increments $v$ by the actual unary
graph. All other fields are skipped with SkipField. The field copies are
ReadField into a distinct work port, then a finite role permutation; fields
not needed after a check release their temporary roles. Copies of $H_0$ and
initial identity needed for a row are obtained by another origin scan, never
by a hidden register. The iterator's R exit is this routine's return edge.

Resolve($i$) receives a constructed newest $U(i)$ on its input role, with
$i<L(K)$. Copy it to a remainder role. Execute IterateDirectory from origin.
For the initial record load its base and length; for each reservation load
its base and length; skip raises. For each such interval Compare(remainder,
length). If less, Add(base,remainder;address) and return at the newest word
of the address role. Otherwise Sub(remainder,length;temporary), exchange
the remainder role with that complete result and continue to the next record.
An out-of-range R exit returns `bad-address`, never an arbitrary default cell.
All other fields are consumed/skipped before the next record. The input
ordinal and unfinished directory position are actual words and heads. Early
return is to the fixed caller's next graph edge; the next invocation starts
again with Home(0). It need not restore the directory head to its old position.

**Lemma 4.3 (real address correspondence).** At every completed maintenance
boundary, Resolve($i$) terminates for $i<L(K)$ and returns exactly
$U(\phi_K(i))$. The map $\phi_K$ is injective, disjoint from every allocated
scratch interval, and a successful Reserve extends it without changing any
of its earlier values.

Proof. Each segment was created by Base before Zero at the arena's current R.
It is disjoint from every preceding arena cell; later allocations begin beyond
it and its delimiter. Thus all source intervals are mutually disjoint and
are disjoint from the intervals designated scratch. In Resolve, after skipping
$a$ segments, the remainder is $i-\sum_{c<a}d_c$. If it is less than $d_a$,
the displayed Add returns $b_a$ plus that remainder, the stated formula.
Otherwise the displayed Sub preserves the next remainder equation. Positive
lengths with sum $L(K)$ force the less branch at exactly one segment before
the final R. Lemma 3.5 gives actual termination of every intervening scan and
arithmetic call. Within each segment the formula is injective; different
segments have disjoint images. Appending a new segment changes neither an
old base nor an old partial sum, proving extension. $\square$

**Definition 4.4 (source-reference compiler).** Source templates operate on
the first $L(h)$ logical source bits. Their private packet is exactly the
$h$-packet; the unused $L(K)-L(h)$ bits remain zero. Use PR57.D4–D6's exact
ReadE and whole-modification templates and LJA Definitions 3.1–3.2's literal
minterm template, with parameter $h$. Thus $N=2h-1$; ReadE keeps its original
$h+5$ coefficient width; the whole-candidate parser still compares to $h$.
Every context is completely acquired/validated, even when it will reject.

The native generator distinguishes a source reference $(S,U(i))$ from a
workspace reference $(W,U(a))$. These are finite tags plus constructed unary
data in its frames. Before emitting *each* of the four address fields of a
gate record, it invokes Resolve for an S reference and Copy for a W reference.
An absolute scratch address is Base plus its actual constructed offset, using
Add. A source destination, as well as a source operand, must take the S path.
Constant/dummy and intermediate-result fields take W paths. The four returned
address words and the finite truth-table code are retained until the record
is written; the generator copies them one field at a time through the raw
unary-copy loop, including each terminal zero. Its code tape is literally

$$
1\;f_0\cdots f_7\;U(d)U(a)U(b)U(c)
$$

per gate, then a terminal 0 header. Every bit is appended by EX; WR; MR;
every copied bit has the source RD and MR too. Source-reference tags are
generator data, not new runtime memory instructions. The generated tape
contains only actual absolute addresses and runs on the unchanged PR57
interpreter, including full field caching, seeks, BF and destination WR.
Generation invokes no private-source test. The generator's local finite
continuation returns from Resolve to the saved field number; variable
expression frames remain constructed PR57 stack data. No current-source
instruction reuses a gate tape from a previous call or previous guard.

**Theorem 4.5 (gate and raw-source refinement).** For every current invariant
state, each admitted original source call has exactly its $F_h$ response and
decoded source successor. This includes ReadE's original coefficient encoding,
every finite literal address, every whole context and each executed reject.
At every source gate boundary, the logical source and workspace operands and
destinations correspond to the actual cells through $\phi_K$ and their real
workspace descriptors. This correspondence also holds while the source word
is temporarily invalid.

Proof. Since $\lambda(t)\le h$, the first $L(h)$ logical bits are exactly the
canonical $h$-packet; all following bits are PAD. Lemma 4.3 supplies a distinct
actual source cell for each of those bits and no workspace alias. Induct over
the ordered generated gate records. Each S operand loads its corresponding
logical bit; each W operand loads the same initial constant or earlier
computed workspace bit. The same finite truth table therefore produces the
same result. A W destination updates the corresponding workspace cell, and
an S destination updates exactly its logical source bit. No gate-boundary
step requires the current raw source word to parse. This proves the induction
through every one of the supplier's in-place MUX writes.

The unchanged supplier template proof now applies to this logical packet.
Whole-candidate acceptance is exactly $\lambda(c)\le h$. If accepted, $c$
fits the first $L(h)$ bits; if rejected every MUX reinstates its old bit.
All higher logical source bits remain zero. ReadE and TagRead have no source
destinations. The minterm table enumerates $4^{2h-1}$ packets, with exactly
one equal to this valid logical packet, and therefore returns its literal
reply by LJA3.3. The original ReadE uses exactly the old width and recurrences,
so no new overflow or coefficient conversion premise arises. At completion
the full $K$-packet again represents the stated successor. Fetch, address
cache, seek and latch cuts between these gate boundaries are genuine actual
states of the unchanged interpreter; the theorem does not identify their
head positions, code lengths or clocks with a contiguous legacy execution.
For equal public history, command and directory layout, the added scans and
address construction have equal public traces independently of source bits.
The inherited private gates never branch or seek on their operands, and
Base tests only the boundary symbol. Thus the only newly acquired
source-dependent value at response release is still the permitted complete
original response, by the suppliers' noninterference argument. Full private
histories retain their actual differing bit values.
$\square$

**Definition 4.6 (resident admission and return).** The native graph installed
at boot has the following dispatch cycle. At its nonterminal idle boundary
all twelve workspace tokens have returned to the producer and the source
service token has returned to the dispatcher. An actor-local computation
or partial token transfer is its own actual phase, not this idle boundary.
At idle it acquires and seals one
canonical complete frame on port 13, parses it, retains its return kind and
command, and takes the source-availability token into the selected service.
It executes ReadState before generation or maintenance. Old source tags go
to Definition 4.4, then the response/counter/semantic-row routines below.
Maintenance tags go to Definition 5.1. Local controller and terminal markers
go to their inherited actually executed code/complete-output routines.
Every route then goes to the unified row/delivery routine of §6, its actual
acknowledgement, TOK returning the source-service token to the dispatcher,
one CTL restoring the idle phase, and the same controller's
saved return edge. A raw external-frame mode instead returns to its next
frame IN. A global-terminal route finishes its row/delivery and actual ACK, and the
requested stop-snapshot/verification/consumer work of §6, before its halt
CTL. A verifier refusal completes that route with no task output. Source calls use CloseFence(`source-start`) before generation and
CloseFence(`response-commit`) after release; NativeLocal and Halt use the
same start/commit pair around their complete marker/output commitment.
These replace, rather than duplicate, any inherited designated fence sites.
They have no directory publication and use `no-publication` in the row.
The complete old/new $q,g,e,j,m$ words are staged before their roles are
reused. At commitment an original source call advances $q$, an accepted
modification $g$, and an accepted Rho $e$. Every source call, NativeLocal and
Halt advances $j$ once, exactly as in LJA4.2–4.3. Local/terminal markers
preserve $q,g,e$; maintenance preserves $q,g,e,j$. Each of these completed
events advances $m$ once. Prepare the required incremented unary versions
before commitment; the committed response and actual phase select them by
paid copying/AppendCounter afterward. A row seal materializes an already
committed event and does not increment it again. Every nonmaintenance route
writes its semantic row and index before its unified row and index, as in
Definition 6.2a. Fence-count $f$ is separate from all these counts.

The same boot installs the auxiliary `journal` call-kind. A source-free
caller reaches that fixed entry through its actually installed public code
with the retained query of Definition 6.2a; it is not an additional raw-frame
tag or a scheduler choice. At acknowledged idle the producer's entry CTL
reserves admission and its TOK holds the source-service token busy before
the actor workspace loan and query channel. The query parser, row/prefix
service, reply checks and final ACK return this call-kind's saved continuation
through source-token TOK and idle CTL. It takes no event-row join. The
producer's local frozen-prefix entry uses its already held phase/token and
returns to that frozen continuation. Neither entry grants any legacy graph
new control or permission, and neither is enabled at an arbitrary busy cut.

The three-bit original frame tags remain ReadE `000`, Rho `001`, TagRead
`010`, Left `011`, Right `100`. Reserve is `101` and Raise is `110`.
Their payload is precisely $U(J)$; their length is the actually supplied
$U(J+1)$ in the common framing `tag; U(length); payload`. Thus the canonical
maintenance frame is $tag\;U(J+1)\;U(J)$, for every $J\ge0$; inadmissible
*values* are paid maintenance refusals, not malformed encodings. In automatic
mode the same complete command block is constructed by literal Append and
word-copy routines from computed public words, with no external IN for those
computed bits. This mode is a boot-installed public choice.

Header supply has three unrolled IN; EX; WR; MR bodies. Unary length supply
uses IN; EX; WR; RD(test); MR per bit, the RD selecting whether MR returns
to IN or goes to length seal. Zero-reserve the payload using its completed
length, position it with At, and run AIF's five-row payload graph: RD(length),
IN, WR, MR(payload), MR(length), with its terminal RD(0). The just-consumed
bit in latch 5 survives until WR. All length/descriptor setup uses
Definitions 3.1–3.3, with bases measured before append; nothing assumes empty
ports on a later call. Retain each header, length and payload block and its
actual descriptor. Public parsing scans the complete retained frame. Original
context conversion uses the supplied prefix parser and token converter;
maintenance checks payload equality with its canonical unary length/value.

The physical header, length and payload are three successive blocks on 13,
with Base measured before each. After the header's third bit append sep and
one zero status bit, construct its descriptor, At its status and WR(1), then
CTL seal. Its length is the constructed literal 3. After the length word's
terminal 0 perform the same sep/status construction, measure its actual
length by the sep-bounded scan, and seal it by At; WR(1); CTL. Copy its
complete unary payload-length value into a work word by At at its saved
base, the zero-copy body and Finish; this is the payload loop's counter.
Base before Zero on 13 supplies the payload's real base. Zero constructs
its $d$ bits and sep; Append(0) constructs its status. Before the first
payload test execute At(13,payload-base) and Last(counter). After the
terminal test execute At(13,status); WR(1); CTL seal. Every status address
is the constructed base+length+1. Their descriptors are the sep-delimited native records of Definition 6.1
on producer block descriptions 17; encoded references in a wire field use
that definition's separate bit-tuple codec. Their separate physical
separators/status bits are not wire-input bits: the chronological wire
frame is exactly the header bits, length bits and payload bits referred to
by those three descriptors. Automatic commands construct the same three
blocks by Append/copy instead of IN, including the same actual status and
descriptor work. This fixes setup and entry positions even on nonempty
port 13 and leaves every acquired-but-unwritten input cut distinct.
Construct the complete request-reference word as $U(k)$ followed by Frame of
each complete block reference: header, length, payload, then any additional
canonical context blocks in order. Its actual count is three plus that
explicit finite list's count, constructed by unary increment during the
retained-list scan. New, UnaryBody, Frame per reference and Finish build
this word; stage it as a complete public block if later work needs its role.
In the original canonical context language the context is already in the
payload, so there are no additional context blocks. The request tuple
therefore neither supplies a larger snapshot nor substitutes a name for
an unacquired payload.

At every physically prescribed IN both supplied bits execute IN and its
receipt/control successor. Canonical-prefix admissibility is only the task
domain restriction. A completed malformed frame enters `frame-fault` with
its retained bits, no source permission and no executed source call. An
unterminated raw unary length remains in actual ingress. A noncanonical bit
is never changed into an unexecuted `none`.

**Lemma 4.7 (installed control, input and return path).** With the boot of
Definition 2.4, every complete canonical frame reaches exactly its selected
service and returns by Definition 4.6 after complete recording/delivery,
provided the reached controller computations and external supplies terminate.
No allocation or descriptor construction grants that route to a legacy graph
without these installed branches.

Proof. The finite header recognizer has a distinct prescribed successor for
each of the seven tags. The supplied length word bounds the explicit payload
loop and its setup; the finite parser determines the selected complete
command. Each branch is an actual inlined graph with the single stated row
and acknowledgement join. Lemma 3.5 terminates the new setup and directory
calls; the reused generator, source and old row services terminate on finite
data by PR57.L1–L4. The field/descriptor and actual fence graphs of Lemma 6.1b and the
complete row/channel/ACK composition of Lemma 6.7 terminate and have that
join as their fixed exit, on every selected branch. The final source-token TOK and idle CTL return to the retained
caller kind; maintenance has not changed the actor's stored continuation or
table. At an unfinished input bit the IN/WR distinction and its successors
are exactly the displayed graph. There is consequently a real route into,
through and out of maintenance, rather than only a copy invariant. Conversely
the transition relation of a closed graph has only its installed edges;
allocating a data word does not add a new control successor. $\square$

## 5. Reservation and explicit guard publication

**Definition 5.1 (complete maintenance graphs).** At entry the command $U(J)$
is retained, the source token is held busy, ReadState has materialized
$h,K,r,p,v$, and $q,g,e,j,m$ are accessible through their complete
counter descriptors. Counter lookup is an origin/ordinal scan of their
immutable versions followed by the supplied complete unary copy; it never
treats an ordinal as a primitive address. The suspended actor continuation
and old archive permissions are untouched. Run CloseFence(`maintenance-start`)
once here, before the branch tests. Retain its complete staged reference and
its constructed fence-count component $U(f_s)$ for either maintenance kind.

For Reserve, Compare($J,K$) selects greater/equal/less. In the greater branch:
Sub and two doublings construct $d=4(J-K)$; increment $r$ and $v$ into prepared
new words; reload the already acquired $U(f_s)$; Base(16) constructs $b$; Zero(16;$d$) creates the interval
and its delimiter. Copy all seven reservation fields into work words, one at
a time as needed; construct the response fields `reserve-ok`, old $K$, $J$,
and new layout ordinal. The fields containing $m$ refer to the completed
pre-operation all-event count. WriteRecord(`01`) appends the complete entry
and publishes it at its seal WR. After its final MR execute
CloseFence(`post-directory-publication`) bound to the new count $v+1$ and
retain its complete reference $f_d$. Its source-service token remains busy.
Construct/seal the finite response block, release its response token by CTL,
and run CloseFence(`response-commit`), retaining its complete reference. The prepared $m+1$ version
is now selected by paid copying/descriptor work. Go to the §6 maintenance
row routine. In the equal and less branches allocate no source segment and
append no directory record: prepare the typed `unchanged` or
`maintenance-refusal` response with the old/current values, commit it, advance
only $m$, and use the identical row/delivery/return route.

For Raise, Compare($J,h$), then Compare($J,K$), selects exactly $h<J\le K$.
In that branch increment $p,v$, reload the acquired $U(f_s)$, construct the
five raise fields and response `raise-ok`, old $h$, $J$, new policy ordinal,
then WriteRecord(`10`), its final MR and
CloseFence(`post-directory-publication`) with the new count. No source cell
is a WR destination. Commit response, run CloseFence(`response-commit`), select $m+1$, and go to the same row route. Equality with $h$
returns `unchanged`; $J<h$ or $J>K$ returns `maintenance-refusal`, with no
directory record. Failure/equality branches use that same entry start reference and run
CloseFence after their own response release, retaining both actual references;
they write
`no-publication` and never borrow either reference as a publication fence. Every invocation prepares both old and required incremented
counter versions before selecting them, as in LJA4.2. Directory count and
$r,p$ at an activated but not-yet-row-sealed cut are determined by the actual
directory prefix and phase; their later wire copies are not atomic counters.

Directory publication and response commitment are different boundaries.
After the seal WR the new binding/guard is authoritative, but a new source
call is still unavailable. The following MR, response sealing/release, closed
fence scans, row writing, channel phases and acknowledgement are all real
states. Before publication, staged allocation/metadata has no current-source
authority. Only after acknowledgement does the dispatcher restore source
admission. A row's manifest payload and complete publication-fence reference are
serialized only after their construction. The latter names its actual
post-publication CTL-fence, not the directory seal WR. All three closed
fence readouts and their staging/descriptor work precede row serialization.
The no-change/refusal branches retain their unchanged complete manifest.
No field predicts its own future completion ordinal.

**Theorem 5.2 (paid source-specific reserve).** From every reached idle valid
state and every actual finite $J>K$, the installed Reserve($J$) has a unique
finite continuation to an idle state whose source is the very same $t$ on
the very same preparation occurrence $\xi$, represented with reserve $J$.
It preserves $h,q,g,e$, the encoded controller continuation, acquired seed
and input, all old archive bytes and permissions. It extends $\phi_K$ on its
whole domain and changes the actual current backing by the fresh segment.

Proof. The command and old state are already materialized finite words.
Lemma 3.5 terminates each arithmetic, base and zero-fill invocation. After
$z$ zero-fill iterations the old arena cells are unchanged and the first
$z$ cells of the new interval are actual constructed zeros. Its fixed bound
$d$ was sealed before the loop and is on another port, so neither arena
extension nor meter growth changes it. At $z=d$ the interval has the claimed
length, zeros and following delimiter, and does not alias any old source,
scratch or archive cell. Metadata writing reads only actual public words;
before its final seal it has no committed-entry status.

At publication, concatenation of the old source bits with these $d$ zeros
is its old preorder code followed by $d/2=2(J-K)$ extra PAD tokens. Its length
is $L(K)+d=L(J)$, so it is exactly the $J$-packet of the same ordered $t$.
The predecessor and source occurrence are fixed by the actual directory
chain starting at its original entry. Lemma 4.3 proves stable address extension.
No new private preparation IN, source reset or representative selection has
occurred. Base's boundary-only arena scan is paid RD work, but its ordinary
bit values neither select a branch nor become new source material.

Publication has changed only source layout and its ordinal. It has changed
neither a source-call counter nor an accepted-update or rho epoch. The actor
table, workspace, seed, consumed input and previous archive intervals lie
outside the newly allocated interval and directory append. Their old payload
bits, owners and seals are untouched. Protected controller heads are unchanged;
archive/checking heads move only by their actual declared service work.
The new response and row/copy work terminate
by Lemmas 6.1b and 6.7, including construction/readout of the new
post-publication CTL-fence, complete manifest transport, final row ACK,
source-token TOK and idle CTL. They restore the prescribed saved return edge.
They add genuine receipts and
history; they do not establish equality of complete pre/post states. This
joint invariant proves a continuing operation on the installed original
source, not a fresh per-capacity installation. $\square$

**Theorem 5.3 (guard and old-domain preservation).** At a fixed guard $h$,
arbitrary finite interleavings of Reserve with original calls have exactly
the $F_h$ source-event responses and source successors, on the same initial
occurrence. Raise preserves the current tree and original occurrence but
changes the future task to the explicitly announced $F_J$. It cannot in
general be projected away from historical guard meaning.

Proof. Theorem 5.2 preserves the relation $\lambda(t)\le h\le K$ and source
value across Reserve. Theorem 4.5 supplies exactly each next $F_h$ call and
successor, including every rejected attempt. Induction on the interleaving
proves the first assertion. Raise writes no source cell, and $J\ge h$
preserves the source-domain condition. Its sealed entry changes the parameter
subsequently read by ReadState and hence the whole-candidate guard.

The exact common-action criterion and its nonintertwining boundary are already
TMC30 subsection 30.4's distinction: reads depend on the same $t$, while a
candidate in $(h,J]$ changes reject to accept. This volume uses that supplied
fact; it does not count a new wrapper proof. For the actual continuing
instrument, start at beta with $h=K=1$, execute and retain a rejected Rho,
Reserve(2), Raise(2), then Rho. The first event remains a reject on beta; the
last accepts $\langle\beta,\alpha\rangle$. Both are reached lawful calls of
this installed graph. A verifier using the newest guard for both calls would
change the first event. The typed guard history in §6 prevents precisely that
change. Once a source exceeds an old guard, truncating its packet is not a
total restriction back to that old source domain. $\square$

## 6. Complete counters, rows, channels and consumers

**Definition 6.1 (one metadata codec and its bit transport).** Native
metadata fields are arbitrary finite bit words, including the empty word.
Their physical encoding is $D(w)=w\mathsf{sep}$. A native record is a fixed
finite kind tag encoded as one such field, its kind's fixed number of $D$
fields, then one seal symbol. There is no separator between the last field's
sep and that seal. A directory tag selects its arity in Definition 3.4;
a counter name selects its one value field. Every new bit-block descriptor has the same
fixed tag `00` and ten fields, in this order:

$$
U(\mathrm{owner}),U(\mathrm{port}),U(b),U(\ell),U(c),
\mathrm{type},\mathrm{initialized},\mathrm{mutable},U(a_{\rm status}),
\mathrm{origin}.
$$

Here owner means the stable descriptor/allocation steward. For an immutable
archive it is its payload owner; for a mailbox the current read-token holder
can change by the explicit TOK while the creation steward/reference stays
fixed. No such handoff grants access to the steward's private descriptor
stream: the channel already carries the actual base/length/status words.
Initialization records actual written cells; mutable is the post-seal
mutability flag. Construction writes while a payload is unavailable remain
permitted; mutable=0 forbids later writes after its complete seal.
Here $c$ is the one-based ordinal of this descriptor in its owner's
append-only descriptor stream, $b,\ell$ are actual payload base/length,
and $a_{\rm status}=b+\ell+1$ for a bit block with following sep/status.
The origin field is empty for an original block and is the complete encoded
sender reference for a received copy. Empty origin is data, not a missing
field. Types and flags have fixed finite encodings. Source intervals have
the separate mutable-interval type and their directory seal reference;
they do not acquire a bit-block status cell or become immutable archives.
Descriptor streams themselves are accessed from L and do not need a
descriptor of their own.

WriteDescriptor counts the complete existing stream's seals by paid unary
increment, prepares $c=1+\text{count}$, executes Tail, literal tag/sep Appends,
ten WriteFields, then EX; WR(seal); MR. Before Tail starts, all ten source
field words are complete on ten distinct roles. Their creation/count scan
uses the other two roles; count-only scanning skips fields and needs only
its count, increment temporary and literal-one roles, one of which is the
creation field itself. No field is fetched through the descriptor stream
while its new record is unfinished. Fixed flags/owner/port/type words are
literally constructed before this append. After the payload copy, a staged
bit block's original source word can be released; its actual base/length
words and constructed zero status remain. The descriptor preparation then
reuses the remaining roles. On return, no more than the caller's needed
base/length/status/origin words remain live; other fields may be reloaded.
For channels, retain mailbox base/status while preparing the receiver's ten
fields, at most twelve roles; reload the sender base from its now-complete
descriptor afterward. Thus no thirteen-word simultaneous state or scan of
a growing descriptor tail is implicit. ReadDescriptor takes a complete
requested ordinal and one fixed field-number (or the finite `count-only`
kind). It starts Home; MR with constructed ordinal zero. Read/check the
next tag (its first RD also detects terminal R). For each actual record
Increment prepares the next ordinal and Compare determines whether this is
the requested record. Use ReadField only for the one
requested field of that record and SkipField for every other field, then
check seal by RD; MR. Only that verified seal permits its copied field's
selection/return. Other fields of the same descriptor are obtained by
repeating this origin scan, never by retaining ten simultaneous word roles.
The count-only kind skips all fields and returns its actual final count.
At terminal RD(R) a field request returns
`no-block` if no such ordinal existed. Wrong kinds and missing seals have distinct metadata-fault edges at the
corresponding tag/seal RD; no incomplete record becomes selected. FieldBody
and SkipField have the stated valid-bit-field precondition. All active
metadata writers preserve it; no arbitrary-symbol metadata import is added. To count for append, use this
same scan with all fields skipped. These scans include all earlier complete records;
no operation uses an ordinal as a head position.

For staging across a call, use fixed finite block types `old-h`, `old-K`,
`old-r`, `old-p`, `old-v`, `old-q`, `old-g`, `old-e`, `old-j`, `old-m`,
`old-semantic-last`, `old-unified-last`, `current-semantic-row`,
and the finite start/publication/response/boot fence kinds. They are complete
ordinary blocks on 21 described on 17. LatestType(type) is Home; MR on the
complete descriptor stream, with an actual zero ordinal: for each record
check tag, increment ordinal, ReadField only its type, SkipField its other
nine fields, check seal by RD; MR; compare that complete type word and on
match Copy the actual ordinal into a selected role plus its CTL exchange.
At terminal RD(R) return the last match or typed `no-block`. Reload a staged
word by that selected ordinal, the individual descriptor field scans, At
and the complete length-bounded copy to a word role. These are paid scans,
not a named-register or pointer lookup instruction. Before each operation,
load/stage every required counter/directory before-field in this fixed order.
Last-reference and current-row types are constructed at their index/row
steps in Definition 6.2a. If ReadState
produces five words, retain only the field being staged and release the
other four; an additional origin ReadState obtains the next one. After
staging, reload only the words currently needed by the arithmetic/record
writer. No old field is inferred from the new guard or reserve.

Serial admission ensures that until this row is complete no later operation
can replace these latest old-field types. CloseFence staging uses its own
distinct types and therefore preserves them. A new operation may append its
own versions only after the preceding ACK/return. Old payloads and their
ordinary references remain immutable. The staging writer reads/copies its
input word and constructs its payload/length first; that word and unrelated
caller roles can then be released before its ten descriptor fields are
prepared. This fixes caller live roles and persistence without scanning
an unfinished descriptor or requiring an unbounded native call stack.

A wire block reference is the fixed-arity bit tuple of owner, descriptor
stream port, $c$, payload port, $b,\ell$, type and status-cell address. Each
component is encoded by Frame below. Its bytes are constructed from the
actual descriptor fields. Resolving it first loads that owner's complete
descriptor by origin/ordinal scan and compares every component, type and
availability, one descriptor component per origin scan. The owner's
payload can then be read by At and its complete
length. A reference to another owner is resolved at a receiver only by
scanning the receiver's own descriptor stream for its equal origin field;
the selected *local* descriptor supplies the local port/base/length.
There is no cross-owner pointer dereference. More than one acquired copy
may exist; this scan selects the first sealed matching copy, whose immutable
payload is equal. To find it, construct ordinal 1 and request that ordinal's
origin field, compare it, then load/check its local type/port/status fields
one at a time. A failed match/availability test increments that ordinal and
restarts the scan; `no-block` terminates the search. Every bound is the fixed
complete local descriptor prefix, not a live destination under construction. A search with no matching acquired copy returns `not-acquired`.
Before copying, the installed receiver-side allocation graph writes its own
receiver descriptor, copying the complete sender reference as origin; its native record seal does not make the still
zero-status receiver payload available. The final payload CTL/TOK does. A mailbox descriptor likewise retains the
original sender reference, rather than replacing it by a different payload
identity; the mailbox-to-receiver copy preserves that original origin key.
All comparisons are complete word comparisons and all local status reads
are actual At; RD occurrences. Existing token ownership supplies the
permission test; knowing the encoded reference supplies no token.

For counters reserve producer port 23. Names `000,001,010,011,100,101`
denote $q,g,e,j,m,f$, where $f$ is PR57.D3's paid fence count. Boot writes
one $U(0)$ record for each. Their native format is name, sep, $U(n)$, sep,
seal. LoadCounter starts Home; MR. At each record it reads three name bits
with RD; MR per bit and checks sep with RD; MR. A matching value uses
ReadField into a fresh work role; a nonmatch uses SkipField. **Both
enter the following RD at the seal**, then MR crosses it. Only after this
seal check does a matching branch execute its CTL role exchange. Continue
to terminal RD(R), returning the last sealed match, or typed `no-counter`.
Thus first, latest and repeated versions have one contract. AppendCounter
uses Tail, literal name/sep Appends, WriteField of the actual unary value,
then EX; WR(seal); MR. During a counter append the effective value is the
prepared old/new word selected by the actual service phase, as in LJA4.2;
a partial append is not an idle bank. The six fixed names are always present
on a valid boot. Every inherited $q,g,e,j$ access/update and every new
$m,f$ access/update uses these LoadCounter/AppendCounter graphs, preserving
the inherited old/new phase rule. There is no independently updated shadow
bank. Counter values are complete unary words; arbitrary empty
fields remain legal in the other metadata schemas.

The bit transport encoding of a field is $B(w)=U(|w|)w$, called Frame($w$).
It has $2|w|+1$ bits and contains **no** sep. Frame enters with its destination
at R. Last(input), New(length), then RD(input); on a bit Append(length,1);
MR(input) and repeat; on sep Append(length,0); Finish(length). Last(input)
repositions the payload. Last(length), UnaryBody(length,destination) copies
the complete length including its zero. FieldBody(input,destination) copies
the payload, leaving input on sep and destination at R. No New or Finish is
performed on the destination inside Frame. A tuple of frames becomes one
work word only when its caller executes its final Finish; a bit-block writer
instead appends its own sep/status. A native descriptor writer always uses
WriteField, never adjacent Frames. A reference *inside* one native field
is a bit tuple and is decoded as such after ReadField has acquired it.

For complete finite bit-block parsing, position its payload with At and
Last on an actual $U(B)$ budget, one 1 for each payload bit. BudgetBit is
RD(budget); on 0 return `short-block`; otherwise RD(source,4) on the typed bit payload,
MR(source); MR(budget). It costs four occurrences per consumed bit, returns
that bit in latch 4, and never touches the physical sep/status. The testing
latch is distinct from 4. ReadUnary copies successive BudgetBits with Append
to a fresh word through and including the first 0, then Finish. Its finite
branch on each copied bit is retained in control across Append.

ReadFrame first ReadUnary's its length into a temporary word. It then New's
an output, Last's that length and repeats RD(length); on 1 BudgetBit;
Append(output,bit); MR(length), on 0 Finish(output) and return. The source
is now immediately after exactly this field's payload and the budget head
has advanced by $2|w|+1$ positions. The output is the exact field $w$, even
when empty. Tuple parsing invokes this graph at the fixed arity; the final
RD(budget) must be 0 and RD(source) must be sep. A manifest has the explicit
finite record count below instead of a fixed outer arity. Missing terminators,
length overruns and extra payload set structural failure on the detecting
paid test. The owner retains/scans the remaining bounded payload on a failure
edge before refusing; it never reads beyond its constructed status boundary.
These bounds also apply to nested reference and receipt tuples.

Word equality executes Last on two distinct word ports. Repeatedly RD(first),
save its symbol in finite control, RD(second); unequal symbols clear a finite
flag. If both are sep, return the flag. Otherwise MR on each non-sep head
and repeat; a sep head stays there. Hence mismatches, unequal lengths and
empty words all receive a complete finite scan. A field in an immutable block
is acquired by its checked descriptor, At, the length/budget-driven RD;
Append; MR bodies, then Finish, before further Frame/ReadField use. No bit
framing is silently converted into native delimiters.

**Definition 6.1a (actual closed fences).** All meter-fence sites in this
installed graph, including inherited source start/response sites, use the
following CloseFence graph. All other CTLs, including record and payload
seals, append ordinary receipts unless this graph explicitly says fence.
LoadCounter($f$), Increment into a distinct complete word, then execute one
**CTL-fence**. Its receipt is the next actual $\mathsf F$. AppendCounter
selects that prepared fence-count version before readout. Between that CTL
and the completed version the prepared word and phase retain the count;
no other fence site or source request is callable. Readout itself creates
only ordinary receipts. This is the supplier's fence counter made explicit,
not an extra primitive or a free counter update.

Execute Home(meter read head); MR. Construct a fresh bound word and a
separate $U(0)$ visited-fence word. For every receipt RD(meter); append one
1 to the bound. On an F, Increment the visited-fence word and Compare it
with the constructed target $U(f)$; on equality terminate at that receipt,
otherwise MR(meter) and repeat. On an ordinary receipt MR and repeat.
The finite F/equality branch is retained across its Append operations.
Append 0 and Finish(bound). The target fence already existed before this
scan; no readout goes to the live meter R. The bound is exactly $U(n_f)$,
where $n_f$ counts all receipts through that actual CTL-fence, inclusively.
The target $U(f)$ and the event ordinal $U(n_f)$ have different meanings.

Now run PR57.D3's second scan at Home(meter); MR, Last(bound), with fresh
tick and fee destinations at R. Its displayed $13n_f+7$ body constructs
$U(n_f),U(2n_f)$, including terminal zeros; Finish their work words. Construct
the bit tuple Frame(kind), Frame($U(f)$), Frame($U(n_f)$), Frame($U(2n_f)$),
Frame(source occurrence), Frame(event/directory binding), with actual word
copies. The last binding is exactly $B(U(m))B(U(v))$, built by two Frames
and Finish from the old event ordinal and the declared cut's directory count.
Start uses the before count; publication and response use the after count;
boot uses event ordinal zero and initial count one. All these are actual
prepared words or complete-record loads. The complete fence-reference word includes all these constructed numerals.
Copy it to one ordinary immutable public block on 21, with its native
descriptor on 17, before another caller reuses the word roles. After its
payload/length copy the temporary tick/fee/tuple word roles can be released;
the descriptor's ten-field preparation is the preceding bounded convention.
The returned handle reloads that complete tuple, including both numeral
payloads; no additional separate numeral-block handles are promised. Staging uses Base,
FieldBody, sep/status construction, status Add/At; WR(1); CTL and
WriteDescriptor, exactly as the row bit-block graph below. These staging
seals are ordinary CTLs. The producer owns the blocks and can reload them
by ReadDescriptor and bounded copy. Delivery of their reference bits inside
a row acquires those bits for the receiver; it grants no meter/private read.
No OUT is required for these internal references.

For a directory operation enter CloseFence(`post-directory-publication`)
immediately after WriteRecord's final MR; its paid counter preparation
precedes its actual CTL-fence, while source service is still busy.
Its binding contains $\xi,m$ and the new complete directory count. It certifies
that closed post-publication cut, **not** the earlier seal WR receipt.
The start fence precedes branch-specific allocation/publication; the response fence follows the
actual response-release CTL. Their kind tags and bindings distinguish them.
For refusal/unchanged or a source/local event there is no new directory
publication: the row writes the literal `no-publication` and performs no
publication-fence call. The boot publication uses its own initial kind.

**Lemma 6.1b (field, counter, reference and fence composition).** For all
finite valid field words and finite complete records, the preceding writers
and readers are inverse on their payloads and have the stated head/latch
exits. Every current caller obtains its fields and fence words by finite
actual occurrences. This includes empty fields, first/latest/multiple records,
all maintenance branches, row transport, verification and receipt consumption.

Proof. Induct on a word's bit length. At zero FieldBody's terminal RD sees
sep; WriteField adds exactly that one destination sep. CopyField's Finish
moves only its distinct destination, and ReadField's final MR crosses the
source sep. At a successor, RD reads exactly the next bit, its three Append
occurrences write that bit, and the source MR reduces the remaining length.
SkipField crosses the same final sep. Thus record induction reaches each
next field and finally the seal, including adjacent empty fields. The seal
RD precedes every selected-record role exchange. Induction over complete
records therefore proves last-sealed counter selection and ordinal descriptor
selection without shifting the seal test or scanning a bit tuple as a field.

For Frame, the first scan constructs exactly one length 1 per source bit;
UnaryBody writes its terminating 0 too. BudgetBit advances one input and
one bound position. Induction on the decoded length gives exact ReadFrame
payload and budget consumption; the zero case consumes the length 0 and
no payload. Induction on tuple arity, then on manifest record count, proves
complete decoding and detection of under/over-lengths. Fixed port cases,
finite kind arities and the explicit bit tests are native finite control.
A copied reference is compared with a complete local descriptor/origin;
At then receives its actual local base, never the remote printed base.

Finally, induct on completed CloseFence calls: there are exactly $f$ F
receipts and the selected/prepared counter is $U(f)$. Its next CTL creates
exactly the next F. The read head reaches that pre-existing finite marker
in finitely many visits; new ordinary receipts are after it. The bound and
second scan count exactly its $n_f,2n_f$. Serialization/staging copies these
actual words, not an ordinal inferred from a future WR. Their typed bindings
have already been written when used by the row writer. Each listed caller
uses precisely these exits or the separately stated raw unary/gate-code
contract. All loops have fixed finite existing source/budget bounds. This
proves finite expansion and the producer/reader correspondence, not an
assumed certificate for an otherwise missing service. $\square$

**Definition 6.2 (row language and producer writer).** Every completed event
has one unified producer row of version `SEG-U1`, with eighteen Frame fields
in the following order:
model/version; source occurrence $\xi$; initial $H_0$/prior reference; old
all-event ordinal $m$; predecessor unified-row reference; event kind;
complete retained request reference; complete response; before/after $h,K$;
before/after layout and policy ordinals; before/after $q,g,e,j$;
before/after committed-directory counts; complete after-directory manifest;
start and response-commit fence references;
post-directory-publication fence reference or the finite tag `no-publication`; original
semantic-row reference or `no-semantic-row`; template/controller identity.
Tuple arities and kind tags are fixed finite values; all fields use Frame.
An optional reference field is the one-bit 0 for its none tag, or 1 followed
by its complete encoded reference. This fixes `no-publication`,
`no-semantic-row` and `no-predecessor` without treating an empty field as none.
Fence-reference payloads are the six-field tuples of Definition 6.1a;
compound before/after fields use nested Frames at their stated fixed arity.
In particular the $h,K$ field has four components (before $h,K$, after
$h,K$), the layout/policy field has four, the $q,g,e,j$ field has eight,
and the directory-count field has two. The semantic $q,g,e$ field below
has six, obtained by omitting $j$ from those same before/after groups.
Context/name/address material and every request frame are copied or referred
to by their complete actually retained descriptors. A reject row has reject
and no rejected candidate payload. A maintenance refusal has its own kind.
NativeLocal and Halt retain their inherited executed-instruction/output types.

There is a semantic row for every original source call, NativeLocal and
Halt, with the inherited event count $j$; Definition 6.2a specifies its
versioned physical representation and its relation to LJA's row language.
Unified maintenance rows have `no-semantic-row`, preserve $q,g,e,j$, and
advance only $m$. A local/terminal marker advances $j,m$ and preserves
$q,g,e$. Every source call advances $q,j,m$, with $g,e$ determined by its
original accept/reject case. Neither copying nor either row seal counts as
another event. No previously sealed row is edited or retyped.
A source response enters the pending-event component at its release, and
unified row seal later transfers it to the sealed unified archive component.
An activated directory entry before response release is actual maintenance
work, not a fabricated old source event. A manifest contains no private
source bits and does not turn a mutable interval into a frozen snapshot.

The manifest is one finite bit word

$$
M_v=U(v)\;\prod_{a=1}^{v}
 \bigl(B(\mathrm{tag}_a)B(w_{a,1})\cdots B(w_{a,k(\mathrm{tag}_a)})\bigr),
\qquad k(00)=6,\ k(01)=7,\ k(10)=5.
$$

BuildManifest($v$) uses a free work-word destination and New, then Last and
UnaryBody to copy the actual $U(v)$ prefix. Execute Home(0); MR. For each
record ReadField copies its tag into another work word; its finite two-bit
test (RD; MR; RD; MR; RD(sep))
selects the arity. Frame that tag to the manifest destination. For each
remaining field ReadField into a temporary word, then Frame it to the same
manifest destination at R. Check seal with RD; MR and increment a separate
actual record-count word. At terminal RD(R), Compare that count with $v$,
then Finish the manifest work word. The directory head is never moved by
Frame's word/length scans, whose ports are distinct. There is no copy of
seal symbols into a bit field. This works from the initial record onward,
with arbitrary finite identity fields and all repeated maintenance records.
The completed word is Frame-copied into the row's manifest field and its
work role can then be released. Boot uses the same graph for $M_1$.

The row transports this payload, not just $U(v)$ or a producer-only handle.
Its before manifest is the previously acquired row's after manifest, or the
acquired boot binding for the first row. A refusal, unchanged request,
source call or local/terminal marker supplies the identical $M_v$; a strict
Reserve or Raise supplies $M_{v+1}$. The complete producer row channel thus
also copies every active base/length and directory start-fence field.
Snapshots need no extra private directory port: their rows contain these
payloads. The producer constructs each manifest on this same run and pays
for every scan, field copy, length construction and Frame. No delivery cost
is assigned merely to its count.

To write a row, first Base(14) records its real beginning. Its fields are
constructed and appended by Definition 6.1 in the displayed order. Append
sep, then append one zero bit as its seal-status cell; measure the completed
payload length by a scan from the saved base up to its first sep, constructing
a unary length word exactly as above. Construct the complete block descriptor,
including the actual address base+length+1 of that status cell, by Add and
WriteDescriptor. The descriptor is a native record, not a concatenation of
wire Frames. Its ordinal is acquired by the explicit descriptor-prefix scan. Seek that cell with At and WR(1); one CTL seals the completed row and
records its immutable availability. The sep/status cell is not a payload bit.
The row's length, descriptor, previous-row link, manifest and earlier
fence references are all actual material. The same Base/length/sep/status/
WriteDescriptor/At; WR(1); CTL graph stages finite public words on 20 or 21
and constructs responses, initialization blocks and verifier receipts.
It reads an already completed source word; its length scan and FieldBody
use distinct work ports, so later stages cannot extend their scan bound. Its seal occurrence is part of the provenance relation;
any serialized fence naming that occurrence is acquired by a later closed
readout and stored in the later delivery descriptor, not inside a row before
its own creation. No self-referential current cost field is required.

After row seal, construct its complete wire reference from that actual
descriptor. Append on index stream 19 a native `00` record with two fields:
$U(m)$ and that reference, then EX; WR(seal); MR. The index writer is Tail,
literal tag/sep Appends, two WriteFields and those three final occurrences.
Its reader is Home; MR, fixed tag RD/MRs, ReadField/SkipField for both fields,
RD(seal); MR, with actual unary ordinal/count comparisons; the first tag RD
also tests R. It can return the last sealed row reference for a predecessor,
or enumerate the full frozen prefix. For the first row the predecessor is
the literal `no-predecessor`. No predecessor is inferred from a raw offset.
The $m$ counter version is already prepared; before completion its meaning
and this unfinished index remain determined by phase. Delivery starts only
after the new row index is complete. A present semantic-row reference is
the actual block reference constructed by Definition 6.2a and indexed on
18. Its semantic ordinal, descriptor ordinal and unified ordinal are
distinct fields. Its payload is copied to a receiver before that receiver
uses it; its printed producer base confers no private read permission.

The response token and row seal are distinct. Between them the producer has
one completed pending event and an unsealed row. At every cut the extended
event word satisfies $E^+=A^+\mathbin{+\!+}P^+$, where $A^+$ is the sealed
row word and $P^+$ is empty or that one committed pending event. Earlier
request-ingress and pre-response source work are unfinished work, not $P^+$.
All bytes, heads, partial descriptors and latches also remain actual state.

**Definition 6.2a (semantic journal, ordinal relation and paid access).**
Write the completed dispatcher-event word as $x_0\cdots x_{n-1}$, including
the acquisition entrance when it precedes the observed suffix. Put

$$
\epsilon(x)=\begin{cases}
0,&x\text{ is Reserve or Raise, with any of its three outcomes},\\
1,&x\text{ is ReadE, TagRead, Rho, Left, Right, NativeLocal or Halt},
\end{cases}
\qquad c_a=\sum_{b<a}\epsilon(x_b).
$$

Executed source rejects and absent literal replies have $\epsilon=1$.
Invalid preparations, unfinished or malformed ingress, unexecuted illegal
calls, archive `no-row`, copying and primitive controller work without a
completed marker add no $x_b$. At acknowledged boundaries $m=n,j=c_n$.
Let $U_a$ be the unified row with old ordinal $a$; let $J_k$, $1\le k\le c_n$,
be the semantic row for the unique event at

$$
\sigma(k)=\min\{a<n:\epsilon(x_a)=1,\ c_{a+1}=k\},\qquad
\epsilon(x_{\sigma(k)})=1.
$$

Thus $\sigma(k)$ is the position of the $k$th semantic event. A nonmaintenance
$U_a$ has before/after $j=(c_a,c_a+1)$ and references $J_{c_a+1}$; a maintenance
row has $(c_a,c_a)$ and `no-semantic-row`. The predecessor of $J_k$ is
$J_{k-1}$, or none for $k=1$. It is not the preceding unified row, which
can be maintenance. The predecessor of $U_a$ is $U_{a-1}$, or none for $a=0$.
In particular $j=m-\#\{b<m:\epsilon(x_b)=0\}$, without identifying any
event count with a descriptor ordinal or a primitive receipt ordinal.

The semantic payload has version `SEG-J1` and fifteen Frame fields, in
this order: version; $\xi$; `INITIAL-SOURCE` occurrence binding; initial
$H_0$/prior binding; **postcommit** ordinal $U(k)$; optional semantic
predecessor reference; one of the seven original event kinds; complete
request/material-reference tuple; exact response/local marker/terminal
output; before/after $q,g,e$ tuple; historical $U(h)$; typed source-layout
tuple; actual template/controller identity; start fence; response-commit
fence. The occurrence binding is the `INITIAL-SOURCE` tag and the boot
tuple $\xi,H_0,16,b_0,L_0,0$, constructed from the retained initial directory
fields. The source-layout tuple is the `SEG-SOURCE` tag and
$\xi,h,K,v,M_v$. It describes the first $L(h)$ logical bits under $\phi_K$;
it does not assert that disjoint segments are one physical interval.
All tuple components use the existing Frame/option codecs. Row creation
and final seal belong to the actual external descriptor/availability chain,
as in LJA5.1; no field predicts that row's future seal or total cost.

For source calls the request tuple retains the actual header/length/payload
and complete context/name/code material already prescribed. A local marker
instead retains its acquired controller-instruction packet; Halt retains
its acquired terminal packet and complete sealed output block. These are
their own typed tuples, not fabricated source-frame inputs. Required
control/output blocks absent at the producer or receiver are actually
copied through Definition 6.3 before use. The local/terminal packet also
retains its installed return kind and complete saved continuation material;
these are acquired fields, not a new evaluator argument. An acquisition producer's internal
Stop has this same Halt journal meaning, while its saved return kind
continues the surrounding dispatcher. A global stop takes the terminal
route only after recording and delivery. This preserves both return paths.

For every nonmaintenance event, after commitment and complete counter
selection, scan the complete index on 18 for its last reference and stage
it as `old-semantic-last`; the empty case constructs the none tag. Reload
the staged before-fields and complete request/response/fences, BuildManifest,
and Frame the fifteen fields, one at a time, into a fresh block on 21.
Use exactly Definition 6.2's Base/payload/sep/zero-status/length/Add/
WriteDescriptor/At; WR(1); CTL graph, with type `SEG-J1` on 17. Construct
its actual reference from that descriptor and stage it as
`current-semantic-row`. Append a native `00` record on 18 with two fields
$U(k)$ and that reference, using Tail, tag/sep Appends, two WriteFields,
EX; WR(seal); MR. Then construct $U_a$ and its index on 19. On maintenance
execute no semantic-row or index append and construct the none tag instead.
Before either writer, obtain `old-unified-last` by the same complete-index
scan on 19. These writer-side last-reference scans start at L and run to
the existing R, incrementing a real count after each verified seal and
retaining the last complete reference. Before $J_k$ they compare index 18's
count with the staged **old** $j=k-1$; before $U_a$ they compare index 19's
count with staged old $m=a$. The already committed event counts can be one
ahead of those indices. They are not passed as if an unfinished current
row already existed. At idle/frozen completed ends the corresponding counts
again agree. No scan of an unfinished index is invoked. The semantic and
unified copies of $M_v$ are both actually constructed and charged.
Staging/reload uses the fixed types in Definition 6.1; only the current
field, output, length/budget and bounded arithmetic roles remain live.
Other fields are loaded by a fresh origin scan, so the twelve-role bound
and the protected actor ports are unchanged.

Both indices have the native two-field reader already specified for 19.
The semantic reader additionally checks successive labels $1,\ldots,j_*$;
the unified reader checks $0,\ldots,m_*-1$. At idle, or in an owner-held
frozen-prefix service, load/construct the complete end count and last
reference before reading. Home; MR enters the index; each tag test,
ReadField/SkipField pair and seal RD; MR consumes one actual complete
record. Increment/Compare on unary words implements its position, label,
requested-ordinal and end tests. Select a reference only after its seal;
continue through the declared closed end to check its count/last reference.
Retain a selected reference on one word role until the closed end; then
release the scan's temporary counters before any ten-field descriptor
staging. The query/end words already have retained blocks and can be
reloaded by fresh scans. At that closed end, zero/out-of-range semantic queries and
out-of-range unified queries return typed `no-row`. A found reference is
resolved by producer ReadDescriptor, not by treating $k$ or $a$ as an address.
For an actor caller copy its whole block and missing dependencies on route
48 through the positioned channel. The caller resolves the equal origin in its own local
descriptor stream before reading. This is GetSemantic($k$) or GetUnified($a$),
respectively; no printed producer base becomes a receiver address.

A source-call ordinal is $q$, not $j$. A source-only query scans the same
semantic prefix, bounded-parses each row, counts just the five source kinds,
and selects its postcall $q$; locals and Halt are skipped without changing
that count; zero or a source ordinal beyond that prefix's $q$ returns
`no-row`. Call this one-based interface GetSourcePost($i$). The original
AIF request ordinal is zero-based: it is $q_{\rm before}=i-1$ for this
event, while $q_{\rm after}=i$. Those retained request fields are unchanged.
A caller of GetSourceRequest($a$) first executes unary Increment on its
actual $U(a)$, then invokes GetSourcePost($a+1$). That translation and
copy are charged; semantic $j$ and unified $m$ are not source-request
ordinals. A semantic-prefix query through $k$ scans unified indices and
their complete acquired rows, increments a separate rank word only at the
seven semantic kinds, and selects the closed end $\sigma(k)+1$; $k=0$
selects the empty prefix. It then uses the full snapshot/dependency routine
of Definition 6.3 for that end. A current whole-prefix query uses $m_*$
and includes any trailing maintenance. Prefix indices zero through their
respective closed counts are legal; a larger prefix index returns `no-row`
after the bounded scan. Hence the shortest prefix through
$J_k$ and the current prefix with the same $j$ are distinct queries.
These finite scans realize rank/select rather than acquiring it for free.
Requests are complete retained public query words on the installed caller's
own tapes: Frame(kind), Frame($U(i)$), Frame(closed-end binding), with five
fixed kinds for the two row queries, source-only and the two prefix queries.
Its fixed code constructs these fields by literal Appends and copies from
acquired data. An actor borrows the pool from the producer, constructs/stages
the packet in its archive/checking work and sends it on route 49. After
that channel has returned the pool to its actor sender, the actor executes
the twelve TOKs and CTL returning it to the producer before producer parsing.
The producer parses the packet's three bounded fields by ReadFrame;
a producer-local call uses its own retained packet and already owned
payload. Verifier/consumer lookups scan their already acquired snapshots
locally; they acquire no new producer-private read or reverse mailbox route.
There is no new raw source-frame tag, free scheduling
choice or unretained external query argument. This is an internal callable
archive routine, also used by the existing snapshot/stop paths. It holds
admission busy and changes only its actual work/copy/meter state. An
idle archive-client call returns its payload or `no-row`, complete ACK,
source-token and idle edges. A producer-local frozen-prefix call instead
returns to its retained frozen/stop continuation, without an idle/admission
edge or a new actor packet/channel. This finite return kind is retained
before the call and selects the installed fixed return edge. It creates no source call, NativeLocal, Halt
or maintenance event and changes neither $q,g,e,j,m$. GetSemantic is the
versioned realization of LJA5.4's callable journal access, not a private
source read or an arbitrary-busy-cut service.

**Lemma 6.2b (all-finite journal and consumer correspondence).** For every
finite lawful execution and every inserted finite maintenance word, the
preceding ordinal relation, both predecessor chains, index lookups and
complete acquired row payloads agree. Filtering unified events by
$\epsilon=1$ gives exactly LJA's semantic-event order, including locals,
rejects and Halt. Its fixed-$H$ operation contract is retained where the
historical guard is $H$; changes of guard use the explicitly annotated
extended contract, never a silent fixed-$H$ identification.

The precise field correspondence with LJA5.1 is:

| LJA field or consumer | Relation in this resident instrument |
| --- | --- |
| Semantic count/event ordinal | Same semantic count $j$; row $k$ uses the postcommit ordinal $k$, while its unified mate has old ordinal $\sigma(k)$ and before/after $j=(k-1,k)$ |
| Sealed predecessor and journal lookup | The $k-1$ semantic predecessor maps to the actual reference of $J_{k-1}$; GetSemantic uses index 18. Unified predecessors and index 19 use their own ordinals. Descriptor ordinal $c$ is obtained separately by ReadDescriptor |
| Original model and $H$ | `SEG-J1` is an explicit new record version; $H$ becomes the row's historical $h$, with $H_0$/prior retained independently. A whole fixed-$H_0$ LJA replay is claimed only when every semantic guard is $H_0$ |
| Preparation and `INITIAL-SOURCE` | The same actual $\xi$ and original ingress tuple, copied from boot; no second preparation, new source value or readable payload is supplied by its name |
| Port, request, complete material, response, before/after $q,g,e$ | Equal original data for all seven kinds, including executed rejects and complete local/output material; source-call-only indices are obtained by the separate kind filter |
| Actual source-block descriptor | The typed layout tuple replaces the contiguous descriptor. Its interpretation is $i\mapsto\phi_K(i)$ for $i<L(h)$, with the actual manifest; old interval handles keep their original meanings |
| Template, start/response fences, row creation | The actual installed compiled template and new paid cut/descriptor references. Corresponding cut kinds and relative order are retained; numerical addresses, fence ordinals, ticks, fees and creation occurrences are not identified with a hypothetical contiguous execution |
| Row copy and received reference | Equality of the whole payload and original reference; receiver allocation/owner/base/status are its own. Only its acquired local descriptor permits reading |
| LJA replay/receipt consumer | The version-aware decoder and joined verifier of Definition 6.5, with the same initial $q_{H_0}$ target, then its actual acquired-binding consumer. An unmodified LJA or PR57 byte parser is not claimed to accept these new versions |

Proof. Induct on completed dispatcher events, simultaneously retaining
the actual before/after source, counter words, sealed indices and returned
owner/continuation boundary. At zero both indices are empty and all five
event counters are zero; boot binding gives the actual initial occurrence.
At a maintenance event $\epsilon=0$, the completed $m$ advances once,
$j,q,g,e$ do not advance, index 18 and every $J_k$ remain untouched, and
one $U_a$ with the prior unified predecessor and none semantic reference
is sealed/indexed. This includes strict, unchanged and refusal outcomes.
Its directory/guard effect is precisely Definition 5.1, not an original
source event. At a source event $\epsilon=1$, Theorem 4.5 supplies its exact
response and successor; the five original source kinds have precisely
LJA4.3's $q,g,e$ cases. At NativeLocal or Halt its actually completed
instruction or complete sealed output commits that marker, preserving
$q,g,e$ and the source. Each of these seven cases advances $j,m$ once.
The last complete semantic index therefore names $J_{c_a}$, and the new
semantic row/index is exactly $J_{c_a+1}$. The last complete unified index
names $U_{a-1}$, and its new row is exactly $U_a$ with that semantic link.
Frame inversion and native seal-gated selection, proved in Lemma 6.1b,
give all payload, counter, predecessor and reference equalities in the
table. The end count is $c_{a+1}$, proving rank/select and $m-j$ by induction.

For intermediate cuts let $E_s$ be the nonmaintenance filter of committed
$E^+$, $A_s$ the sealed semantic-row word and $P_s$ its committed unsealed
suffix. Commitment adds exactly the same one semantic event to $E_s,P_s$
when $\epsilon=1$, and none on maintenance. Semantic row seal transfers
that event from $P_s$ to $A_s$; its following index append and unified row
seal add no event. Thus $E_s=A_s\mathbin{+\!+}P_s$, $|P_s|\le1$, alongside
the existing $E^+=A^+\mathbin{+\!+}P^+$; the two pending fields need not
empty at the same cut. Partial index/status/copy words remain unavailable
and the phase retains the committed/prepared counts. Busy admission prevents
a second event before both rows, indices, dependencies and final ACK.
This covers all primitive cuts without asserting equality of in-flight
archive lengths or incrementing a counter at a later seal.

Index induction visits a fixed finite complete prefix and selects exactly
its requested label after the seal; payload field induction gives the
seven-kind and source-only filters. A successful local-origin lookup reads
the equal acquired payload; absent/unfinished copies fail availability.
The rank scan is over those same complete rows, so the selected prefix
includes all preceding maintenance and omits no historical guard. Every
word, selection, dependency, returned token and head is furnished by the
listed finite graphs; bounded scans, not an oracle, implement the table.
At constant historical guard $H_0$ the original row replay therefore has
the same requests, replies, source successors and initial-target fiber.
After Raise only the guard-annotated replay has that assertion; the old
fixed-$H_0$ claim is not made. Changed physical descriptors, schedules and
references are related by the displayed maps, not by fictitious byte
equality with an unexecuted legacy run. Definitions 6.3 and 6.5 below
copy and check these joins before any continuation or target output.
$\square$

**Example 6.2c (local, terminal and maintenance ordinals).** Relative to
zero starting event counts, NativeLocal; TagRead(root); Halt on alpha at
$h=K=1$ has semantic successors $j=1,2,3$ and source-call successors
$q=0,1,1$. Its semantic rows are $J_1,J_2,J_3$, including the local and
terminal payloads. Insert Reserve(2) before the local, Reserve(2) between
the local and read, and Raise(1) between the read and Halt. These are,
respectively, strict reservation, unchanged reservation and unchanged raise;
the source and guard stay alpha and 1. The six unified rows have after-$j$
values $0,1,1,2,2,3$ and after-$m$ values $1,2,3,4,5,6$. Thus
$\sigma(1)=1,\sigma(2)=3,\sigma(3)=5$, and $J_2$'s predecessor is $J_1$,
not the intervening maintenance row $U_2$. A semantic-prefix query through
2 selects four unified rows; a current query after the fifth row selects
five, despite both having $j=2$. At a common nonzero entrance the actual
stored counts and predecessor references are added/carried through, not
reset. The beta/rejected-Rho/Reserve/Raise/accepted-Rho example in Theorem
5.3 additionally shows why the guard history cannot be removed by this
ordinal relation.
For the supplied stationary full-source producer on $\ell$ leaves, LJA7.3's
$2\ell-1$ reads, $2(\ell-1)$ locals and one Halt therefore contribute exactly
$4\ell-2$ to $j$. This uses the supplied traversal, including its two local
actions per branch, rather than counting only its source rows.

**Definition 6.3 (fully positioned two-stage channel).** A sender block is
sealed, immutable and readable by its actual owner. Its length $\ell$ and
base are loaded from its real descriptor by Definition 6.1. Construct a
complete $U(\ell)$ counter on a work port. Before any mailbox allocation,
Base on its assigned mailbox port measures the actual base; Zero reserves
and initializes its $\ell$ payload cells and following sep. Append one
zero seal-status cell immediately after that sep, by the three-primitive
Append; construct the mailbox descriptor with status address
base+$\ell+1$. Do the identical Base/Zero/status/descriptor construction at
the receiver's archive port. The receiver constructs its own block and local descriptor during the
explicit workspace loan of Definition 2.2, then returns the pool for stage
one. These ports can be nonempty: both bases are
measured at their actual current R. Their distinct intervals, tokens and
status cells exist before copying. Sender, mailbox and receiver coexist.

For the first stage, Last(counter); At(sender,base); At(mailbox,base).
The six-row loop is RD(counter,test); on 0 go to sealing, on 1 RD(sender,data);
WR(mailbox,data); MR(sender); MR(mailbox); MR(counter) and back to the test.
The private/data latch and public counter-test latch are distinct. At exit,
At(mailbox,status); WR(1) is the seal-status prelude; CTL seals the whole
mailbox; TOK hands off its read token. Lend the word pool to the receiver
by Definition 2.2. For the second stage reposition
Last(counter), At(mailbox,base), At(receiver,base), run the identical six-row
loop, At(receiver,status); WR(1); CTL seal; TOK copy completion. Complete its requested receiver checks
and return the word pool before the sender continuation/row ACK. These
At invocations include Last on their actual address words. Every computed
status address and its duplicate needed for later positioning is copied
before the corresponding body. The destination's following sep permits its
last MR. Sender remains immutable; mailbox becomes readable after its own
seal/handoff; receiver is unavailable until its final seal. A finite token
does not stand for an unconstructed seal table.

Consequently the two payload loops, terminal tests, CTL seals and TOKs have
exactly $12\ell+6$ occurrences, as in AIF6.4. The two real status-positioning
and WR preludes, all Base/Zero/status/descriptor construction, actual workspace loans/returns, first positioning
and between-stage repositioning are additional displayed graph evaluations.
There is no assertion that $12\ell+6$, or $8\ell+4$, is the complete bill.
Each such Prelude, At, Frame, Last, Base and Zero has its expansion here or
in the exact supplier; the channel has no unnamed setup service.

The mandatory row route copies the complete unified row, its semantic row
when present, and any request/context/control/output material absent at the
actor through fresh mailboxes into that actor's append-only archive.
Only after all these blocks have arrived and the receiver checks both whole
row payloads and their local availability does its final TOK
acknowledge the row. A channel stage's receiver-seal TOK is an internal
copy completion; the row caller does not treat it as this final row ACK.
Required ancillary blocks are sent in fixed order: boot binding/initialization/prior if
absent, the complete typed request's enumerated blocks in order (source
header/length/payload then contexts, or local/terminal packet and its
control/output dependencies), then the semantic row if present, then the
unified row. Absence is tested by the local origin scan, not an external assertion.
The receiver uses its origin-to-local descriptor records for every referenced
payload check. Its bounded decoder checks `SEG-U1`, identity, all before/after
fields, full manifest, final status and predecessor against the previous
acquired unified row, or boot at zero. It computes $\epsilon$ from the actual
kind, checks $j'=j+\epsilon$ and the applicable $q,g,e$ cases. On maintenance
it requires `no-semantic-row` and retains its previous semantic end. Otherwise
it loads the present `SEG-J1` through its acquired local origin, checks all
fifteen fields against this unified event, checks ordinal $j+1$, and compares
its predecessor to the previous acquired semantic end. Its occurrence,
historical guard/layout manifest, template, request/response and two fences
must all agree. The first semantic predecessor is none even after leading
maintenance; it never uses the preceding unified reference as that predecessor.
Any local expected count/end word is staged in that owner's archive/checking
work using its own descriptors while the pool is lent to it. A new joined
end is installed by full word copies only after both checks succeed.
Failed structural checking takes the paid refusal edge with
no new service-admission token; authentic rows follow the success edge. The row-copy caller resumes Definition 4.6 at that actual
acknowledgement. At stop freeze that already complete index-19 prefix:
scan its records once, constructing its unary count, and retain its last
row reference and event count $m_*$. Its bounded row scans count semantic
events, construct $U(j_*)$ and retain the last semantic reference; compare
them with the complete index-18 prefix and its closed end. The frozen prefix
binding is $(m_*,j_*,\mathrm{last}\ U,\mathrm{last}\ J)$, with explicit none
tags for empty ends. No later event is admitted during this stop route.
Construct a snapshot-index bit word with Frame(`SEG-P1`), $U(m_*)$, $U(j_*)$,
Frame(optional last unified reference), Frame(optional last semantic reference),
Frame(boot-binding reference), Frame(prior reference), then, in index order,
Frame(unified row reference), Frame(complete request-reference tuple),
Frame(optional semantic-row reference). Iterate the
frozen indices by the preceding native reader; each row's bounded ReadFrame
scan obtains its retained request-reference tuple. New/UnaryBody/Frame/Finish
and the ordinary staging bit-block graph construct/seal this finite index
on 21; its bound is obtained by the same length scan, not a live meter end.
Each typed request tuple explicitly enumerates all its source or local/terminal
material references with its constructed finite count. Its bit parser is
ReadUnary followed by that count's ReadFrames and a remaining-budget check.

Through the same full channel first copy the boot binding/prior and every
semantic/unified row and request/context/control/output block in this frozen
finite list to the verifier, in the same dependency order and testing
its local origins to avoid a missing dependency; then copy the sealed
snapshot index. Its reference fields keep their producer origin meanings;
the verifier reads payloads through its acquired local descriptors. The
snapshot consists of these actual blocks and that completed index, and
its release CTL follows the complete index seal and dependency checks.
There is no atomic multi-tape freeze/copy or uncharged import. An empty
frozen list still constructs both zero counts, both none ends, version,
boot/prior fields and status.
Earlier snapshots and archives are retained; no arbitrary external
transcript-import port is added.

**Theorem 6.4 (authentic rows, old handles and complete maintenance delivery).**
Every available receiver row equals its designated sealed sender payload,
including every manifest, maintenance/guard/binding and acquired fence field, and every verifier snapshot
equals the producer's frozen actual prefix with its two journal ends.
Semantic ordinals and predecessors are those of Lemma 6.2b, with an actual
copied semantic row for every source/local/Halt event. Every previous archive handle
retains its payload, prefix, owner, seal and type. A source-occurrence handle
continues to call the current source through ReadState and Resolve. An old
physical interval handle continues to name precisely its old interval; it
is not a new whole-source descriptor or a historical snapshot.

Proof. At each copy iteration source and destination heads address the same
relative payload index, and the real counter bounds the loop. RD followed by
WR writes precisely that bit. Induction gives equality of the copied prefix.
No other writer can mutate the immutable sender or the sealed mailbox in
their respective phases. The receiver's status starts at constructed zero,
is changed only after all $\ell$ bits have been written, and its availability
is released only by the following CTL/TOK. Thus a readable receiver has the
whole equal payload, not merely its copied prefix. Origin references in the row are copied bits. The receiver's local
descriptor fields are constructed at its actual Base before copying and
retain that exact origin. Equality of the two payloads does not identify
their distinct owner, port, base or seal cells. Subsequent lookup uses the
local descriptor, not the origin's private physical address.

BuildManifest's record induction copies exactly each tag and all of its
finite fields after consuming their true native separators. Its completed
count is the actual directory length. Thus a delivered row contains the
whole active manifest and each acquired fence tuple, not merely references
to inaccessible directory or meter payload. The receiver's bounded decoder
recovers those same words by Lemma 6.1b, including empty identity/origin
fields and every old segment. The producer writer appends without modifying
any prior row or its descriptor.
The mandatory route completes the same check on each successive row, so
induction gives predecessor continuity and exact archive prefixes. The frozen
bound excludes later append and the readout's own receipts, so snapshot
equality follows by the same bit induction. All the new row fields have been
constructed by Definition 6.1 and their complete sender seal precedes copying.
Lemma 6.2b identifies exactly which semantic row belongs to each unified
event; the receiver's joined check uses the two different predecessor
chains. Index labels are copied data, and each received block has its own
local descriptor. Their relation supplies neither a cross-owner token nor
an equation between descriptor ordinals and event ordinals.
This proves the full maintenance return route as well as its copy invariant.

Source addresses retain Lemma 4.3's stable images. The logical source service
therefore uses the same $\xi$ with the newest complete layout/guard. An old
physical source descriptor is still correct for its own interval and owner,
but after Reserve that interval is only an initial part of the source. Its
bytes remain mutable under future genuine source gates; it was never made
an acquired frozen snapshot by naming it in a row. For example after beta,
Reserve(2), Raise(2), accepted Rho, the old initial interval's bits themselves
can change as part of the new preorder packet. Epoch-bound literal replies
and frozen receipt fields remain about their original events. The actor
never gains private RD or WR from possession of any of these names. No old
whole-source raw writable actor capability exists in the declared interface.
Arbitrary aliasing external pointers would require a different bridge.
$\square$

**Definition 6.5 (historical-guard verifier and actual receipt consumer).** The
verifier receives only its sealed snapshot, copied public initialization/prior
and target proposal. Enumerate initial candidates exactly as PR57.D8, over
all $4^{2H_0-1}$ initial packets, validate each and apply the actual prior
$D\subseteq\mathcal T_{H_0}$. For each retained candidate $s$, keep its initial
target $q_{H_0}(s)$ distinct from its replay-current syntax and counters.
Initialize replay $h=K=H_0$ and $r=p=q=g=e=j=m=0$; both expected predecessor
references start as none. Replay counts are constructed local verifier
words, never private bank-23 reads. Scan *every* unified row, its semantic
mate when present, and complete associated request/control/output material
in order, using the preceding explicit framing,
ordinal, field and block-access scans. Malformed identity, predecessor,
length, seal, manifest, directory-count, fence binding or counter relationships
set a public failure
bit; no shortened scan substitutes for the full frozen prefix.

First bounded-parse the `SEG-P1` snapshot index and its two counts/two ends.
For each position $a$, require `SEG-U1`, old $m=a$, prior after-fields equal
to current before-fields and the exact previous unified reference. Compute
$\epsilon$ from the kind, construct $j+\epsilon$ and compare both $j$ fields.
On maintenance require the none semantic tag. Otherwise resolve its copied
`SEG-J1` and compare all fifteen fields, including postcommit ordinal $j+1$,
the previous semantic reference and the same boot/prior, historical guard,
source layout/manifest, request/response, template and two fence tuples.
Use the same joined-row checker as the actor, on verifier-owned acquired
origins. In particular a private audit handle without its local payload
does not pass. Compare the snapshot's optional semantic reference for this
position to that actual unified field as well. Retain these proposed
after-versions for the event's replay update below; select each counter
once, not once in this check and again in source replay. Its local semantic
end changes only on a semantic event, and its unified end changes on every
event. At the frozen end require both constructed counts and both last
references to equal the snapshot header. Leading, intervening and trailing
maintenance therefore have their distinct complete-prefix meanings.

Read the boot-binding manifest first. Parse each later manifest by
ReadUnary for $v$ under its actual bit budget, then a $v$-bounded record
loop. ReadFrame acquires the tag; its finite check supplies the arity; the
inner fixed-arity ReadFrames acquire every field. Check its remaining budget
and complete shape, not just its count. The first record must agree with
the copied $\xi,H_0,b_0,L_0,16,0$ boot binding. Maintain the preceding complete
manifest as an immutable local block. Compare all previous records/fields
in full, using the same scans and word equality. For an ok reservation the
new final record must be exactly tag `01` with $J,b,4(J-K),r+1,m,v,f_s$;
for an ok raise exactly tag `10` with $J,p+1,m,v,f_s$. Check their resulting
count, $h,K,r,p$, and that the declared new interval is positive and beyond
every prior source interval. The intervening scratch gap is permitted;
authentic provenance supplies its actual Base, not a candidate-tree guess.
Every other event must have a byte-equal manifest and unchanged directory
count. Thus unequal $h,K$, multiple records and no-change histories all
retain their true meanings. Fence-reference tuples must have their expected
kind, $\xi,m$ and before/after directory-count binding, and $2n$ fee relation; a successful publication has
its distinct acquired post-publication fence between the start and response
fences. A no-publication branch must have that literal tag. Their authenticity
comes from the writer/channel, not from arithmetic on these labels.

For a reservation row, recompute the public comparison and $d=4(J-K)$;
check its exact ok/unchanged/refusal case and directory successor/count;
on ok change only replay $K,r$ among source/layout/guard fields, preserving
$q,g,e,j$ and advancing $m$. For a raise row,
check $h<J\le K$, equality and refusal cases; on ok set only replay $h,p$.
It likewise preserves $q,g,e,j$ and advances $m$ on every outcome.
Construct replay counter versions by the same unary graphs. For an original
source event and its semantic row, run the supplied whole candidate/read algorithm on the replay
syntax with *that row's replay $h$*, compare the complete response, and
install its candidate only on the recorded true guard. Replay guards and
all metadata must agree with the row's before/after fields. The replica
syntax is public enumerated work, not a new source port. Its backing can
be Zero-allocated at the current replay $h$ and copied by the same bounded
public routines; no private source is reacquired.

Literal replies use the supplied public locator; ReadE and targets use the
exact supplied coefficient and normal-form recurrences. NativeLocal markers
and terminal blocks are checked with their installed actual source-free
controller table and complete acquired requests/responses, by PR57.D5's
row-by-row table interpreter; nonterminating local work has no completed
marker to verify. All declared finite prior computations must terminate.
The acquired terminal packet's return kind is checked against the installed
code: an acquisition-internal Halt returns its complete output to its saved
surrounding continuation; a global Halt finishes terminal services and
admits no later event. Replay does not stop at an internal producer return
or silently replace it by an unrecorded local microstep.
Every source event advances replay $q,j,m$, with its exact accepted $g,e$
case; each completed NativeLocal/Halt advances only $j,m$. Row construction,
copying, lookups and seals advance none of these replay event counts.
Layout bases and creation/fence references are checked as authentic provenance
fields of the copied actual trace, not inferred from a candidate's tree value.
There is no pretend test that a numerical name independently authenticates an
external transcript. Provenance here comes from the exclusive owned writer
and these allowed copies.

The stop proposal is an actual retained output/input block, not a mathematical
parameter converted to bytes for free. Copy it with the initialization and
frozen-prefix binding from the producer to verifier archive 32 on route 50.
After the snapshot index is sealed, its actual constructed reference and
$(m_*,j_*,\mathrm{last}\ U,\mathrm{last}\ J)$ supply that binding. Construct a typed expected-task binding block from these
complete words by Frame and the ordinary staging graph. Before consuming a
receipt, copy this block on route 51 to consumer archive 40 as well, with
its actual local descriptor on 41. The consumer loads its expected
$\xi,H_0,D$, proposal, prefix and snapshot values from this acquired block;
its requested target type is the fixed `INITIAL-q_H0` program tag. It does
not compare a receipt against unacquired free parameters. These additional
mandatory binding/proposal copies and construction are included in the
same stop recurrence and use no source read.

For each surviving initial candidate compare the proposal with the saved
$q_{H_0}(s)$, using PR57.D8's literal tag/tuple encoding and complete
normal-coordinate adapter if needed. The decision is nonempty compatible
fiber AND equality of *all* surviving initial targets AND all structural
checks. This is a finite exhaustive enumeration and finite replay recurrence:
advance the base-four word; parse; evaluate prior; reset its replay state;
consume the next complete row via its stored finite bound; execute the
selected finite operation graph; conjoin comparison bits; continue through
the last row and last initial candidate. All constituent scans, arithmetic,
gates, replicas, field writes and copies have the specified expansions.

An accepted receipt has model version `SEG-R1`, type `INITIAL-q_H0`, the complete $\xi,H_0,D$,
literal proposal, both frozen journal counts and both optional last references,
and snapshot reference, verifier
creation/seal references in its completed delivery descriptor. These are the
actual descriptor ordinal and constructed status-cell reference, with the
sender's seal CTL in its authentic provenance; any numeric fence for that
seal is obtained only by a later CloseFence and belongs to that delivery
descriptor. The receipt payload does not predict its own seal-fence numeral.
Copy it completely through Definition 6.3 to the
consumer. The consumer first parses every field and checks model/type,
$\xi,H_0,D$, both journal counts/ends and snapshot binding, proposed target and actual accepted
receipt seal by finite scans and word comparison, before selecting its
public success edge. Then Zero-allocate its task-output block and copy every
target bit by the same bounded body; seal it and perform any required OUT
one bit at a time. Wrong type/identity/proposal, ambiguity, refusal or
malformation yields no task output. A requested current $q_h(t)$ or enlarged
initial $q_J(u)$ requires its own explicitly typed verification and paid
data; Raise does not convert an old receipt into either one.

**Theorem 6.6 (guard-faithful record-only soundness).** On an authentic finite
prefix with actual $u\in D$, the actual initial source survives this verifier.
Subject to its structural checks, acceptance is exactly constancy of the
original $q_{H_0}$ on the nonempty compatible initial-source fiber of the
extended event word. Every actual consumer output equals $q_{H_0}(u)$.

Proof. The initial enumeration is complete and duplicate-free by PR57.T1/D8.
Theorem 6.4 authenticates every copied row and request, and Lemma 6.2b
supplies their exact semantic/unified counter and predecessor correspondence.
Induct over those rows
with the actual initial candidate $u$. Reserve and Raise have the precise
public cases of Definition 5.1 and preserve its replay-current tree;
their metadata updates match ReadState's actual directory. Theorem 4.5 then
gives the same next genuine source response and successor under the recorded
historical guard. The same source-free controller and acquired responses
give the same local/stop markers. Hence every comparison for $u$ succeeds.
The joined decoder's local $j$ counts these markers as well as source calls;
its $m$ also counts maintenance. Thus both prefix ends and every semantic
payload check succeed for the actual source, including terminal recording
before global halt and the acquisition producer's internal return.

Conversely, for each surviving $s$ the same induction says exactly that this
initial source under those retained commands, policies and historical guards
produces the recorded source responses and event meanings. Reserve supplies
no source-dependent payload to distinguish further candidates. Authentic
physical-layout fields constrain the actual instrument/provenance, not a
fictitious guessed source value. More explicitly, induct simultaneously on
equal acquired public command/response prefixes. Theorem 4.5's generator,
source-address and private-gate schedules have identical public event words
until each release; equal released responses then determine identical
post-release work. All directory, counter, descriptor, manifest and fence
routines depend only on these public words and the deterministic allocator.
Thus they construct identical public payloads, cut ordinals and fees for
any candidate in this fiber. They cannot silently delete a candidate that
has all the same original responses. This applies to rejected and unchanged
branches as well as accepted/strict-publication branches. Thus the survivor set is precisely that
compatible initial-source fiber, with the stated structural checks. The
complete enumeration's nonempty/constant decision is the asserted condition.
The preserved initial-target computation is the existing exact $q_{H_0}$
computation. Applying constancy to the actual survivor $u$ proves the receipt
value. Whole receipt copying and the consumer's type/binding checks preserve
that value before actual task-output writes. No target is re-evaluated under
the newest guard merely because its archive is now read later. $\square$

**Lemma 6.7 (complete caller and returned-boundary composition).** Every
valid finite complete canonical request at a reached acknowledged idle state
has the selected finite paid continuation through its complete row ACK to
its saved return edge, or through its terminal ACK and requested stop work to halt. This includes
source acceptance/rejection, Reserve greater/equal/less and all Raise
comparison branches, every finite valid context and finite literal address.
Reached local/controller computations and required external supplies must
terminate. During this continuation the actual finite partial phases are
not callable extra services and are not projected out of the actual state.

The complete producer/consumer map is:

| Material and writer | Actual reader and endpoint |
| --- | --- |
| Boot source ingress/validation, initial native directory and six counters | ReadState/Resolve and LoadCounter by ReadField/SkipField; boot CloseFence and boot-binding copy finish before acquired-controller use |
| Native directory/counter append | Complete-record scan; the matching and skipping branches both reach the following seal, and only a seal permits selection |
| Producer native block descriptors on 17; local copy descriptors on 29 and verifier/consumer work | Origin/ordinal native scan, full field equality, actual local availability/At reads; remote references use acquired origin matches |
| Source S/W fields and generated code | Resolve for every S operand **and destination**; Copy/Add for W; unchanged raw-unary interpreter after complete code construction |
| Every source response, NativeLocal and Halt commitment | Inherited $q,g,e,j$ cases, complete `SEG-J1` row/index and its unified mate; Lemma 6.2b's two predecessor chains |
| Semantic/unified indices and GetSemantic/GetUnified/source-only/prefix scans | Paid ordinal/rank/select scan, descriptor/origin resolution, actual acquired payload or typed `no-row`; no new semantic event |
| Start, successful publication and response CloseFence | Already constructed typed closed reference blocks, reloaded through their native descriptors into the row fields; no publication call on no-change branches |
| Retained ingress/header/length/payload/context blocks | Complete parser and row request references; missing actor copies arrive through the positioned channel before final row ACK |
| BuildManifest and complete semantic/unified bit-row writers | Bounded joined-row/manifest decoder at actor and verifier; full $M_v$, $j$ transitions and both predecessors checked before final ACK |
| Sender/mailbox/receiver and local origin descriptors | Both length-bounded copy stages, actual status WR/CTL/TOK; only complete receiver material can be parsed |
| Frozen semantic/unified rows, all dependencies and two journal ends | `SEG-P1` verifier snapshot, full ordinal/guard/manifest checks and finite initial-candidate enumeration |
| Accepted SEG-R1 INITIAL-q_H0 receipt and completed delivery descriptor | Consumer compares both journal counts/ends and all other acquired expected binding fields before writing/sealing/OUT of the target; refusal has no task output |
| Final row parser | Final row ACK TOK, source-service-token TOK, idle CTL, fixed retained caller return edge; a terminal route instead completes its requested snapshot/verification/consumer work before halt CTL |

Proof. Lemma 6.1b is a structural proof for arbitrary finite valid words and
records, not a length bound on this table. At every listed join it supplies
the next reader's actual entry head and complete material. In particular
WriteRecord ends at R; its next CloseFence creates its own F and materializes
its own count/closed ordinal. The row writer reloads these completed words
and builds the manifest only after the selected directory is complete.
No publication field has an unbound value or a future completion reference.
On no-change/refusal branches no directory is appended, and BuildManifest
therefore reads the identical finite record sequence. Source accepts and
rejects both pass through their completed semantic row, preserve its true
historical guard, and use the unchanged manifest. NativeLocal/Halt commit
their own executed marker/output and also write their semantic row, advancing
$j$ once. Maintenance writes no semantic row. Lemma 6.2b proves these cases
and both indices uniformly. Each branch writes exactly one new unified row
for its one committed event and has the same finite delivery join.

For a channel, induction on $0\le i\le\ell$ gives equality of sender/mailbox
and then mailbox/receiver prefixes and heads at their next relative index.
At $\ell=0$ the terminal test still runs and the distinct zero-status cell
is sought, written and sealed. At $i<\ell$ the data latch is written before
any next public counter test; public and data latches are distinct. All
bases/status addresses came from actual Base/length/Add words and actual
native descriptors, even on nonempty ports. Local origin records preserve
which sealed copy each owner may read. All required referenced payloads are
finite and the ordered missing-copy scan terminates. The complete receiver
row parser consumes all its bounded fields, semantic mate, manifest and seals,
checks both predecessor/count relationships, then emits
the final row ACK. For these authentic outputs the checks succeed. At that
edge the service still has its busy source token; the subsequent explicit
TOK and idle CTL restore admission and the saved return edge, without changing
the stored controller/table/seed or waiting Native command. A paid structural
refusal on malformed acquired material grants no success/output token.

Verification has a fixed finite initial-packet enumeration and finite row
bounds; each declared prior/reached local computation terminates by premise.
The workspace handover is a fixed twelve-port induction: after its $i$th
TOK exactly ports 1 through $i$ have the new owner, the rest retain the old
owner, and every word/head is unchanged by these TOKs. Its final CTL enables
the new owner's helper. Reverse induction gives all twelve back before
sender/dispatcher return. No mixed-transfer cut enables a helper or another
source request. This proves the local permission/continuation joins, not
just equality of two copied payloads. Their arithmetic/field calls run only after the twelve actual workspace
TOKs have reached that owner, and return those tokens before a different
owner resumes. The same field induction covers its manifest/reference/receipt readers and
the consumer's success and refusal cases. Thus the table contains actual
finite compositions at every caller, not required future implementations.
Every prefix within a loop, staging block, readout, seal/status transition,
copy, parser or token return has the next installed primitive and retains
its own heads, latches, tokens, partially constructed words and meter.
Only required but withheld input or divergent reached local computation can
prevent the stated progress conclusion. $\square$

## 7. Exact cost recurrence and all actual cuts

**Definition 7.1 (evaluable primitive recurrence).** Expand the finite graphs
in Definitions 2.2–6.7, the actual controller graph of Definition 8.1, and the
cited exact supplier graphs. For a graph entry
$G$, actual joint configuration $z$ and actual supplied input word $I$, define
its evaluation recursively. At its stated return/halt edge set $V(G,z,I)=0$.
At a non-IN primitive with enabled successor $z'$ set
$V(G,z,I)=1+V(G',z',I)$. At IN with next supplied bit $b$ set
$V(G,z,bI)=1+V(G',z_b',I)$. A terminal test chooses the stated successor on
its actual finite read symbol; it is that primitive, not a free predicate.
CTL role changes, all seal/status operations and tag transitions each
contribute 1. Unsupported/disabled calls have no executed edge. Withheld IN
or divergent local work has no finite return value. On every lawful finite
completed operation here the recurrence terminates by the preceding proofs.

The following equations expose the helper and complete-service bills.
Every cost is evaluated in the actual configuration reached by the preceding
summand; repeated Last/Tail calls are not coalesced. Write $L_s$ for that
call's Last cost, $N_d$ for its New/Tail cost, and $F_d=3+L_d$ for Finish
at its actual entry. A role exchange contributes its separate CTL.

$$
\begin{aligned}
V(\mathrm{WriteField}(w))&=L_s+5k+4,\\
V(\mathrm{ReadField}(w))&=N_d+5k+2+F_d,\\
V(\mathrm{SkipField}(w))&=2k+2,\\
V(\mathrm{NativeWrite}(t;w_1,\ldots,w_a))
 &=\mathrm{Tail}+3(|t|+1)+\sum_i(L_i+5k_i+4)+3,\\
V(\mathrm{Frame}(w))&=L_s+N_c+(5k+1)+3+F_c
                       +L_s+L_c+5(k+1)+(5k+1),\\
V(\mathrm{ReadFrame}(w))&=N_c+7(k+1)+F_c+N_d+L_c+(9k+1)+F_d,
\qquad k=|w|.
\end{aligned}
$$

The $+2$ in ReadField is its terminal field RD and final source MR; its
Finish is separate. ReadFrame includes all BudgetBit tests and source/budget
moves: seven occurrences per unary length bit, nine per payload bit, one
terminal length RD. Its tuple-end budget/status tests are additional.
NativeWrite gives directory overhead 12, counter overhead 15 and descriptor
overhead 12 before the displayed field terms. WriteDescriptor additionally
pays its complete count-only origin scan, ordinal increment and all ten
field preparations *before* NativeWrite; any caller staging/reload is counted
at its actual graph occurrence. In a complete counter lookup,
Home; MR and terminal RD cost Home$+2$; each record contributes 10 for
name/sep and seal RD/MRs, its selected ReadField or SkipField cost, and one
CTL only if a verified matching value replaces its role. Descriptor lookup
uses the analogous tag/ten-field/seal recurrence plus every unary ordinal
increment/Compare. Zero retains Last/Tail, $5d+1$ and its delimiter cost 3.
All equality/failed-test/remaining-block scans follow their displayed actual
branches. A malformed partial graph is billed by its executed prefix,
not by substituting the successful formula.

For a complete directory with fields $w_{a,i}$,

$$
P_v=|M_v|=v+1+\sum_{a=1}^{v}
 \left(5+\sum_{i=1}^{k(\mathrm{tag}_a)}(2|w_{a,i}|+1)\right).
$$

BuildManifest evaluates New(destination), Last($v$), UnaryBody($v$),
Home(directory); MR, construction of its zero count; for each record
ReadField(tag), its two-bit kind check (RD; MR; RD; MR; RD(sep), cost 5),
Frame(tag), each ReadField/Frame pair, RD(seal); MR and the paid count
Increment; then RD(R), Compare(count,$v$), Finish(destination).
These terms determine its exact cost on any finite directory. The manifest
row field alone writes $2P_v+1$ bits; a row with field lengths $k_i$ has
$\ell=\sum_i(2k_i+1)$ payload bits. All those field lengths, including $P_v$,
are actually constructed by the length scans. Row construction additionally
evaluates Base, the final sep/status Appends, length scan, status Add,
WriteDescriptor, At(status); WR(1); CTL. There is no manifest-copy cost hidden
behind a prefix count.

CloseFence evaluates LoadCounter($f$), Increment, its one CTL-fence,
AppendCounter, and the two explicit closed scans and staging. More precisely,
its first scan's receipt bodies cost

$$
5n_f-1+\sum_{a=1}^{f}
  \bigl(V(\mathrm{Increment}(\mathrm{visited}))+
        V(\mathrm{Compare}(\mathrm{visited},f))\bigr).
$$

Each nonterminal receipt has RD, Append(1), MR, costing 5; the selected F has
no final MR, giving the minus one. Add Home; MR, New(bound), literal visited
zero construction, Append(0), Finish(bound), every selected-role CTL, and the
second scan's actual positioning/New calls, $13n_f+7$ body and two Finishes.
Add every Frame, closed-block Base/copy/sep/status/descriptor/At/WR/CTL
staging occurrence, LatestType scan and later reload. The $n_f$ here describes the selected
existing finite prefix; its *executable* bound is the actual stored scan
result, never a free instruction argument. This is a nonrecursive meter
readout despite the ordinary receipts created by both scans.

For one channel of $\ell$ bits, evaluate sender descriptor lookup/status
checks and length copy, both Base/Zero/sep/status/Add/WriteDescriptor
constructions, first and between-stage Last/At positionings, and both
At(status); WR(1) preludes. Add $12\ell+6$ for the two payload loops and
their CTL/TOK pairs. Add any caller's complete parsing/local origin scans
and **final row ACK** separately. Each workspace loan or return contributes
exactly 13 occurrences (twelve TOKs and its phase CTL). A channel with receiver
setup and return as above has four such handovers, 52 occurrences, in addition
to its setup, positioning, status preludes and $12\ell+6$ copy core. In particular that ACK is not the
intermediate copy-completion TOK. The complete row return sequence is row
construction, missing-block tests and their ordered channels, row channel,
complete receiver checks, final ACK TOK, source-token TOK, idle CTL, fixed
return edge. At stop it instead takes its actual terminal edge after ACK and the
requested finite stop work described next.
Each of these summands is an above finite graph evaluation, not an unknown
setup service. Row-index append is NativeWrite with tag length 2 and two
fields. Stop evaluates the frozen index scan/count, each bounded row/request
scan, construction of the snapshot-index word (UnaryBody and the displayed
Frames), its staging block, the finite ordered dependency channels, snapshot
index channel and release/dependency checks. Verification then sums the
complete initial-packet enumeration, declared finite prior computations and
all historical row/manifest replays and the actual owner-workspace loans;
expected-task binding/proposal construction/channels, receipt construction/channel, consumer
full checks and its selected output/refusal branch follow before halt.
All replica allocation, local descriptor scans and target-bit OUTs stay in
these same primitive recurrences.

For strict Reserve the service order is entry counter/state loads,
before-field staging/reload, CloseFence(start), public comparison/arithmetic/version preparation,
Base/Zero, actual field/response construction, WriteRecord,
CloseFence(publication), response seal/release, CloseFence(response),
AppendCounter($m+1$) and the complete row return sequence. Strict Raise has
its two comparisons and metadata/version preparation, WriteRecord and the
same three fence calls, with no arena Zero. All equal/refusal cases have
entry/start, their actual comparisons/response construction, response
seal/release, response CloseFence, $m+1$ and the same row return sequence;
they have no directory write, new source allocation or publication fence.
Source accepts/rejects both include their actual generator/gates, original
response and applicable $q,g,e$ selection, and the two source-start/response
fence calls, followed by the semantic/unified return route below.
Before commitment, entry counter work prepares $m+1$ and, for each
nonmaintenance event, $j+1$, by their actual Increment/copy/staging graphs.
Source $q,g,e$ versions retain LJA4.2's preparation of both applicable
accept/reject successors without a private branch. This preparation is
counted at its actual precommit position. For a nonmaintenance event the
common postcommit route evaluates selection/AppendCounter of the already
prepared $j+1,m+1$ versions, the complete old semantic/unified-end
scans and staging, the fifteen semantic-field constructions/Frames,
BuildManifest for its layout tuple, semantic bit-block seal/descriptor/
reference construction on 21/17, and the two-field index append on 18.
The unified row then constructs its own full manifest and present semantic
reference. A local or Halt has this same route and its actual packet/output
dependency channels; it is not charged as only a unified marker. Maintenance
has no semantic writer/index/channel, keeps $j$ and its semantic end, and
constructs the literal none tag. Every before-field reload, including $j$
and both predecessor references, is a displayed native descriptor/origin scan.

More explicitly, let $w_1,\ldots,w_{15}$ be the actual semantic field words
at their successive writer entries. Its payload length is
$\ell_J=\sum_{i=1}^{15}(2|w_i|+1)$. Its writer evaluates Base(21), each
field's construction/reload and Frame, sep/status construction, the actual
payload-length scan, Add(status), WriteDescriptor, At(status); WR(1); CTL,
followed by actual reference construction/staging and
NativeWrite(`00`;$U(k)$,reference) on 18. These are the same explicitly
expanded bit-block and native-write graphs above, not service constants.
Add the actual full channel for $\ell_J$ unless that immutable origin is
already acquired, and the joined decoder's fifteen bounded ReadFrames,
all nested tuple checks, unary comparisons and full field equalities.
The actor and verifier each evaluate that checker at their own actual
entry heads; the corresponding workspace transfers and staged local end
words are included. Snapshot construction and dependency delivery include
both counts/ends, every present semantic row and every control/output block.
Receipt and expected-binding construction/copy/checking include those same
two counts/ends. No row reference is charged as though it supplied its payload.

Journal access evaluates its retained query-packet construction and, for an
actor client, the entry admission CTL/busy TOK, actual loan to the actor,
route-49 channel and twelve-token
return to the producer before parsing. A producer-local frozen-prefix helper
uses its owned packet without that channel/loan. Both evaluate the
closed-end scan, every native two-field read, label Increment/Compare,
selected-reference staging, descriptor/status/origin scan, requested row
and missing dependency channels when the caller is the actor, complete
receiver checks and its ACK/source-token/idle return. A producer-local
frozen call returns to its retained frozen continuation without restoring
admission. Source-only and semantic-prefix access additionally sum the bounded
row decodes and kind-filter/rank increments; the selected prefix uses the
same full snapshot route. A zero-based source-request query additionally
evaluates its caller's unary Increment/copy before the source-only packet.
A `no-row` branch evaluates its closed scan, response construction/channel
and return, but creates no journal
event. These extra routines and finite tags are installed and paid in the
same original boot, using only the existing owner partitions and token pool.

These sequences, with $V$ applied left to right to their changing states,
are exact executable recurrences for this graph. They do not predict the
end ordinal from a precomputed favorable fixture.

Gate generation includes every source-field Resolve, real absolute-address
arithmetic and all emitted bits. A gate record has length
$13+d+a+b+c$ in the exact unary encoding. Its interpreted cost is PR57.06,
with its actual head distances, four full address-field copies and their
real descriptor/positioning expansions. The caller supplies the actual
constructed addresses, not a free address map. ReadE, modifications and
literal minterms use the same templates and public loop bounds as their
suppliers. Controller work additionally evaluates its packet channel/canonical frame
construction, actual table/local segments, workspace handovers and complete
returned-state installation from Definition 8.1. Installation evaluates the actual finite native-description
encoding and every boot bit; it is not excluded as a constant migration
premise. The AIF empty-port setup formula is not reused for later nonempty
ports; their Base/Zero/At graphs are evaluated instead.

**Theorem 7.2 (one-run costs and storage).** Let $r$ be any finite actual
primitive prefix, including boot and acquisition if they precede it. If
$n(r)$ is its primitive length and $A(r)$ its number of constructed ordinary
cells, excluding the receipt meter, then

$$
T(r)=n(r),\qquad F(r)=2n(r),\qquad
S(r)=S_0+b_{\rm ctl}(r)+8A(r)+8n(r).
$$

The recurrence in Definition 7.1 determines each operation's exact
contribution and its opcode/owner-purpose counts. All retired words, old
segments, descriptors, gate tapes, candidates, requests, rows, mailboxes,
snapshots, receipts and copied outputs coexist in this storage count.
Neither source-event projection nor mathematical simulation preserves these
clocks or erases the paid audit.

Proof. Induct on actual primitives. Each primitive contributes one tick,
one core fee and one receipt-construction fee, and constructs precisely its
declared finite set of ordinary cells plus one meter receipt. This is exactly
the supplier's primitive convention. Word/code/status/descriptor cells are
ordinary cells, regardless of their logical names. No routine deallocates
them; WR erasure or retirement does not reverse construction. The induction
therefore gives the formula, with actual installed control/token/latch bits
in $b_{\rm ctl}$. Label each primitive by its actual opcode and current
finite owner-purpose phase; summing those disjoint counts recovers $n$,
without counting a helper both as setup and as its caller. Definition 7.1
adds exactly one for that same primitive, so it computes the same totals.
Every strict Reserve performs positive zero-fill, directory and row work;
all other Reserve/Raise branches still perform positive response/row work. A projection omitting their labels
therefore cannot have the same primitive length. $\square$

**Proposition 7.3 (storage-layout costs are different coordinates).** In a
strict Reserve($J$), the newly designated source payload has exactly
$4(J-K)$ new bit cells. No old source payload bit is copied into another
source cell by this operation. A contiguous relocation alternative that
allocates a complete $J$-packet and copies all of the old $K$-packet instead
has $L(J)$ newly designated payload cells and $L(K)$ actual bit transfers.
Both packet relations are sufficient to preserve the same tree if their
own installed authority, routing and publication contracts are fulfilled.
These facts imply no total-runtime dominance between layouts.

Proof. The segmented graph allocates exactly its displayed $d$, and makes
no source-data WR into another cell: its only new source WRs write literal
zero. The old concatenated packet followed by those zeros is the required
$J$-packet, as in Theorem 5.2. For the alternative, a complete new packet
has $L(J)$ cells; copying each of the $L(K)$ old bits and padding the rest
gives the same canonical packet by bit induction, using the already supplied
PR57 allocation/copy services. Copying requires at least the corresponding
RD/WR occurrences, besides all its seeks and metadata. These two relations
are compatible sufficient representation choices, not incompatible source
semantics. The segmented implementation additionally scans its interval
directory on every source-reference compilation. A contiguous implementation
can use a base-plus-offset address. Their metadata sizes, address lengths,
generation work, source accesses and retained cells are separate coordinates;
the displayed payload counts compare only one coordinate. This proposition
does not assert an implemented contiguous dispatcher or a legacy retrofit.
The complete actual instrument of this volume is the segmented one.
$\square$

**Theorem 7.4 (full-cut determinacy and acquired replay extension).** Fix the
installed native graph and boot data, allocator convention and owner model.
After the paid acquired-seed entrance, the acquired seed syntax, actually
consumed public input prefix and absolute primitive ordinal reconstruct the
full actual continuing history and endpoint of this instrument on its lawful
canonical-prefix domain. This includes every inherited busy cut and each
new partial allocation, directory, status, counter, row and channel phase.
Physically executed noncanonical IN remains an executed successor outside
that domain.

Proof. Reuse AIF4.4's primitive induction with the now specified finite graph.
The paid acquisition determines the original seed; initial source ingress
and validation are the declared canonical $H_0$ packet. Boot/public programs
and automatic growth mode are fixed data. From a known state, every non-IN
edge is uniquely prescribed: its head, finite latch, code field, seal mark
or test determines its actual successor. At an IN the retained next input
bit is the only additional choice and determines the corresponding raw
latch/receipt successor. Induct up to the absolute ordinal, retaining all
intermediate primitive states rather than just decoded trees. Resolve and
directory publication have no nondeterministic allocator or hidden pointer;
the new exact graphs thus meet the replay supplier's missing-specification
premise. In particular the copied-but-not-yet-selected counter word, on-sep
versus after-sep field positions, partial Frame lengths and budgets, staged
fence numerals, readout head before its selected F, manifest construction,
local origin descriptors, receiver statuses all partial workspace-token transfers, and the final row/source-token/idle
edges are retained as actual states. The induction uses their installed
next occurrence, not an abstract invariant standing in for that occurrence.
Canonical-prefix input is exactly the same admissibility restriction
for the extended seven-tag language. Both raw bits remain physically enabled
at IN; choosing an inadmissible bit executes it and exits the theorem's
canonical-prefix domain. There is no illegal-none rewrite. The ordinal is a
mathematical replay parameter; accessible closed-cut numerals still require
the actual paid fence scans. This is joint replay, not independent recovery
from each of four natural views or a busy-cut callable materialization
service. $\square$

## 8. One continuing Native/effective execution

**Definition 8.1 (actual effective-controller interface).** A controller is
given by its actually installed finite deterministic transition table,
initial tape and a faithful encoding of the Native control $C$ and operation
packets. It reads only its own state, acquired input and complete returned
responses. Its code has no hidden source, physical-address, clock or future
input argument. For a reached Native instruction, its finite table execution
produces one of local successor, literal address with four continuation
codes, rho successor, or terminal finite output. The code and every
configuration/packet/reference are constructed words, as in PR57.D5 and the
NativeSerialEffective `OriginalCodeRealization` interface. A mathematical
partial-recursive selector without an actual supplied code is insufficient.

Each simulated table step scans its whole finite table, compares actual
unary state/symbol fields, and uses its matching row to write the encoded
new state/symbol and move its simulated tape. The supplied two-stack tape
representation appends complete frames on push and scans/copies a complete
prefix on pop. There is no atomic integer configuration update. Its work is
the exact inherited table-step recurrence evaluated by Definition 7.1.
Finite reached controller computation is an explicit service-progress
premise; divergence retains its actual local primitive history. The waiting
operation packet and continuation remain stored while maintenance runs.
Upon service return, the corresponding successor or acquired-reply branch
is installed by full word copies into controller-owned state, with its
actual table/word positioning. No new controller table is installed after
boot and no command is selected using a free hidden tree size.

The table/local phase borrows the twelve public word ports by the actual
TOK/CTL sequence of Definition 2.2. It completes its persistent state and
waiting packet on 25/27 before returning that pool. At an external Native
instruction it seals the complete operation packet on 27 and sends it by
Definition 6.3 to a producer-owned retained block on 21. This copy occurs
before maintenance; the head/bytes/continuation of 27 at that completed
handoff are then protected throughout the ensuing maintenance. Parse that
acquired packet by its fixed opcode and bounded Frame fields. For a literal
read, copy its entire address into the canonical TagRead payload; for Rho
construct the literal three-bit Rho header and empty payload. The common
header/length/payload construction of Definition 4.6 writes these complete
retained blocks, using copies/Appends instead of IN for computed bits.
Local/stop packets likewise carry their complete executed successor/output
marker material. Continuation codes remain actual words in 27, never a
source-owner oracle or an unstored return register.

Local/terminal packets enumerate the complete executed instruction/output
material they reference. The terminal output is first actually sealed on
31; its complete payload and origin are copied to producer 21 by the same
actor send phase, with its actual workspace loan/return, on route 49 if not
already acquired there, before Halt commits and its semantic
row uses that material. This additional copy preserves 24–27 and is included
in the terminal recurrence. Local packet dependencies use the same rule;
no instruction/output reference substitutes for acquired data.

After all required maintenance and the genuine semantic/unified row return, lend the
pool to the actor for its return handler. It locates the acquired row through
29's local origins, bounded-parses its complete response, scans the retained
packet on 27 for the corresponding fixed successor or four-way literal
continuation, and copies that complete code/state into 25 with the supplied
stack/table word routines. Rho's waiting packet is used only after the genuine
Rho; each intervening Reserve/Raise returns to the producer's suspended
public growth-policy edge. Then return the workspace pool before the next
producer dispatch. Every packet copy, canonical transduction, table segment,
loan/return and state installation is an actual finite graph included in
Definition 7.1; an uncompleted local segment retains its actual unfinished
history rather than supplying a boundary action.

**Definition 8.2 (source-blind safe growth policy).** In the automatic Native
mode, just before an unconditional Native rho instruction, load actual $h,K$
with ReadState and construct $h_*=2h$ by Copy and Add. If $K<h_*$, construct
the complete Reserve($h_*$) command and run its resident service to its actual
acknowledgement. Then construct and run Raise($h_*$) to its acknowledgement,
and finally invoke the original whole Rho once. These internal commands
are constructed public data, retained like other commands, and have no
external IN choices. During them the waiting Native continuation is fixed.
No old reject is first executed and then suppressed. Original guarded clients
use their submitted commands with their existing guard; this policy is a
separately installed mode, not an automatic change of their task.

For an optional explicitly unguarded whole graft with its fully acquired
public context of $d$ leaves, the same mode uses $h_*=h+d$ computed by a full
public context parse and unary Add. The service itself still constructs and
guards the entire actual candidate. Literal reads, ReadE and NativeLocal
need no automatic reserve or raise. The initial acquisition is stationary.

**Theorem 8.3 (uniform finite-prefix lift on the same source).** Fix a valid
paid boot and actual acquired-seed entrance, and an effective controller of
Definition 8.1. Every reached finite Native execution prefix whose local
computations terminate and required finite input is supplied has one finite
paid lift under Definition 8.2 on the same preparation $\xi$, controller,
acquired seed/input and old archives. At completed pure-Native cuts its
current tree is $\rho^e u$. Its Native suffix has exactly the original local,
literal-read and unconditional-update chronology, and its terminal output
when present. Nested prefixes extend this one actual run rather than choose
new per-$H$ installations.

Proof. Maintain $\lambda(t)\le h\le K$ at completed boundaries. For a finite
tree with $a$ alpha and $b$ beta leaves, structural induction on pairing and
the two leaf equations gives

$$
\lambda(\rho t)=a+2b\le2(a+b)=2\lambda(t)\le2h.
$$

The computed $h_*=2h$ is therefore a safe public bound without inspecting a
private count. If necessary, Theorem 5.2's actual Reserve establishes enough
backing while preserving this very $t$. Definition 5.1's Raise is valid and
Theorem 5.3 preserves it while changing the explicit guard. By Theorem 4.5,
the subsequent original Rho must accept and install precisely $\rho t$;
only that genuine accepted rho advances $e$. Its returned response, source
row and maintenance rows are all retained and delivered by Theorem 6.4.
The waiting Native successor is copied into the same controller's state at
the actual return, not into a new machine.

For a literal read, Theorem 4.5 gives precisely the original four-way reply
at the actually submitted finite address, and the given code installs that
reply's continuation. For a local instruction, the given terminating table
execution supplies its exact encoded successor and the inherited local
marker, without touching the source. By Lemma 6.2b its $j$ increment and
semantic row are the inherited local event, not a source call or a
maintenance row. For stop, complete output sealing and
delivery precede the global terminal state. The controller equation and
existing Native trace induction thus give $t=\rho^e u$ and the stated
chronology. The lift's Native suffix starts after the fixed acquired-seed
entrance; that entrance's own old rows remain in the actual archive.
Its local/terminal rows also participate in the absolute semantic ordinal
and predecessor chain; a suffix projection does not reset their stored
counts. All semantic/unified joins and acquired lookups are those of
Lemma 6.2b and the version-aware actual consumers of §6.

Lemma 6.7 supplies the exact common returned boundary, including all
ancillary delivery, final ACK, source-token return and idle CTL; a directory
seal alone is not that boundary. Lemma 6.1b supplies complete fields and actual
fence numerals on the successful and no-change/refusal paths. Each readout
stops at a pre-existing marker despite its own additional receipts.
Each new stage is a finite graph with finite constructed bounds; the reached
table/supply premises make the inherited stages finite too. Inductively
concatenate their actual shared endpoints. The native graph, source, state,
allocated intervals and consumed choices at an earlier endpoint are exactly
the ones from which the next fragment starts. Determinacy gives prefix
agreement; no final horizon, new preparation or freely supplied larger
snapshot is chosen. For $r$ Native updates the displayed policy has
$h=2^rH_0$, with finite backing at each finite stage. The optional graft
variant uses $\lambda(\langle v,t\rangle)=d+\lambda(t)\le d+h$ and the same
induction; it retains the tree/capacity invariant but does not have the
pure-rho orbit equation. Every added primitive and receipt is still present
in the full history and costs of Theorem 7.2. $\square$

**Corollary 8.4 (unbounded run versus infinite source).** If an infinite
Native command execution satisfies the reached local/input progress premises,
the construction determines one mathematical infinite primitive execution,
with finitely many constructed cells at every finite cut. This does not
construct an arbitrary infinite *initial* source or finite-resource global
acquisition of one.

Proof. Theorem 8.3 produces compatible finite fragments, each containing an
actual positive finite number of primitives. Their successive concatenation
therefore has order type omega and its finite cuts lie inside finite
fragments. Lemma 3.5 and Theorem 7.2 make storage finite at each such cut.
The initial source was one finite $u$. No step adds an unknown infinite
payload; reservation appends only zeros and genuine updates compute finite
successors. Thus neither a new infinite initial object nor a finite end at
which all its payload has been acquired follows. Withheld input or divergent
local work also prevents an unconditional service-progress conclusion.
$\square$

## 9. Recovery directions and exact outstanding domains

**Definition 9.1 (projections and identity types).** Let the complete actual
history retain every IN, write, gate, head move, receipt, status change,
publication, response, row, copy and acknowledgement. The source-event
projection retains genuine ReadE/TagRead/modification calls and their original
responses, including every reject, and separately records the intervening
guard sequence. The pure-Native projection in Theorem 8.3 retains Native
local/read/update events and terminal output. These are different projections.
The semantic-journal projection retains all seven LJA kinds, including Halt,
and omits maintenance; its length is $j$. The source-call projection omits
local/Halt as well and has length $q$. The unified event length is $m$.
Lemma 6.2b relates their ordinals; no projection changes an old record's
actual ordinal, reference or seal meaning.
Source occurrence, tree value, allocation interval, layout ordinal, policy
ordinal, accepted generation, rho epoch, frozen archive prefix and receipt
creation are distinct identity types.

**Theorem 9.2 (the operational bridge and its precise ceiling).** Within the
declared ideal model, the original acquired source, controller and archive
configuration has a reachable paid operation changing its current source
backing/capacity, together with source-address/destination, owner, input,
identity, historical-guard and one-run cost correspondence. At fixed guard
this preserves all original lawful source calls; explicit guard raising
allows the continuing Native lift. This supplies the operational extension
left outside LJA's pointwise capacity-safe theorem. It supplies neither a
retrofit of a closed legacy graph nor individual exact kernels for natural
space, time, boundary and callable memory views.

Proof. The original entrance and installed authority are Definitions 2.3–2.4
and 4.6. Theorem 5.2 gives the actual reached reservation on that source;
Lemmas 4.3 and Theorem 4.5 give the physical source operands and destinations,
including raw update cuts. Theorem 6.4 supplies old-handle meanings, complete
delivery and owner correspondence; Lemma 6.2b supplies the full semantic/
unified record, index, predecessor and acquired-lookup relation, including
NativeLocal/Halt and every maintenance outcome. Theorem 6.6 supplies the actual
historical-guard consumer and unchanged initial-target type. Theorem 7.2
accounts for all occurrences on that run and Theorem 7.4 retains every busy
state and acquired input distinction. Theorem 8.3 composes these actual
endpoints into one continuing effective execution. These statements prove
the positive conclusion without borrowing allocation, replay or infinite-tree
semantics as a missing source-owner action.

The domain expressly begins with this resident extension's boot. A closed
legacy graph need not have a maintenance entry or permission, so this
construction provides no transition from its arbitrary state into the new
domain. Further, joint replay has a lossless *tuple* as input. It proves
neither that an individual natural-view map is injective on the relevant
task fibers nor that that view has a lawful paid inverse. No theorem above
provides those missing inclusions or inverse services. $\square$

**Definition 9.3 (remaining programme obligations).** The following domains
are not claimed by the instrument:

1. A real authority-preserving retrofit from an already closed legacy graph,
   or an arbitrary external raw-pointer inventory with its own alias rights.
2. Arbitrary-busy-cut callable freeze/recovery, crashes, concurrent source
   access, interrupt resumption, and a physical refinement below the declared
   atomic primitives. Busy states and their deterministic replay exist here;
   those extra services do not.
3. Separate natural spatial/support, temporal-history, boundary-response and
   callable-memory maps with both kernel inclusions, lawful transport and
   paid individual recovery. Renaming the joint replay tuple would not supply
   these maps.
4. An actual infinite initial alpha/beta source with locally acquired
   observations, an infinite-source exhaustion/acquisition bridge, or
   finite-resource global acquisition. TMC23's compatible infinite semantic
   carrier remains reused semantic work.
5. The full late-target memory-rate, sharp-rate and effective all-size
   certification programme, and any optimality or total-resource dominance
   of this layout/policy. The expensive minterm literal instrument is only a
   sufficient instrument.
6. Lean certification of this new construction or empirical conformance of
   devices to its owner, allocation, seal and receipt conventions.

The source-event capacity spectrum/timetable characterizations are not used
as a substitute for this instrument. If attached as an additional audit,
they must use the fixed seed and read-consistent completed source-event word
produced by the historical-guard consumer. They do not classify full input,
PC, receipt-cost or partial-state histories. The existing TMC30.3 witness and
TMC30 subsection 30.4 static projection remain credited suppliers, without
a new-content claim.

## 10. Mathematical sources and applicability

**Convention 10.1 (literature correspondence).** The segmented directory,
resident admission, real source-reference compiler, metadata consumer and
their joint ordinary proofs are `repo-derived` compositions of the specified
suppliers. No research-originality claim is made. Primary literature supports
the following exact external structures, rather than providing this source
instrument, its paid clock or its archive identities.

| Primary source | Exact correspondence and boundary |
| --- | --- |
| Nancy Lynch and Frits Vaandrager, *Forward and Backward Simulations, Part I: Untimed Systems*, Information and Computation 121(2), 1995, 214–233; [author manuscript](https://groups.csail.mit.edu/tds/papers/Lynch/IC95.pdf), §3.2, Lemma 3.8 and Theorem 3.10, manuscript pp. 11–12 | An initial-state relation and a finite matching fragment from every related state establish trace inclusion. Theorem 4.5 supplies the particular gate correspondence here, and Theorems 5.2/8.3 supply actual continuing fragments. The cited theorem does not give an inverse decoder, installed owner authority or equal clocks. |
| Xavier Leroy and Sandrine Blazy, *Formal Verification of a C-like Memory Model and Its Uses for Verifying Program Transformations*, Journal of Automated Reasoning 41(1), 2008, 1–31, DOI [10.1007/s10817-008-9099-0](https://doi.org/10.1007/s10817-008-9099-0); [author manuscript](https://xavierleroy.org/publi/memory-model-journal.pdf), §5.1, Lemma 38, and §5.4, Lemmas 65–69, manuscript pp. 13, 22–23 | Mapped loads, disjoint intervals and compatible extensions motivate the explicit $\phi_K$ relation. Compatible extension preserves every old mapped block at the same image; it is not permission to rebind a previously mapped block. Lemma 4.3 proves that property for this representation, with actual paid unary resolution. The paper does not include $\xi$, guards or PR57 receipts. |
| David Monniaux, *Memory Simulations, Security and Optimization in a Verified Compiler*, [arXiv:2312.08117v1](https://arxiv.org/html/2312.08117v1), §4.2; CPP 2024, DOI [10.1145/3636501.3636952](https://doi.org/10.1145/3636501.3636952) | Pointer operations and external calls must commute with their injection; testing particular offset bits can fail to commute. This corresponds to requiring source operands *and destinations* to resolve through the same map and to excluding arbitrary pointer-bit observations. It supplies no source-growth dispatcher or historical-guard equivalence. |
| Nick Wanninger, Tommy McMichen, Simone Campanoni and Peter Dinda, *Getting a Handle on Unmanaged Memory*, [arXiv:2405.00038v1](https://arxiv.org/html/2405.00038v1), §§3.2, 4.1.3–4.1.4; ASPLOS 2024, DOI [10.1145/3620666.3651326](https://doi.org/10.1145/3620666.3651326) | Translated handles pin backing while raw pointers exist; compiler StackMaps, safepoints and barriers locate valid pin sets. Its external-library/allocation/alias assumptions are substantive. The present sequential instrument instead has an explicit exclusive source token and gives the actor no raw source pointer. Its old-handle theorem is proved for that smaller declared interface, not imported from Alaska or extended to its concurrent setting. |
| Samson Abramsky and Achim Jung, *Domain Theory*, Handbook of Logic in Computer Science, volume 3, 1994; [corrected author version](https://www.cs.ox.ac.uk/files/298/handbook.pdf), Definitions 2.2.20–2.2.21 and Proposition 2.2.22 | Ideal completion requires an abstract approximation basis with finite interpolation and constructs a continuous semantic domain. It is a semantic-completion reference for the already supplied infinite-domain discussion, not a paid source entrance, local observation or growth mechanism. |

The assumptions of these references do not identify mathematical completion,
trace refinement, memory injection, acquired payload and actual installed
authority. Those are separate relations above. Every new finite recipe is
specified in terms of the declared primitive model; none of these literature
names is used as a missing implementation step.

## 追加锚（本行以下为增补区）

## 11. Uniform structural storage for the capacity instrument

**Convention 11.1 (source, task and credited interfaces).** Write CAP for
this volume, SSA for *Native structural storage, support, and the
terminal-boundary atlas*, AIF for *Native acquired-input frontier and exact
replay*, RCA for *Native retrospective cut acquisition*, and CSA for
*Native callable storage atlas*. The following application uses CAP
Definitions 2.2–2.4, 3.3, 5.1, 6.1–6.5 and Theorems 5.2, 7.2, 7.4;
SSA Definitions 3.1–6.1 and Theorems 4.4, 6.2; and CSA Definitions
3.1–4.1 and 8.2, Lemma 3.4 and Proposition 8.1. It does not identify the
operational domains of those volumes. In particular CSA's installed RCA
service has a fixed source-capacity parameter; its four-kernel and Call
theorems are not cross-capacity theorems about CAP.

Fix one actual finite CAP native graph, resident boot, raw or effective
mode, controller realization where used, allocator convention and supplied
initial data. Keep its original $H_0$, preparation occurrence $\xi$ and
actually acquired seed syntax of $u$. At later cuts write $t$ for the
current source. Reserve changes its backing; genuine Rho or grafting can
change $t$; Raise changes a later admission guard. None changes the
meaning of the initial target $q_{H_0}(u)$ or an earlier row's guard. All
statements below concern this one initialized instrument. Variable
integers, programs, controller states and saved returns remain its actual
tape words, rather than values stored in an unbounded finite controller.

The original continuation task is AIF Definition 2.6's partial
finite-experiment response task instantiated with CAP's installed rows and
seven-tag canonical source/maintenance language. It retains legal domains,
labels and complete original successors; hidden successor coordinates are
mathematical observations, not actor read permissions. Its actual domain
includes busy parsing, address resolution, source overwrites, maintenance,
rows, copied descriptors, checks and returns, rather than just idle
endpoints. At a physically enabled IN both raw bits still execute. A bit
leaving the canonical-prefix domain has its real latch/control/receipt
successor and exits that domain. Boot/preparation/acquisition have their
original entrance restrictions. A global Halt retains its original
terminal meaning. Call this task $Q_{\rm CAP}$. No assertion below replaces
it by an everywhere-continuing diagnostic task.

**Definition 11.2 (the sole physical-record representation).** Let $b\ge1$
be a finite number of potential native finite-bit locations, enumerated
from the fixed graph and its boot constructors. This bounds the native
primitive PC, latches, ownership/control flags and finite row-selection
material, not the sizes of code or counter words on tapes. Let $z_i$ be
$\bot$, 0 or 1 according as location $i$ is not yet constructed or holds
that bit. Use CSA's actual optional socket, not an initially present zero:

$$
a(\bot)=\bullet,\qquad
a(0)=((\bullet,\bullet),\bullet),\qquad
a(1)=(\bullet,(\bullet,\bullet)),\qquad
R(z)=F_b[a(z_1),\ldots,a(z_b)].
$$

Use SSA's eight-track cell switch, right-spine tape encoding and outer
$F_{65}$ with the 64 actual tapes and $R(z)$. Include the actual tape
boundary symbols, head marks and maintained origin/head links. A head link
is absent before its original constructor; the meter has two distinct
head links. No descriptor-to-payload access edge is added. Denote the
resulting tree and linked carrier by $U(W)$ and $\Gamma(W)$, where $W$ is
the comparison raw record of actual finite bits and tape tracks. On the
structural realization the incidences are the storage: a second copy of
$W$, a replay archive or a shadow source is not maintained beside them.
The fixed empty socket scaffold and finite rule description are priced
apparatus. Unbounded future reserve values are not apparatus parameters.

**Proposition 11.3 (uniform raw-storage application).** On the stronger
priced atomic patch basis of SSA Assumption 3.1, the one fixed CAP graph
has a finite structural row realization independent of a future maximum
reserve. It represents its original boot and all actual subsequent native
rows, with the same inputs, core/receipt effects, owner guards and return
edges. At its native-row boundaries define independently

$$
S_{\rm raw}(W)=\operatorname{Pos}(U(W)),\qquad
B_{\rm raw}(W)=\operatorname{Leaves}(U(W)).
$$

Then each of these two observations, separately, has equality kernel
exactly raw-record equality:

$$
\begin{aligned}
S_{\rm raw}(W)=S_{\rm raw}(W')&\ \Longleftrightarrow\ W=W',\\
B_{\rm raw}(W)=B_{\rm raw}(W')&\ \Longleftrightarrow\ W=W'.
\end{aligned}
$$

Here positions and leaves are actual ordered spatial paths, and equality
of raw records includes the construction domain. The statement is not an
assertion that raw-record equality equals $Q_{\rm CAP}$-equivalence.

Proof. Instantiate SSA Definition 5.2's finite pattern enumeration with
the fixed CAP rows. Each row uses fixed finitely many tape/head roles,
finite latch/control tests and at most its core cell constructor plus its
receipt constructor. All unbounded iteration in Resolve, Zero, field
scans, gate interpretation, journals and verification is iteration of
these rows. It does not require a new pattern for a larger unary numeral.
Combine actual core/receipt aliases before assigning a target, exactly as
in SSA. A newly constructed finite bit uses CSA Definition 3.3: retain its
socket root, create the four prescribed vertices and initialize their
28 slots and the root's two child slots. The choice of bit is its actual
native constructor value. Its absence is never treated as zero.
Existing-bit writes, cell appends and head moves use the supplier's
bounded stencils. The finite pattern table keeps each original guard,
including ownership and source availability. Internal trusted probes
supply no actor with an all-owner read operation.

Start with the actual native foundation, its two meter boundary cells and
actually endowed finite bits. Represent subsequent boot constructors as
their own rows. Induction on the actual next row proves the commuting
core-and-receipt square and keeps the actual head/link relation. The IN
case includes either raw bit even when it leaves the task domain. Source
bit overwrites are represented as raw bytes without asserting a valid tree
midway. The same induction covers copied-but-unavailable blocks, directory
publication before response commitment, either journal's partial seals,
old and new guard/counter versions, lookup, verifier work and Halt. A
structural patch is one declared atomic commitment per native row; no
claim is made about a finer cut inside its slot assignments. The induction
can be extended at every actual Reserve/Raise on the same initialized
execution, without reinstallation or an upper bound on later $K$.

For the inverse, decode each fixed finite socket as absent/zero/one; its
three shapes differ. Decode each eight-track cell and the end of each
right spine by SSA Theorem 4.4. This recovers every raw track, finite flag
and head mark; the marks determine the access links. Conversely the raw
record constructs exactly that support. Independently, a finite full
ordered tree satisfies

$$
\operatorname{Pos}(U)=\{p:p\text{ is a prefix of a terminal path of }U\}.
$$

Thus the actual terminal antichain reconstructs the whole support and the
same component inverse. Each equality has both inclusions. Actual native
creation identities remain those of the commuting execution; structural
auxiliary identities use its occurrence and fixed constructor role. This
is the SSA/CSA storage construction instantiated at CAP, not another
generic compiler or a new kernel theorem. $\square$

**Proposition 11.4 (one-run structural accounting).** In this application
let $C_{\rm cell}$ count all constructed native tape cells, including
boundary cells and the meter, let $c$ count actually constructed finite
bits among the $b$ sockets, and let $\ell_{\rm head}$ be the actual number
of constructed head links. The carrier counts are

$$
\begin{aligned}
V&=127+2b+4c+48C_{\rm cell},&
L&=64+b+2c+24C_{\rm cell},\\
E_{\rm tree}&=V-1,&E_{\rm access}&=\ell_{\rm head}\le65.
\end{aligned}
$$

Occupied endpoint slots number $2(V-1+\ell_{\rm head})$ and slot capacity
is $7V$. After boot/acquisition $\ell_{\rm head}=65$. There is no subtraction
for dead words, overwritten data, inactive control versions or copied
outputs. $K$ remains designated source reserve, not $C_{\rm cell}$ or $V$.

For the same actual row $i$ let $e_i$ count core-plus-receipt cell appends,
$s_i$ fresh finite bits, $t_i$ designated existing-bit targets after alias
combination, $r_i$ retargeted head links, and $a_i$ first head activations.
An unchanged-value designated write is counted. A bit in $s_i$ is excluded
from $t_i$. Use the ordered probes $p_i$ of CSA Definition 8.2, with its
finite-slot parameter $q=b$ and its actual pre-row $c$. Explicitly, with
that definition's cell-role, append-site, old-head-walk and fresh-slot-root
lists $\mathcal C_i,\mathcal A_i,\mathcal J_{i,\rm old},\mathcal Z_i$,

$$
\begin{aligned}
p_i={}&d_r+6b+12c_{i-1}-4
 +\sum_{x\in\mathcal C_i}(|\pi_x|+140)
 +\sum_{z\in\mathcal A_i}(|\pi_z|+2)\\
 &+\sum_{w\in\mathcal J_{i,\rm old}}|w|
 +\sum_{z\in\mathcal Z_i}(|\pi_z|+2),\\
v_i={}&48e_i+4s_i,\\
w_i={}&4t_i+2e_i+2s_i+3r_i+2a_i+7v_i,\\
g_i={}&1+p_i+w_i+v_i.
\end{aligned}
$$

Here $d_r$ is the fixed root-to-register route. Repeated probes and routes
are charged again; access is by maintained links, not a numeric Seek.
With $C_{{\rm cell},0}=2$ and actually endowed $c_0$, the foundation has
$V_0=223+2b+4c_0$ and replacement price $g_0=1+8V_0$. At a finite native
prefix of length $n$ use $G=g_0+\sum_{i=1}^n g_i$, and also charge the
finite apparatus description and mechanism. $G$ is the structural
replacement tariff; if both native and structural tariffs are levied,
the declared combined fee is $2n+G$.

Proof. The fixed socket component has $2b-1+4c$ vertices and $b+2c$
terminals. Each tape with $k$ cells contributes $48k+1$ vertices and
$24k+1$ terminals. Adding the outer 64 internal vertices gives the two
formulas, including the two-cell foundation. The per-row expressions are
CSA.11–CSA.13 with these actual lists: seven initialized slots for every
new vertex, two root slots per append or fresh bit, four assignments per
existing bit, and three/two per moved/new head link. In particular a fresh
finite bit has $4$ vertices and $28+2=30$ assignments before its native
control/receipt effects. Summation is on this same CAP execution. In its
original tariff Theorem 7.2 still gives $T=n$, $F=2n$ and
$S=S_0+b_{\rm ctl}+8A+8n$, where $A$ excludes the meter and uses that
theorem's ordinary-cell convention. It is not the total-cell convention
$C_{\rm cell}$ above. All installation, acquisition, directory resolution,
source writes, both journal writers/readers, copies, checks, output and
retired material are included whenever they occur in that prefix. No
physical latency, energy bound or total-resource improvement follows.
$\square$

**Remark 11.5 (the terminal-task obligation).** Spatial support, physical
terminal antichain and literal retained history can distinguish two raw
records even when a chosen future task cannot. A storage terminal is a
leaf of $U$; a global Halt is an operational terminal. They are different
notions. SSA's and CSA's task-rigidity proofs use a lawful continuing
successor at every cut. CAP also admits an absorbing global terminal,
where that argument is unavailable. On an absorbing subdomain where every
nonempty experiment is rejected or undefined in the same way, future
equivalence is just equality of its allowed terminal readout (and type).
Lossless historical views have the same kernel there only if that readout
separates the histories they separate. This is an exact missing condition, not evidence of an actual
terminal collision or proof of terminal injectivity. No such pair or
separation proof is supplied here. Proposition 11.3 therefore asserts raw
physical exactness only; it does not change $Q_{\rm CAP}$ to force a
four-view theorem.

## 12. Acquired response frontiers and historical cuts

**Definition 12.1 (an actually acquired frontier).** Work after the genuine
seed acquisition in the same initialized execution. Choose a reached
nonterminal acknowledged return $d_i$ of the ordinary seven-tag dispatcher
or of its fixed installed automatic/effective controller. For this
statement no independently selected optional archive/service command is
inserted between those requests. Such a command would require its own
retained/acquired input and stopping rule. Let $D_i$ consist of what the
actor actually possesses there: its acquired seed and original fixed
boot/mode/controller data; all delivered unified rows through that
return, their semantic mates when present, both predecessor chains; the
complete copied request, control, return and output dependencies; and their
sealed local origin descriptors and current read rights. These are the
mandatory acquisitions of Definition 6.3, not proposed rows or a producer
pointer. In particular all external canonical request bits through this
return are present in their actual event order. Generated automatic
commands and computed source replies are not additional external INs.

Let $\nu_i$ be the primitive ordinal of this last event's response-commit
fence. Its row includes the complete acquired fence word

$$
\operatorname{Frame}(\mathrm{kind})\,
\operatorname{Frame}(U(f))\,
\operatorname{Frame}(U(\nu_i))\,
\operatorname{Frame}(U(2\nu_i))\,
\operatorname{Frame}(\xi)\,
\operatorname{Frame}(\mathrm{event/directory\ binding}).
$$

Definition 6.1a's paid scans constructed these numeral payloads before
row delivery. $f$ is the fence ordinal, $\nu_i$ the absolute primitive
ordinal, the unified row has its own event ordinal, and its local copy has
its own descriptor ordinal. None substitutes for another. Source-only and
semantic counts do not include maintenance in the way the unified count
does; Definition 6.2a's $\epsilon$ and $\sigma$ remain the actual join.

**Proposition 12.2 (response-frontier application of acquired replay).**
From $D_i$ there is a finite mathematical procedure that reconstructs the
same actual primitive history through $\nu_i$, and, for every selected
ordinal $k\le\nu_i$ after acquisition, its literal prefix and complete
endpoint. It can also compute the ordinal $N_i=|d_i|$ of this nonterminal
acknowledged return and extend the reconstruction through $N_i$. At any
later such actually acquired frontier, reconstruction restricts to the
identical earlier prefix, including its old guards, layout, rights and
preparation occurrence.

Proof. Apply the actual local descriptor/origin resolution of Definition
6.1 to the acquired material, not to a remote owner's private address.
The bit decoders of Lemma 6.1b give the original request headers, lengths
and payloads, in unified-row order. In raw mode concatenate their actual
wire bits, excluding physical separators, status cells and computed
responses. In the fixed automatic/effective mode, Definitions 4.6 and
8.1–8.2 instead generate those command blocks by Append/copy from already
acquired data, so their bits are not put in the external-input reservoir.
The fixed boot mode and deterministic control distinguish these cases;
no classification is guessed from equal command bytes. Acquired initial
input and any actual externally supplied command bits are retained in
their prescribed input-site order. For local/controller markers use the
acquired instruction/return dependencies and the fixed installed graph;
do not fabricate external input frames. Thus the resulting finite
reservoir contains exactly the actual external input consumed through
$d_i$. In particular it is a superprefix of the input consumed at
$\nu_i$ and at every earlier selected $k$.

The response fence's $U(\nu_i)$ is actually present. Run Theorem 7.4 with
the acquired original seed and this reservoir, stopping after $\nu_i$
original primitives, or after $k$ of them. Its induction requests a bit
only at the actual next IN before that stop, so it consumes exactly the
corresponding input prefix; an unused reservoir suffix has no effect.
This is RCA Lemma 4.5's superprefix argument applied to CAP's specified
graph, not a new replay theorem. Its state includes an IN-before-WR latch,
a partial invalid source packet, staged counters, pending semantic or
maintenance event, either journal writer and an unavailable copy whenever
that is the actual phase. Old permission bits are reconstructed as data;
they are not activated in the present machine.

For the last nonterminal row, response commitment is followed by the
specified fence readout, manifest and row construction, dependency copies,
actor checks, final row ACK, source-token return, idle CTL and saved
return edge. The installed graph and complete acquired dependencies fix
this tail; it admits no additional independent external IN before that
return. Simulate it until that particular row's acknowledged saved return,
counting every original primitive. Lemmas 6.1b and 6.7 give termination.
This computes $N_i$ rather than assuming the response fence is already the
row seal, ACK or return. It is the closed-boundary stopping method of RCA
Theorem 4.4 on this restricted CAP return, with the response ordinal
already acquired. For any $k\le N_i$ stop this same reconstruction at $k$.

Later delivered rows append without altering the acquired immutable
prefix. Determinism and the same boot, allocator and input choices make
later reconstruction agree at each earlier primitive. Reserve's stable
address extension and Raise's historical-guard checks are retained as
executed work, not replaced by the latest reserve or guard. $\square$

**Corollary 12.3 (conditional retrospective coverage).** If one actual
continuing execution has cofinal such acquired acknowledged returns, then
every finite cut after acquisition lies in one of their reconstructible
intervals. For a finite flight the corresponding assertion holds only
through its reached final frontier. A selected older busy cut need not
have been callable at that older time.

Proof. Cofinality gives a reached $d_i$ with $k\le N_i$ for the actual
finite ordinal $k$. Proposition 12.2 gives that prefix. It supplies no
frontier when input is withheld or local work does not terminate. Its
hypothesis is an actual continuing execution, not compatible descriptions
from which an infinite input, source or run can be inferred. $\square$

**Remark 12.4 (acquisition and payment still required).** The computation
above reuses the CAP/AIF/RCA mathematical reconstruction interfaces. It
does not add a callable decoder to CAP. $D_i$ gives neither an actor
token for the producer meter nor permission to invoke RCA on CAP's
occupied verifier lanes. Even if a future paid decoder enumerates every
eligible older ordinal, the intended one must be lawfully bound or
acquired; a later archive cannot supply an uncommunicated intention.
Section 13 gives a concrete growing selection requirement. A terminal
verification/proposal route is not the nonterminal tail used above: any
independent terminal proposal or prior input must also be acquired, and
the terminal stopping/callability conditions proved for that route. Those
obligations are left open. Existing terminal consumer work is preserved.

## 13. Mandatory Reserve cuts distinguish unchanged acquired memory

**Definition 13.1 (the actual zero-fill cut family).** Fix a reached idle
valid state with current source $t$, guard $h$ and reserve $K$, and an
actual canonical strict Reserve($J$), $J>K$. The source, preparation
$\xi$, original $H_0$ and acquired $u$ are the ones of that execution.
Put $d=4(J-K)$. In Definition 3.3's Zero(16;$d$), after Last(bound) and
Tail(16), let $c_z$, $0\le z\le d$, be the cut immediately before its
bound-test RD after $z$ successful iterations. In particular $c_d$
precedes the terminal-zero test, not the appended delimiter. Write
$n_0=n(c_0)$ for its actual absolute primitive ordinal.

Define $C_{\rm old}$ at these cuts to retain only the already acquired
preinterval material: the actual protected controller table, persistent
state, seed and saved return on 24–27 with their heads and rights; the
previously acquired immutable archives, dependencies, sealed descriptors
and handle meanings; and the common busy/Zero-test phase. It contains no
producer work head, bound-cursor position, new arena cell, live meter,
pulse counter or copy of the primitive ordinal. Previously acquired
source-layout descriptors keep their original typed meanings; they grant
no private-source read. This is a specified observation of old acquired
material, not a claim that every conceivable retained-memory view omits
a frontier.

**Theorem 13.2 (a concrete growing discrimination requirement).** For all
$0\le z\le d$ the $c_z$ are lawful cuts of this same invocation, with

$$
n(c_z)=n_0+5z,\qquad C_{\rm old}(c_z)=C_{\rm old}(c_0).
$$

They are pairwise inequivalent for $Q_{\rm CAP}$. Consequently any
supplement $E$ for which $(C_{\rm old},E)$ determines either the selected
complete cut or its full $Q_{\rm CAP}$ response profile must take at least
$d+1$ distinct values on this family. A fixed-width $b_{\rm sel}$-bit
supplement must satisfy

$$
2^{b_{\rm sel}}\ge d+1,\qquad
b_{\rm sel}\ge\lceil\log_2(d+1)\rceil.
$$

Proof. The bound is a sealed $U(d)$ on another port. One successful
iteration executes exactly RD(bound), EX(16), WR(16,0), MR(16),
MR(bound). It consumes its next leading 1 and constructs one fresh zero
payload cell. Before publication none of those rows changes the old source
payload, active reserve, current guard, completed directory or committed
semantic/unified event counts. They leave 24–27 and the old acquired
archives/rights untouched. The bound cursor, producer heads/latches,
new arena and meter do change, and were explicitly excluded from
$C_{\rm old}$. Induction on $z$ proves its constancy and the exact ordinal.
At $z=d$ the cursor has reached the sealed zero; this is still a lawful
pending RD. All these cuts have the same prescribed Advance for that RD.

Its complete successor has $n_0+5z+1$ receipts. Different $z$ therefore
give different complete successors on this same legal one-primitive
experiment, whether the RD reads 1 or the final 0. The original
complete-successor task distinguishes them without a private read by the
actor. If two of their $E$ values were equal, a decoder of their equal
$(C_{\rm old},E)$ would have to give two different cuts or response
profiles. This is impossible. Counting the values proves the inequality.
It is RCA Theorem 3.3's generic selection principle with an explicitly
instantiated mandatory CAP fiber, not a new abstract information theorem.
$\square$

**Proposition 13.3 (a legal five-cut instance).** After the actual acquired
beta entrance with $H_0=h=K=1$, supply Reserve(2). Its five Zero-test cuts
have ordinals
$n_0,n_0+5,n_0+10,n_0+15,n_0+20$. All preserve that old acquired material.
Their next RD successors have pairwise different receipt lengths. A
fixed-width binary discriminator needs at least three bits.

Proof. Theorem 5.2 applies to this same finite source; no update or guard
raise is necessary. Here $d=4$, so Theorem 13.2 gives the five cuts, their
ordinals, unchanged old acquired material and distinct successor receipt
lengths. Its bound gives $b_{\rm sel}\ge\lceil\log_2 5\rceil=3$. This witness
uses legal states of one source, rather than two inconsistent packet
interpretations or arbitrary supplied pointers.
$\square$

**Corollary 13.4 (no fixed finite supplement over all actual reserves).**
In raw dispatcher mode, start at that acquired beta state and successively
supply Reserve($2K$), retaining $h=1$ and the current $t=\mathrm{beta}$.
Under the actual input and local-progress premises, these completed
invocations concatenate on the same source. The invocation indexed by
$r\ge0$ enters with $K=2^r$ and has $4\cdot2^r+1$ pairwise distinguished
Zero-test cuts with the same $C_{\rm old}$ within that invocation. No
supplement with one fixed finite alphabet distinguishes all these fibers.

Proof. Each strict Reserve preserves $t,h,\xi,u$ and returns with reserve
$2K$ by Theorem 5.2. Induction gives the stated entrance. Theorem 13.2
applies to each actual finite fragment. An alphabet of size $M$ fails as
soon as $4\cdot2^r+1>M$. This is one recursively supplied sequence of
commands and compatible reached entrances, not a separate realization for
each cutoff. Without its supplied commands and progress, only the finite
concatenations are asserted; compatible storage descriptions alone do not
supply an omega-run. The example also does not require changing the fixed
effective growth policy of §8 into this raw-mode sequence. $\square$

**Proposition 13.5 (a later common archive does not select an intention).**
Fix one of these invocations and a later reached acquired frontier covering
all its $c_z$. Consider the $d+1$ possible recovery requests whose intended
targets are those cuts, with the actual execution and later acquired data
held fixed. Any successful target-selection interface must distinguish
these intentions by an actually bound/acquired relation with at least
$d+1$ values. Supplying more identical copies of that common later history
does not remove this requirement.

Proof. The later acquired object is identical for all these requests;
only their intended target varies. The requested outputs are pairwise
distinct by Theorem 13.2. A deterministic selector with identical acquired
arguments returns the same output, so it cannot satisfy two distinct
intentions without an additional distinguishing argument or previously
bound selector state. The same counting argument gives the bound. An
already acquired authentically indexed frontier can provide such a
relation; it is not ruled out. This proposition requires no Freeze at the
older busy cut and proves no impossibility for a later authorized paid
recovery. It identifies information that a recovery interface must really
receive. $\square$

**Proposition 13.6 (local costs on that invocation).** Measured on its one
actual native run, from $c_0$ to $c_z$,

$$
\Delta T=5z,\qquad \Delta F=10z,\qquad
\Delta A=z,\qquad \Delta n=5z,\qquad \Delta S=48z.
$$

Here $A$ and $n$ use Theorem 7.2's nonmeter ordinary-cell and primitive
receipt conventions. No finite-bit location is constructed in this loop;
finite control values can change. From $c_0$ through the final bound test,
the loop uses $5d+1$ primitives and $d$ new source payload cells. Its
following delimiter costs three more primitives and one more ordinary
cell; setup, publication, fences, journals, copies and ACK are additional.
For the first $R$ completed doubling invocations of Corollary 13.4 the
Zero bodies alone, including each final test, contribute exactly

$$
\sum_{r=0}^{R-1}(5(4\cdot2^r)+1)=20(2^R-1)+R
$$

primitives and $4(2^R-1)$ source payload cells. These are lower bounds on
whole-prefix time and total construction, not a complete-operation saving.

Proof. Count the displayed five rows per successful iteration. Only EX
constructs a nonmeter cell; each of the five rows constructs its one
receipt. Theorem 7.2 gives $8z+8(5z)=48z$ additional modeled storage.
The terminal RD adds a receipt but no payload. Append(sep) is EX; WR; MR
and is outside the displayed sum. The geometric sum gives the last two
expressions. Entire-run resource accounting still uses §7 or Proposition
11.4 on that very execution, including all input acquisition, allocation,
directory/source addressing, row writers/readers, local copies, checking,
return and retained dead material. The selector bit count is not a
pointer-length bound, an executable decoder price, physical memory bound
or proof of total-resource optimality. $\square$

## 14. The literal CAP-verifier and RCA-bank common-entry obstruction

**Definition 14.1 (unchanged-entry comparison).** Compare CAP Definition
2.2 and RCA Definitions 11.1–11.4 at their actual initialized service
entrances. The literal-identification hypothesis would use the same
physical port 33, same L origin, same original readers and writers, and
no added translation or prefixed-sentinel exception. It would retain CAP's
verifier and consumer rather than substituting RCA's service for them.
RCA assigns its eight word-compiler lanes 32–39 to its owner; bank B is
33. Both banks receive an initial literal F sentinel before any version.
CAP assigns 33 to the verifier's native bit-block descriptor stream. These
are actual uses, not names for two freely supplied disjoint ports.

**Theorem 14.2 (no literal common initialized descriptor/bank entry).**
Under this unchanged-entry hypothesis no physical state satisfies both
original ready-stream invariants. If the separate owner tokens are kept,
CAP has no right to read the RCA-owned lane. Identifying those tokens does
not repair the stream grammar.

Proof. CAP Definition 6.1's ReadDescriptor begins Home; MR. Its first RD
recognizes terminal R or the first tag bit. Every nonempty valid descriptor
stream starts with the literal tag `00` followed by sep, ten bit-word
fields each followed by sep, then seal. Hence at this origin the first
symbol after L is R for an empty stream or 0 for a nonempty one. There is
no leading-F branch. RCA initializes bank B by appending F; later bank
versions are appended and no old sentinel is overwritten. Its first
ordinary symbol at that same origin is therefore F, including when B has
no completed version yet. The supplier alphabet has distinct symbols
F, R and 0. The two ready invariants are disjoint.

Ownership gives an additional interface distinction: RCA's installation
transfers the lane token to its compiler owner. With that token retained,
a CAP verifier read is unexecuted for lack of permission. If a proposed
literal identification instead makes the token available, the original
CAP tag reader encounters F, which is neither terminal R nor the first
bit of `00`; its specified wrong-kind test takes metadata-fault. This is
a conditional prediction from the impossible common-entry hypothesis,
not a report that any combined runtime has been installed or executed.
A different paid placement, origin or translation may avoid the conflict;
none is supplied by calling the two tapes the same port. $\square$

**Proposition 14.3 (the existing consumer makes the distinction material).**
CAP's existing receipt/output pipeline uses the disputed descriptor
interface. Removing that interface would remove an original consumer of
the growing-source instrument.

Proof. Definition 6.3's route 50 copies the frozen producer snapshot,
boot/prior/proposal and complete referenced dependencies to verifier
archive 32, with local descriptors on 33. Definition 6.1 resolves each
acquired origin by that owner's complete native descriptor scan and local
availability tests. Definition 6.5's verifier then checks every unified
row, its semantic mate and predecessor where present, the complete source
manifest and historical guard. Its initial candidate and target remain
$D\subseteq\mathcal T_{H_0}$ and $q_{H_0}$, even after Reserve/Raise.
An accepted result is the `SEG-R1`/`INITIAL-q_H0` receipt. Route 51 copies
it to consumer archive 40 with descriptors on 41; its binding checks
precede task-output construction, seal and OUT. Thus stream 33 belongs to
a current paid verification/acquisition path with an original output,
not an unused scratch convention. Both archives, both descriptor formats,
all checks and both mailbox routes must survive any composition.
$\square$

**Remark 14.4 (what the obstruction leaves to construct).** The
SSA/CSA cell encoder stores F and 0 differently and retains token bits;
it does not allocate a new role namespace or merge stream grammars. CSA
realizes RCA's fixed-domain installation on lanes lent to RCA; it does not
prove CAP's verifier lanes available at a common growing-domain entrance.
A future construction must give an actual finite installed role map,
stream origins and live lease/return graph. If it reuses a lane, it must
supply an explicitly paid parser/translation or a proved nonoverlapping
lifetime with actual retention and copying. It must retain every CAP
source, controller, semantic/unified journal, snapshot, verifier, receipt
consumer and return path, and retain the complete external-input language
and the original source/owner/guard provenance. Merely asserting these
conditions as a hypothetical interface is not an implementation theorem.

The same construction must also carry authentic backing/frontier rights,
a lawfully bound target selector as in §13, acquisition of any additional
control or terminal proposal, and a paid installed decoder with output,
ACK and return. Its added rows have new actual ordinals and receipts;
old original receipts/guards are not retroactively changed. No all-owner
scanner, arbitrary-busy snapshot, infinite initial source or activation of
reconstructed old permission bits is included in the present results.

## 15. Supplier correspondence, finite discriminators and remaining scope

**Convention 15.1 (mathematical scope and supplier correspondence).** The CAP-specific content
is the mandatory Reserve family with its actual ordinal, selection and
local-cost formulas, and the literal port-33 entrance obstruction with its
current CAP receipt consumer. The uniform physical-record construction
and acquired-response-frontier result are explicit applications of
supplier interfaces. They preserve useful source/phase/cost conditions;
they are not new general storage, replay, kernel or factorization results.
No claim of literature originality or physical implementation is made.

| Supplier | Exact parameter map and remaining boundary |
| --- | --- |
| CAP §§2–8 and 9.2–9.3 | Fixed actual boot/mode/graph, original $H_0,\xi,u$, current $t,h,K$, real strict Reserve and Raise, stable $\phi_K$, semantic versus unified ordinals, actual fences, joined verifier and unchanged `INITIAL-q_H0`. These supply the actual cut family and consumer. Joint replay does not give four individual paid inverses. |
| SSA §§3–6, 8, 12.1; CSA §§3–4 and 8 | Instantiate their literal switch/cell/tape storage and priced finite row enumeration with CAP's finite interpreter rows; use CSA's optional native-bit sockets during boot. Source reserve $K$ maps to designated CAP payload; CSA's total tape-cell count maps instead to $C_{\rm cell}$. Neither the generic encoding nor CSA's fixed-source RCA Call supplies a CAP common service entrance. |
| AIF §§2, 4.4–4.5; RCA §§3.3, 4.3–4.5, 11.1–11.4 and 15.1 | Complete successors and raw-IN domain are kept. Acquired seed/input plus an actual bound give literal replay; superprefix stopping and closed-return tally are reused in §12. Generic target-selection counting is reused in §13. RCA's actual banks/leases, not an abstract word register, yield §14. |
| LJA §§5.1–5.3; CAP §§6.1–6.7 | Actual sender/mailbox/receiver status, descriptors, local origin, ACK and row dependencies are the acquisition relation for $D_i$. A copied producer reference grants no private token. Frozen lookup retains its existing target/fence scope. |
| NCR §§5.3, 6.3, 11.3; PR57.D1 and its owning native suppliers | Existing restricted natural atlas and sufficient sequential foundations remain credited. NCR's atomic-source/fixed-controller domain is not identified with CAP's bitwise raw work and capacity maintenance. PR57 rows are counted at their declared atomicity. |
| `NativeSerialMachine.nativeStep`, `replay_deterministic`, `operational_replay`, `reached_prefix_replay`; `NativeFullSourceProducer.native_source_producer` and its private `traverse`, `production_reads`, `stationary`; owning Scribes | These describe finite source-level control, literal source-specific replay and genuine full-source acquisition. They do not implement CAP's new cross-capacity recovery service or the port-role composition. Private proofs are credited as existing results rather than rediscovered. |
| `NativeSerialEffective.OriginalCodeRealization`, `original_code_service_simulation`, its private evaluator/prefix/erasure lemmas; `NativeEffectiveSourceProducer` and `NativeConstructorArrays`; owning Scribes | Keep the actual genuine-code realization and original source/input, and the existing finite constructor representation. Unbounded code/state stays tape data. Source-level evaluator erasure does not erase the physical overhead or grant a new owner token. |
| `TypedFiniteViewKernel.typed_finite_view_kernel`, `PredictiveMemoryMinimalQuotient`, `RealizedImageKernelFactorization.realized_image_unique_factorization_iff_reverse_kernel`; owning Scribes | Typed legality, roots/readouts, complete finite responses and realized-image kernel inclusion are existing abstract results. Their task and map parameters must be instantiated. Raw storage invertibility alone does not establish the reverse inclusion for the original terminal task or acquire an inverse. |

**Convention 15.2 (primary-source hypothesis map).** The following primary
texts support only the stated correspondences. The CAP-specific proofs
above discharge the displayed local claims directly.

| Primary text | Applicable structure, parameter correspondence and unproved transfer |
| --- | --- |
| Driscoll, Sarnak, Sleator and Tarjan, *Making Data Structures Persistent*, [author PDF](https://www.cs.cmu.edu/~sleator/papers/making-data-structures-persistent.pdf), introduction/model and §2.3, PDF pp. 2–5, 8–9 | Their named entry pointers and accessed-node restriction correspond to actual accessible origins/head links, not arbitrary references. Node-copying amortized bounds require constant bounded indegree and their update model. A persistent version is not an acquired CAP cut intention or owner lease; their bounds are not substituted for CAP's retained receipts, paid scans or total storage. |
| Leroy and Blazy, *Formal Verification of a C-like Memory Model and Its Uses for Verifying Program Transformations*, [author PDF](https://xavierleroy.org/publi/memory-model-journal.pdf), Lemma 38 and Lemmas 65–69, PDF pp. 13, 22–23 | Mapped accesses use block-plus-offset embeddings; injection extension keeps every old mapped block at the same target. Map the old CAP segment images to the fixed part of $\phi_K$ and the new disjoint segment to its extension. Alignment, mapped-access and disjoint-allocation conditions are substantive. These lemmas supply neither CAP's actual unary resolution price nor source authority, history selection or stream composition. |
| Lynch and Vaandrager, *Forward and Backward Simulations, Part I: Untimed Systems*, [author PDF](https://groups.csail.mit.edu/tds/papers/Lynch/IC95.pdf), §3.2, Lemma 3.8 and Theorem 3.10, PDF pp. 11–12 | Related initial states and matching finite fragments are required. Here the structural foundation and each actual CAP core/receipt patch supply that comparison. Trace inclusion neither supplies a reverse natural-view kernel nor acquired backing, selection, equal prices or an infinite actual source. |
| SSA §11 and §13.6, CSA §10, CAP §10 | Graph-local replacement, observation factorization and semantic completion retain their already stated primary-source hypotheses. No new theorem is transferred from those references here. In particular a semantic compatible limit is not an operationally supplied run. |

**Open problem 15.4 (the precise remaining construction).** The storage
representation is uniform over actual finite capacity changes, and a
reached acquired nonterminal response frontier supports mathematical
historical reconstruction with the correct ordinals. Old acquired
material alone fails at a mandatory Reserve family of unbounded size;
a later common archive still requires a lawfully distinguished target.
Literal identification with RCA also fails the existing verifier stream
entrance. These results retain the actual initial target, source,
preparation, historical guards, old bytes, ownership and original
consumers.

The remaining constructive problem is a single finite common-role and
paid recovery realization for this growing CAP runtime, including the
acquired selector/frontier, retained backing and present rights, all
added control/input and output/ACK/return costs, and both kernel inclusions
for each proposed natural expression on the original task. Boot and
pre-acquisition interpretations and global terminal-task separation must
be justified on their actual domains. No such common service or complete
four-expression instance has been constructed here. The original
CAP9.3(3) programme remains unproved.

## 追加锚（本行以下为增补区）
## 16. Terminal fibres of explicitly installed finite extensions

**Convention 16.1 (runs, task readout, and terminal fibre).** Fix one valid
CAP preparation occurrence $\xi$, one finite initial source $u\in\mathcal T_{H_0}$,
its acquired input and all of the owner, guard, descriptor, receipt and
consumer conventions of §§2–9. A complete run is the ordered primitive word
$T$ together with every constructed cell, latch value, head mark, pending or
sealed row, input bit, return token and terminal status. It includes the
private preparation, acquisition, every raw `IN`–`WR` and invalid packet phase,
directory and guard work, partial seals, both channel copies, verification,
output, acknowledgement and return. Let $Q$ be the original continuation and
authentic-audit response map of AIF §§2.4–2.6 and SSA §1.3, instantiated with
CAP's original task. Its empty response records the running/terminal type and
the actual terminal task output; it does not append the complete past trace.
The trace-valued `terminalObservation` of `NativeSerialEffective` is therefore
a different map. Write $T\sim_QT'$ when $Q(T)=Q(T')$ and write
$T\sim_TT'$ when the ordered primitive words, including retained raw material,
are equal.

The terminal argument below is made only for the two finite extension classes
that are explicitly installed at boot. It is not a claim about an unchanged
automatic CAP controller. The distinction is necessary because ownership of a
stored bit does not create an entry edge, and a terminal type does not by
itself specify a terminal readout.

**Definition 16.2 (the activation family $W_r$).** Take $H_0=1$,
$u=\alpha$, $\xi$ and prior $D=\mathcal T_1=\{\alpha,\beta\}$, and perform
the original private packet, validation, directory/counter/fence preparation,
stationary acquisition and seed delivery once. Keep CAP ports $0$–$63$ and
all old owner partitions unchanged. The supplied actor table on 24 is the
fixed source-blind client $C$ which performs `Local`, `TagRead(root)` with all
four continuations equal, and `Stop(\tau)`, where $\tau=q_1(\alpha)$ is the
original initial-target output. Boot actually writes this finite table,
its supplied initial configuration and literal finite output material,
by §§2.4 and 8.1. The original acquisition delivers the actual seed to 26
before $C$ starts. Its fixed handoff continuation lends the twelve word
ports to the actor with twelve TOKs and its CTL, writes the literal supplied
initial-configuration word into a fresh current state on 25 by the installed
finite Append code, and completes the initially empty waiting word on 27
using the original block/status/local-descriptor routines. These are actual
finite word writes; the empty word is inert until the client produces a
command. The actor returns the twelve tokens and CTL to the producer before
normalization. Thus 25 encodes the initial `Local` entry and 27 has no
pending command. This initializes the client once and does not reinstall
its table or repeat source acquisition.
During the activation/frame loop, 24–27 remain parked at this client entry;
ordinary row acquisition may append to 28–31 with its original permissions.

The additional producer call site is fixed by native inlining, not by a
saved-return register. Let $F^W$ be a separately numbered inlining of the
complete seven-tag external-frame graph of §4.6 and its §6 services. It has
the same header/length/payload ingress, parser, fault branches, admission,
source/maintenance branches, rows, dependency copies and final row ACK.
Its only changed successor is that of its final producer-idle CTL:

$$
\operatorname{rowACK};\operatorname{TOK}_{\rm source\to dispatcher};
\operatorname{CTL}_{\rm idle}[W_{\rm return}].
$$

Here $[W_{\rm return}]$ is the literal successor row number in the installed
CTL encoding of §2.3. At $W_{\rm return}$ a producer CTL selects the wrapper
phase and the identity permutation of its twelve word roles, Tail(13) and
Tail(17) restore their R heads, and one CTL enters $W_{\rm entry}$. The first
acknowledged idle return after seed delivery takes this same normalization
path. These are finite native rows and actually executed Tail loops.
The original raw graph still has its original next-frame IN successor;
the automatic graph retains its original saved-caller successor, including
the Reserve/Raise/Rho policy of §8.2. Their installed entries and domains
are unchanged; their boot branches keep their original supplied-controller
initialization. The client initialization and joins above belong only to
the additional $W$ boot branch, whose entry is $W_{\rm entry}$;
there is no runtime switch from an unfinished old call into this loop.

At $W_{\rm entry}$ the following entry relation holds. The producer holds
all twelve word-port tokens, its original tokens for 0 and 13–23, and
the dispatcher holds the available source-service token. Every prior row,
dependency, channel check and ACK is complete. Port 13 is at its actual R;
17 is a complete native descriptor stream at R. Directory, counter and
journal streams have their original completed-boundary invariants, with
$1\le H_0\le h\le K$ and the actual source represented by $\phi_K$.
No wrapper work word or latch carries a live return value. The parked
24–27 bytes, heads and owners are unchanged. Other heads/latches are their
actual retained values; each helper positions its own inputs before reading.
Only the fixed wrapper successor is enabled during activation preparation,
not a second source or actor call. The activation graph is the following.

1. Base(13;$a$) constructs the actual $U(a)$ and leaves 13 at R. Execute
   IN(5); EX(13); WR(13,latch5); MR(13), then Append(13,sep) and
   Append(13,0). Thus the payload bit is at $a$, sep at $a+1$ and its
   initialized unavailable status at $a+2$. Input latch 5 is not touched
   between IN and WR. The unconsumed-input and acquired-but-unwritten cuts
   are distinct ordinary states.
2. Using §§3.1–3.3 and 6.1, construct all ten source field words and run
   WriteDescriptor on 17. Its unchanged tag is `00`, followed in order by
   $U(\mathrm{producer}),U(13),U(a),U(1),U(c)$, the fixed `activation`
   type, initialized flag 1, post-seal mutable flag 0, $U(a+2)$, and the
   empty original-origin word. Every field has its physical sep, including
   the empty origin, and the record has its final seal. The one-based $c$
   is obtained by the paid complete-stream count, not supplied as an
   address. This is exactly the ten-field native grammar of §6.1.
3. Retain only the complete base/status words after that writer; its other
   field roles are dead. At(13,status); WR(13,1); CTL seals the bit block.
   At(13,base); RD(13,6) acquires the now-sealed bit into branch latch 6.
   Tail(13), using test latch 4, restores R without overwriting latch 6;
   17 is already at R. One CTL branches on latch 6. No value in latch 4
   is retained across a positioning call. At this branch no wrapper word
   must survive either callee.
4. For bit 0 the CTL enters $F^W$ at its original header Base/setup
   prelude, before the first header IN. All its entry tokens are those
   just listed; it acquires its own complete frame and takes the source
   token only at the original admission point. For any
   completed canonical frame, the final ACK, source TOK and idle CTL
   reach $W_{\rm return}$, hence $W_{\rm entry}$, before any next IN.
   No frame header bit is consumed as an activation or conversely. A
   malformed frame takes the original retained `frame-fault` branch;
   an unfinished length/payload stays in its original ingress phase.
5. For bit 1 the CTL enters the producer-to-actor loan prelude. Execute
   the twelve TOKs of §2.2, then its CTL entering $C$'s already initialized
   `Local` state on 25. The source-service token remains at the dispatcher
   during this actor-local phase. No actor helper starts during the
   partial loan. The actor has its own 24–31 and the twelve public word
   ports, its acquired seed on 26 and no private source/producer-descriptor
   read right. This is precisely the actual table entry of §8.1.

The client uses §8.1's complete persistent-state/packet writer on 25/27.
While the pool is at the actor, it sends each actual packet and its
dependencies on route 49 to producer 21; nested channel loans return it
to the actor as sender. It then returns all twelve workspace tokens and
CTL to the producer before dispatch.
Its `Local` marker completes its semantic/unified row and final ACK before
the fixed producer successor lends the pool for the actor return handler.
That handler reads its acquired row through local descriptors on 29, installs
the root-read successor in 25 from its retained packet, returns the pool,
then takes the next fixed table-entry loan. The root TagRead constructs its
ordinary canonical frame from the acquired operation packet, calls the
original source service, and follows the same ACK/loan/return-handler path.
The acquired literal reply selects one of the four equal retained Stop
continuations. Each actor resumption therefore starts with the actual
completed state/packet and full workspace loan, rather than a live latch
left over from the activation reader. These are the fixed §8.1 call sites,
not returns into $W_{\rm entry}$.

For Stop the actor actually seals its output on 31 and copies its complete
payload and origin on route 49 into producer 21 before Halt commits. Its
packet declares global Halt, not acquisition-internal return. The old §6
terminal row/dependency delivery, frozen snapshot/proposal binding, route
50 to verifier 32 with descriptors on 33, verifier receipt, route 51,
consumer checks, task-output on 43, OUT and final ACK/return all precede
the global halt CTL. Each nested channel returns the word pool to its
actual sender as in §2.2. This terminal successor is not the activation
return. No added terminal audit or reassigned verifier/consumer role occurs.

Let $U(n)=1^n0$, $R_2=101\,U(3)\,U(2)$ and
$A_2=110\,U(3)\,U(2)$. A member of $W_r$, for $r\ge1$, supplies the finite
sequence

$$
\operatorname{activate}(0),R_2,\operatorname{activate}(0),A_2,
\operatorname{activate}(0),F_1,\ldots,
\operatorname{activate}(0),F_r,\operatorname{activate}(1),
\operatorname{client},
$$

where each $F_i$ is either $R_2$ or $A_2$. Activations and external frame
bits are actually acquired by their distinct IN sites. Client packets are
actually constructed from its installed table/state and acquired material;
computed bits are copied/Appended, not fictitious external inputs.
All these blocks, branches, copies, partial seals and returns belong to
the same run. The installed graph has no $r$-dependent quota or
future-capacity constant.

**Proposition 16.3 (finite installation and original-consumer correspondence
for $W_r$).** The extension in Definition 16.2 is a finite installed
wrapper/control/storage extension, and each $W_r$ member reaches the original
CAP verifier and consumer with the original target and source conditions.

**Proof.** The code consists of one copy of each fixed helper at each static
call site, the finite client table, one $F^W$ inlining and the displayed
control joins. Its only cycle between complete frame calls is
$W_{\rm entry}\to F^W\to W_{\rm return}\to W_{\rm entry}$.
This is an ordinary finite graph cycle under §2.3, not recursive native
calls or an unbounded return stack. All successor numbers, branch states,
port/latch choices and the new finite block type are literally boot
installed. No runtime return-kind word is needed for this fixed call site.
The original frame command and the actor's genuine §8.1 packets and saved
continuations still occupy their actual retained storage.

The original paid preparation and acquired-seed return establish the stated
completed-boundary invariants, and the first normalization establishes the
heads and word-role permutation of $W_{\rm entry}$. From that relation,
Base and Append give the displayed three initialized cells on 13. The
descriptor writer has ten complete field words, including base and status;
its other two roles suffice for its count as in §6.1. Thus it needs no
thirteenth simultaneous word. Seal then licenses the producer's RD of its
own bit; this is not a descriptor-derived cross-owner read. The RD into 6
and Tail using 4 prove the branch latch invariant. Its base/status roles
are dead at the branch, so the frame or actor may reuse the pool.

For bit 0, §4.7 and Lemma 6.7 apply to $F^W$ with their original guards,
owners, actual retained inputs and complete row/channel return. Renumbering
its nodes changes no primitive before the final idle successor. At that
successor every workspace token is back at the producer, the source token
is back at the dispatcher and every mandatory ACK is complete. The return
normalization therefore reestablishes exactly $W_{\rm entry}$, including
the parked 24–27 state and a longer complete stream on 13/17. Induction
gives this entry relation after any finite number of canonical frames,
not only after the first one. Partial and fault branches keep their
original successors and do not receive a spurious completed return.

For bit 1, the actual twelve TOKs and CTL establish the §8.1 actor entry
relation. Its Local and literal-read returns have complete retained packets,
acquired row responses and the declared fixed handler successors. Their
loans/returns preserve producer admission and install the next actual state
on 25. The terminal packet/output copies supply the old global-Halt entry;
the complete §6.5 consumer, rather than the wrapper, selects and outputs
the checked target. The acquired initial root still identifies $\alpha$ in
$D$, so the compatible initial-source fibre is $\{\alpha\}$. Consequently
the authentic snapshot and historical guards pass with the proposal
$\tau=q_1(\alpha)$ and the unchanged `INITIAL-q_H0` target. No later guard
changes the saved initial target. Finite completion uses actually supplied
finite input and termination of reached local/prior computations.
The same finite $F^W$ code handles arbitrary finite request words and
capacities on the original admission domain; none is stored as a future
maximum. Finite initial source does not bound these retained runtime tapes.
Infinite continuation would additionally require continuing actual input
supply and completion of every reached local computation.

For completeness, expand these additional rows by the same recurrence
$V$ of §7.1 in the actual state left by each preceding fragment. Let
$B$ be this run's complete boot/acquisition/client-initialization/first
normalization cost, $A_i$ its $i$th activation block/read/branch cost,
$P_i$ its $i$th complete $F^W$ cost through idle CTL,
$D_i$ its return-normalization cost, and $L_C$
its final workspace loan and complete client/terminal cost. For $r+2$
frames the absolute length is

$$
n=B+\sum_{i=1}^{r+2}(A_i+P_i+D_i)+A_{r+3}+L_C.
$$

These are consecutive fragments of one execution, not separately optimized
runs; their actual supplied bits and reached heads fix every summand.
In particular $A_i$ includes IN, base/address/ordinal construction, all
ten descriptor fields, status/seal, reread, Tail and branch; $D_i$
includes its two CTLs and both Tail loops. $L_C$ includes all pool TOKs,
state installation, packet construction, both channel stages, every row,
snapshot, receipt, consumer output, ACK and halt. The boot code of $F^W$
and every literal successor/control bit is in $B$ and $b_{\rm ctl}$.
Each executed occurrence contributes one tick, two fee units and one
receipt, and every constructed activation, word, descriptor and retired
cell stays counted in $A$ of §7.2. Thus the same run satisfies
$T=n$, $F=2n$, $S=S_0+b_{\rm ctl}+8A+8n$; there is no free return
storage or uncharged controller. This proves the finite installation and
original-consumer correspondence uniformly in $r$. $\square$

**Theorem 16.4 (the $2^r$ terminal family).** For every $r\ge1$, $W_r$
contains $2^r$ complete runs with pairwise different retained full histories
but the same original task response: for distinct words $w,v\in\{R_2,A_2\}^r$,
$T_w\not\sim_TT_v$ and $T_w\sim_QT_v$.

**Proof.** The first $R_2$ is a strict `Reserve(2)` from $K=1$ and appends
$4$ source cells. The next $A_2$ is `Raise(2)` and changes the semantic guard
without changing the source. Subsequent occurrences are complete paid
unchanged maintenance branches with the same finite return contract. All
members therefore have the common acquired source $\alpha$, $h=K=2$, the
same layout and policy ordinals, and the same client proposal. Relative to the
common prefix, the event counts are

$$
(q,g,e,j,m)=(q_a+1,g_a,e_a,j_a+3,m_a+r+5).
$$

If $w$ and $v$ first differ at position $i$, the reached ingress cell at that
position receives the different acquired headers $101$ and $110$. The header,
its source origin, its row and the later retained block are append-only
material, so the complete primitive words and retained cells differ. This
proves $T_w\not\sim_TT_v$.

All command frames are finite and use the same acquired source and original
owner paths. The verifier receives an authentic snapshot and binding for each
run, checks the same initial target $q_1(\alpha)$, and the consumer emits the
same target output. At global halt the original row delivery, verifier,
consumer, `OUT`, `ACK` and return have already completed. Every prescribed
producer or journal entry requires acknowledged idle or a held frozen
continuation, and neither is available after the final halt control edge.
Thus every enabled continuation experiment has the same disabled response and
the empty response has the same terminal type and output. Hence
$Q(T_w)=Q(T_v)$, proving $T_w\sim_QT_v$. There are $2^r$ words. $\square$

**Definition 16.5 (the four-stage family $C_{4,M}$).** Keep the same finite
$\xi$, $H_0=1$, acquired $\alpha$ and original roles, and install at boot a
four-stage saved-return client. Each stage enters the existing complete CAP
canonical-frame service, waits for all row/dependency deliveries, channel
acknowledgements, source-token return and idle return, and then executes one
finite stage-join control edge. Stage four computes the proposal from the
acquired initial syntax, seals it on the inherited terminal/output role and
invokes the unchanged verifier, consumer and global halt route. For fixed
$M\ge4$ and $J\in\{2,\ldots,M-1\}$, supply

$$
\operatorname{Reserve}(J),\quad \operatorname{Reserve}(M),\quad
\operatorname{Raise}(M),\quad \rho,\quad\operatorname{Stop}(q_1(\alpha)).
$$

The words $J$ and $M$ are supplied runtime words. They are not constants in
the installed control. The two strict reservations append
$4(J-1)$ and $4(M-J)$ source cells; together with the initial two-cell source
packet their source payload is $4M-2$. This is a payload subtotal, not a total
runtime-space count.

**Proposition 16.6 (finite installation and terminal family for $C_{4,M}$).**
For fixed $M\ge4$, the $M-2$ runs indexed by $J=2,\ldots,M-1$ have distinct
full histories and the same original terminal task response.

**Proof.** Four saved-return states and their join controls are finite and are
installed once. The old raw frame, invalid packet, directory, guard, row,
channel, verifier, consumer and return phases are called with their original
entries; no verifier lane or consumer lane is reassigned. The first and
second reservations are strict, `Raise(M)` is valid after the second one, and
$\rho$ is the original guarded source operation. All actual allocation,
partial cells, descriptor/seal states and ACKs remain in the history.

Different $J$ values leave different first unary request words and first
immutable reservation records. The final state may have $h=K=M$ and the same
accepted $\rho$ successor, but the retained histories still differ. The
truthful acquired initial source again makes the verifier's initial-source
fibre singleton. Each authentic snapshot therefore passes the same
`INITIAL-q_H0` binding, and the consumer copies the same $q_1(\alpha)$ target
before the final halt. The posthalt argument of Theorem 16.4 applies verbatim.
Thus $T_J\not\sim_TT_{J'}$ for $J\ne J'$ while
$T_J\sim_QT_{J'}$, giving $M-2$ histories in one terminal $Q$-fibre.
$\square$

**Corollary 16.7 (the scoped task-kernel obstruction).** On either displayed
finite extension class, $\ker(T)\subsetneq\ker(Q)$. Any natural view $V$ that
retains the differing immutable ingress header or full chronology is also
strictly finer than $Q$ on the exhibited fibre. A terminal-type coincidence
alone is insufficient: the equality of $Q$ additionally uses the same actual
terminal target/output and the absence of an enabled original posthalt audit.

**Proof.** Determinism gives $T\sim_TT'\Rightarrow T\sim_QT'$, hence
$\ker(T)\subseteq\ker(Q)$. Theorem 16.4 or Proposition 16.6 supplies a pair
in the reverse difference. A view retaining the differing cell or ordered
primitive word separates that pair. The qualification about output and audits
is exactly the step in the proofs where terminal type is strengthened to an
equal response map. $\square$

These families do not establish a failure for every task-relative natural
view. They establish that exact full-history recovery, or any view that keeps
the displayed terminal distinctions, cannot be identified with the original
terminal task on these explicitly installed extensions. The fixed-initial-state
and finite-fragment discipline is the one used by Lynch and Vaandrager,
*Forward and Backward Simulations*, §3.2, Lemma 3.8 and Theorem 3.10; those
results supply no reverse decoder or paid owner authority.

## 17. The actual Ready horizon and the constructive preterminal domain

**Definition 17.1 (stopping cuts and admitted covers).** Let
$X_0,\ldots,X_N$ be one complete finite CAP extension run, with $X_N$ the
final global halt cut. A cut is *service-admissible Ready* when the installed
entry is enabled, the relevant joint successor has completed, all required
row/channel acknowledgement has occurred, and the owner holds the return
authority. Let $R$ be the nonempty set of such cuts before the final stopping
flight and let $b^*=\max R$. A historical `Cover` entered at a Ready cut has an
immutable target bound $b(c)$ equal to the acquired prefix endpoint. The
no-extra-entry class assumes that no recovery entry is installed inside the
final stopping flight and that no event follows $X_N$.

**Proposition 17.2 (an actual stopping witness).** There is a finite source
instance satisfying the original task in which the final stopping flight has
positive output, verification and return work after the last Ready cut. Take
$H_0=1$, $u=\beta$, $D=\mathcal T_1$, the private packet for $\beta$, and the
finite controller that constructs the original $q_1(\beta)$ proposal, performs
`Reserve(2)`, `Raise(2)`, one genuine $\rho$, and then stops. The source packets
are $10$, then $100000$ after reservation, and $111001$ after the accepted
update, representing $\langle\beta,\alpha\rangle$.

**Proof.** The first packet is the supplied private source, so its origin and
owner are those of the original preparation. `Reserve(2)` is strict from
$K=1$ and `Raise(2)` is valid after it; the guarded $\rho$ accepts the displayed
finite successor. The original target is $q_1(\beta)=(0,B,1)$, and truthful
acquisition identifies $\beta$ in $\mathcal T_1$. CAP's verifier therefore
accepts the original binding. Row delivery, snapshot and descriptor checks,
consumer output, `OUT`, `ACK` and the final halt control are all finite under
the declared reached-local completion and supplied-input premises. In
particular, output/check/return work is completed before the distinct final
halt edge, so the last Ready is followed by a nonempty terminal suffix.
$\square$

**Theorem 17.3 (last-Ready stopping-cover horizon).** In the class of
Definition 17.1, every admitted cover satisfies $b(c)\le b^*$. Consequently
no target cut $k$ with $b^*<k\le N$ is recoverable through those covers, and
$b^*<N-1$ in the witness of Proposition 17.2. The cut $N-1$ is therefore a
proper preterminal witness for the Ready-only obstruction.

**Proof.** A cover is admitted only at a member of $R$, and its immutable
endpoint is the acquired prefix at that member. Hence $b(c)\le b^*$.
Every issued target is required to satisfy $k\le b(c)$, so it is at most
$b^*$. The final suffix contains output/check/return work and then a distinct
halt edge; therefore at least two event positions follow $b^*$, giving
$b^*<N-1$. A cut after $b^*$ is outside every admitted cover, and after
$X_N$ no event exists from which a paid call could be entered. This proves the
stated horizon without requiring an immediate `Freeze` at a busy cut or a
call that recovers the final state itself. $\square$

**Proposition 17.4 (strict-past final-cut consequence).** Suppose instead
that a finite run admits any finite collection of strict-past services, each
with target $k_i$ strictly before its actual admission and with completed
return no later than $N$. Then $k_i<N$ for every $i$. This excludes the final
cut only; it does not exclude every proper preterminal cut.

**Proof.** For each completed service, $k_i<\operatorname{admit}_i\le
\operatorname{return}_i\le N$. Taking the maximum over the finite collection
still gives a bound strictly below $N$ for every target. No assertion about
$N-1$ or an earlier cut follows from this inequality alone. $\square$

**Proposition 17.5 (the earlier covered domain remains constructive).** The
zero-fill checkpoints and their selector lower bound are already supplied by
CAP Theorems 13.2–13.6. Those results apply when a later acquired frontier,
actual target binding, owner token and reached-local completion are present.
They do not add an entry to the no-extra-entry final suffix of Definition 17.1.
Consequently the present horizon result removes only the unsupported claim of
cofinal Ready-only recovery; it leaves the earlier acquired recovery route
available on its stated domain.

**Proof.** CAP Theorem 13.2 gives the $d+1$ lawful cuts and their distinct
complete successors, while Proposition 13.5 requires an acquired distinction
for the intended target and Proposition 12.2 supplies the retained-prefix
reconstruction conditions. Each of those statements is conditional on an
actual later frontier and paid selector/call. Definition 17.1 explicitly
withholds such an entry in the final stopping flight. Therefore the two
claims concern disjoint admission domains and can be combined without
requiring an immediate busy-cut `Freeze` or a terminal self-call. $\square$

## 18. Literal encompassing images and completed-call resource bounds

**Definition 18.1 (literal image and absolute cell count).** At absolute native
ordinal $k$, let $C(k)$ count every constructed port cell in the represented
endpoint, including the two meter foundation cells, retired/dead material,
all descriptors and the image's own receiver/output cells. A raw cell record
has eight literal bits. The declared codec uses
$\operatorname{Frame}(w)=1^{|w|}0w$ and the nested port-list codec of
RCA Definitions 12.1–12.2;
compressed keys, program descriptions and proper task projections are outside
this definition. Every primitive appends one receipt cell, so
$C(k)\ge k+2$.

**Proposition 18.2 (self-encompassing literal image exclusion).** Let an
image of the complete encompassing endpoint at cut $k$ have $m>0$ wire bits.
If the image is resident inside that same endpoint with one stored symbol cell
per wire bit, or if all its bits have already been printed by cut $k$, the
respective construction is impossible.

**Proof.** A complete literal image has at least eight bits for each of the
$C(k)$ represented cells, so $m\ge8C(k)$. If it is resident in the endpoint,
its $m$ distinct payload bits occupy cells counted by $C(k)$, hence
$C(k)\ge m$, which contradicts $m\ge8C(k)$ for $C(k)>0$. If it has all been
printed by cut $k$, one output event is required per wire bit, so $k\ge m$;
then $m\ge8C(k)\ge8(k+2)>k$, again a contradiction. The nested 64-port
list gives the stronger source codec subtotal $m\ge257+36C(k)$ when that
list is included: an eight-bit cell list on port $i$ has length $18c_i+1$,
and the outer list has length
$1+\sum_{i=0}^{63}(2(18c_i+1)+2)=257+36C(k)$.
The eight-bit inequality already proves the exclusion.
A later sender/archive/mailbox/receiver delivery escapes the self-containment
premise because those cells lie outside the represented older endpoint.
$\square$

**Proposition 18.3 (copy, seal, handoff and print subtotals).** For a complete
published payload of length $L$, one tested copy body has exactly $6L+3$ rows:
six rows per bit, followed by its terminal read, seal control and token
handoff. Two copies therefore use $12L+6$ rows through the second handoff,
whereas the prefix only through the second receiver seal uses exactly
$12L+5$. Mandatory printing costs $5L+1$ additional rows. Thus the completed
copy-plus-print body is

$$
(12L+6)+(5L+1)=17L+7.
$$

**Proof.** The first copy contributes six rows for each of its $L$ payload
bits and three final rows. The second copy has the same complete body. If the
second body is stopped at its seal, its final token handoff has not yet
occurred, so its contribution is $6L+2$ and the prefix is
$(6L+3)+(6L+2)=12L+5$. Including that handoff gives $12L+6$. The mandatory
receiver print has its five-row-per-bit loop and terminal row, namely $5L+1$.
All three bodies are on the same completed call, so their rows add. Setup,
framing, archive serialization, allocation, descriptors, positioning,
completion records, authority checks, ACK and return are additional
nonnegative rows, not silently absorbed into these subtotals. $\square$

**Corollary 18.4 (ordinal lower bounds for a literal completed call).** Let a
historical call target the absolute cut $0\le k\le s$ on the same run,
start at ordinal $s$ and return Ready at $t$. Under the conventions of
Proposition 18.3,

$$
 t-s=17L+7+R,\qquad R\ge0.
$$

If the published word contains the historical target word $U(k)$, then
$L\ge k+1$ and
$t\ge18k+24$. If it is a literal encompassing image of that target cut, then
$L\ge8(k+2)$ and
$t\ge137k+279$. If that target's exact 64-port nested list is included, the supplied
subword bound $L\ge257+36C(k)\ge36k+329$ gives the conservative
$t\ge613k+5600$.

**Proof.** The equality is the disjoint body count plus the residual work $R$.
For a call that starts at $s\ge k$, substitute $L\ge k+1$ to obtain
$t\ge k+17(k+1)+7=18k+24$. The literal-image inequality gives
$t\ge k+17\cdot8(k+2)+7=137k+279$. The nested-list inequality gives
$t\ge k+17(36k+329)+7=613k+5600$. These are necessary bounds on one actual
run, not sufficient schedules and not physical time or energy laws. $\square$

**Corollary 18.5 (combined horizon bound).** In the Ready-only stopping class,
a historical literal encompassing-image call satisfying Corollary 18.4 and
targeting cut $k$ can complete before the final halt only if

$$
 k\le b^*\qquad\text{and}\qquad
 k\le\left\lfloor\frac{N-279}{137}\right\rfloor.
$$

The inequalities are necessary only. A proper archive, compressed key,
program-relative description, external destination or later acquired target
changes the premises and is not a counterexample to this corollary.

**Proof.** The first inequality is Theorem 17.3. The second follows from
$ t\le N$ and Corollary 18.4. $\square$

## 19. Exact boundary for the next common-runtime construction

**Definition 19.1 (admissible next bridge).** A candidate common runtime after
these results must be one fixed finite boot installation, uniform in future
$h$ and $K$, with an explicit owner/origin map for every added role and every
old CAP role. It must acquire the activation and target-selection words, keep
all old raw and partial phases, preserve the original verifier/consumer and
`INITIAL-q_H0` target, and return through actual ACK and installed fixed or
saved-continuation edges. For an earlier cut it must additionally provide
an acquired immutable
covering prefix, an owner-authorized `Next` or `Select` binding, a live token,
complete package serialization, both initialized copies, mandatory print,
ACK and Ready return. No free activation, arbitrary-busy scanner, terminal
history reader or retroactive permission is admissible.

**Proposition 19.2 (what the new bounds change).** The admissible construction
class is restricted in three concrete ways. First, a terminal collision repair
must install its finite activation and return control at boot and prove its
original verifier/consumer correspondence; an unchanged automatic CAP graph
cannot inherit the $W_r$ or $C_{4,M}$ branches. Second, a recovery construction
must target the actual covered preterminal domain of Theorem 17.3 or the
strict-past domain of Proposition 17.4; a finite final drain does not make the
last suffix cofinal. Third, a literal final-state dump cannot repair either
obstruction under Definition 18.1; a candidate must use a properly scoped
archive or a different, explicitly priced representation.

**Proof.** The first statement is the finite-entry premise used in
Proposition 16.3 and Proposition 16.6. The second follows from the cover
endpoint inequality and the strict-past admission inequality. The third is
Proposition 18.2 together with the corrected copy/handoff accounting of
Propositions 18.3–18.4. These are restrictions on the next construction
interface, not a proof that no task-relative four-view construction exists.
The remaining work is to supply the common finite role/ownership graph,
selector, both kernel inclusions for each natural view and lawful transition
transport on its actual domain; no such common installation is asserted
here. $\square$

The external structural analogies retain their limited hypotheses: compatible
memory-extension maps preserve old blocks only under disjoint allocation and
map extension (Leroy and Blazy, Lemmas 65–69), and simulation results require
an initial relation plus matched finite fragments (Lynch and Vaandrager,
Lemma 3.8). Neither citation supplies CAP's owner token, source growth,
terminal readout or primitive fee. The full CAP9.3(3) programme, including all
four independent natural views and its common operational instance, therefore
remains an open construction boundary rather than a conclusion of this
appendix.

## 追加锚（本行以下为增补区）


## 20. Serial literal self-images under calibrated clocks

**Definition 20.1 (one actual serial image protocol).** On the same native run
and with the literal codec, copy, handoff and Ready conventions of
Propositions 18.2–18.3, let $s_0<s_1<\cdots<s_j$ be absolute native ordinals.
Round $i$ starts at $s_i$, targets the cut $k_i=s_i$, and returns a literal
encompassing image of that cut before round $i+1$ begins at $s_{i+1}$.
Extra work and gaps between completed calls are allowed. Put
$W_j=s_j-s_0$, counting every intervening native primitive, rather than
counting one completed image as a unit-cost step. A statement for $j$ rounds
is conditional on all those calls actually completing; their existence is
not supplied by this definition.

**Proposition 20.2 (serial image amplification and the round horizon).** Every
protocol of Definition 20.1 satisfies

$$
\begin{aligned}
s_j&\ge137^j s_0+\frac{279(137^j-1)}{136},\\
W_j&\ge(137^j-1)\left(s_0+\frac{279}{136}\right).
\end{aligned}
\tag{C.20.1}
$$

If $s_j\le N$, then

$$
j\le
\frac{\ln((136N+279)/(136s_0+279))}{\ln137}.
\tag{C.20.2}
$$

Proof. Corollary 18.4, applied to the actual call with $k_i=s_i$, gives a
completion ordinal at least $137s_i+279$. Seriality therefore implies
$s_{i+1}\ge137s_i+279$. Set $b=279/136$; then
$s_{i+1}+b\ge137(s_i+b)$. Induction gives
$s_j+b\ge137^j(s_0+b)$, and subtracting $s_0+b$ gives the work bound.
For the horizon bound, $137^j(136s_0+279)\le136N+279$, whose positive terms
permit taking logarithms. The mechanism and constants are derived from the
actual source codec and body counts, not from a general theorem about all
self-representations. $\square$

**Definition 20.3 (a calibration of the same trace).** Fix positive units
$\tau_0,M_0,a_0$. For inputs of length $n$, partition the entire execution
between $s_0$ and $s_j$ into its $W_j$ native intervals. Let interval $i$ have
positive proper duration $d_i$ and let $t(\tau)$ be an absolutely continuous,
strictly increasing reference clock with
$dt/d\tau=1/\alpha(\tau)>0$ almost everywhere. All waiting, control,
communication and copying in this interval is included in the partition.
Write

$$
T_\tau=\sum_{i=1}^{W_j}d_i,\qquad
T_t=\int_0^{T_\tau}\alpha(\tau)^{-1}\,d\tau.
\tag{C.20.3}
$$

A polynomial calibration supplies fixed polynomials $p,q\ge1$, evaluated at
$n$, with

$$
\frac{\tau_0}{p(n)}\le d_i\le\tau_0p(n),\qquad
\frac1{q(n)}\le\alpha(\tau)\le q(n)
\quad\text{almost everywhere}.
\tag{C.20.4}
$$

This is an additional implementation assumption; a native tick is not
identified by definition with a physical second.

**Proposition 20.4 (image rounds in a polynomially comparable clock).** Under
Definitions 20.1 and 20.3 with (C.20.4),

$$
\frac{W_j}{p(n)q(n)}
\le\frac{T_t}{\tau_0}\le p(n)q(n)W_j,
\qquad
\frac{T_t}{\tau_0}\ge
\frac{(137^j-1)(s_0+279/136)}{p(n)q(n)}.
\tag{C.20.5}
$$

In particular, if $T_t/\tau_0\le B(n)$ for a fixed polynomial $B\ge0$, then

$$
j\le\frac{\ln\left(1+
 B(n)p(n)q(n)/(s_0+279/136)\right)}{\ln137}
=O(\log(n+2)).
\tag{C.20.6}
$$

Proof. The elementary calibrated-trace estimate recorded in
[Cook's model-robustness note](../../../Library/ConceptDynamics/cook2006pversusnp.md#primitive-simulations-and-calibrated-execution-costs)
is used as an intermediate step: on interval $i$, integration of
$q(n)^{-1}\le\alpha^{-1}\le q(n)$ gives reference duration between
$\tau_0/(pq)$ and $\tau_0pq$. Summing gives the first two-sided bound.
Apply Proposition 20.2 for the last bound. Rearranging it under the budget
$B$ gives (C.20.6); its asymptotic estimate uses
$s_0+279/136\ge279/136$ and the fixed polynomial upper bound on $Bpq$.
This limits serial literal-image rounds in the stated trace. It is not a
lower bound on a task computed by a different trace or representation.
$\square$

**Definition 20.5 (static exterior calibration).** Supply a Schwarzschild
vacuum exterior with source mass $M(n)>0$, constants $G,c>0$, and a test
apparatus held at fixed areal radius $R(n)>2GM(n)/c^2$. Its reference $t$ is
normalized at infinity. Backreaction, rotation, free fall and additional
kinematic time dilation are excluded. Supply the proper-duration bounds
of (C.20.4) for the actual native intervals; they are not consequences of
the metric. Let $a(n)$ be the proper acceleration required to remain
static. Assume bounds on numerical values in fixed units,

$$
M(n)\le M_0P(n),\qquad a(n)\le a_0Q(n),
\tag{C.20.7}
$$

for fixed polynomials $P,Q\ge1$. These assumptions do not assert that a
physical suspension or its construction has been supplied at polynomial
cost. The source mass $M$ is not the observer's record length and is not
the bottom probability mass of the five-state pyramid.

**Proposition 20.6 (conditional Schwarzschild cost of the native image
protocol).** Under Definitions 20.1, 20.3 and 20.5, set

$$
C=\frac{64GM_0a_0}{9c^4},\qquad
q_{\rm S}(n)=2+C P(n)Q(n).
$$

The actual static clock satisfies

$$
1\le\alpha^{-1}\le q_{\rm S}(n),\qquad
\frac{T_t}{\tau_0}\ge
\frac{(137^j-1)(s_0+279/136)}{p(n)}.
\tag{C.20.8}
$$

If instead an external reference interval $T_{\rm ext}\ge0$ is compared
with this apparatus's elapsed proper waiting time $\tau_{\rm wait}$,

$$
\frac{T_{\rm ext}}{q_{\rm S}(n)}
\le\tau_{\rm wait}=\alpha T_{\rm ext}\le T_{\rm ext}.
\tag{C.20.9}
$$

Thus this static, polynomially bounded source-and-acceleration family
cannot convert an exponentially long external interval into a polynomial
proper waiting interval. This compares interval lengths and supplies no
external computation, return signal or readout protocol.

Proof. Use the classical Schwarzschild clock and acceleration formulas as
intermediate facts, with their derivation and limitations in
[Reall's black-hole note](../../../Library/Observer/reall2024blackholes.md):

$$
\alpha=\sqrt{1-\frac{2GM}{c^2R}},\qquad
 a=\frac{GM}{R^2\alpha},\qquad
 Ma=\frac{c^4}{4G}\frac{(1-\alpha^2)^2}{\alpha}.
\tag{C.20.10}
$$

For $0<\alpha\le1/2$,
$(1-\alpha^2)^2\ge9/16$ gives
$\alpha^{-1}\le64GMa/(9c^4)\le C P(n)Q(n)$.
For $1/2<\alpha<1$ its inverse is less than two. This proves the first
bound, with $q_{\rm S}$ a polynomial majorant for both branches.
Since $\alpha\le1$, each actual native interval costs at least
$\tau_0/p(n)$ in reference time; summing and applying Proposition 20.2
proves the second bound in (C.20.8). At fixed $R$, $\alpha$ is constant,
so (C.20.9) follows by integration of $d\tau=\alpha\,dt$.
$\square$

**Convention 20.7 (scope of computation and physical identification).**
The following supplied bridges are kept distinct. Polynomial simulations
between primitive models concern a uniform algorithm on all inputs,
including negative instances; mutually polynomial simulations preserve P
and verifier-defined NP as recorded in the Cook note. Proposition 20.2
concerns only serial literal-image calls; incremental records, shared
substructures and task projections do not inherit its premises merely
by representing the same final answer. Polynomially calibrated durations
compare the same actual execution, with all its charged operations;
they do not establish that every abstract program has such a physical
implementation.

For the static conditional histories of
[Collective oscillators, Definition 10.1](AURIC_COLLECTIVE_OSCILLATORS_AND_RECORD_CAPACITY.md),
positive rescalings of the same propagation constraints preserve their
common kernel but do not fix the physical energy scale; the intermediate
linear-algebra facts are recorded in
[Bausch--Crosson's note](../../../Library/Observer/bauschcrosson2018modifiedcircuits.md).
A zero-energy history state does not itself traverse its conditional
clock positions under its propagation Hamiltonian.

For the pyramid's fixed-fiber equation, the already supplied solution
$\kappa(t)-\kappa_*=(\kappa(0)-\kappa_*)e^{-\gamma\varrho t}$
in [§3 of its dynamics volume](AURIC_FIB_PYRAMID_INFORMATION_ESCAPE_DYNAMICS_THERMODYNAMIC_ACTION.md#3-κ-纤维上的质量作用动力学)
uses $\varrho=1-Z$ as probability mass. Its parameter time and relaxation
rate are not identified with $\tau$ and $\alpha$. A relation to a common
physical clock for different local processes remains a separate supplied
or derived interface. None of these protocol bounds decides P versus NP.

## 追加锚（本行以下为增补区）

## 21. Endogenous primitive time and the size of the completed observer

**Definition 21.1 (a task-start cut and endogenous completion).** Fix a finite uniform controller, an actual native start cut $s_0$, a problem record $x$ already present there, and $n=|x|$. The record need not originate outside the observer. After $k$ further primitives write the actual state as $\mathcal O_k(x)$ and its operation word as $h_k$; define $\tau(h_k)=k$. A completion flag and output port belong to the controller. Let $T(x)$ be the first $k$ at which that flag and its specified output are delivered, or $\infty$ if this never happens. Computing the flag, control, acquisition, copying and readout uses the same primitives. No external answer oracle or physical clock calibration from §20 is supplied.

The following properties are distinct: the next primitive is legal at every nonterminal state; every input eventually completes; and there exist fixed $C,d$ with $T(x)\le C(n+1)^d$ on every input. The last includes negative instances of a decision task. Input-dependent auxiliary structure and its acquisition are charged when making a complexity claim; its presence at the chosen cut does not make it free advice.

**Proposition 21.2 (the actual native time–storage consequence).** Let $r_x$ be the actual finite prefix ending at a completed task output, and write $K_{\rm nat}(r_x)$ for the quantity called $n(r_x)$ in Theorem 7.2. For that theorem's construction-counted storage,

$$
T(x)\le K_{\rm nat}(r_x)\le S(r_x)/8.
\tag{C.21.1}
$$

Consequently, completion with correct output and a uniform bound $S(r_x)\le Q(|x|)$ on every input imply $T(x)\le Q(|x|)/8$. Here $Q$ is measured against the task-start problem record, not against the completed history's encoding length.

Proof. Reuse Theorem 7.2 on the same actual prefix:

$$
S(r_x)=S_0+b_{\rm ctl}(r_x)+8A(r_x)+8K_{\rm nat}(r_x).
$$

All terms apart from the last are nonnegative. The task interval is a subinterval of this prefix, giving (C.21.1), and substitution gives the stated consequence. This does not assert that the task's incremental storage is exactly eight times its time: ordinary cells, control, acquisition and pre-start history are included in $S$. $\square$

**Convention 21.3 (expanded size and initial size).** For a general append-only record with disjoint retained event fields of at least $b>0$ bits per primitive, counting fields gives $S_k\ge bk$ and hence $k\le S_k/b$. Proposition 21.2 uses the actual native receipt meter. A run with $T(x)\ge2^{|x|}$ must, in this record convention, leave at least $b2^{|x|}$ such bits. Its linear bound in completed size is compatible with exponential time in initial size. Compression without those disjoint fields and machines that erase their history do not inherit this storage argument. A polynomial bound on completed recorded size is an additional sufficient premise, not a consequence of defining one primitive as one tick.

**Definition 21.4 (cost-supported task progress).** Expand a macro trajectory $s_0(x),s_1(x),\ldots$ into actual completed native segments with integer costs $c_j\ge1$. Every reachable nonterminal macro state supplies its next completed segment under the same uniform controller. Let a nonnegative task potential satisfy

$$
\Phi_x(s_0(x))\le q(n),\qquad
c_j\le p(n)\bigl(\Phi_x(s_j(x))-\Phi_x(s_{j+1}(x))\bigr),
\tag{C.21.2}
$$

for fixed polynomials $p\ge1,q\ge0$. Initialization and final delivery are included or separately polynomially bounded; terminal outputs satisfy the task specification. The potential need not be computable by the observer. If the controller uses its value to choose operations, computing it belongs to the charged segment.

**Proposition 21.5 (endogenous completion from paid progress).** Under Definition 21.4, the macro-segment cost is at most $p(n)q(n)$ and the task completes in polynomial native time, including the stated preparation and delivery costs.

Proof. Apply the standard telescoping estimate in [the amortized-analysis note](../../../Library/Computability/tarjan1985amortized.md) to the same native segments. Every finite prefix has cost at most $p(n)(\Phi_x(s_0)-\Phi_x(s_m))\le p(n)q(n)$. An infinite sequence would have prefix cost at least $m$ for every $m$, a contradiction. The next-completed-segment premise excludes getting stuck or running forever inside a macro update. Thus a terminal state is reached, with the specified correctness and preparation/delivery bounds. The additional project obligation is an actual native construction satisfying (C.21.2), not the telescoping identity. $\square$

**Convention 21.6 (self-generation does not supply a progress rate).** [Predictive memory, Definition 1.3](RECURSIVE_RELATIONAL_OBSERVATION_SELF_GENERATED_PREDICTIVE_MEMORY.md) uses the same $U$ and emission rows $e_z$ for retention and the self-generated stochastic decoder. For $e_z(y)>0$, its finite-word product gives $D_z(\,\cdot\mid y)=D_{U(z,y)}(\,\cdot)$. This residual consistency supplies no bound of form (C.21.2). Its all-history, all-horizon accuracy requirement is a separate condition, not implied merely by deterministic control.

Fix a total computable $f:\mathbb N\to\mathbb N$. As a conditional implementation example, suppose an actual finite deterministic controller table has been supplied and installed by the native boot interface, with native routines that scan a lawfully acquired finite input $x$ and its end marker, compute $f(|x|)$, perform that many counter advances, and deliver a fixed output. The table is fixed for $f$ across inputs; the growing counter and records are tape data, not unbounded controller fields. Require these routines to terminate and their finite allocations and accesses to remain legal on each input. Total computability alone does not supply this installed table or its acquisition interface. Input acquisition and scanning, compilation and installation, evaluation, counter operations, retained records and output delivery are all charged; no polynomial bound on these costs is assumed. Each counter advance includes at least one actual primitive, so any such completed task interval containing the loop has at least $f(|x|)$ primitives. Its next operation is determined by the current full configuration. A local next-action forecast can use the same transition rule, with its own implementation charged. This is the weaker local deterministic consistency notion, not a finite-state competitor for the fixed stochastic source of Predictive memory. It is not an optimal-algorithm lower bound: under the same fixed-output interface the unnecessary loop can be omitted. It separates lawful local self-generation from a completion-rate bound for the supplied controller.

For SAT prefixes the rank $m-|u|$ decreases on every extension. Selecting that extension while maintaining a nonempty set of satisfying completions is the additional condition. The classical search/decision correspondence is already stated in [History records, §195](AURIC_FIB_HISTORY_RECORDS_TIME_ARROW.md); it does not follow from rank decrease or a unit-cost primitive clock.

**Convention 21.7 (native controls, compilation and reliable answers).** Assumption 55.2 and Theorem 64.1 of [Static compatibility fibers](AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md) give a continuously parameterized exact finite-word menu. Its §61 counts adjustable pulses even if each is generously counted as one tick. An arbitrary real pulse parameter is not thereby an effectively specified native digital instruction: producing its parameter, selecting its site and implementing the requested accuracy remain charged obligations.

Fix a local dimension $d_0$ and a finite inverse-closed instruction set $\mathcal G\subset SU(d_0)$ generating a dense subgroup, independently of input size and trajectory length. For $L\ge1$ effectively supplied targets $U_i\in SU(d_0)$ at declared sites, with effective numerical access sufficient for operator-norm accuracy $\epsilon/L$, the compilation and telescoping estimate in [Dawson–Nielsen's note](../../../Library/Computability/dawsonnielsen2006solovaykitaev.md) give compiled word length $O_{d_0,\mathcal G}(L\log^c(L/\epsilon))$ and total error at most $\epsilon$, for $0<\epsilon<1/2$. The exponent and constants are those of the fixed compiler; no uniformity in a growing whole-register dimension is asserted. This word-length bound uses the declared site-access model. Acquiring target descriptions, selecting sites, wiring or routing, obtaining precision, numerical arithmetic, compilation and installation are charged in any native total-work claim, along with preparation and final readout. None is made a free primitive by this estimate. This transfers a supplied trajectory bound; it supplies neither $L\le\operatorname{poly}(n)$ nor a constant probability of the correct task answer. The verifier experiment and uniform bounded-error definition in [Watrous's circuit note](../../../Library/Computability/watrous2011quantumcircuits.md) separate those obligations: a polynomial quantum SAT solver gives $\mathrm{NP}\subseteq\mathrm{BQP}$, whereas a deterministic polynomial classical solver gives $\mathrm P=\mathrm{NP}$. These distinctions use endogenous operation counts. This section contains reference-input derivations, without a claim of kernel certification or a solved SAT growth construction.

## 追加锚（本行以下为增补区）
