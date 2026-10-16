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
Successful reservations and strict raises have separate layout and policy
ordinals $r,p$. Every accessible ordinal is a constructed unary word.

Maintenance is admitted only at the serial idle boundary after previous
mandatory row delivery and acknowledgement. All inherited ingress, generation,
source-write, pending-row and partial-copy cuts remain runtime states. The
restriction on maintenance admission removes no original busy cut or original
continuation. No arbitrary-busy-cut migration, concurrency, crash recovery or
interrupt service is included.

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
17 holds block descriptions, 18 the old source-row stream, 19 unified-row
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
serialization, source generation, dispatch and rows.
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
to Definition 4.4, then the inherited response/counter/source-row routines.
Maintenance tags go to Definition 5.1. Local controller and terminal markers
go to their inherited actually executed code/complete-output routines.
Every route then goes to the unified row/delivery routine of §6, its actual
acknowledgement, TOK returning the source-service token to the dispatcher,
one CTL restoring the idle phase, and the same controller's
saved return edge. A raw external-frame mode instead returns to its next
frame IN. A terminal route finishes its row/delivery and actual ACK, and the
requested stop-snapshot/verification/consumer work of §6, before its halt
CTL. A verifier refusal completes that route with no task output. Source calls use CloseFence(`source-start`) before generation and
CloseFence(`response-commit`) after release; NativeLocal and Halt use the
same start/commit pair around their complete marker/output commitment.
These replace, rather than duplicate, any inherited designated fence sites.
They have no directory publication and use `no-publication` in the row.
The complete old/new $q,g,e,j,m$ words are staged before their roles are
reused. An original source call advances $q$, an accepted modification $g$,
and an accepted Rho $e$; the old source-row seal advances $j$. Local/terminal
markers and maintenance preserve $q,g,e,j$. Each completed unified event
advances $m$ once. Fence-count $f$ is separate from every one of these.

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
$h,K,r,p,v$, and inherited $q,g,e,m$ are accessible through their complete
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
load/stage every required before-field in this fixed order. If ReadState
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
has one unified producer row, with the following finite ordered fields:
model/version; source occurrence $\xi$; initial $H_0$/prior reference; old
all-event ordinal $m$; predecessor unified-row reference; event kind;
complete retained request reference; complete response; before/after $h,K$;
before/after layout and policy ordinals; before/after $q,g,e,j$;
before/after committed-directory counts; complete after-directory manifest;
start and response-commit fence references;
post-directory-publication fence reference or the finite tag `no-publication`; original
source-row reference or `no-source-row`; template/controller identity.
Tuple arities and kind tags are fixed finite values; all fields use Frame.
An optional reference field is the one-bit 0 for its none tag, or 1 followed
by its complete encoded reference. This fixes `no-publication`,
`no-source-row` and `no-predecessor` without treating an empty field as none.
Fence-reference payloads are the six-field tuples of Definition 6.1a;
compound before/after fields use nested Frames at their stated fixed arity.
Context/name/address material and every request frame are copied or referred
to by their complete actually retained descriptors. A reject row has reject
and no rejected candidate payload. A maintenance refusal has its own kind.
NativeLocal and Halt retain their inherited executed-instruction/output types.

The old producer source-row stream continues to receive each original source
event with its original $q,g,e,j$ meanings and original occurrence field.
Its physical source descriptor at that event means its actual interval then;
the new row supplies the complete active public manifest payload defined
below and the historical guard. No manifest field contains private source
bits or changes an old interval into a frozen snapshot.
No old row is edited or retyped. Unified maintenance rows have
`no-source-row`, preserve $q,g,e,j$, and advance only $m$. Original calls advance their actual applicable $q,g,e,j$ indices and $m$;
local/terminal markers preserve $q,g,e,j$ and advance $m$ only. A source response enters
the pending-event component at its release, and row seal later transfers it
to the sealed archive component. An activated directory entry before response
release is actual maintenance work, not a fabricated old source event.

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
after the new row index is complete. The old source-row reference is the
inherited sealed journal ordinal/owner/type, constructed by its supplied
journal writer; it is an audit reference, not a transferred private read
permission or a replacement for the new row's actual copied fields.

The response token and row seal are distinct. Between them the producer has
one completed pending event and an unsealed row. At every cut the extended
event word satisfies $E^+=A^+\mathbin{+\!+}P^+$, where $A^+$ is the sealed
row word and $P^+$ is empty or that one committed pending event. Earlier
request-ingress and pre-response source work are unfinished work, not $P^+$.
All bytes, heads, partial descriptors and latches also remain actual state.

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

The mandatory row route copies the complete unified row and any request/context
material absent at the actor through a fresh mailbox into that actor's
append-only archive. Only after all referenced request/context blocks absent locally have
arrived, and the receiver parses the whole row's framing, model/type, source
identity, predecessor, manifest and final status/seal, does its final TOK
acknowledge the row. A channel stage's receiver-seal TOK is an internal
copy completion; the row caller does not treat it as this final row ACK.
Required ancillary blocks are sent in fixed order: boot binding/initialization/prior if
absent, request header/length/payload, then named context blocks in request
order. Absence is tested by the local origin scan, not an external assertion.
The receiver uses its origin-to-local descriptor records for every referenced
payload check. Failed structural checking takes the paid refusal edge with
no new service-admission token; authentic rows follow the success edge. The row-copy caller resumes Definition 4.6 at that actual
acknowledgement. At stop freeze that already complete index-19 prefix:
scan its records once, constructing its unary count, and retain its last
row reference and event count. No later source event is admitted during
this stop route. Construct a snapshot-index bit word with the actual count,
Frame(boot-binding reference), Frame(prior reference), then, in index order,
Frame(row reference), Frame(complete request-reference tuple). Iterate the
frozen indices by the preceding native reader; each row's bounded ReadFrame
scan obtains its retained request-reference tuple. New/UnaryBody/Frame/Finish
and the ordinary staging bit-block graph construct/seal this finite index
on 21; its bound is obtained by the same length scan, not a live meter end.
Each request tuple explicitly enumerates its header/length/payload and any
context references with its constructed finite count. Its bit parser is
ReadUnary followed by that count's ReadFrames and a remaining-budget check.

Through the same full channel first copy the boot binding/prior and every
row/request/context block in this frozen finite list to the verifier, testing
its local origins to avoid a missing dependency; then copy the sealed
snapshot index. Its reference fields keep their producer origin meanings;
the verifier reads payloads through its acquired local descriptors. The
snapshot consists of these actual blocks and that completed index, and
its release CTL follows the complete index seal and dependency checks.
There is no atomic multi-tape freeze/copy or uncharged import. An empty
frozen list still constructs its zero count, boot/prior fields and status.
Earlier snapshots and archives are retained; no arbitrary external
transcript-import port is added.

**Theorem 6.4 (authentic rows, old handles and complete maintenance delivery).**
Every available receiver row equals its designated sealed sender payload,
including every manifest, maintenance/guard/binding and acquired fence field, and every verifier snapshot
equals the producer's frozen actual prefix. Every previous archive handle
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
Initialize replay $h=K=H_0,r=p=0$. Scan *every* unified row and complete
associated request material in order, using the preceding explicit framing,
ordinal, field and block-access scans. Malformed identity, predecessor,
length, seal, manifest, directory-count, fence binding or counter relationships
set a public failure
bit; no shortened scan substitutes for the full frozen prefix.

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
on ok set only replay $K,r$ to the declared successors. For a raise row,
check $h<J\le K$, equality and refusal cases; on ok set only replay $h,p$.
Construct replay counter versions by the same unary graphs. For an original
source row, run the supplied whole candidate/read algorithm on the replay
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
Layout bases and creation/fence references are checked as authentic provenance
fields of the copied actual trace, not inferred from a candidate's tree value.
There is no pretend test that a numerical name independently authenticates an
external transcript. Provenance here comes from the exclusive owned writer
and these allowed copies.

The stop proposal is an actual retained output/input block, not a mathematical
parameter converted to bytes for free. Copy it with the initialization and
frozen-prefix binding from the producer to verifier archive 32 on route 50.
After the snapshot index is sealed, its actual constructed reference supplies
that binding. Construct a typed expected-task binding block from these
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

An accepted receipt has type `INITIAL-q_H0`, the complete $\xi,H_0,D$,
literal proposal, frozen prefix end and snapshot reference, verifier
creation/seal references in its completed delivery descriptor. These are the
actual descriptor ordinal and constructed status-cell reference, with the
sender's seal CTL in its authentic provenance; any numeric fence for that
seal is obtained only by a later CloseFence and belongs to that delivery
descriptor. The receipt payload does not predict its own seal-fence numeral.
Copy it completely through Definition 6.3 to the
consumer. The consumer first parses every field and checks model/type,
$\xi,H_0,D$, prefix/snapshot binding, proposed target and actual accepted
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
Theorem 6.4 authenticates every copied row and request. Induct over those rows
with the actual initial candidate $u$. Reserve and Raise have the precise
public cases of Definition 5.1 and preserve its replay-current tree;
their metadata updates match ReadState's actual directory. Theorem 4.5 then
gives the same next genuine source response and successor under the recorded
historical guard. The same source-free controller and acquired responses
give the same local/stop markers. Hence every comparison for $u$ succeeds.

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
| Original source response and old source row | Historical $h$ guard, inherited $q,g,e,j$ rules; complete response commitment and genuine accepted/rejected successor |
| Start, successful publication and response CloseFence | Already constructed typed closed reference blocks, reloaded through their native descriptors into the row fields; no publication call on no-change branches |
| Retained ingress/header/length/payload/context blocks | Complete parser and row request references; missing actor copies arrive through the positioned channel before final row ACK |
| BuildManifest and complete unified bit-row writer | Bounded ReadFrame/manifest decoder at actor and verifier; the row channel copies the full $M_v$ payload, not a directory count alone |
| Sender/mailbox/receiver and local origin descriptors | Both length-bounded copy stages, actual status WR/CTL/TOK; only complete receiver material can be parsed |
| Frozen rows/requests/prior/boot binding | Verifier's acquired snapshot, full historical-guard and manifest checks, finite initial-candidate enumeration |
| Accepted INITIAL-q_H0 receipt and completed delivery descriptor | Consumer checks all fields and seals using its local acquired descriptors before writing/sealing/OUT of the target; refusal has no task output |
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
rejects both pass through their completed old source row, preserve its true
historical guard, and use the unchanged manifest. NativeLocal/Halt commit
only their own executed marker/output. Each branch writes exactly one new
unified event and has the same finite delivery join.

For a channel, induction on $0\le i\le\ell$ gives equality of sender/mailbox
and then mailbox/receiver prefixes and heads at their next relative index.
At $\ell=0$ the terminal test still runs and the distinct zero-status cell
is sought, written and sealed. At $i<\ell$ the data latch is written before
any next public counter test; public and data latches are distinct. All
bases/status addresses came from actual Base/length/Add words and actual
native descriptors, even on nonempty ports. Local origin records preserve
which sealed copy each owner may read. All required referenced payloads are
finite and the ordered missing-copy scan terminates. The complete receiver
row parser consumes all its bounded fields, manifest and seals, then emits
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
Source accepts/rejects both include their actual generator/gates/old row
work and the two source-start/response fence calls before the same return.
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

After all required maintenance and the genuine source row return, lend the
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
marker, without touching the source. For stop, complete output sealing and
delivery precede the global terminal state. The controller equation and
existing Native trace induction thus give $t=\rho^e u$ and the stated
chronology. The lift's Native suffix starts after the fixed acquired-seed
entrance; that entrance's own old rows remain in the actual archive.

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
delivery and owner correspondence; Theorem 6.6 supplies the actual
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
