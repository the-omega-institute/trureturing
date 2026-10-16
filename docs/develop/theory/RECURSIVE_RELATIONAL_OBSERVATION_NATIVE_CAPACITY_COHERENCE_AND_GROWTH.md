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

A native call is inlined with its fixed return edge, as in PR57.D1. There is no
unbounded native call stack. Twelve word-role names can be permuted among the
twelve work ports by a finite-control CTL; this is a permutation of twelve
fixed ports, not a variable-address pointer. Arithmetic outputs always use a
port distinct from their inputs. A needed repeated operand is copied to a
spare port first. After the result is complete, one such CTL exchanges its role
with the old destination role. Every routine below uses at most six operand,
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
roles. Thus the twelve ports suffice. Old words
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
routine calls form the order: primitive word routines, arithmetic, field
iteration, directory state/resolution, source generation, dispatch and rows.
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

For a directory/frame field whose head already points to its first bit,
CopyField uses the identical loop without Last($s$). It stops at that field's
actual sep. SkipField repeatedly RD; on sep MR and return; otherwise MR and
repeat. On $k$ bits it costs $2k+2$. All source heads and destination tails
in these calls are those actual marked cells. No mathematical offset is used
as an unexecuted stopping test.

Equivalently, FieldBody is just that sep-terminated $5k+1$ loop, entered
with source at its first bit and destination at R, returning with source at
sep and destination at R. CopyField is New(destination), FieldBody, Finish;
Copy additionally positions the source with Last. A caller writing a
directory or framed row invokes FieldBody and its displayed Append(sep),
rather than CopyField's work-word Finish. UnaryBody copies a complete
$U(a)$ using RD(source); EX(destination); WR(destination,read-bit);
MR(destination); MR(source) for every bit, including its terminal 0. The
RD successor repeats on 1 and returns after those same four remaining
occurrences on 0. Its cost is $5(a+1)$; source returns one cell past the 0
and destination at R. The raw zero-copy calls below mean this graph, with
their explicitly stated source positioning and destination already at R.

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
descriptor copies use Definition 3.1 and the framing in Definition 6.1.

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
three finite field counts. Each field is either CopyField into a work role
followed by MR(0), or SkipField. It checks the seal by RD; MR, then repeats;
at R the testing RD returns. A seal cell is never copied as field data. A
record's tag, field cursor and finite number of remaining fields are finite
control. Record ordinals, if needed, are unary work words incremented by
Definition 3.2 after each seal. No scan bounds itself by the growing meter.
An incomplete tail is ignored by the mathematical committed-prefix relation;
the executable iterator is called only with a complete idle directory or a
previously frozen complete copy. It is never run concurrently with its writer.

WriteRecord executes Tail(0), appends the two literal tag bits and sep, then
for each listed field executes Last on that field's work port and the
CopyField loop to directory 0, followed by Append(0,sep). Its source word
heads end at sep and destination remains at R. Finally EX(0) constructs the
prospective seal cell, WR(0,seal) publishes it, and MR(0) returns to R.
Publication is precisely that one WR, after every field has been written.
The preceding EX, WR and following MR are three distinct runtime cuts. A
partial record grants no source authority. No operation atomically installs
its variable-length fields or writes an unbounded current pointer.

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
CopyField into a distinct work port, then a finite role permutation; fields
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
at boot has the following dispatch cycle. At idle it acquires and seals one
canonical complete frame on port 13, parses it, retains its return kind and
command, and takes the source-availability token into the selected service.
It executes ReadState before generation or maintenance. Old source tags go
to Definition 4.4, then the inherited response/counter/source-row routines.
Maintenance tags go to Definition 5.1. Local controller and terminal markers
go to their inherited actually executed code/complete-output routines.
Every route then goes to the unified row/delivery routine of §6, its actual
acknowledgement, one CTL restoring the idle phase, and the same controller's
saved return edge. A raw external-frame mode instead returns to its next
frame IN. A terminal route finishes its row/delivery before global halt.

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
is the constructed base+length+1. Their descriptors are framed actual
words in producer block descriptions on 17. Their separate physical
separators/status bits are not wire-input bits: the chronological wire
frame is exactly the header bits, length bits and payload bits referred to
by those three descriptors. Automatic commands construct the same three
blocks by Append/copy instead of IN, including the same actual status and
descriptor work. This fixes setup and entry positions even on nonempty
port 13 and leaves every acquired-but-unwritten input cut distinct.

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
data by PR57.L1–L4. The complete row and channel expansions in §6 terminate
and have that join as their fixed exit. The final CTL returns to the retained
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
and old archive permissions are untouched.

For Reserve, Compare($J,K$) selects greater/equal/less. In the greater branch:
Sub and two doublings construct $d=4(J-K)$; increment $r$ and $v$ into prepared
new words; obtain an already closed start fence $f_s$ by PR57.D3's fence and
full finite readout; Base(16) constructs $b$; Zero(16;$d$) creates the interval
and its delimiter. Copy all seven reservation fields into work words, one at
a time as needed; construct the response fields `reserve-ok`, old $K$, $J$,
and new layout ordinal. The fields containing $m$ refer to the completed
pre-operation all-event count. WriteRecord(`01`) appends the complete entry
and publishes it at its seal WR. Its source-service token remains busy.
Construct/seal the finite response block, release its response token by CTL,
and take the already closed response-commit fence. The prepared $m+1$ version
is now selected by paid copying/descriptor work. Go to the §6 maintenance
row routine. In the equal and less branches allocate no source segment and
append no directory record: prepare the typed `unchanged` or
`maintenance-refusal` response with the old/current values, commit it, advance
only $m$, and use the identical row/delivery/return route.

For Raise, Compare($J,h$), then Compare($J,K$), selects exactly $h<J\le K$.
In that branch increment $p,v$, take the closed start fence, construct the
five raise fields and response `raise-ok`, old $h$, $J$, new policy ordinal,
then WriteRecord(`10`). No source cell is a WR destination. Commit response,
take its fence, select $m+1$, and go to the same row route. Equality with $h$
returns `unchanged`; $J<h$ or $J>K$ returns `maintenance-refusal`, with no
directory record. Failure/equality branches also take their own start and
response fences. Every invocation prepares both old and required incremented
counter versions before selecting them, as in LJA4.2. Directory count and
$r,p$ at an activated but not-yet-row-sealed cut are determined by the actual
directory prefix and phase; their later wire copies are not atomic counters.

Directory publication and response commitment are different boundaries.
After the seal WR the new binding/guard is authoritative, but a new source
call is still unavailable. The following MR, response sealing/release, closed
fence scans, row writing, channel phases and acknowledgement are all real
states. Before publication, staged allocation/metadata has no current-source
authority. Only after acknowledgement does the dispatcher restore source
admission. A row's directory reference and publication fence are serialized
after they exist; no field predicts its own future completion ordinal.

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
by §6 and restore the prescribed idle return. They add genuine receipts and
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

**Definition 6.1 (counter and field access without free references).** For a
fully specified counter-bank convention, reserve producer port 23 for public
counter versions. Its record is a three-bit name, sep, $U(n)$, sep, seal;
names 000,001,010,011,100 denote $q,g,e,j,m$. Boot appends a zero record for
each. LoadCounter(name) executes Home; MR and a record scan: read three bits
with RD; MR, check sep with RD; MR, CopyField the value when the finite name
matches and otherwise SkipField, check seal with RD; MR, then repeat until
the terminal RD(R). Each matching copy replaces that role by a finite port
permutation; the last matching sealed version is returned. AppendCounter
executes Tail, literal name/sep Appends, the raw copy loop on the selected
complete $U(n)$ through its terminal zero, Append(sep), EX; WR(seal); MR.
This is the explicit origin/version access used by Definition 5.1. It does
not require a recursively positioned descriptor. Bank bits are public
metadata under producer ownership, not secret source operands. All counter
updates occur on these actual records. After commitment and before record
completion their effective semantic values are determined by phase and the
already prepared old/new words, as in LJA4.2; no partial unary word is current.

Each new row field is a finite bit string. Frame($w$) writes $U(|w|)$ followed
by exactly those bits. To construct its length, position a complete work word
with Last, start an output work word with New, then repeatedly RD(input); on
sep terminate with Append(0), Finish, otherwise Append(1); MR(input) and
repeat. This length scan has $5|w|+1$ occurrences before the final 0/Finish.
Reset the source with Last, append the complete unary length by its raw
zero-copy loop to the row tail, then copy its bits by the sep-terminated raw
copy loop. Output row position remains at R throughout those bodies; those
raw loops omit New/Finish on their destination. Field-source positioning and
the terminal tests remain present. A field already in a sealed block is
loaded by At on its descriptor's constructed base and the actual length
counter; RD; Append; MR(source); MR(length), with its initial/final length
tests, produces the corresponding complete work word before Frame.

A block reference is a framed tuple of unary owner, port, actual Base offset,
length and creation ordinal, together with its type and seal-cell reference.
Every reference field is produced by these same routines. Origin access to
a block-description stream counts its actual seals with the unary increment
and Compare graphs until the requested ordinal; each preceding field uses
SkipField. The requested complete record's fields are copied with CopyField.
At its terminal R the scan returns typed `no-block`. There is no descriptor
lookup primitive. Existing immutable block descriptors and archive lookups
retain the supplier's owner/seal checks and actual paid scans.

For clarity, the arbitrary-word equality used in the new parsers and consumers
has its own finite graph. Execute Last on two distinct complete word ports;
set a finite control flag to true. Repeatedly RD(first), save its symbol in
finite control, RD(second). Unequal symbols clear the flag. If both symbols
are sep, return the flag. Otherwise MR on each head whose symbol is not sep
and repeat. A head already on sep stays there. Thus both words are completely
scanned even after a mismatch, including different lengths. Parsing Frame
first copies its unary length by the zero-terminated raw copy; position its
completed counter with Last, then repeat RD(counter); on 1 RD(payload);
Append(output,bit); MR(payload); MR(counter), on 0 Finish(output) and return.
The caller consumes exactly its fixed field arity and checks the block's
actual remaining length. These graphs supply the new framing/equality checks
in Definitions 6.2–6.5; the original tree/normal-form parsers retain their
exact supplier graphs.

**Definition 6.2 (row language and producer writer).** Every completed event
has one unified producer row, with the following finite ordered fields:
model/version; source occurrence $\xi$; initial $H_0$/prior reference; old
all-event ordinal $m$; predecessor unified-row reference; event kind;
complete retained request reference; complete response; before/after $h,K$;
before/after layout and policy ordinals; before/after $q,g,e,j$;
before/after committed-directory counts; start and response-commit fences;
directory-publication fence or the finite tag `no-publication`; original
source-row reference or `no-source-row`; template/controller identity.
Tuple arities and kind tags are fixed finite values; all fields use Frame.
Context/name/address material and every request frame are copied or referred
to by their complete actually retained descriptors. A reject row has reject
and no rejected candidate payload. A maintenance refusal has its own kind.
NativeLocal and Halt retain their inherited executed-instruction/output types.

The old producer source-row stream continues to receive each original source
event with its original $q,g,e,j$ meanings and original occurrence field.
Its physical source descriptor at that event means its actual interval then;
the new row separately supplies the full active manifest prefix and guard.
No old row is edited or retyped. Unified maintenance rows have
`no-source-row`, preserve $q,g,e,j$, and advance only $m$. Original calls and
markers advance their inherited indices and $m$. A source response enters
the pending-event component at its release, and row seal later transfers it
to the sealed archive component. An activated directory entry before response
release is actual maintenance work, not a fabricated old source event.

To write a row, first Base(14) records its real beginning. Its fields are
constructed and appended by Definition 6.1 in the displayed order. Append
sep, then append one zero bit as its seal-status cell; measure the completed
payload length by a scan from the saved base up to its first sep, constructing
a unary length word exactly as above. Construct the complete block descriptor,
including the actual address base+length+1 of that status cell, by Add and
Frame. Seek that cell with At and WR(1); one CTL seals the completed row and
records its immutable availability. The sep/status cell is not a payload bit.
The row's length, descriptor, previous-row link and earlier fences are all
actual material. Its seal occurrence is part of the provenance relation;
any serialized fence naming that occurrence is acquired by a later closed
readout and stored in the later delivery descriptor, not inside a row before
its own creation. No self-referential current cost field is required.

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
the receiver's archive port. These ports can be nonempty: both bases are
measured at their actual current R. Their distinct intervals, tokens and
status cells exist before copying. Sender, mailbox and receiver coexist.

For the first stage, Last(counter); At(sender,base); At(mailbox,base).
The six-row loop is RD(counter,test); on 0 go to sealing, on 1 RD(sender,data);
WR(mailbox,data); MR(sender); MR(mailbox); MR(counter) and back to the test.
The private/data latch and public counter-test latch are distinct. At exit,
At(mailbox,status); WR(1) is the seal-status prelude; CTL seals the whole
mailbox; TOK hands off its read token. For the second stage reposition
Last(counter), At(mailbox,base), At(receiver,base), run the identical six-row
loop, At(receiver,status); WR(1); CTL seal; TOK acknowledgement. These
At invocations include Last on their actual address words. Every computed
status address and its duplicate needed for later positioning is copied
before the corresponding body. The destination's following sep permits its
last MR. Sender remains immutable; mailbox becomes readable after its own
seal/handoff; receiver is unavailable until its final seal. A finite token
does not stand for an unconstructed seal table.

Consequently the two payload loops, terminal tests, CTL seals and TOKs have
exactly $12\ell+6$ occurrences, as in AIF6.4. The two real status-positioning
and WR preludes, all Base/Zero/status/descriptor construction, first positioning
and between-stage repositioning are additional displayed graph evaluations.
There is no assertion that $12\ell+6$, or $8\ell+4$, is the complete bill.
Each such Prelude, At, Frame, Last, Base and Zero has its expansion here or
in the exact supplier; the channel has no unnamed setup service.

The mandatory row route copies the complete unified row and any request/context
material absent at the actor through a fresh mailbox into that actor's
append-only archive. Only after the receiver parses the whole row's framing,
model/type, source identity, predecessor reference and final status/seal does
its TOK acknowledge. The row-copy caller resumes Definition 4.6 at that actual
acknowledgement. At stop, freeze the actual complete unified row/request/prior
prefix; obtain its finite bound by scanning that already closed prefix;
copy it through the same full channel to a fresh verifier snapshot. A snapshot
is readable only after its complete receiver seal. Earlier snapshots and
archives are retained; no arbitrary external transcript-import port is added.

**Theorem 6.4 (authentic rows, old handles and complete maintenance delivery).**
Every available receiver row equals its designated sealed sender payload,
including the maintenance/guard/binding fields, and every verifier snapshot
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
whole equal payload, not merely its copied prefix. Descriptor and origin
fields are among those copied bits; they are not newly chosen by a receiver.

The producer writer appends without modifying any prior row or its descriptor.
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
length, seal, directory-count or counter relationships set a public failure
bit; no shortened scan substitutes for the full frozen prefix.

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
creation/seal references. Copy it completely through Definition 6.3 to the
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
fictitious guessed source value. Thus the survivor set is precisely that
compatible initial-source fiber, with the stated structural checks. The
complete enumeration's nonempty/constant decision is the asserted condition.
The preserved initial-target computation is the existing exact $q_{H_0}$
computation. Applying constancy to the actual survivor $u$ proves the receipt
value. Whole receipt copying and the consumer's type/binding checks preserve
that value before actual task-output writes. No target is re-evaluated under
the newest guard merely because its archive is now read later. $\square$

## 7. Exact cost recurrence and all actual cuts

**Definition 7.1 (evaluable primitive recurrence).** Expand the finite graphs
in Definitions 2.3–6.5 and the cited exact supplier graphs. For a graph entry
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

This is a primitive evaluation, not a schematic sum of services of unknown
cost. For example WriteRecord with field lengths $k_1,\ldots,k_f$ evaluates
to its actual Tail cost, 12 tag/seal occurrences, and, for each field,
its actual Last cost plus $5k_a+4$. Zero has its actual Last/Tail calls,
$5d+1$ body and 3 delimiter occurrences. Resolve's value is obtained by
following its actual tag/field scan, Compare/Sub calls and the one successful
Add, with every input Last and field delimiter. Reserve's value follows
Definition 5.1's actual selected graph through row acknowledgement and its
final idle CTL. No symbol such as an unspecified setup, migration or
publication charge occurs in this recurrence.

Gate generation includes every source-field Resolve, real absolute-address
arithmetic and all emitted bits. A gate record has length
$13+d+a+b+c$ in the exact unary encoding. Its interpreted cost is PR57.06,
with its actual head distances, four full address-field copies and their
real descriptor/positioning expansions. The caller supplies the actual
constructed addresses, not a free address map. ReadE, modifications and
literal minterms use the same templates and public loop bounds as their
suppliers. Installation evaluates the actual finite native-description
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
Every Reserve performs positive zero-fill, directory and row work; every
Raise performs positive metadata/row work. A projection omitting their labels
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
premise. Canonical-prefix input is exactly the same admissibility restriction
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
