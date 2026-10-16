# Actor-local acquired Reserve phases and paid historical return

## 1. The original source and the added owned carrier

**Definition 1.1 (source and target).** Let
$\mathcal T=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle$,
with the substitution and leaf count of
[CAP](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CAPACITY_COHERENCE_AND_GROWTH.md),
Definitions 1.2–1.4. Fix one finite original preparation $\xi$, initial
$H_0\ge1$, actual $u\in\mathcal T_{H_0}$ and actual prior
$D\subseteq\mathcal T_{H_0}$ containing $u$. The source parameters satisfy
$H_0\le h\le K$ and $\lambda(t)\le h$ at completed source boundaries.
The initial source packet, contiguous initial interval and single private
preparation are CAP Definition 2.4's. Later source addresses use its
$\phi_K$, not an independently prepared packet. The original target is
$\operatorname{INITIAL}\text{-}q_{H_0}$, with its original proposal,
verifier, receipt and consumer. An Image below has a separate type and is
never substituted for that target.

**Assumption 1.2 (primitive foundation and finite supply).** Use the sequential
atomic model of [TMC, PR57.D1–D2 and D7–D9](RECURSIVE_RELATIONAL_OBSERVATION_TRANSPORT_MEMORY_COMPLETION.md#57-a-complete-paid-ideal-realization-of-the-original-ordered-tree-interface),
with CAP's finite row/effect encoding and actual initialized channels.
One occurrence is RD, WR, ML, MR, EX, BF, IN, OUT, TOK or CTL, including
its specified finite boot variant. Each has one receipt, one tick and two
fee units. Boundary construction and finite control-bit installation are
paid boot variants. An ordinary symbol is one of
$L,R,0,1,\square,\mathsf{sep},\mathsf{seal},\mathsf F$.
A cell has the supplier's eight literal tracks. There is one actual meter;
its read and append heads remain distinct. Exclusive writers, provenance,
seals and current tokens have their original meanings.

Required finite input is actually supplied at its prescribed IN sites.
Every reached computation of an original controller or prior used in a
claimed completed flight terminates. These are pointwise premises, with
no deadline and no premise supplying a future capacity maximum. No
physical conformance or physical energy law is included in this model.

**Definition 1.3 (the 74-role assignment).** Keep every original port 0–63,
owner, origin, mailbox route and source mask of CAP Definition 2.2. The
following ten new ports all belong to the existing actor $A$.

| Port | Physical role |
| --- | --- |
| 64 | Word bank A |
| 65 | Word bank B |
| 66 | Native Base, saved-distance and ordinal scratch |
| 67 | Native length scratch |
| 68 | RCA-format descriptor stream |
| 69 | Installation fields and later native staging |
| 70 | Retained outer choices and history ingress |
| 71 | Immutable history archive and published sender blocks |
| 72 | Dedicated history mailbox |
| 73 | Dedicated history receiver |

In particular CAP verifier 32–39, consumer 40–47 and their routes 50–51
are occupied and remain unchanged. Port 33's native CAP descriptor origin
is not port 65's bank origin. Original actor archive 28 and descriptors 29
are the history module's old-data sources, not compiler scratch. No token
for 0–23, 24–27, 32–63 is transferred to this compiler. Handler and client
are installed phases of $A$. Their invocation-availability slots and the
mailbox-availability slot are distinct finite slots; TOK between slots
is executed even though the payload owner is the same principal.

**Definition 1.4 (two descriptor grammars).** CAP native records on 29 have
physical form

$$
00\mathsf{sep}\;w_0\mathsf{sep}\cdots
w_9\mathsf{sep}\;\mathsf{seal}.
$$

Their fields, in order, are owner, port, base, length, creation ordinal,
type, initialized, mutable, status address and origin. Numeric fields are
$U(n)=1^n0$. The CAP creation ordinal is one-based. An immutable bit block
has payload at $[b,b+\ell)$, following sep at $b+\ell$, and status at
$b+\ell+1$. Its origin is empty or the complete framed remote reference,
not a native address at the recipient.

The compiler's descriptors on 68 instead have RCA Definition 11.3's
concatenated unary owner, port, base, length, flags 10, creation ordinal,
then F and seal. Their ordinal is the number of preceding descriptor Fs,
hence zero-based. History records contain explicit kind tags. These two
grammars are parsed separately; neither a CAP seal nor a CAP sep is an
RCA bank delimiter. This distinction implements the origin and grammar
separation required by CAP Proposition 14.2.

## 2. Finite expansion and a physically initialized word bank

**Definition 2.1 (word notation and its expansion).** A word register is a
field in RCA Definition 11.1's complete bank, with compiler roles
32–39 relocated respectively to 64–71. The only assignments are empty,
copy, literal-bit cons and tail; tests are empty or first-bit tests.
Reverse, Cat, Length, Equal, Frame, Take, ReadUnary, ReadFrame, ReadList,
Nth, Replace and AppendItem mean exactly the acyclic expansions of
[RCA](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RETROSPECTIVE_CUT_ACQUISITION.md),
Definition 12.1. An internal natural is $1^n$; emitting its wire form
requires an additional literal zero. A tuple is an explicitly framed list
of fixed arity. Every numeric field is checked for exhaustion after
ReadUnary. Failure of a bounded Take, an arity test or an exhaustion test
has its own finite failure successor.

Unary comparison and subtraction copy the two natural words to distinct
cursors and tail both while both are nonempty. If only the right cursor
remains, comparison is less and subtraction fails; joint exhaustion means
equality; otherwise the remaining left cursor is the exact positive
difference. Addition is Cat on natural words. Multiplication by four is
two Cats producing two and then four copies; successor is literal cons 1.
These are abbreviations for the same assignments/tests, not new leaves.
List cardinality is a ReadList traversal consing one 1 per item. Every
range, count, difference and bound test below uses these expansions.

Every assignment expands into RCA Definition 11.3's two-pass bank
construction: actual Base; dry length count; real field emissions,
separators and F; bank seal; closed descriptor count; actual descriptor
write; parity CTL. Its LastBank, Field and LastScratch are Definition
11.2's literal scans. In particular an assignment is not one native row.
The source bank is immutable during both passes, and all old versions,
scratch words and descriptors remain constructed.

Use first-occurrence order for the finitely many registers after hygienic
inlining. Inline fixed calls and the acyclic macros before numbering native
rows, in the order of the definitions below, then textual row order.
Finite alternatives use ascending port/latch order and the symbol order
$L,R,0,1,\square,\mathsf{sep},\mathsf{seal},\mathsf F$.
Branches list false before true. While joins its last successor to its
actual testing row. A join introduces no occurrence unless a CTL is
explicitly specified. The resulting finite native graph is $G$; its
register count is a syntactic finite constant, independent of all runtime
word lengths and capacities.

**Definition 2.2 (native helper meanings).** The following table fixes the
native leaves used outside a word assignment. An input or length latch
is never reused as the test latch before its matching write.

| Helper | Native expansion |
| --- | --- |
| Home($i$), Tail($i$) | RD testing L or R; on failure ML or MR and repeat. |
| Append($i,b$) | EX($i$); WR($i,b$); MR($i$), with $i$ initially at R. |
| Base($i$) to 66 | Tail(66); Home($i$); MR($i$); for each non-R RD append 1 to 66 and MR($i$); at RD(R) append 0, sep, and seal to 66. |
| UnaryCopy | RD(source); EX(destination); WR(read bit); MR(destination); MR(source), including the terminal zero, with its encoded zero successor exiting. |
| Seek($i$) | Home($i$); MR($i$); RD of the positioned copied address; per leading 1 MR($i$), MR(address); final RD(0) exits. |
| CountDescriptors | Home(68); MR; RD; at F append 1 to distinct scratch, then MR; at another non-R symbol MR; at R append 0, sep and seal. |
| Native field import | Position the actual source; per payload bit RD, finite bit test, literal compiled cons, MR; at its delimiter Reverse the accumulator. |
| Native field export | Measure destination Base, dry-count the positioned bank field on 67, reposition it, copy by RD/Append/MR, append F and seal, then count and write its descriptor. |

Unless another latch is named, native public reads use latch 4. Ingress
uses latch 6, with length tests on 5. Fixed bit choices are selected into
literal control branches before a word helper overwrites latch 4.
Each row preserves every unmentioned cell, head, latch and finite bit.
Native field export is RCA Definitions 11.3 and 13.4's exact measured
copy schema, not a constructor accepting a mathematical string.

**Definition 2.3 (empty-bank prelude).** After ordinary boundary construction,
append one F to each of 64 and 65. If $r$ is the syntactic register count,
measure Base(64), construct $U(r)\mathsf{sep}$ on 67 by $r$ unrolled
Append(1)s and Append(0), and seal that word. Append $r$ seps and F to 64,
seal it, count the preceding descriptors on 68 and append its full
actual descriptor. A CTL sets parity A. Every register is then empty.
No compiled assignment occurs before this prelude.

**Definition 2.4 (compiler instance relation).** The word-boundary relation
here is RCA Proposition 11.4's represented register/bank/descriptor/parity
relation with the injective relocation 32–39 to 64–71 and the syntactic
register count of $G$. Interior helper cuts have its raw partial-bank
relation. Source/destination distinctness, fixed-field numbering and
closed-end scans are the same conditions; they refer to these actual new
owned tapes. This is a use of the supplied compiler relation, not a claim
that its old unused-verifier condition holds on CAP's occupied ports.

## 3. Actor-local old-data acquisition and exact finite parsing

**Definition 3.1 (a closed owned-tape importer).** Let $i$ be one of 26, 28,
29, with its actual read token, and let its complete ordinary prefix remain
unchanged during this importer. Clear a saved-distance register $d_i$.
At Save read $i$ testing L; on a non-L branch execute ML($i$), then the
compiled literal cons $d_i:=1d_i$, and repeat Save. At L perform MR($i$).
Clear a reverse symbol accumulator. At Scan read $i$ testing R. At each
non-R symbol choose its literal three-bit symbol code
$b_0b_1b_2$ by the eight finite cases, execute the three literal cons
assignments in order $b_0,b_1,b_2$, then MR($i$) and repeat Scan.
At R Reverse gives the forward concatenation of the symbol triples.
Clear/copy a restore counter from $d_i$; Home($i$); while this counter is
nonempty, execute MR($i$) and its compiled tail. Stop on its compiled empty
test. Distinct registers retain the copied symbol word and $d_i$.

The source-head save includes all cells from the original marked cell to L,
not only payload bits. The scan excludes L and R and includes physical
seps, statuses, F and seal symbols. Compiler rows touch only 64–68; they
never move $i$. The branch encoding a symbol is fixed before its three
cons assignments. No symbol is expected to survive in latch 4 across an
assignment. The scan does not read the seal track or change source bytes.

**Proposition 3.2 (import and head restoration).** The importer returns
exactly the ordinary symbol word of the chosen actual tape and restores
its entry head. It terminates with paid finite work, including on an empty
tape. It neither acquires another owner's backing nor grants authority
from an encoded permission.

Proof. After $a$ Save iterations, the source has moved $a$ cells toward L
and the bank distance has $a$ leading ones. Source L already exists, so
Save terminates at its actual original distance $h_i$. After $j$ Scan
iterations the source points to the next cell and the accumulator is the
reverse of the first $j$ literal triples. The finite symbol branch and
three cons assignments establish this invariant without using a surviving
read latch. Because no source writer runs during Scan, its existing R is
fixed. Reverse returns exactly its finite symbol word. Home and the
$h_i$ actual restore moves return the mark to its old cell, including when
that cell was R. Word-bank updates preserve the source mark. All loops
consume a fixed finite source, distance or accumulator. No assertion about
restoring the compiler's own heads or latches follows or is needed. ∎

**Definition 3.3 (the CAP descriptor parser).** Decode symbol triples by
successive three-bit Takes and the finite inverse table. A trailing partial
triple is ParseFault. Parse 29's copied word from its beginning, repeating
the following finite operation until its exact end:
read literal 0,0,sep; read ten sep-terminated bit fields, including empty
fields; require the following seal symbol. Each field is accumulated with
bit tests, cons and Reverse. Any other symbol or missing separator/seal
is DescriptorFault. Count records by consing one unary mark per completed
record. Require each numeric field to be one complete $U(n)$; owner,
port, flags and kind must be in their finite ranges, and creation ordinal
must equal that record's one-based count.

To resolve an acquired remote reference, ReadFrame its fixed-arity tuple;
scan this copied list for an equal complete origin field. Use the first
matching available local record. For a delivered row/dependency require
local owner $A$, designated archive port 28, initialized=1 and mutable=0.
For the initial acquired seed/boot material permit its actual designated
26 or 28 delivery interval and kind, using the corresponding initial
copied symbol word; these are two fixed cases, not a variable native
read port. Cancel a copied unary base against that designated symbol list;
Take its copied length in symbol units; require binary payload symbols,
following sep, and symbol 1 at the actual status address $b+\ell+1$.
Compare that address with its descriptor's field. Require its actual CAP
kind and complete origin/reference equality. A missing, unavailable or
wrong-kind record has distinct finite rejection. Local-origin-free initial
blocks are selected by their actual local reference and the same checks,
not by searching for a remote empty origin shared by many records.

The tests on copied status symbols are finite word tests. Current live read
permission and authentic sealing come separately from the reached CAP
acknowledged-return invariant. No copied flag issues TOK. A copied
immutable flag describes the completed block, not arbitrary bytes with
forged provenance. More than one actual copy is harmless: CAP Theorem 6.4
gives equal payloads for the equal complete origin.

**Definition 3.4 (row and request parsing).** A bit tuple is parsed by
ReadFrame exactly its stated number of times, followed by exhaustion.
Use the following finite arities from CAP Definitions 6.2–6.2a.

| Type | Fields and required subordinate grammar |
| --- | --- |
| SEG-U1 | Eighteen Frames: version, $\xi$, initial/prior binding, old $m$, unified predecessor, kind, request references, response, one four-component $h,K$ tuple, one four-component layout/policy tuple, one eight-component $q,g,e,j$ tuple, one two-component directory-count tuple, manifest, start fence, response fence, publication option, semantic option, template identity. |
| SEG-J1 | Fifteen Frames: version, $\xi$, initial occurrence, initial/prior binding, post-$j$, semantic predecessor, kind, requests, response/marker/output, six $q,g,e$ fields, historical $h$, source-layout tuple, template, start fence, response fence. |
| Request-reference tuple | ReadUnary count followed by exactly that many framed complete references, then exhaustion. |
| Complete CAP reference | Eight successive Frames, then exhaustion: owner, descriptor-stream port, one-based creation ordinal, payload port, base, length, type, status address. Numeric components must each be one complete $U(n)$; the type is its finite CAP bit tag. |
| Manifest | ReadUnary $v$; exactly $v$ records, each framed tag and respectively 6, 7 or 5 framed fields for tags 00, 01 or 10; then exhaustion. |
| Fence | Six Frames: kind, $U(f)$, $U(n)$, $U(2n)$, $\xi$, event/directory binding. |
| Optional reference | Literal 0 and exhaustion, or literal 1 and the complete reference codec. |

Starting with the acquired boot binding, check successive old unified labels
$0,1,\ldots$, predecessor references and before/after fields. For a semantic
event require its actual acquired semantic mate with post-$j$, its separate
semantic predecessor and all fifteen fields. Maintenance has none. Resolve
every enumerated request/control/output dependency through Definition 3.3;
parse the original header, length and payload from their three separate
binary blocks, excluding their physical seps/status cells. The first five
source tags and maintenance 101/110 retain CAP Definition 4.6's grammar.
There is no ninth or implicit source opcode.

Every list traversal is ReadList; every index is Nth with unary cancellation;
every field comparison is Equal. Fixed-arity products use fixed field
numbers, never a variable native register. Each outer record iteration
consumes at least its kind and delimiter; each inner field iteration
consumes a symbol or returns a finite failure. Thus this is a finite word
program with an explicit compiler expansion, including all malformed finite
arguments. It is not a mathematical pointer dereference.

**Proposition 3.5 (the acquired CAP-to-word join).** At a completed CAP row
ACK followed by source-token/idle return, importing closed 28 and 29 and
applying Definitions 3.3–3.4 returns exactly the actor's complete delivered
rows and enumerated dependencies, with their actual origins and event order.
It restores those two native heads. For the acquired seed/boot material on 26 the initial importer uses its
actual delivery descriptor, complete kind/status/origin and the copied 26
symbol word. This initial word is retained in the immutable manifest;
later cycle parsing need not reread a seed tape through a changed head.

Proof. CAP Definition 6.3 requires these payloads, local descriptors,
statuses and joined checks before the row ACK. Its Theorem 6.4 gives
immutable payload equality and origin preservation. During this importer
no CAP writer extends either source tape. Proposition 3.2 therefore copies
their exact physical symbols. The ten-field/seal parser consumes their
actual grammar, with the correct one-based descriptor ordinal. Base
cancellation and length Take extract precisely the local interval,
including its distinct following sep and status test. The row field
counts and predecessor checks are the supplied CAP codecs, so field
inversion identifies the same rows and dependencies. All raw source
states reconstructed later come from replay, not from asserting that
archive 28 is a private-source snapshot. ∎

## 4. One boot, code capture and original-client parking

**Definition 4.1 (a parked original client).** Fix an actual finite CAP
controller table and initial state whose next entry is $r$, before its
workspace loan. Execute CAP Definition 2.4's public boot, single private
preparation/validation, counters/directory/fences and stationary seed
acquisition/delivery. At its handoff initialize that actual table/state
on 24/25 and its initially empty waiting packet on 27 by CAP Definition
8.1's paid writes and channel/loan discipline, as in CAP Definition 16.2.
Return the twelve work tokens to the producer. Ports 24, 25 and 27, including
their heads and owners, are now parked until the original client is resumed.
Port 26 retains its acquired seed and owner; its initial import temporarily
moves its head and then restores it before the first outer entry.
The acquired initial seed and actual public/prior bindings remain readable
by $A$. There is no pending actor operation requiring a public work word.

The added source caller is a separately numbered inlining $F^A$ of CAP's
complete seven-tag raw frame graph, from its header Base prelude through
its final row ACK, source-token TOK and idle CTL. Only that final CTL's
successor changes, to the fixed label InnerReturn. It does not enter the
old raw graph's next-frame IN. Its input latch remains 5, as in CAP;
these INs are actual external input even when the parked original client
has an effective automatic mode. No original waiting packet is rewritten.

At InnerReturn a producer CTL selects identity public-word permutation,
Tail(13), Tail(17) and a CTL select CaptureCAP. The same normalization is
used after initial acquisition, before activation. All public work words
and scratch latches are dead at these normalized entries; their actual
bytes are retained. CAP's directory, counters, source, journals, descriptor
streams and source-token/producer-workspace ownership have their complete
boundary invariants. Only a later explicit loan enters $r$.

This is the normalized parked-client domain. It does not assert that an
auxiliary source call preserves arbitrary live public arithmetic words
at an internal automatic-maintenance return. In that different situation
history work on fresh ports preserves them, but a raw CAP call may reuse
them. Here the actual finite joins establish the needed entry instead of
postulating an arbitrary continuation-restoration operation.

**Definition 4.2 (finite boot extension).** Construct ten additional ordinary
L/R pairs and their heads, and install their finite $A$ owner bits and the
history phase/token slots, by Assumption 1.2's paid boot variants. Original
preparation and acquisition remain the single original ones, with their
new run's actual origins and absolute ordinals. At the fixed normalized
acquisition return take one boot-authorized CTL into the two fresh-version
bootstrap mechanism of RCA Definition 14.1. Its permission is for exactly
the following fixed capture graph $L$ and graph $G$, not an arbitrary
loader and not a new entry into a closed legacy graph.

$L$ is RCA's native capture-only graph relocated to scratch 66–67,
descriptors 68 and capture 69. Omit its eight old-verifier TOKs: these new
ports already belong to $A$. It appends the unique initial F on 69,
then acquires $101\,U(\delta)\,\Delta(G)$ with $\delta=|\Delta(G)|$
by RCA Definition 13.2's native bit ingress, measured length, descriptor
and seal, with no Import or word assignment. Its first descriptor on 68
has ordinal zero and actual base one. Its finite return CTL enters the
second bootstrap. $L$ contains no description or length constant for $G$.

Each bootstrap has NEXT testing its fixed version's control-store end,
INPUT, one-bit WRITE, ADVANCE, and DONE. A version with $e$ installed bits
therefore uses $4e+2$ rows. Raw partial bits and inactive old versions
remain stored. DONE alone enables a completely installed table. Actual
canonical supply consists of $E(L)$, the stated capture frame, and $E(G)$.
$E$ is the literal installation serialization; $\Delta$ is the framed
row/effect/entry description of RCA Definition 12.2. Its finite serializer
removes framing and emits the same row/effect bits in installation order.
The two strings are not identified.

**Definition 4.3 (initialization order).** On entry to $G$, append bank
sentinels and construct the empty active bank by Definition 2.3. Append
one F sentinel to each of 70–73. Do not append a second initial F to 69.
Before any later channel staging, append the following binary fields to
69 in this fixed order, each with measured Base, length, actual descriptor,
F and seal:

1. After the existing code field zero, the actual public initialization,
   mode, $H_0,\xi$, prior, controller table/initial-data bindings and the
   acquired boot binding.
2. The finite descriptions of the earlier original graph, its boot and
   the capture graph $L$, emitted by literal paid Appends.
3. The actual acquired seed syntax and its actual delivery/local origin.
4. The closed acquired 28/29 import, with the actual pre-activation
   input/request dependencies in their prescribed chronological order.
5. The saved-head table for 26/28/29 and the fixed activation-position
   description: the first normalized return after acquisition, with no
   independent late-position choice.

Variable material is obtained by Definitions 3.1–3.5 from actual owned
backing, then exported by Definition 2.2. In particular the boot binding,
source identity and seed delivery resolve through their actual local
references; their remote names alone do not supply these words. The
original controller table, finite initial configuration, public prior
program and original boot description are fixed parameters of this
apparatus. Their canonical literal words are also emitted bit by bit in
this field, just as the fixed old graph/$L$ descriptions are. Canonical
original supply requires those same words at their original paid IN
sites; they are not new source-dependent advice or an unacquired variable
table. A different public controller or prior program chooses a different
fixed apparatus, whereas every future capacity is still runtime input.
Neither earlier graph contains $G$. Actual public variable data are
acquired data, not substituted compiler literals.
Imports restore 26/28/29 before proceeding. All the initial field exports
are complete before ManifestPrefix is entered.

ManifestPrefix is RCA Definition 13.2's full-prefix graph with port
37 replaced by 69: Home; MR; MR, then BeginField/FieldRead, literal
bit cons, Reverse, AppendItem, delimiter MR, and finally the manifest
copy. It imports every field, including empty fields; it omits only the
initial sentinel. Field zero must parse as $101U(\delta)\Delta(G)$ with
exhaustion, and its description must pass row/effect/entry validation.
Only then initialize completed cycles $M$, covers and packages and their
cursors. Hand the history invocation slot to the outer client by TOK,
then execute its Ready CTL. This is the first $R_r$.

The importer used to prepare these fields already has an empty initialized
bank. ManifestPrefix's later register initialization does not erase its
source fields or require an uninitialized compiler. Initial saved distances
are bank words from Definition 3.1, and the copied CAP reference fields are
bank words from Definition 3.3. They can be exported directly in the
prescribed field; no extra top-level staging field is inserted into this
initial prefix. After ManifestPrefix, native metadata on 66/67 that must
enter a bank is first staged on 69 by RCA Definition 13.2's Stage34/Stage35
relocation, then imported there. No bank assignment reads its own native
scratch through a head that its rebuild will move.

**Proposition 4.4 (actual initialized lineage).** Under canonical finite
supply, Definitions 4.1–4.3 reach $R_r$ finitely, with an actual acquired
manifest, correct $E/\Delta$ lineage and initialized owned compiler.
The parked 24–27 data/heads and original source/consumer ownership are
preserved. No self-description constant or old-verifier loan is needed.

Proof. CAP's complete acquisition return supplies the original data and
permissions before activation. The ten new boundary pairs and all control
bits are finite paid boot constructions. The first bootstrap installs $L$
before its first row; its native capture does not call a word routine.
Its actual Base is one after its single F sentinel, and its first descriptor
is zero by the empty descriptor-prefix count. The second bootstrap installs
the serialization of that same captured description, by the canonical
supply premise. Retaining $E$ separately from $\Delta$ gives the exact
raw partial-installation states rather than treating a partly installed
table as the active table.

Definition 2.3 now gives an active bank without a word assignment.
Propositions 3.2 and 3.5 give the finite actual asset imports and head
restorations. Export never aliases its source. The closed initial 69
prefix consequently has precisely RCA Lemma 13.2a's shape. Its two
entrance moves cross L and the one initial sentinel; its field-zero
parser reaches the actual code bits, not an empty field caused by a
second sentinel. That lemma and RCA Proposition 11.4 give actual manifest
fields and actual resulting bank/parity. All staging begins after that
scan, so it cannot lengthen the import boundary. The token and Ready
rows establish the declared live entry. No step touches 24, 25 or 27,
original private source, verifier or consumer work; the owned seed read
on 26 restores its head and changes no cell. Descriptions of the earlier
finite graphs may be emitted in $G$; its own description is read only
from the actually acquired capture. This avoids a description fixed point. ∎

## 5. Outer choice, auxiliary source call and completed-cycle capture

**Definition 5.1 (the outer entry relation).** At $R_r$ the following relation
holds. The producer has the twelve original word tokens, identity role
permutation, original source/directory/journal/counter tokens, and heads
13 and 17 at R. The source-service token is at its dispatcher. All previous
CAP row/dependency checks and ACKs are complete. The original client is
still parked at $r$ on 24–27. No public work word, shared latch or native
stack slot carries a value needed by $r$. Before entering it, its actual
loan/positioning code will establish its own inputs.

The history banks have a complete active parity and immutable completed
lists. Their persistent values include manifest, $M$, covers, packages and
any fixed current selector/callback bindings. Temporary word registers
are dead unless explicitly named by the current stage. All new ports
have $A$ ownership; the invocation slot is at the outer client and mailbox
availability is idle. Old 26/28/29 heads are at their actual CAP return
positions. Meter/readout heads remain their actual new-run positions;
no service uses a live scan to the moving meter end.

**Definition 5.2 (literal outer receiver).** At $R_r$, Tail(66); Base(70)
records the choice base before any IN. Execute
IN(6); EX(70); WR(70,6); MR(70).
Testing CTL on the unchanged ingress latch selects 1 immediately, or
on 0 executes a second identical four-row reception and its finite test.
Thus the prefix-free choices are 00, 01 and 1. No compiler assignment
occurs between these bit receptions and their finite tests.

Append F and seal the choice block. Construct its literal length $U(2)$
for 00/01 or $U(1)$ for 1 on 67, with sep/seal. Count preceding descriptors
and write the complete 68 descriptor, using the saved measured base and
actual creation count as in RCA's native ingress recipe. Import this
sealed block from 70, retaining its value in the bank; no choice exists
only as an unstored branch latch.

| Acquired choice | Actual successor |
| --- | --- |
| 00 | TOK handoff to the original-client loan prelude; twelve old workspace TOKs and CTL enter the already initialized $r$. |
| 01 | CTL enters $F^A$ at its original header Base/setup prelude, before any header IN. Its own source-token admission is unchanged. |
| 1 | TOK from outer-client invocation slot to history handler; reserve CTL; acquire one history frame on 70. |

For 00, finite new-role setup finishes before the old workspace loan. No
new helper starts during a partial twelve-token transfer. The terminal
client route has no interception at global halt. For 01, all seven old
canonical tags retain their exact CAP branch, guard, actual raw ingress,
row/dependency/channel/ACK and fault behavior. The finite inner return
is InnerReturn; the outer return remains $r$. These are different static
labels, not a variable return-address word.

**Definition 5.3 (history receiver and invalid domain).** After choice 1,
acquire a three-bit tag, unary length and length-bounded payload on 70
by RCA Definition 13.2's literal native ingress, with scratch 66/67 and
descriptors 68. Header bits have IN/EX/WR/MR; unary length bits additionally
have their distinct RD test; payload bits have the tested six-row append
ingress. Following F, seal, measured whole-frame length and descriptor
construction, import the frame by actual RD/cons/MR/Reverse.
The canonical request is

$$
111\;U(|U(m)U(z)U(s)|)\;U(m)U(z)U(s).
$$

The payload contains exactly three unary fields and no suffix. Other
complete tags/payloads take paid MalformedRecovery or range/occurrence
rejection, with full publication, ACK and the same return. They never
become source replies. A raw unterminated length remains in ingress.
Every supplied raw bit at an enabled IN executes its latch/control/receipt
successor, whether or not it preserves canonical extendibility. Source
frame-fault is CAP's actual retained raw branch. A missing token, busy
second entry or premature unsealed read has no executed edge or receipt.
Invalid private preparation and intermediate invalid source overwrite
packets likewise remain the original raw states. Wrong bootstrap supply
has its actual partial-store successor; it is outside the canonical-version
premise, not silently replaced by the prescribed bit or an initialized bank.
The carrier retains such states without a successful-recovery assertion.
More generally its raw control-store coordinate admits every finite supplied
bit pattern. After a raw DONE, main-row enabledness uses its actually
decoded row and finite local effect: absent, duplicate or out-of-range row
fields give no enabled main row. The preceding IN/WRITE/DONE occurrences
remain executed history. A uniquely well-typed row has the primitive
successor of that actual table, subject to its actual tokens and boundaries.
No canonical table is substituted for a malformed one. The positive graph
and code-lineage assertions concern the canonical-version subdomain only;
raw data and raw later continuations are not collapsed to a success or
silently removed from the carrier.

**Definition 5.4 (CaptureCAP and $M$).** After a completed 01 call and its
InnerReturn normalization, import closed 28/29. Resolve its newly delivered
unified row and all dependencies by §3. Append a complete cycle item to
$M$ containing the acquired choice 01, actual header/length/payload input
bits in IN-site order, row occurrence and origins, and their actual
acquired dependencies. Restore 28/29 heads. A CTL selects the same outer
$R_r$. No old word pool is borrowed by CaptureCAP.

$M$ is an encoded list of completed cycles, not an independent semantic
execution log. A history cycle item retains choice 1, its actual supplied
frame, typed outcome and received-reference bindings. Append it only after
its full final ACK. Internal callbacks and computed output are not external
IN. The initial pre-activation prefix has its fixed manifest field. Choice
00 and its unfinished/terminal suffix remain actual retained 70/old-port
material, even though no completed-cycle item is appended if there is no
new Ready. A cover freezes the predecessor $M$ and $R_r$, before the
current choice's Base/IN work; its current physical request stays retained
on 70 but outside that frozen predecessor.

**Proposition 5.5 (literal entry and return).** At every reached $R_r$, a
completed canonical 01 call has a finite paid return to the same relation
with the actual new source state and longer $M$. History entry has the
stated actual retained selector and invocation token. Choice 00 reaches
the unchanged original client entry with its required actual workspace
loan. All partial token, input, parser and callback phases remain distinct.

Proof. The choice receiver preserves latch 6 until its write/test and
constructs its physical descriptor before bank work reuses scratch.
Its prefix cases consume exactly one or two input bits, so none is
silently taken as a frame header. On 01, the source-token preconditions
are those of CAP Definition 4.6. CAP Lemma 6.7 gives complete finite
recording, mandatory acquisition, final row ACK, source TOK and idle CTL.
The inlining changes only that final successor. No compiler assignment
occurs inside $F^A$, so its history-bank parity is retained in a finite
product of the source control with the two possible parities. Its
normalization sets the public role permutation and pays both Tail scans.
The original source/counter/directory changes are genuine operations;
no old current-state snapshot is restored over them. Proposition 3.5
then gives the exact new cycle item and restored archive heads.

The parked 24–27 heads/bytes and all old handle meanings survive by CAP's
maintenance/source boundary discipline. Public scratch need not equal
its earlier bytes; none is live for the parked entry. On 00 the twelve
actual TOKs and final CTL establish CAP Definition 8.1's actor entry;
its table execution positions and constructs its own state/packet work.
Thus the entry follows from the explicit parked-client construction,
not an assertion that an arbitrary raw call preserves a suspended
arithmetic computation. On 1 the actual TOK and native ingress establish
both present invocation authority and retained selector material. Every
interior state has its installed next row; no partial seal or loan grants
another entry. ∎

## 6. Typed reservoirs and literal Step on the entire carrier

**Definition 6.1 (input-site partition).** The replay reservoir has the
following disjoint site kinds, selected by represented version, PC and
call site, not by equality of bit strings.

| IN kind | Actual acquired or fixed canonical backing |
| --- | --- |
| Original public boot | Actual initialization/prior/controller material and bindings in the manifest. |
| Original private preparation | Canonical padded packet reconstructed from the actual acquired initial syntax and $H_0$. |
| First/second fresh bootstrap | Prescribed $E(L)$, and serialization $E(G)$ of the actual captured $\Delta(G)$. |
| Capture-controller ingress | Actual captured $101U(\delta)\Delta(G)$ field. |
| Outer gate | Its completed-cycle choice, with a second bit only after first bit 0. |
| Auxiliary raw CAP | The actual three-block wire frame acquired and resolved for that 01 cycle. |
| History request | Its actual complete 70 frame for that history cycle. |
| Original computed command/callback | No IN; replay executes its literal Append/copy/RD rows. |

Seed conversion scans the actual prefix syntax: branch 0 emits private
token 11; leaf 11 emits 01; leaf 10 emits 10. An open-slot unary word
starts at 1; branch replaces one slot by two and a leaf removes one.
At slot zero require syntax exhaustion; pad by 00 to $2H_0-1$ tokens.
The count $2H_0-1$ is constructed by two unary copies and one tail.
This is RCA Definition 13.1's finite converter to CAP's original packet,
not the noncomputable `NativeEffectiveSourceProducer.sourceDecoder` and
not an identification of two different source codecs.

For covers, all variable reservoirs are obtained from the fixed manifest
and frozen completed-cycle list. For a general raw finite prefix, the
model additionally contains its actually consumed current input and
occupied IN-to-WR latch; this is not asserted to be already available to
a cover that precedes that input. Source-raw, gate, selector, bootstrap and
capture inputs all retain their types. No invocation or schedule choice
other than those installed sites is inferred from primitive time.

**Definition 6.2 (Step74).** Use RCA Definitions 12.2–12.4's complete
physical-state codec, but with 74 port-list entries and the finite token,
control-version, phase and entry slots of $G$. Cell identity is the port
and its actual creation-chain position. Lookup traverses the full framed
row list, decodes its seven unary fields and finite effects, and requires
one matching state. Validate port range 0–73, latch range 0–7, symbol
range, Boolean-table range, unique state numbers, successors and finite
entry/effect fields. Mark lookup, Nth, Replace and AppendItem are the
literal word expansions of §2.

| Native row | Represented effect before its receipt |
| --- | --- |
| RD | Select the actual marked cell, copy its symbol to the designated latch, and take the row's actual test branch. |
| WR | Check represented writer/writability, then change that one symbol using its literal/latched variant. |
| ML/MR | Check the existing adjacent cell and represented token, clear/set the same head track on the two cells. |
| EX | At ordinary R replace it by blank retaining its head, append a new unmarked R, preserve creation identity of the old cell. |
| BF | Select its literal eight-bit table entry from represented operand subfields and replace result subfield 3. |
| IN | Pop from the site kind of Definition 6.1 and change only its represented ingress latch. |
| OUT | Append the represented actual output bit to the event; perform no live OUT from that bit. |
| TOK | Check and update precisely its finite named port/phase availability slots. |
| CTL | Apply its finite list of purpose/phase/parity, seal, bootstrap entry/advance/DONE, commitment or halt effects, then its prescribed successor. |
| Boot boundary/control-bit variant | Construct one designated boundary cell or write one prescribed finite control bit and update its finite bootstrap cursor. |

There is no effect constructor for a whole string assignment, counter
increment, M append, source change, Cover or Call. Those are native rows
of their expanded graphs. New phase effects name only a fixed finite
slot and literal finite value. The initial finite ownership/token words
are installed bit by bit. Concretely, a finite effect is a list of the
following constructors in its written order: preserve; set one named
finite bit to literal 0/1 or a designated latch bit; set the seal/mark bit
at a named port's current or immediately preceding existing marker; select
one named bootstrap/version/stage; advance one slot of that version's
fixed finite cursor; select halt; select the F receipt. A phase name,
parity, role permutation or fixed return label has its finite bit encoding;
setting it expands to that fixed finite list. A TOK has named source and
destination slots, guard source=1/destination=0, then their two literal
bit updates. A public CTL test is equality of its designated latch with
its literal symbol, as in PR57.03. Commitment changes only the declared
finite phase/availability bits; its semantic event interpretation reads
the already constructed packet and counter versions. There is no finite
effect whose argument is a runtime list, address, code word or natural.
Current raw code bits and last completed active code are separate
coordinates; bootstrap rows stay active until DONE.

The common receipt stage appends exactly its ordinary/F receipt on the
represented meter, preserving the core row's newly updated meter read
mark. Append one unary tally mark and one complete event, including
actual operand identities and read/written/supplied/emitted symbol.
Tick and fee wire words are built by unary copy/doubling. The acquisition
annotation copies its actual tally. Completed-cycle annotations are at
outer Ready after actual M append/token return, not source ACK or an
internal callback. These annotations update simulator bookkeeping by
word instructions; they are not extra coordinates of the old physical
state. The physical projection contains only its actual cells, control
stores, PC, heads, latches and tokens.

**Proposition 6.3 (the added-row correspondence).** Starting from the encoded
actual pre-row state of this 74-role instance and its authentic input,
Step74 has a finite word expansion and returns exactly its complete actual
successor/event/receipt. It includes new bootstrap, gate, importer,
callback and return rows as well as every original CAP row and invalid
source overwrite phase.

Proof. RCA Proposition 12.5 supplies the ten local opcode cases and the
meter overlap rule. Here its finite port alternatives are explicitly
extended to 74, and token/control effects are the finite table of
Definition 6.2; no old 64-port theorem is applied without this change.
For each newly added row, RD still selects the same marked symbol,
WR/EX/ML/MR have those same local cell effects, and its finite CTL/TOK
field selects exactly its installed phase/slot. Ingress classification
uses the actual inlined call site. In particular an auxiliary 13 IN is
not erased because an original automatic command with equal bytes
would be computed. Outer second-bit IN exists only in the first-0
branch; callback imports are RD, not IN. Bootstrap supply uses the
captured description's serialization, while its raw store remains
partially written until DONE. These checks cover every new row kind.

All list and field operations have finite source words, and each table
case uses only earlier terminating macros. No Step case recursively
executes a semantic recovery request. Represented code may itself be
executing an earlier Step, but its next transition is still one literal
native row. The copied actual row input ensures that an IN-before-WR
cut has the changed latch with the still-old destination, and EX-before-WR
has its actual blank cell. This gives correspondence at every interior
cut, rather than just word or service boundaries. Historical tokens
remain encoded data throughout. ∎

**Definition 6.4 (closed Boundary74 and Prefix74).** Boundary74 starts at
the canonical irreducible entrance, constructs the original private packet
by Definition 6.1, and executes Step74. Its stopping test is the conjunction:
activation complete; completed-cycle count equal to the actual cardinality
of frozen $M$; PC equal to its particular outer $R_r$. It returns the
acquisition tally $a$ and that boundary tally $b$. It does not stop merely
on input exhaustion, a source ACK, a callback or a pre-activation Ready.
Prefix74 copies a constructed internal natural $k$ into a countdown,
executes one Step74 and tails that countdown per iteration, and stops
before the next row when it is empty. It returns the exact consumed
variable-input prefix $I_k$, native history and physical-state tuple.

**Proposition 6.5 (earlier recovery is counted literally).** For a frozen
completed predecessor at a reached $R_r$, Boundary74 returns its actual
absolute $a,b$ finitely. Prefix74 at $a\le k\le b$ returns that run's
exact length-$k$ prefix and raw endpoint. These assertions include every
earlier recovery's native rows and cells, and any finite number of earlier
such cycles.

Proof. Induct on the completed-cycle list. Proposition 4.4 supplies the
base initialized Ready, including its entire boot/capture/import prefix.
For an added source cycle, Proposition 5.5 and CAP Lemma 6.7 give a finite
actual fragment. For a history cycle, its frozen predecessor is shorter
than the current cycle list. Its Boundary/Prefix operations therefore
refer to already finite actual prefixes, and Proposition 6.3 simulates
each of their native rows finitely. The remaining parsing/publication
and return operations in §§7–8 have fixed finite inputs and closed ends.
This is simultaneous induction with their finite-completion assertion:
the zero-cycle case contains no history call; at the induction step all
historical operands refer to earlier completed boundaries or cuts thereof.

The conjunction in Boundary is false at every earlier Ready with fewer
completed cycles and before activation. At the intended Ready it is true.
Following its finite actual prefix with Proposition 6.3 proves termination
and the tally value. Prefix has exactly $k$ countdown marks and hence
exactly $k$ finite Step executions. Determinism gives the actual input
prefix, including a last acquired but unwritten bit when present. A later
reservoir suffix has no influence before a further IN. This is RCA
Lemma 15.1's argument applied through the newly supplied CAP/74-role
input and entry joins. It does not replace an earlier history service
by its semantic answer or omit its compiler/receipt work. ∎

## 7. Actual receiver callbacks and immutable Issue/Call

**Definition 7.1 (positioned publication).** Publish serializes its tagged
result with Frame/Cat, exports it to a new immutable sender block on 71,
then executes RCA Definitions 13.2 and 13.4's native three-placement-record
channel with sender 71, mailbox 72 and receiver 73. Scratch/descriptors/
staging are respectively 66–67/68/69. Measure each actual Base, allocate
and initialize its complete length and single F delimiter, prepare its
full descriptor, and stage the complete sender, mailbox and receiver
placement records in that order. Immediately after a descriptor is
created, copy it to its own measured/sealed staging block. Measuring
that stage uses a dry descriptor-bit count, without changing the source
descriptor. Count and write the staging block's own descriptor only
once its payload is complete. No recursive staging of that descriptor
occurs. Here the delimiter constructor selects the literal F variant
of Append; its one delimiter is included once in allocation. This is the
new channel's grammar, not a reinterpretation of CAP's sep/status blocks.

Every result tuple has a common framed prefix containing the active
service/capture binding and $\xi$; the table below displays its remaining
kind-specific fields. Bindings are complete encoded reference tuples
resolved against owned backing, not opaque names granting permission.
For these new tuples use Definition 2.1's list-of-Frames codec. In order
its fields are the four-bit kind, the service binding, $\xi$, then the
displayed kind-specific fields. The service binding is the fixed-arity
tuple of original/capture/current version tags, the actual code-capture
placement and captured field zero, and the initial seed's complete delivery
reference. Its captured bits and seed reference are imported manifest
fields. The capture placement is the native tuple
$(A,69,1,2\delta+4,0)$: owner, port, base, length, zero-based descriptor
ordinal. Construct it by literal cons, unary copies and Cat from field
zero's parsed $\delta$; Proposition 4.4 identifies these constructed values
with the actual already sealed capture interval and descriptor. It is
not a freely supplied pointer. The kind tags
are CoverRef=0000, PackageRef=0001, Image=0010 and Rejection=0011.
Their remaining arities are respectively three $(c,a,b)$, four
$(p,c,k,\varrho)$, five $(p,c,k,\varrho,\text{image})$, and two
$(\text{reason},\text{raw request})$. Numeric fields use wire $U$;
the raw request is the actually imported whole history frame. Reasons
are the fixed four-bit tags, in order: malformed frame 0000, descriptor
failure 0001, unavailable dependency 0010, no occurrence 0011, invalid
phase 0100, no cover 0101, no package 0110, description failure 0111,
binding/range failure 1000. Thus finite rejection also has a unique
wire serialization rather than an unspecified output symbol.

The latest-three staging invariant holds throughout the native channel.
Recover sender length from its staged record before each allocation and
copy; do not reuse a staging-wire length as a payload length. Recover
both endpoint bases from those actual records and Seek the endpoints.
Perform the two six-row length-tested payload loops, with distinct data
and test latches, final seals and TOKs. Append their immutable completion
records on 71, not 69, so those three placement records remain selected.
The mailbox's availability token is separately acquired and returned.

After receiver completion, recover its actual base and sender's length
from the same staged records, reposition them and execute the mandatory
print loop: RD(length,5); on 1 RD(73,4), OUT(4), MR(73), MR(length),
repeat; terminal RD(0) exits. ACK is a further actual TOK. Receiver
payload, sender and mailbox intervals remain distinct and retained.
Live phase tokens and the reached seal invariant authorize the client
read; old permission fields printed in an Image do not do so.

**Definition 7.2 (received-reference importer).** At the fixed callback,
use the still-latest receiver placement record on 69 to obtain its actual
base by native unary copies and Seek(73), before any word assignment.
At its first bit, run the native binary field importer on 73 until its
already constructed F delimiter, then Reverse. Its word assignments touch
64–68 and preserve head 73. It is not bounded by length scratch 67 while
those assignments are rebuilding that same scratch. Parse the received
result tuple and require exact kind and source/version/cover binding.
Its immutable payload and current read authority follow from the actual
channel completion. After this importer, descriptor/staging recency is
not assumed to remain what it was before bank work.

**Definition 7.3 (the finite three-stage client).** The following entries
are distinct installed labels. They have a finite product with bank parity;
they create no native return stack. Manifest, frozen $M$, selector,
cover/package lists and the stated bindings are persistent bank fields.
Serialization and export copy unchanged persistent fields through every
bank assignment. After those operations the native channel/print sequence
contains no word assignment and preserves the active bank parity. Word
assignments at callbacks likewise copy unchanged persistent fields.

| Entry | Actual work, live fields and successor |
| --- | --- |
| Recover | Retain the acquired selector; freeze predecessor $M$. Run Boundary74; construct the actual list-cardinality ID $c$ and append immutable cover record $(c,\text{manifest},M,a,b)$ on 71 and in the bank. Publish CoverRef$(c,a,b)$; full receiver print/check/ACK; TOK handler slot to client; CTL to ClientCover. |
| ClientCover | Clear the internal cover-number temporary. Import and parse the actual received CoverRef by Definition 7.2; retain acquired $c$ and its binding. TOK client slot to binding handler; CTL to Bind. |
| Bind | Resolve $c$ by its immutable list/backing, parse the retained selector, and perform §8's actual occurrence/ordinal computation. Require $a\le k\le b$. Run Issue$(c,k)$ below; Publish PackageRef$(p,c,k,\varrho)$; print/check/ACK; TOK handler to client; CTL to ClientIssue. |
| ClientIssue | Clear the internal package-number temporary. Import the actual sealed PackageRef, check $\xi,c,k,\varrho$ and current invocation slot. Retain this acquired $p$. TOK client to Call handler; CTL to Call. |
| Call | Resolve that immutable $p$, run Prefix74 on its own copied manifest/$I_k$/$k$, serialize its exact raw HistoricalImage on 71, and Publish Image$(p,c,k,\varrho,\text{image})$ through receiver seal/print; TOK handler slot to client and CTL to ClientImage. |
| ClientImage | After print, import/check the received finite codec and all binding fields, ACK, return mailbox availability, append the complete history cycle to $M$, TOK invocation slot to outer client, CTL Ready with successor $R_r$. |

Cover and Package publication perform their channel completion check,
ACK and mailbox-availability return before the fixed reference callback;
the sealed receiver read token remains retained. Image publication hands
the invocation slot to ClientImage after receiver completion/print; that
client checks before its ACK and mailbox return. No handler entry is
enabled during either check. A subsequent Bind or Call stage obtains its
live invocation slot only after the preceding receiver completion/ACK. No external copying of $c$ or $p$ is requested.
The same principal owns all these backing intervals; knowing a numeral
without the phase token still provides no entry. Unknown cover/package
with its token yields paid NoCover/NoPackage and a full rejection return;
without the token there is no executed successor. Finite tuple/description
parse failure likewise takes a typed rejection route, not an inferred
original source answer.
At every such reached failure retain its literal reason and actual raw
request. From ClientCover or ClientIssue first TOK its invocation slot
back to the handler; their preceding channel ACK has already returned
mailbox availability. From a handler failure that slot is already held.
Publish Rejection through the same initialized channel and print,
then TOK the handler invocation slot to ClientImage and take that fixed
label's rejection branch. It imports/checks the Rejection fields against
the retained reason/request, then executes its same ACK, mailbox return,
completed-cycle append, invocation return and Ready rows. The Image branch
instead checks its image codec and $p,c,k,\varrho$. This finite type test
adds no callback or external choice. The first detecting parser failure
selects the reason; checks are performed in their written order.
An unexpected ClientImage binding/codec failure takes a distinct finite
refusal branch: retain the literal binding-failure reason, append its
tagged fault record on 71, perform this channel's ACK/mailbox return,
and append the failed cycle before invocation/Ready return. It does not
claim successful recovery or attempt a new mailbox setup while this
one is busy. On an authentic publication the channel equality and tuple
writer make that branch unreachable, for both Image and Rejection.

Issue runs Prefix74 on its immutable cover at $k$, obtains exactly $I_k$,
and copies manifest, code lineage, $\xi,c,k,\varrho,z,s,I_k$ into a new
sealed package on 71 and its bank list. Its creation number is the actual
list cardinality word. The package never points to latest cover or
current capacity. Call's HistoricalImage is RCA Definition 12.2's full
raw physical/history codec with 74 ports and the target's actual active
version/partial-installation tag. Simulator bookkeeping is separate from
that physical projection. Serializer work and its new bank/archive cells
are actual later work, outside the selected older endpoint.

**Proposition 7.4 (acquired references, paid call and full return).** On an
authentic successful Recover flight, Bind uses an actually receiver-acquired
$c$, and Call uses an actually receiver-acquired $p$ with present invocation
authority. The received Image is exactly its immutable selected old prefix
and endpoint. Full ACK and Ready return preserve the parked original client,
current source, $h,K$ and every old acquired handle; 26/28/29 heads are
restored. The history banks and new-role heads have their actual resulting
values, and the meter has all additional receipts.

Proof. At each publication the exact staged bases and actual length
satisfy RCA's initialized two-copy relation. Its induction on payload
positions gives equal sender/mailbox/receiver bits; the final seal/TOK
provides the actual read token before the client callback. Native Seek
positions receiver 73 using the complete local placement record. Its
F-bounded importer cannot lose this source position during bank rebuilds.
Clearing the internal numeral before parsing ensures that the next
stage's numeral is the one actually read from received backing.
The parsed binding is the serialized immutable cover/package binding,
and the explicit TOK establishes the next invocation slot. Neither an
unacquired producer reference nor a historical permission bit enters
this implication.

Issue and Call use the same fixed $k$ and copied $I_k$. Proposition 6.5
gives the exact raw endpoint/history, even if the last selected event
is IN or EX. Prefix never reads a live private port: its represented
private cells come from acquired initial data and literal simulation.
The three outputs all undergo actual serialization, setup, copies,
printing, checking and ACK. The final $M$ append occurs only after the
Image's complete client check; the final token and Ready CTL are actual
rows. New routines access only their ten owned ports and the closed owned
imports. The latter restore heads by Proposition 3.2. They do not touch
24–27, source/private producer material or the original verifier/consumer.
Thus $R_r$ is reestablished with longer history, not by rolling back any
actual cost or source evolution. ∎

## 8. Binding an actual Reserve occurrence and its five-phase family

**Definition 8.1 (occurrence).** In the cover's decoded acquired CAP chain,
$m$ means the old all-event ordinal in SEG-U1, starting at zero. It is
neither semantic $j$, source $q$, descriptor $c$, nor primitive time.
Require its unique row to have kind Reserve, outcome ok and old/current
$J>K$. Resolve its complete request-reference tuple and actual unified-row
origin. Set

$$
\varrho=(\xi,m,\text{unified-row origin},\text{complete request origins}).
$$

Check its before/after $K$, layout ordinal, manifest extension and
$d=4(J-K)>0$ by the finite tuple/unary operations of §3. The request's
$U(J)$ must be exactly the actual acquired payload. Equal frame bytes at
a later occurrence have another $m$ and origin. Unknown $m$, an unchanged
or refused Reserve, another kind, or an unresolved acquired dependency
returns paid NoOccurrence with complete rejection publication/ACK/return.

**Definition 8.2 (paid entry recognizer).** From the canonical entrance,
execute Step74 with that cover's reservoir, maintaining its unary tally.
Recognize the unique source Zero entry of this $\varrho$ by the following
conjunction on represented actual fields:

1. PC is the specific Reserve-greater Zero(16) test label in $F^A$,
   after its Last(bound) and Tail(16).
2. The represented old unified count is $m$ and the represented producer
   request has exactly the complete original references later acquired in
   $\varrho$, with payload $U(J)$. Its producer-local descriptors already
   exist here; no future actor delivery is required at this represented cut.
3. Read the represented actual bound at its marked cursor, decode $U(d)$,
   and compare with the independently computed $4(J-K)$.

These are Nth/marked-cell scans, block extraction, Frame/unary parsing and
Equal on the encoded state. Save the actual tally as $n_0$. Compiler,
mailbox, receiver and ingress zero-fill labels have different PCs. Only
this source call site can satisfy item 1. No physical source head is read
by the historical actor, and no fence ordinal is substituted for $n_0$.
For an initial fixed original-controller call site added to this same
wrapper, its separately numbered Reserve label and installed call kind
would require their own finite recognition case; the present family uses
$F^A$ throughout.

**Definition 8.3 (five-phase selection).** Require $0\le z\le d$ and
$s\in\{0,1,2,3,4\}$. Construct five actual word copies of $1^z$, concatenate
them to a copy of $1^{n_0}$, then concatenate the literal unary natural
$s$. Append its wire zero to obtain the actual $U(k)$ for

$$
k=n_0+5z+s.
$$

For $z<d$ the five cuts are respectively before bound RD, after that RD,
after source EX and before WR(0), after WR and before source MR, and
after source MR and before bound MR. For $z=d$ they are before terminal
RD(0), after it and before delimiter EX, after delimiter EX and before
WR(sep), after WR and before MR, and after that delimiter MR. The last
cut is the Zero return, before the subsequent reservation-field work.

**Proposition 8.4 (uniform exact binding).** Every valid acquired selector
in Definition 8.3 names exactly one of all $5d+5$ cuts of this actual
$5d+4$-row Zero fragment. Definition 8.2 finds $n_0$ by finite paid work,
and Issue/Call recovers that exact cut, including a blank-after-EX target.
All these cuts satisfy $a\le k<b$ for the later completed-cycle cover.
This selector alone asserts no coverage of the other Reserve phases.

Proof. CAP Definition 5.1 computes $d=4(J-K)$ in the strict branch and
calls exactly one source Zero at this site. CAP's complete unified chain
has unique old ordinal $m$, and its acquired dependency/origin checks
identify exactly that request. Thus the actual finite prefix contains
one matching Zero entrance. Step74 reproduces its actual PC, bound cursor
and request fields; its tally counts every preceding row, including
initialization, import, prior recovery and native receiver callbacks.
Following that finite prefix terminates at its matching entrance with
precisely $n_0$ marks. The independently checked $d$ is its actual bound,
not a desired allocation size assumed in advance.

For each positive iteration the literal rows are bound RD, EX(16),
WR(16,0), MR(16), MR(bound). At $z=d$ only RD(0), delimiter EX, WR(sep),
MR follow. Hence the five listed offsets for each $z$ are consecutive
and disjoint, their union being exactly $0,\ldots,5d+4$. There are
$5d+5$ of them. At $s=2$ the applicable EX has retained its new blank
and WR has not occurred; at $s=3$ that blank has become 0 or sep.
The whole packet need not be interpreted as a valid tree at any raw
busy cut. Paid unary copies/Cats produce precisely the stated ordinal.

The stationary acquisition precedes this auxiliary call. The source
Zero fragment precedes reservation publication, response/rows, mandatory
copies, ACK, inner normalization and CaptureCAP, all before the later
outer $b$. Its final delimiter MR is therefore also strictly earlier
than $b$. Proposition 6.5 supplies Prefix74 at each of these targets;
Proposition 7.4 supplies actual issued backing, acquired $p$, Call,
output, ACK and return. The selector contains the actual supplied $z,s$,
so a common archive is not being asked to infer an uncommunicated
intention. CAP Theorems 13.2–13.6 remain the supplied checkpoint
selection lower bounds; this result adds the actual phase acquisition,
occurrence recognition and complete returning paid route. ∎

## 9. One fixed beta boot with arbitrary finite future Reserve values

**Definition 9.1 (the fixed INITIAL-Stop client).** Set $H_0=h=K=1$,
$u=\beta$, with actual finite preparation $\xi$ and prior
$D=\mathcal T_1=\{\alpha,\beta\}$. The original finite client table's
next instruction is Stop with the original proposal
$\tau=q_1(\beta)=(0,B,1)$. Its actual finite output material, initial
configuration and table are written once by CAP Definitions 2.4 and 8.1.
Acquire the initial beta by the original stationary producer and park
this client at its initial table entry as in §4. The original seed
acquisition's own Stop returns to the surrounding dispatcher; it is not
the global Stop of this parked client.

Install the fixed $L,G$ and owner/role assignment above. Its constants
contain neither a future $J$ nor a future list length. History requests,
auxiliary source frames and gate choices are actual runtime inputs.
The original client has no history-opcode knowledge and receives no
future-capacity advice.

**Theorem 9.2 (one-boot uniform returning recovery).** For the one fixed
initialization of Definition 9.1 and every finite strictly increasing
list $1<J_1<\cdots<J_t$, actually supply choice 01 and CAP's canonical
Reserve$(J_i)$ frame for each $i$. Between these calls insert any finite
number of canonical recovery requests for completed strict occurrences,
with actual acquired $m$ and $0\le z\le4(J_i-K_i)$,
$0\le s\le4$. Under Assumption 1.2 and canonical code supply:

1. Every such source call is the genuine strict Reserve on the one original
   source and has its full original acquired row/ACK return to $R_r$.
2. Every such recovery acquires its actual cover reference and package
   reference, returns the exact requested raw prefix/endpoint with all
   intervening historical native work counted, and finishes output,
   check, ACK, token and outer return finitely.
3. After the finite list, choice 00 resumes the original INITIAL-Stop
   consumer and reaches its genuine global halt with target $q_1(\beta)$.

The same boot allows, after enough reservation, optional actual auxiliary
Raise and original Rho frames before choice 00. They use their historical
current guard; Reserve alone never changes it. No per-capacity
reinitialization, reseeding or new original controller is involved.

Proof. Proposition 4.4 gives the first actual initialized $R_r$ with the
parked Stop client. Induct on the supplied finite cycle list. At an
auxiliary Reserve entry the actual current reserve is the preceding $J$
(or 1 initially). Strict increase makes its greater branch genuine.
CAP Theorem 5.2 preserves $t=\beta,h=1,\xi,u$ and extends the real
$\phi_K$; its complete return and Proposition 5.5 reestablish $R_r$
with its actual acquired row and longer $M$. No supplied future maximum
was used. A history cycle satisfies Propositions 6.5, 8.4 and 7.4;
its old targets lie in its already completed predecessor and its newly
executed rows enter the next real prefix. The induction also supplies
the finite-predecessor condition needed when a later Boundary simulates
this very recovery. The original 24–27 client state remains parked,
while the source's real counters/layout and the meter evolve.

For optional Raise, CAP Theorem 5.3 changes only the current guard on its
lawful strict branch. A subsequent original Rho has CAP Theorem 4.5's
whole-candidate behavior under that guard, including an executed reject
if it is insufficient. Neither operation changes the acquired initial
source or retroactively changes any earlier row's guard. Proposition
5.5 gives their actual auxiliary returns too.

Choice 00 transfers and loans the original workspace as in §5 and
enters the actual original client table. It constructs/seals its output
on 31 and copies the complete output/terminal packet to producer 21 on
route 49, with all CAP workspace loans/returns. Its global Halt marker
has its genuine semantic/unified rows, dependencies and mandatory ACK.
The terminal route freezes both original journal ends, builds SEG-P1,
copies every dependency and snapshot to verifier 32 on route 50 with
native descriptors on 33, and executes CAP Definition 6.5's historical-
guard enumeration/checks. Acquired initial beta identifies the actual
initial candidate in $D$; its original target is $q_1(\beta)$ even if
optional Rho has changed the current source. CAP Theorem 6.6 therefore
accepts this truthful proposal. Its SEG-R1 receipt travels on route 51
to consumer 40, whose original binding checks, allocation, target copy,
OUT, ACK and return precede the actual global halt CTL. No new history
entry is enabled after that edge. This proves the original-target and
terminal assertion on the same continuing execution. ∎

**Proposition 9.3 (one blank-recovery witness and its uniform scope).** In
Definition 9.1's one boot, supply 01, the actual Reserve(2) frame, then
1 with its delivered old unified ordinal $m$, $z=0,s=2$. Recovery returns
the actual first source blank after EX and before WR(0), at $k=n_0+2$,
then returns to the parked original client. Optional 01/Raise(2) and
01/Rho followed by 00 produce the original INITIAL output and global halt.
The source payloads on this optional route are $10$, $100000$, and
$111001$, while the target remains $(0,B,1)$.

Proof. Here $d=4$. Proposition 8.4 gives 24 fragment rows and 25 cuts,
including the selected first blank. Proposition 7.4 supplies the three
actual deliveries and callbacks, not merely an available integer package.
Raise(2) is valid and the original beta Rho accepts
$\langle\beta,\alpha\rangle$ under guard 2. CAP Proposition 17.2 supplies
the displayed packet/initial-target correspondence. Theorem 9.2 gives
the full original consumer and halt. Its arbitrary-$J_i$ induction,
rather than this $d=4$ arithmetic instance, is the uniformity argument. ∎

**Definition 9.4 (generic-source scope).** Definitions 1–8 apply to any
actual finite $H_0,\xi,u$ with their actual acquired seed and boot/prior
material, and any original finite client parked at its initialized
pre-loan entry. The auxiliary raw Reserve/phase-recovery induction uses
no beta-specific packet. Resuming that generic client has only CAP's
original conditional verifier/consumer guarantee: its actual proposal,
compatible initial-source fibre, declared prior computation, reached
local termination and intended stop kind must satisfy CAP Definitions
6.5 and 8.1. A truthful constant INITIAL-Stop output for every possible
source is not inferred from the fixed beta witness. History service
preserves the present source, old guards and parked client; subsequent
genuine source commands may change the present source under their
original guards. This is a scoped entry correspondence, not equality
with an unextended run's clocks, addresses or complete physical state.

## 10. Componentwise prices on one actual run

**Definition 10.1 (complete run vector).** For one actual finite run let
$N_{o,p}(n)$ count its first $n$ rows with opcode $o$ and entering purpose
$p$. Purposes are the disjoint PR57.D9 classes, refined finitely for
new-role initialization, import/parser, Boundary, binding, Issue, Call,
publication and each callback. A helper inherits its caller's purpose
unless its explicit CTL changes it. Each row has exactly one such pair.
Let $A(n)$ count all constructed nonmeter ordinary cells after the
irreducible entrance, and $b_{\rm ctl}(n)$ count every constructed control
bit, active or inactive. Let $C_\tau(n)$ count actually consumed IN bits
of each site kind $\tau$ in Definition 6.1. Complete code captures,
current partial blocks, all captured inputs, dead banks and old control
versions are retained, not erased from these counts.

For an enabled actual row $o_n$ at $x_n$, its entire component recurrence is

$$
\begin{aligned}
N_{o,p}(n+1)&=N_{o,p}(n)+[ (o,p)=(o_n,p_n)],\\
A(n+1)&=A(n)+a(o_n,x_n),\\
b_{\rm ctl}(n+1)&=b_{\rm ctl}(n)+c(o_n,x_n),\\
C_\tau(n+1)&=C_\tau(n)+[o_n=\operatorname{IN}_\tau],\\
T(n+1)&=T(n)+1,\qquad F(n+1)=F(n)+2,\\
S(n+1)&=S(n)+8a(o_n,x_n)+c(o_n,x_n)+8.
\end{aligned}
$$

Here $a=1$ precisely for one-cell ordinary EX or a one-boundary constructor,
and otherwise zero; $c=1$ precisely for a newly installed finite control
bit, and otherwise zero. Existing-cell WR, including erasure or overwriting
an old source bit, decreases no storage. A disabled attempt is no row and
has none of these increments. At an IN the supplied actual bit determines
$x_{n+1}$ and consumes exactly that typed reservoir bit. The terminal
and returned-boundary cost is zero only after the stated final row.

Equivalently the full opcode/purpose cost satisfies
$V(e,x,I)=\mathbf e_{o,p}+V(e',x',I')$ at an enabled row. Sequence evaluates
the second vector at the first fragment's complete successor. Tests use
their actual RD/CTL successor; while repeats at its actual updated bank
and heads. Withheld input or divergent original local work has no finite
completed-flight value. No maximum or independently optimized fragment
is inserted into this recurrence.

**Definition 10.2 (all nonprimitive recurrence terms).** The finite expansion
which determines each component of $V$ is as follows.

| Term | Full recurrence leaves |
| --- | --- |
| Boot/activation | Original extended boot/source/acquisition/client writes; twenty new ordinary boundary constructors; every old/new finite control/token bit; activation CTL; the two actual five-state bootstraps; native capture ingress, descriptor and seal. |
| Bank instruction | Definition 2.1's Base, dry emission, real emission, separators/F/seals, descriptor count/write, parity/purpose CTLs, all Last/Field/scratch scans, exactly as RCA Definition 11.5. |
| Old-tape import | Every Save RD/ML and compiled distance cons; initial source MR; each Scan RD/finite CTL, three literal cons assignments and MR; Reverse; Home, compiled distance tests/tails and each restore MR. |
| Parser/lookup | Every triple Take, symbol test, field accumulator and Reverse; ReadUnary/ReadFrame/ReadList; unary cancellation, Nth/Equal, complete count/predecessor/availability checks and their actual failure branches. |
| Outer/history ingress | Saved Base, all native IN/EX/WR/MR and length tests, actual payload bounds, delimiter/seal, length construction, descriptor count/fields, native Import and branch/token CTLs. |
| CaptureCAP | Actual closed imports and row/dependency parser, external/computed site classification, all complete cycle copies/Appends and return CTL. |
| Boundary/Prefix | Each literal Step74 row lookup, marked-cell scan, replacement, boot/control/latch/token update, receipt/event serialization and tally, plus actual stop/countdown tests. Earlier recovery work has these same native leaves. |
| Binding | Row/origin lookup, whole actual replay to its matching Zero PC, bound extraction, $4(J-K)$ construction, five copies of $z$, all Cats, $s$ cases, wire zero and $a,b$ comparisons. |
| Cover/Issue/Call | Every immutable list/archive record copy, creation count, Prefix, full-state/history serializer, Frame/Cat, measured sender export, descriptor and seal. |
| Each publication | Sender/mailbox/receiver Base, length copies, initialized allocation and single delimiters, setup descriptors and three staged placement records, both positioned tested copies, completion records, all TOKs, print, callback import/parse, ACK and availability return. |
| Original continuation | Actual twelve workspace loans/returns, state/table/packet work, original terminal dependencies/rows, snapshot, verifier enumeration/prior/replay, receipt route, consumer checks/target copy/OUT, final ACK and halt. |

The word macros in this table are precisely Definition 2.1's finite acyclic
list, with no string-operation leaves. Native scratch staging uses the
actual source offsets specified by RCA Definition 13.2: Stage66 increases
its old scratch offset after new Base; Stage67 constructs its copied
wire length on distinct scratch. Descriptor-source positioning precedes
dry counting/copy, and each complete stage is described once. Thus
setup, copies of $c,p$, parsing, ACK and return have recurrence leaves;
they are not unnamed constant overheads.

**Proposition 10.3 (same-run equations and honest subtotals).** The preceding
recurrences account for every component of one finite returning execution.
In particular, with $n=\sum_{o,p}N_{o,p}(n)$,

$$
T(n)=n,\qquad F(n)=2n,\qquad
S(n)=S_{\rm irreducible}+b_{\rm ctl}(n)+8A(n)+8n.
$$

For one recovery, at its successive actual states, its vector is the ordered
sum of gate, selector ingress/import, Boundary, cover record/publication,
ClientCover, binding, Issue/package publication, ClientIssue,
Call/serializer/Image publication, ClientImage/ACK and
$M$ append/token/Ready vectors. Preceding actual CaptureCAP costs are
additional source-cycle work. For the three published payload lengths
$L_C,L_P,L_I$, the two tested copies through the second handoff and mandatory
print have scalar subtotal

$$
\sum_{i\in\{C,P,I\}}\bigl((12L_i+6)+(5L_i+1)\bigr)
=\sum_i(17L_i+7).
$$

The whole recovery equals this subtotal plus the nonnegative sum of its
other actual rows. It is not that subtotal alone. Its distinct immutable
sender/mailbox/receiver payloads alone retain at least $3\sum_iL_i$ cells.

Proof. At every expansion leaf Assumption 1.2 gives exactly the displayed
increment. Induction over actual sequence/test/loop successors proves
all vector coordinates and the storage equation, including partial data.
In a later bootstrap the control installs contribute
$(4|E(L)|+2)+(4|E(G)|+2)$ rows; the intervening actual $\Delta(G)$ capture,
manifest copies and bank initialization are separate recurrence terms.
Inactive versions remain in $b_{\rm ctl}$. The ten new boundary pairs
contribute twenty cells/constructors in $A$, with their receipts too.

CAP Proposition 18.3 supplies the copy endpoint: $12L+6$ ends after the
second handoff; stopping at the second seal would give $12L+5$. The
$5L+1$ print has its own terminal test. Base/allocation, descriptors,
positioning, status/completion, client parsing, ACK and final return
are disjoint additional rows in Definition 10.2. Applying this to each
actual publication gives the stated decomposition. The three payload
intervals coexist and are not aliases. These are additions at actual
shared endpoints, without combining separately optimal schedules. ∎

**Proposition 10.4 (local Reserve account and original counters).** In
Definition 8.3, from $n_0$ to $k$ the Zero fragment has $5z+s$ rows and
$2(5z+s)$ fee units. For $z<d$ it has constructed $z+[s\ge2]$ new source
cells. For $z=d$ it has constructed $d+[s\ge2]$, the extra cell being the
delimiter. Its complete fragment has $5d+4$ rows, $10d+8$ fee units and
$d+1$ nonmeter cells; setup and all later Reserve work are additional.
On the whole run, original CAP counters $q,g,e,j,m$ change only at their
original source/local/Halt/maintenance events, with exactly CAP's cases.
Every history/compiler/client row adds primitive work but no CAP event.

Proof. Count the literal rows in Proposition 8.4. EX occurs at the second
row of each positive iteration and second row of the final delimiter
segment. All other rows create receipts but no ordinary source cell.
The complete fragment is $d$ five-row iterations plus four terminal rows.
Original source calls advance $q,j,m$, accepted modification advances $g$,
accepted Rho also advances $e$; Local/Halt advance $j,m$; maintenance
advances only $m$. The auxiliary caller executes those very original
commitment rows, once each. History rows contain no such event-commit
annotation or original journal writer, so they alter none of these five
counters. Explicitly, writing $S_n,L_n,H_n,M_n$ for the indicators that
row $n$ is respectively an original source, Local, Halt, or maintenance
commit, and $G_n,E_n$ for accepted-modification and accepted-Rho commits,
the interpreted event coordinates obey

$$
\begin{aligned}
q_{n+1}&=q_n+S_n,&g_{n+1}&=g_n+G_n,&e_{n+1}&=e_n+E_n,\
j_{n+1}&=j_n+S_n+L_n+H_n,&
m_{n+1}&=m_n+S_n+L_n+H_n+M_n.
\end{aligned}
$$

These are interpretations of the original prepared/selected counter words,
not atomic updates added to the machine. The actual counter writes remain
in $V$. At an authoritative strict-Reserve directory-seal WR, the interpreted
$K,r,v$ become $J,r+1,v+1$; at a strict-Raise directory-seal WR,
$h,p,v$ become $J,p+1,v+1$. All other rows preserve those interpreted
parameters except their original boot initialization. Partial-record raw
states keep their actual old/new phase rather than an invented committed
entry. Separate actual cycle/cover/package/descriptor unary counts remain
distinct from primitive tally and original event counts. ∎

**Definition 10.5 (resource limitations).** No numerical $n_0$, code length,
whole-run occurrence count or total fee is specified by these symbolic
equations. Neither a minimum-port result nor complete-run cost superiority
is asserted. Finite initial source does not bound retained runtime memory.
An infinite continuation additionally requires continuing actual input
supply and reached-local finite completion. SSA's structural replacement
and CSA's callable structural atlas require a separately initialized
74-role instance and its own actual finite rule/owner correspondence.
Replacing a native tariff by a structural tariff and adding another
tariff are distinct conventions. Neither is implicitly applied here.

## 11. Task kernels, terminal limits and supplier correspondence

**Definition 11.1 (full remaining four-view problem).** Let $Q$ be the
original typed continuation/audit response map of AIF Definition 2.6,
instantiated with CAP's original task and the actual installed entry
relation. Empty response retains terminal type and actual task output.
Write $Q_G$ separately for the response map that also includes the new
history entries and their actual typed outputs. No equality of these two
response maps is assumed. The original-consumer correspondence of §9
concerns the original target and its actual terminal route, rather than
silently redefining $Q$ by adding a full-state terminal readout.
The full carrier includes every original and added partial native phase,
raw enabled input successor, invalid packet, incomplete bank/descriptor,
code version, loan, sender/mailbox/receiver state and final halt.

For four independently defined spatial support/incidence, ordered-operation,
terminal-boundary and retained/callable-memory expressions $V_i$, the
remaining exactness obligations are, separately for each $i$,

$$
V_i(x)=V_i(y)\ \Longrightarrow\ Q(x)=Q(y),\qquad
Q(x)=Q(y)\ \Longrightarrow\ V_i(x)=V_i(y).
$$

Their lawful partial-transition transport must additionally preserve
simultaneous legality, labels, successor relation, and all terminal
readouts. A fourfold copy of manifest/$I_k$/$k$, a shadow source, or an
intersection of kernels is not such an independent definition. Theorem
9.2 supplies an actual acquired returning historical interface on its
specified preterminal family; it supplies none of these eight implications
for independently defined natural views.

The abstract statement `typed_finite_view_kernel` in
[D5 TypedFiniteViewKernel](../../../D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.lean)
(and its owning Scribe) concerns independently specified typed edges,
labels and readouts. The statement `predictive_memory_minimal_quotient` in
[D5 PredictiveMemoryMinimalQuotient](../../../D5/S3/ObserverMemory/RefinementClosure/PredictiveMemoryMinimalQuotient.lean)
(and its owning Scribe) assumes both readout and update factorization.
Neither provides this missing concrete natural-view identification or
actual owner authority.

**Proposition 11.2 (terminal and horizon compatibility).** This construction
retains the hypotheses of CAP's absorbing-terminal and Ready-only horizon
results. Its historical outputs are later images of strictly older cuts;
they do not identify complete history with original terminal behavior,
provide a self-encompassing literal endpoint image, or cover the final
stopping suffix through a Ready that does not exist there.

Proof. Theorem 9.2 has no history entry after original global halt. The
terminal target remains $q_{H_0}(u)$, with no added empty-response archive.
CAP Corollary 16.7's exhibited finer-history terminal fibres therefore
remain a constraint wherever its same-output/no-audit hypotheses apply;
no terminal-type coincidence alone is used here. Every issued target
has $k\le b$ for its acquired predecessor. The final stopping route has
no new Ready interception. CAP Theorems 17.3–17.4 consequently retain
their exact endpoint restrictions, including the distinction between
Ready-only and arbitrary strict-past services. The received Image is
constructed at later cuts, outside the represented old endpoint, as
required by CAP Proposition 18.2. Its completed output/copy cost also
retains Proposition 18.3's endpoint and Corollaries 18.4–18.5's applicable
necessary bounds. No 64-port nested-codec constant is silently transferred
to a 74-port list. ∎

**Definition 11.3 (scoped mathematical suppliers).** The following parameter
correspondences specify the intermediate results used in this volume.

| Supplier | Exact parameter map and retained boundary |
| --- | --- |
| CAP §§2–8; §§12–13; Proposition 16.3 | Same $H_0,\xi,u$, source 16, $\phi_K$, historical guard, actor 24–31, acquired 28/29, original verifier/consumer. The normalized parked-client and inlined raw-caller joins follow §16's finite-entry construction; no arbitrary live-workspace return is inferred. |
| RCA §§11–14, Lemma 15.1, §16 | Compiler 32–39 to 64–71; mailbox 48 to 72; receiver 40 to 73; both service/client payload owners to $A$, with distinct actual phase slots. Literal compiler, codecs, capture and initialized publication are intermediates. The 74-port input/effect/occurrence and callback joins are supplied in §§3–8, not assumed from RCA's fixed-$H$/unused-verifier domain. |
| SSA Theorems 6.2, 7.2, 12.1; CSA Theorems 4.4, 6.3, 7.3, 8.3 | Finite local structural storage, actual-input retention and initialized fragment correspondence are supplied on their own stated images. They give no automatic CAP task-kernel equality or new 74-role tariff. |
| NativeSerialMachine, `nativeStep`, `Run`, `replay_deterministic`, `reached_prefix_replay`, `actual_register_execution`; owning Scribe | One actual original register, truthful reads and source-free replay at its abstract action level. The abstract control can be unbounded; no native finite-code or price consequence is imported. |
| NativeFullSourceProducer, `sourceControl`, `native_source_producer`, private `traverse`, `production_reads`, `stationary`; owning Scribe | The stationary acquisition is the same actual initial source and chronological truthful traversal. Proof-side subtrees are not input material or source oracles. |
| NativeEffectiveSourceProducer, `FullSourceAcquisition`, `effective_source_producer`, `sourceDecoder`; owning Scribe | Effective abstract acquisition preserves common input/epoch/source. Its classical semantic inverse is not the installed parser; the actual packet converter is Definition 6.1. |
| NativeSerialEffective, `OriginalCodeRealization`, evaluator soundness/completeness and `original_code_service_simulation`; owning Scribe | Actual supplied original table/code and genuine state correspondence remain premises of CAP's controller interface. `terminalObservation` is trace-valued and is not the original terminal task readout. |

The intermediate persistence distinction is the version-index/backing
relation of Driscoll, Sarnak, Sleator and Tarjan, *Making Data Structures
Persistent*, JCSS 38(1), pp. 86–124,
[primary text](https://www.cs.cmu.edu/~sleator/papers/making-data-structures-persistent.pdf).
Here it is realized by the actually received immutable $c,p$ and owned
backing; its pointer-structure amortized bounds are not tape prices.
Current rights and represented old rights remain distinct in the sense
of Watson et al., *Capsicum: Practical Capabilities for UNIX*,
[primary text](https://www.cl.cam.ac.uk/research/security/capsicum/papers/2010usenix-security-capsicum-website.pdf);
no operating-system callback or rights theorem constructs the native
TOKs of §7. Input completeness is the record/replay requirement discussed
by O'Callahan et al., *Engineering Record And Replay For Deployability*,
[primary text](https://arxiv.org/pdf/1705.05937); its Linux mechanisms,
counter prices and schedules are not transferred. The operative finite
row correspondence is Proposition 6.3, with the concrete input sites and
return labels specified here.

## 追加锚（本行以下为增补区）
