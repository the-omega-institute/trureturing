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

## 12. Arbitrary-operand source-write chronology

This section fixes the value-level operation language used by the preceding
CAP/ARC construction. It does not enlarge the installed controller. The
mathematical source is the free set

$$
\mathcal T::=\alpha\mid\beta\mid\langle x,y\rangle,
\qquad
\rho(\alpha)=\beta,
\quad
\rho(\beta)=\langle\beta,\alpha\rangle,
\quad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle .
\tag{SW.1}
$$

Write $\lambda(t)$ for the number of leaves of $t$, and write
$a(t),b(t)$ for its numbers of $\alpha$ and $\beta$ leaves. Thus
$\lambda(t)=a(t)+b(t)$. The three accepted modifying values are

$$
S(x)=\rho(x),\qquad
\operatorname{Left}(c)(x)=\langle c,x\rangle,
\qquad
\operatorname{Right}(c)(x)=\langle x,c\rangle,
\tag{SW.2}
$$

where every operand $c$ is a nonempty finite tree. These are command and
operand values. They are not complete histories, physical states, or an
identity of two source occurrences.

The image $I=\rho[\mathcal T]$ and the actual image inverse $\delta:I\to
\mathcal T$ are the ones already supplied by JOINT_MOMENT_FIBERS 36.2.
For $t\in\mathcal T$, let $\mu(t)$ be its maximal actual substitution
ancestry: the largest $m$ for which $t\in\rho^m[\mathcal T]$. Thus
$\delta^j(t)$ is defined exactly when $0\le j\le\mu(t)$, and
$\rho^j\delta^j(t)=t$ on that range. The finiteness of $\mu(t)$ is
part of the same actual-image result; it also follows from (SW.7) below, since
every $\rho$ step raises $W$ by the positive number $\lambda(t)$.

**Definition 12.1 (retained occurrence and outward siblings).** Let $p$ be
an actual address of a node of $v$, written from the root to that node in
the usual $L/R$ convention. For the chronology below, read the same address
from the retained occurrence outward, so its first symbol is the innermost
retained-child choice. Put $g=|p|$. If the retained occurrence is the
left child at a step, the final sibling at that step is the right sibling;
if it is the right child, the final sibling is the left sibling. Read these
final siblings from the retained occurrence outward as
$w_1,\ldots,w_g$. The resulting outward word is the reverse of the usual
root-to-node address, but the two descriptions name the same actual nodes.

The retained child $L$ is rebuilt by a $\operatorname{Right}$ graft and the
retained child $R$ by a $\operatorname{Left}$ graft. This convention keeps
an address even when two sibling values are equal: equality of values never
identifies the two actual addresses.

**Theorem 12.2 (complete accepted-word parameterization).** Fix
$u,v\in\mathcal T$. A value word in $S$, $\operatorname{Left}(c)$ and
$\operatorname{Right}(c)$ carries $u$ to $v$ if and only if it is obtained
from the following data:

1. an actual address $p$ of $v$ and $g=|p|$;
2. an integer $r\ge0$ such that
   $v|_p=\rho^r(u)$;
3. ages $r\ge s_1\ge\cdots\ge s_g\ge0$ satisfying
   $s_i\le\mu(w_i)$ for every $i$.

For these data the unique value word is

$$
S^{\,r-s_1},\ G_1,\ S^{\,s_1-s_2},\ G_2,\ldots,
G_g,\ S^{\,s_g},
\tag{SW.3}
$$

where $G_i=\operatorname{Right}(\delta^{s_i}(w_i))$ when the retained
child at the $i$th outward step is $L$, and
$G_i=\operatorname{Left}(\delta^{s_i}(w_i))$ when it is $R$. For $g=0$
the word is $S^r$ and the condition is $v=\rho^r(u)$.

More precisely, the displayed map is a bijection between the feasible
triples $(p,r,(s_i))$ and value words together with their retained actual
occurrence. After forgetting that occurrence, two triples may project to the
same endpoint value only through the ordinary coincidence of equal source
values; the classification never identifies distinct addresses or asserts
a complete-history equivalence.

*Proof.* First take a feasible triple. Starting at $u$, perform the initial
$r-s_1$ substitutions. At the first outward step attach
$\delta^{s_1}(w_1)$ on the non-retained side. Perform $s_1-s_2$ further
substitutions, attach $\delta^{s_2}(w_2)$ on the next non-retained side, and
continue. The last $s_g$ substitutions act on the whole current tree.
The retained occurrence has undergone exactly $r$ substitutions. The
$i$th operand has undergone exactly $s_i$ subsequent substitutions, so its
final value is
$\rho^{s_i}\delta^{s_i}(w_i)=w_i$. The graft orientation is exactly the
one prescribed by the retained child. Induction on $i$ therefore gives the
ordered tree $v$.

Conversely, consider any accepted value word from $u$ to $v$. Mark the
unique source occurrence that is retained by every graft. A substitution
preserves that occurrence; a graft adds one edge to it. At the end its
actual address is some $p$, and the number of grafts is $g=|p|$. Counting
all substitutions gives $r$. Let $s_i$ be the number of substitutions
strictly after the $i$th graft. The chronology forces
$r\ge s_1\ge\cdots\ge s_g\ge0$. The operand at the $i$th graft is a tree
$c_i$ whose final sibling is $w_i=\rho^{s_i}(c_i)$. Hence
$w_i\in\rho^{s_i}[\mathcal T]$, $s_i\le\mu(w_i)$, and injectivity of $\rho$
with the supplied inverse gives $c_i=\delta^{s_i}(w_i)$. The retained-child
orientation gives the stated $G_i$. This recovers (SW.3).

The value word itself records $r$ as its number of $S$ letters and $g$ as
its number of graft letters. The orientation of each graft records the
outward address, and the lengths of the intervening $S$ runs recover the
$s_i$. The endpoint then fixes each $w_i$ at its actual address. Thus the
recovery is unique at the value-and-address level. Equal values at two
addresses remain two entries of the same recovered address list. No claim
about unrecorded physical provenance is used. $\square$

The proof also handles all degenerate cases. There are no feasible data
when no actual address and age tuple satisfies the displayed conditions.
The empty word occurs exactly for $u=v$, $p=\varepsilon$, $r=g=0$. If
$r=0$, every feasible age is zero and the word consists only of grafts.
Ages may repeat, including $s_i=s_{i+1}$, and a repeated sibling value does
not collapse the two grafts. A zero substitution count therefore does not
mean that the source was not acquired or that a call was omitted; it only
specifies the modifier word.

**Corollary 12.3 (the two endpoint bounds).** Define

$$
W(t)=a(t)+2b(t).
\tag{SW.4}
$$

Every feasible parameter tuple satisfies

$$
 r+g\le W(v)-W(u).
\tag{SW.5}
$$

If the operational start $u$ contains a $\beta$ leaf, then the stronger
leaf bound holds:

$$
 r+g\le\lambda(v)-\lambda(u).
\tag{SW.6}
$$

The second bound is an operational statement only; it is not a bound for
all algebraic starts.

*Proof.* Directly from (SW.1),

$$
W(\rho t)-W(t)=\lambda(t),
\qquad
W(\langle c,t\rangle)-W(t)=W(c),
\qquad
W(\langle t,c\rangle)-W(t)=W(c).
\tag{SW.7}
$$

Every tree is nonempty, so every substitution and every graft increases
$W$ by at least one. Summing the increments along the word proves (SW.5).
For leaves,

$$
\lambda(\rho t)-\lambda(t)=b(t),
\qquad
\lambda(\langle c,t\rangle)-\lambda(t)=\lambda(c),
\qquad
\lambda(\langle t,c\rangle)-\lambda(t)=\lambda(c).
\tag{SW.8}
$$

A $\beta$ leaf remains present under $\rho$, and a graft retains the old
source as one child. Thus a $\beta$-containing start has $b(t)\ge1$ at every
substitution point, while every context has at least one leaf. Summing
(SW.8) proves (SW.6). If the start is all-$\alpha$, its first substitution
has $b(t)=0$ and preserves leaf count: $\alpha\mapsto\beta$ is the explicit
plateau. Therefore (SW.6) cannot be applied to arbitrary algebraic starts.
Equation (SW.5) still applies on those plateaus. $\square$

In particular, a negative right side in either bound certifies
infeasibility, while a zero right side permits only the empty word in the
corresponding nonempty-source class. These are bounds on the modifier
word, not on acquisition, parser, return, storage or total execution.

## 13. The exact age frontier and the finite write comparison

**Definition 13.1 (feasible age set).** For a fixed feasible $(p,r)$, let
$\mathcal A(p,r)$ consist of all integer vectors satisfying

$$
 r\ge s_1\ge\cdots\ge s_g\ge0,
\qquad s_i\le\mu(w_i).
\tag{SW.9}
$$

Put

$$
 s_i^*=\min\{r,\mu(w_1),\ldots,\mu(w_i)\}
 \qquad(1\le i\le g).
\tag{SW.10}
$$

**Theorem 13.2 (greatest feasible ages).** The vector $s^*$ belongs to
$\mathcal A(p,r)$ and is its greatest element in the coordinatewise order.
Consequently, for every $s\in\mathcal A(p,r)$ and every $i$,

$$
\lambda(\delta^{s_i^*}(w_i))\le
\lambda(\delta^{s_i}(w_i)),
\qquad
3\lambda(\delta^{s_i^*}(w_i))-1\le
3\lambda(\delta^{s_i}(w_i))-1.
\tag{SW.11}
$$

Thus the canonical word with $s^*$ simultaneously minimizes every supplied
context leaf count and every canonical context payload length. Equal minima
are possible.

*Proof.* The prefix minima in (SW.10) are nonincreasing, are at most $r$,
and are at most each corresponding $\mu(w_i)$, so $s^*\in\mathcal A(p,r)$.
For $s\in\mathcal A(p,r)$, induction gives
$s_i\le r$, $s_i\le s_{i-1}\le\mu(w_{i-1})$, and
$s_i\le\mu(w_i)$; hence $s_i\le s_i^*$ for every $i$.

If $0\le j<\mu(w)$, then
$\delta^j(w)=\rho(\delta^{j+1}(w))$. By (SW.8),
$\lambda(\delta^{j+1}(w))\le\lambda(\delta^j(w))$. Iterating proves the
first inequality in (SW.11). The supplied original context grammar has
branch code $0$, leaf codes $11$ and $10$, and recursively codes an ordered
pair by a branch followed by its two child codes. A tree with $m$ leaves
therefore has $m-1$ branches and payload length

$$
 d(m)=(m-1)+2m=3m-1.
\tag{SW.12}
$$

The second inequality follows. A strict decrease need not occur: for
example $\delta(\beta)=\alpha$ and both trees have one leaf. This accounts
for ties. $\square$

**Definition 13.3 (canonical write subtotal).** For a feasible $(p,r)$,
use $s^*$ and set

$$
I_{\mathrm{write}}(p,r)=
6r+6\sum_{i=1}^{g}\lambda\!\left(\delta^{s_i^*}(w_i)\right)+4g.
\tag{SW.13}
$$

This is the exact CAP7.2 subtotal for accepted modifying **external**
outer-01 source cycles in the comparison class of this section: six units
for each whole-source $S$ cycle, six units per supplied context leaf, and
four units for each accepted graft. The Rho call has both its external
outer-01 entry and its canonical source frame `0010`; this frame is part of
the six-unit $S$ subtotal. A Left or Right call has the same outer entry
and carries one context payload, whose payload length is (SW.12). The
formula is a source-write subtotal, not a measurement of elapsed time.

For an arbitrary feasible age vector define the analogous value by replacing
$s^*$ in (SW.13) with $s$. Theorem 13.2 proves

$$
I_{\mathrm{write}}(p,r;s^*)
 \le I_{\mathrm{write}}(p,r;s).
\tag{SW.14}
$$

The inequality is simultaneous in all context coordinates; it does not
trade one operand against another. The possible equality cases are exactly
the payload ties allowed by (SW.11).

**Theorem 13.4 (complete finite nondominated frontier).** Let
$\mathcal C(u,v)$ be the set of triples

$$
\bigl(r,g,I_{\mathrm{write}}(p,r)\bigr)
\tag{SW.15}
$$

over every actual address $p$ of $v$ and every $r$ satisfying the endpoint
condition and the feasibility of (SW.9). Project away duplicate triples,
and retain the coordinatewise nondominated ones. This finite set is the
complete nondominated frontier for accepted modifying external outer-01
source cycles between $u$ and $v$.

*Proof.* By (SW.5), only finitely many pairs $(r,g)$ can occur. The finite
tree $v$ has finitely many actual addresses. For each $(p,r)$, Theorem
13.2 replaces every feasible age vector by $s^*$ without increasing any
of the three coordinates in (SW.15), since $r$ and $g$ are unchanged and
(SW.14) decreases the third. Thus every feasible word is weakly dominated
by one of the displayed canonical triples. Conversely each displayed
triple is realized by Theorem 12.2 and its canonical payload grammar, so
no member of this comparison class is omitted. Removing coordinatewise
dominated triples is precisely the definition of the nondominated frontier.
Distinct addresses are considered before projection; equal endpoint values
may consequently coalesce only after their actual-address distinction has
been recorded. $\square$

The frontier is deliberately limited. It does not optimize total time,
storage peak, acquisition or ingress, context generation, copying/backing,
maintenance, automatic-mode computed commands, primitive source work,
rows/dependencies, checks, ACKs, returns, retention or output. Those
coordinates retain their original CAP/ARC and GENERAL foundation/tariff
and are charged when the corresponding phases occur. Nor does the finite
frontier assert a measured speedup or a universal optimum for a different
menu.

**Example 13.5 (a repeated-age canonical word).** Let $u=\beta$, let the
retained occurrence have outward choices $(R,L)$, and let its final
siblings be $w_1=w_2=\beta$. Take $r=1$. Since $\mu(\beta)=1$,
(SW.10) gives $s_1^*=s_2^*=1$. The canonical operands are both
$\delta(\beta)=\alpha$, and the word is

$$
\operatorname{Left}(\alpha),\quad
\operatorname{Right}(\alpha),\quad S.
\tag{SW.16}
$$

It sends

$$
\beta
\mapsto\langle\alpha,\beta\rangle
\mapsto
\langle\langle\alpha,\beta\rangle,\alpha\rangle
\mapsto
\left\langle\left\langle\beta,\langle\beta,\alpha\rangle\right\rangle,\beta\right\rangle.
$$

The two ages are equal and the two sibling values are equal, yet the two
actual addresses and the two oriented graft commands remain distinct. The
example illustrates a value-level word; it is not an execution trace or a
measured benchmark.

## 14. One authentic CAP/ARC consumer

The classification above is algebraic for all nonempty finite endpoints.
The following is the actual operational subdomain, with every extra
condition visible. It is the only consumer claimed here.

**Definition 14.1 (beta-boot write consumer).** Start from the completed
beta-boot relation supplied by NATIVE_CROSS_EPOCH_RELATIONS 13.1–13.2 and
this volume's Definitions 4.1 and 5.1–5.4: source value $\beta$,
$H_0=h=K=1$, the original verifier and INITIAL consumer installed, the
source-service token at its dispatcher, producer work tokens at their
owners, and the original Stop client parked on its actual ports. Let a
finite preparation, using the existing accepted graft calls and any
lawful Reserve/Raise calls, reach an authentic ARC Ready boundary whose
current source value is $u$ and whose current source syntax has actually
been acquired at that epoch. The preparation is allowed only when $u$
contains a $\beta$ leaf, as guaranteed by NCE 13.2.

Before modifying the source, retain the target-side operands and the final
literal target syntax in the existing owned immutable backing. For a
canonical tuple $(p,r,s^*)$, this means retaining the actual finite
contexts $\delta^{s_i^*}(w_i)$ and the authenticated endpoint specification
$v$; the context words are supplied through the original context grammar,
not generated by an unrecorded planner. The current source and target
records carry their actual source epoch, origins and permissions. A formula
for $v$ alone is not an acquisition and cannot open this consumer.

Choose a guard/capacity $H\ge\lambda(v)$. If the reached Ready has
insufficient $h=K$, complete the existing Reserve/Raise route to this
finite $H$ and return to Ready before issuing the modifier word. No new
capacity operation is introduced. Since the retained source contains a
$\beta$ leaf and all contexts are nonempty, (SW.8) shows that every
intermediate source and every final context fits the same finite bound
$H$; if a stricter installed guard is used, raise to that guard instead.

**Theorem 14.2 (actual completion of one canonical word).** Under
Definition 14.1, every letter of (SW.3) has an actual finite CAP/ARC call
and the complete word reaches a genuine Ready boundary with source value
$v$. Every accepted call is one of the following existing frames:

- $S$ is the external outer-01 call followed by source frame `0010`
  (tag `001`, empty payload and its terminating zero);
- $\operatorname{Left}(c)$ or $\operatorname{Right}(c)$ is the same
  outer-01 call followed by tag `011` or `100`, unary length $U(3\lambda(c)-1)$,
  and the original context payload code (branch `0`, alpha `11`, beta `10`,
  and recursive pair branches).

For each call, the consumer performs, in order, the actual outer-01
acquisition, seal, descriptor construction and import; the $F^A$ header
Base/setup; all required input, source work, row/dependency construction,
checks and response publication; final row ACK; source-token TOK and idle
CTL; InnerReturn normalization; closed-28/29 import; the CaptureCAP append
of the actual cycle item; restoration of the archive heads; and the next
ARC Ready relation. The next letter is issued only after this return.

*Proof.* The frame forms are exactly CAP Definition 4.6 and the source
frame grammar of the structural-storage atlas. The source frame for Rho is
`0010`; its tag is not an inferred mnemonic. The context parser reads the
unary length and then exactly the payload length in (SW.12), so every
canonical operand is a finite accepted word. The endpoint guard is at most
$H$ by Definition 14.1, and the canonical source effect is the one in
(SW.2), so the installed admission predicate accepts every letter in the
word.

At an authentic Ready, ARC's outer-01 selector owns the invocation and
CAP's resident admission supplies the actual current source token. CAP
Lemma 6.7 gives the complete finite row/dependency/response/ACK/source-token
return under the original local-progress premises. The changed final idle
CTL enters InnerReturn exactly as in Definition 4.1. Proposition 5.5 then
normalizes the public roles and reaches CaptureCAP; Proposition 3.5 parses
and authenticates the delivered rows/dependencies and restores the 28/29
heads. The CaptureCAP item records the actual input bits, origins and
accepted source effect before the Ready CTL. At the next Ready, the source
syntax is the newly returned current source and is not replaced by a stale
pre-write snapshot; the retained target backing remains data only. Induction
on the letters of (SW.3), with Theorem 12.2 for the semantic source value,
proves both finite termination and the final endpoint $v$.

No accepted write is left unrecorded between two Ready boundaries. A
malformed, refused, partial or busy input remains in its corresponding raw
or refusal phase and is not silently reclassified as an accepted letter.
Every maintenance, read, copying/backing, other ingress, automatic-mode
computed command, primitive row, dependency, capture, check, ACK, return,
retention and output operation used by this induction keeps its original
phase and charge. The subtotal (SW.13) counts only the selected external
modifier cycles. $\square$

**Corollary 14.3 (current-source reads occur only after the write).** After
the final Ready in Theorem 14.2, the live source has endpoint value $v$.
A later authorized TagRead at an actual address $q$ returns the literal
reply for the current $v$ at $q$, subject to CAP's source token, guard and
row conditions. Such a reply is a later source read; it is not a planning
oracle, a retroactive validation of an operand, or a replacement for the
retained target syntax used before the word.

**Proposition 14.4 (consumer boundary).** The consumer does not provide
any of the following: arbitrary Busy-cut admission, halt re-entry,
original-annex Advance admission, an autonomous planner, a cross-source
identity, a physical executor, a reset, a clone, an inverse source port, or
a new callable service. It also does not identify a full history from the
command/operand value word, and it does not extend the leaf bound to an
all-$\alpha$ algebraic start.

*Proof.* The start is the specific beta-boot Ready relation, and every
entry is the installed outer-01 selector. CAP's admission clause is for
that acknowledged idle relation; no claim is made for a different Busy or
terminal cut. The parked Stop client remains parked until its own original
route is selected and therefore cannot plan or issue the word. All source
syntax and contexts used above are supplied finite material with current
origins and explicit owner permissions. The only inverse used in planning
is the mathematical $\delta$, while execution uses the existing source
parser and controller. The original-interface exposure volume leaves the
annex Advance judgment open, so no such edge is used here. These are exactly
the stated premises and exclusions. $\square$

**Definition 14.5 (comparison-class accounting).** For an executed
canonical word, the retained accounting vector is split into

$$
\mathbf C=\mathbf C_{\rm acquire}+\mathbf C_{\rm plan}
+\mathbf C_{\rm context}+\mathbf C_{\rm copy}
+\mathbf C_{\rm ingress}+\mathbf C_{\rm maint}
+\mathbf C_{\rm auto}+\mathbf C_{\rm primitive}
+\mathbf C_{\rm rows/deps}+\mathbf C_{\rm checks/ACK}
+\mathbf C_{\rm returns}+\mathbf C_{\rm retain/output}.
\tag{SW.17}
$$

The first, second, and every later coordinate is charged only when its
actual original phase runs. The mathematical planner that enumerates
(SW.3) is a proof-side finite calculation and is not a newly callable
service. Canonical modifier input has one operand coordinate per graft;
there is no hidden second input for provenance or a complete target state.
Equation (SW.13) is the exact projection of $\mathbf C$ onto the selected
external source-write subtotal. CAP7.2's actual primitive ticks/fees/storage
and GENERAL's foundation/tariff remain separate coordinates.

**Supplier map and nonduplicate boundary.** The following published
interfaces are used as suppliers, with no stronger result imported:

| Supplier | Reused fact here | Boundary retained here |
| --- | --- | --- |
| [ER](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ENTRY_REFERENCE_AND_GRAFT_ORDER.md), §§9, 16, 20–23 | Fixed-c correspondence, actual retained occurrence, source framing, current operand material and returned-cut discipline. | Its fixed-menu and received-shape results are not reinterpreted as this arbitrary-operand classifier. |
| [NCE](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CROSS_EPOCH_RELATIONS.md), §§13–14 | Beta-boot attainment, source-value chronology and the distinction between source-value history and complete history. | It does not identify all complete physical histories or authorize a Busy/terminal entry. |
| JOINT_MOMENT_FIBERS, §§36.2–36.3 | Actual image inverse $\delta$ and maximal substitution ancestry. | No new inverse operation or source port is installed. |
| [SSA](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_STRUCTURAL_STORAGE_ATLAS.md), §§1–2 | $3m-1$ prefix-code payload length and the actual tags `000`–`100`. | Code length is a payload coordinate; it is not a total execution or storage optimum. |
| CAP, [capacity coherence](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CAPACITY_COHERENCE_AND_GROWTH.md), Definition 4.6 and Lemma 6.7 | Canonical frame admission, source work, complete rows/dependencies, ACK and source-token/idle return. | Only the installed acknowledged-idle domain is used. |
| ARC, this volume, Definitions 4.1 and 5.1–5.4 and Proposition 5.5 | Actual outer-01 entry, InnerReturn, CaptureCAP, retained cycle item and next Ready. | The parked client is not an autonomous planner and no arbitrary internal cut is admitted. |
| Native Original Interface Exposure and Recovery, §§3–4 | The explicit open boundary for original annex Advance admission. | No original-Q claim is made for that annex. |
| Native Finite Obstruction, §§3–7 | One-read prescribed-budget decision and its own optimization scope. | Its menu is not silently enlarged to these CAP arbitrary contexts. |

The resulting increment is a classification of command/operand values, its
exact age-and-payload frontier, and one actual returned CAP/ARC consumer.
It is not a claim of worldwide originality, a new Lean theorem, a full
history decoder, a universal source bridge, or completion of the broader
space/continuation/boundary/memory objective.

## 追加锚（本行以下为增补区）

## 15. Acquired requests and the two-step source relation

**Definition 15.1 (source projection and encoding).** Use the nonempty
finite ordered trees and the unchanged CAP operations of Definition 1.1
and (SW.1). In §§15–19 write

$$
E(t)=\rho^2(t),\qquad n(t)=a(t)+b(t),\qquad
w(t)=n(E(t))=2a(t)+3b(t).
\tag{GT.1}
$$

Here $E$ is a tree encoding, not CAP's Clifford-valued ReadE observable.
The original boot parameter is denoted $H_{\rm boot}=1$; the symbols
$H_j$ below denote later active guards, not a second boot parameter.
At an authentic Ready, $\pi_{\rm src}$ denotes the logical tree represented
by source16 through that path's actual $\phi_K$. It does not denote the
whole arena, an acquired snapshot, or a writable actor register.

For a request $A$ define its whole candidate and its encoded request by

$$
\begin{array}{c|c|c}
 A&c_A(t)&\widehat A\\\hline
 \operatorname{Rho}&\rho t&\operatorname{Rho}\\
 \operatorname{Left}(v)&\langle v,t\rangle&\operatorname{Left}(E(v))\\
 \operatorname{Right}(v)&\langle t,v\rangle&\operatorname{Right}(E(v)).
\end{array}
\tag{GT.2}
$$

Every $v$ is an arbitrary whole nonempty finite original operand, with its
brackets and left/right order. A request outside the current guard remains
a canonical request and performs an executed source refusal. Acceptance
installs the entire candidate; refusal retains the entire old tree.
The response label in this appendix is exactly that existing
accept/executed-refusal component of the original modifier response.
No candidate value is exposed by a refusal.

The homomorphism and composition identities used below are the suppliers
ABT (ABT.66), (ABT.68), ER (ER.33), and
GenealogicalFiberTransport's substitution and composition, including
one_step and transport inside fiberMap. In particular

$$
\begin{aligned}
E(\rho t)&=\rho(E(t)),&
E\langle x,y\rangle&=\langle E(x),E(y)\rangle,\\
2n(t)&\le w(t)\le3n(t),&
w(\rho t)-w(t)&=a(t)+2b(t)>0.
\end{aligned}
\tag{GT.3}
$$

For a graft, $w(c_A(t))-w(t)=w(v)>0$. These are reused tree and
count identities, not new inverses or source services.

**Definition 15.2 (finite reference schedule).** Fix $N\ge0$, a starting
tree $t_0$, finite integers

$$
n(t_0)\le h_0\le K_0,\qquad
h_0\le h_1\le\cdots\le h_N,
\tag{GT.4}
$$

and $N$ requests $A_1,\ldots,A_N$ of (GT.2). For $1\le j\le N$ put

$$
\begin{aligned}
c_j&=c_{A_j}(t_{j-1}),&
\ell_j&=n(c_j),&d_j&=w(c_j),\\
\varepsilon_j&=\begin{cases}
 \mathsf{accept},&\ell_j\le h_j,\\
 \mathsf{refuse},&\ell_j>h_j,
\end{cases}&
t_j&=\begin{cases}
 c_j,&\varepsilon_j=\mathsf{accept},\\
 t_{j-1},&\varepsilon_j=\mathsf{refuse}.
\end{cases}
\end{aligned}
\tag{GT.5}
$$

The reference continuation publishes guard $h_j$ before request $j$:
when needed it first uses Reserve$(\max(K_0,h_j))$, then Raise$(h_j)$,
omitting either call whose value is already current. Its reserve after
round $j$ is $\kappa_j=\max(K_0,h_j)$, with $\kappa_0=K_0$.
It then performs the single whole request $A_j$. This explicitly changes
the historical task from $F_{h_{j-1}}$ to $F_{h_j}$ when the schedule
strictly increases; no old refusal is reinterpreted under the new guard.

Each integer in (GT.4) is finite. The finite word is a quantification
domain for the theorem, not advice supplying its future maximum at boot.
The rule below uses only the next guard and next request together with
the current retained data. No infinite completion is included.

**Assumption 15.3 (authentic preparation and early material).** The
operational domain is the beta-boot-derived consumer of Definition 14.1,
using Definitions 4.1 and 5.1–5.4 and NCE §§13–14. One finite preparation
from its first Ready reaches a Ready $p$ with actual current source
$t_0$, guard $h_0$, reserve $K_0$, and the original parked client,
verifier and INITIAL consumer. Its current source syntax has actually
been acquired at that source epoch, with its actual origin and present
read permission. Thus $t_0$ contains a beta leaf; the algebraic assertions
below need only nonemptiness. A stale seed or a mathematical source name
is not this acquired-current-syntax premise.

The acquired syntax is retained in existing owned immutable backing.
Counts are obtained by a paid traversal of that syntax: a leaf contributes
$(1,0)$ or $(0,1)$ and an ordered branch adds its two count pairs.
Before the first outer-choice Base/IN prelude of round $j$, including any
maintenance prelude in that round, the next $h_j$, request kind, and any
whole operand $v_j$ and its encoded material $E(v_j)$ are already actually
owned and readable. They have their real epochs, origins, descriptors,
permissions and backing. The equality of encoded material to $\rho^2v_j$
is established by finite syntax construction or a paid complete comparison;
it is not an unverified encoding promise or a new source oracle.
Copying and retaining these words and their construction are charged.
They are then actually supplied anew at the prescribed frame IN sites.
Ownership of an early copy does not eliminate those later IN occurrences.

When $N>0$, only the first request must be available initially; later requests
may be acquired at their preceding completed Ready. No operand first
learned in a Busy ingress may be moved to an earlier cut. The retained
record for round $j$ is used at its current authorized preparation cut,
not through a historical permission. All required finite supply arrives
at its installed sites, and every reached local/prior computation used
by a claimed completed flight terminates, as in Assumption 1.2.
All acquisition, count/encoding/arithmetic/planning, material copying,
backing, source work and return/retention work are paid. There is no
premise granting a branch-transport service, a new planner, or a current
caller inside the parked client.

**Definition 15.4 (matched completed relation).** The two continuations
are alternative finite extensions of this same reached $p$. The reference
extension starts its rounds at $p$. The encoded extension first performs
the preparation in Proposition 17.1. At their designated completed cuts
$p_j,\widehat p_j$, define the source relation by

$$
\begin{gathered}
\pi_{\rm src}(p_j)=t_j,\qquad
(h,K)(p_j)=(h_j,\kappa_j),\\
\pi_{\rm src}(\widehat p_j)=E(t_j),\qquad
(h,K)(\widehat p_j)=(H_j,K_j),\\
H_j=\max(h_j,w(t_j)),\qquad K_j=\max(K_0,H_j).
\end{gathered}
\tag{GT.6}
$$

Both cuts are authentic ARC Ready cuts after the full return and capture
of their respective last call. They retain the original source occurrence
$\xi$, source16 and their actual continuing address maps. Each map extends
the map at $p$ on its old logical domain; later allocated absolute
addresses on the two alternatives need not coincide.

This is a relation between reachable endpoints, not two live callable
registers. All complete joint states, requests, replies, heads, latches,
bytes, tags, counters, origins, rows, permissions and receipts retain their
actual values. They are not equated by (GT.6). The compared components are
the modifier label and the displayed logical-source successor relation.
Maintenance rows and their responses remain actual paid events even when
they have no paired reference modifier.

## 16. Admissible guards and monotone finite transport

**Theorem 16.1 (exact request-dependent guard conditions).** Suppose a
matched cut has reference source $t$, last reference guard $h_-$, encoded
guard $H_- =\max(h_-,w(t))$ and encoded source $E(t)$. Let the next
reference guard be $h\ge h_-$ and let $c=c_A(t)$ for one request of
(GT.2). Set

$$
B=\max(H_-,h)=\max(h,w(t)),\qquad d=w(c).
\tag{GT.7}
$$

Among new encoded guards $G\ge B$, the guards which preserve both the
original modifier label and $\widehat t'=E(t')$ are exactly

$$
\begin{array}{c|c}
 n(c)\le h& G\ge\max(B,d)\\
 n(c)>h& B\le G\le d-1.
\end{array}
\tag{GT.8}
$$

Both rows have a solution. The following particular selection is
nondecreasing from $H_-$ and has the precise post-request value
$\max(h,w(t'))$:

$$
G_A(t,h)=
\begin{cases}
 \max(h,d),&n(c)\le h,\\
 \max(h,w(t)),&n(c)>h.
\end{cases}
\tag{GT.9}
$$

*Proof.* The whole encoded candidate is $E(c)$ by (GT.2)–(GT.3).
Its leaf count is $d$, so CAP's unchanged modifier guard accepts it
exactly when $d\le G$. Consequently an accepting reference request
requires and suffices to have $G\ge d$, in addition to $G\ge B$.
When both accept the actual installed successor is $E(c)=E(t')$.
A refusing reference request requires and suffices to have $G<d$;
when both refuse their old sources remain related. This proves the
necessity and sufficiency of both intervals in (GT.8), using whole
original requests and their actual refusal case.

It remains to show that monotonicity has not made the refusal interval
empty. For every modifier, (GT.3) gives $d>w(t)$. In its refusing case,

$$
d\ge2n(c)\ge2(h+1)>h.
\tag{GT.10}
$$

Thus $d>\max(h,w(t))=B$, with integer endpoints, so $B\le d-1$.
The accepting interval is unbounded above. In that case $d>w(t)$
also gives $\max(B,d)=\max(h,d)$. Its choice in (GT.9) is exactly
$\max(h,w(c))$. In the refusing case $t'=t$, so its choice is exactly
$\max(h,w(t'))$ as well. Both are at least $B\ge H_-$. No lowering
operation is required. $\square$

**Definition 16.2 (the finite preparation rule).** At round $j$, compute
$(\ell_j,d_j)$ from the retained current count pair $(a,b)$ and the
acquired operand counts $(a_v,b_v)$ when present:

$$
\begin{array}{c|c|c}
 A_j&\ell_j&d_j\\\hline
 \operatorname{Rho}&a+2b&3a+5b\\
 \operatorname{Left}(v),\operatorname{Right}(v)
   &a+b+a_v+b_v&2a+3b+2a_v+3b_v.
\end{array}
\tag{GT.11}
$$

Compare $\ell_j$ with the acquired $h_j$. Select the corresponding
$G_j$ by (GT.9) and set $J_j=\max(K_0,G_j)$.
From the encoded previous completed cut, perform Reserve$(J_j)$ if
$J_j$ exceeds the current reserve, then Raise$(G_j)$ if $G_j$ exceeds
the current guard. Return completely after each such call. Then perform
exactly the single modifier $\widehat A_j$ with its whole encoded operand,
and return completely again. Equal maintenance calls are omitted by this
rule; if performed separately, they have their actual unchanged outcome
and an additional bill.

For the next round, an accepting Rho changes the retained count pair to
$(b,a+b)$, an accepting graft to $(a+a_v,b+b_v)$, and a refusal preserves
$(a,b)$. The retained syntax is correspondingly $\rho t$, the specified
ordered pair, or the same $t$. These are finite computations on acquired
material. Unary addition, comparison and maximum may be performed by
finite scans and copies, with maximum selecting a copied operand;
substitution recursively emits beta for alpha and the ordered pair
$(\beta,\alpha)$ for beta. Two such finite traversals construct $E(v)$.
Their finite work and output backing are included in Assumption 15.3.
This rule does not invoke the source to learn an unexposed refused
candidate. The comparison in (GT.11) is made before the request enters
its source body, and the installed original guard independently decides
the actual outcome there.

**Theorem 16.3 (finite mixed transport invariant).** For every datum of
Definition 15.2, start an encoded source at $E(t_0)$ with
$H_0=\max(h_0,w(t_0))$ and $K_0^{\rm enc}=\max(K_0,H_0)$.
Under CAP's whole-modifier and Reserve/Raise contracts, the rule of
Definition 16.2 preserves (GT.6) for all $0\le j\le N$. Every matched
modifier has exactly the label $\varepsilon_j$, and the actual encoded
source successor is $E(t_j)$, including at a refusal followed by any
later acceptance. Both $H_j$ and $K_j$ are nondecreasing. No restriction
is placed on the finite order of Rho, Left and Right or on the sizes,
labels or brackets of their nonempty operands.

*Proof.* At $j=0$ the asserted relation is the stipulated start. Suppose
it holds through $j-1$. The reference source fits its previous guard;
since $h_j\ge h_{j-1}$ it also fits $h_j$. Reserve followed by Raise
therefore publishes that guard lawfully without changing $t_{j-1}$.
The reference modifier has exactly (GT.5)'s whole-candidate outcome.

On the encoded side apply Theorem 16.1 with
$t=t_{j-1}$, $h_-=h_{j-1}$ and $h=h_j$. It gives
$G_j\ge H_{j-1}$ and the correct actual modifier branch. Since
$K_{j-1}=\max(K_0,H_{j-1})$, also
$J_j=\max(K_0,G_j)\ge K_{j-1}$. If a reserve is needed it strictly
extends the current backing while preserving the source. A subsequent
strict raise has $H_{j-1}<G_j\le J_j$; if no raise is needed the guard
is already $G_j$. Thus all scheduled maintenance has an allowed strict
branch, and the encoded modifier starts with source $E(t_{j-1})$ and
guard $G_j$. By (GT.8) its label is $\varepsilon_j$ and its source
successor is precisely $E(t_j)$. Equation (GT.9) gives
$G_j=\max(h_j,w(t_j))=H_j$, and its reserve is then $J_j=K_j$.
This closes the induction and proves both monotonicities.

In particular a refusal does not create a persistent encoded surplus:
its endpoint guard is exactly $\max(h_j,w(t_{j-1}))$. A later request
is assessed afresh with its actual operand. No rule forbids a later
acceptance or requires all refused candidates to be below a preselected
future maximum. $\square$

## 17. Attainment on the continuing CAP/ARC occurrence

**Proposition 17.1 (two actual substitutions at the reached preparation).**
Under Assumption 15.3, the encoded initial cut required by Theorem 16.3
is reached from $p$ on the same source occurrence by at most four
complete calls: Reserve$(\max(K_0,H_0))$ and Raise$(H_0)$ when strictly
needed, followed by two original Rho calls. Both Rho calls accept.
Their actual completed Ready endpoint has source $E(t_0)$, guard $H_0$
and reserve $\max(K_0,H_0)$.

*Proof.* The two maintenance targets are nondecreasing and lawful by
$H_0\ge h_0$ and $\max(K_0,H_0)\ge K_0,H_0$. CAP Theorems 5.2–5.3
preserve $t_0$, $\xi$ and all old handles while extending its actual
$\phi_K$. Along two substitutions the candidate leaf counts obey

$$
n(t_0)\le n(\rho t_0)\le n(\rho^2t_0)=w(t_0)\le H_0,
\tag{GT.12}
$$

by the original composition update. Hence both whole Rho candidates
accept. Every call is the installed outer01 path, and CAP Lemma 6.7
and Proposition 5.5 provide its complete row/dependency/ACK/source-token/
idle/InnerReturn/CaptureCAP return before the next call. The final value
is the actual result of these two substitutions; it is not written from
an acquired copy, freshly prepared on another source, or inferred from
an even global counter alone. $\square$

**Theorem 17.2 (paid acquired-material Ready realization).** Under
Assumption 15.3, every finite schedule and request word of Definition
15.2 has the following two alternative finite continuations from $p$.
The reference uses its published guard schedule and original whole
requests; the encoded continuation uses Proposition 17.1 and Definition
16.2. At each designated matched completed Ready boundary they satisfy
(GT.6), every paired modifier has the same original
accept/executed-refusal label, and its actual encoded source successor is
$E$ of the reference source successor. All entries use the existing
outer01/$F^A$ supplier; no new source action, source entrance, return or
current actor capability is required.

*Proof.* Use the arithmetic selection of Definition 16.2 on the actual
early acquired words. This computes the guard targets and the original
and encoded frames, without presuming an actual source reply. Counts
from $t_0$ are valid by its acquired current syntax. Theorem 16.3 shows
inductively that the syntax and count updates, once their corresponding
calls complete, describe the actual source related by (GT.6). Retained
computed syntax is distinguished from a fresh source observation; its
validity here comes from the acquired start and the proved actual
successor relation. Its construction, checking, copying and immutable
retention still require their own paid finite work. The next operand
and its encoding are present before that round's prelude by Assumption
15.3, so the selection never reads a future Busy-ingress value.

At any reached Ready, the full call has the following actual order.
First the outer01 receiver performs its choice Base, literal reception,
seal, descriptor construction and import, and enters $F^A$ at its header
Base/setup prelude before any header IN. It acquires the canonical frame,
retains and parses the complete request, obtains the current source-service
admission and executes ReadState. A maintenance uses CAP Definition 5.1;
a modifier uses CAP Definition 4.4 with its actual current guard. Its
source operands and destinations are resolved by the path's current
$\phi_K$, including temporary raw source words. No old generated gate
tape is reused after a guard or layout change.

The modifier frames are literally `0010` for Rho and tag `011` or `100`,
$U(3w(v)-1)$ and the complete original prefix code of $E(v)$ for the
encoded Left or Right. Maintenance retains tags `101` and `110` with
the complete $U(J+1)U(J)$ length/payload fields. No new opcode or
provenance operand is inserted into a canonical modifier frame.

The operation then performs its genuine response commitment and applicable
counter updates, semantic/unified row construction, all required dependency
and row copies, complete receiver checks and final row ACK. It performs
the source-token TOK and idle CTL. The unchanged $F^A$ return successor
then enters InnerReturn, normalizes the dead public workspace and heads,
and reaches CaptureCAP. The closed 28/29 import resolves the actual newly
delivered row and all dependencies through their acquired local origins,
appends the complete cycle item to $M$, restores the archive heads, and
returns to the next Ready. These are CAP Lemma 6.7 and Definitions
4.1, 5.2, 5.4 and Proposition 5.5, with their real current token and
owned-backing hypotheses. An intermediate copy-completion TOK is not
substituted for the final row ACK.

A reference refusal and its encoded mate both take the original executed
refusal route: full context acquisition/validation, candidate generation,
whole guard/MUX work, response, rows and the same complete return all
remain. Neither is a Busy attempt, malformed frame, absent read or an
unexecuted unauthorized none. A strict maintenance preserves the source
and the protected client while publishing its actual layout or guard;
its row retains that historical guard and all before/after fields.
A requested value never becomes an unpaid assignment to $h$ or $K$.

Each selected frame is finite and canonical. CAP's local-progress and
finite-supply hypotheses give the finite completion of every displayed
call. Proposition 17.1 establishes the encoded start; induction over the
finite rounds then applies Theorem 16.3 at the actual returned cuts.
There are only finitely many such calls at each finite $N$, so composing
their returns is finite without a uniform deadline. No two calls overlap
and no partial token-transfer cut supplies another entry.

The reference and encoded paths retain their different actual complete
successors, input bits, layouts, counters and receipts. The common
preparation is not executed twice within either path, and neither
continuation is callable from the other endpoint. The construction is a
relation on alternatives of the one occurrence and introduces no clone,
reset, second private preparation or independent source register.
The reference uses (GT.4)'s announced guards; the encoded path uses
(GT.9)'s announced guards. Only the displayed modifier labels and source
relation are compared, not these different historical guard contracts
or their complete original responses. $\square$

**Corollary 17.3 (retained image at the matched cuts).** Every encoded
cut $\widehat p_j$ in Theorem 17.2 has its actual source in
$E[\mathcal T]$. If its complete current ordered source shape, or its
complete current ordered support, is additionally lawfully acquired with
its current binding and paid retention, ABT Theorem 12.1 recovers exactly
$t_j$ from that acquired image. For every $r\ge0$, a lawfully acquired
current erased prefix through radius $r+1$, or current presence prefix
through radius $r+2$, determines the reference labeled prefix through
radius $r$ on this actual image. No shape or support acquisition is
supplied by this corollary.

*Proof.* Equation (GT.6), established from actual operations, witnesses
image membership by $t_j$. ABT12's existing inverse $D$ applied to the
current $\operatorname{sh}(E(t_j))$ equals $t_j$; full ordered support
first determines that same shape. The acquired-observation premise is
independent of the source equation and supplies the material on which
that inverse can be evaluated. NESK's two_step_prefix_kernel has the
same source pair, ordered addresses and radius shift, so its finite-prefix
conclusion applies on precisely those inputs. A global accepted-Rho count
alone would not establish this image premise after arbitrary grafts,
as ABT18 already shows. During in-place raw overwrites the packet need
not parse at all; at an intermediate maintenance Ready the active guard
can already be $G_j$ while the source is still $E(t_{j-1})$.
Neither cut is a matched post-round cut for (GT.6). $\square$

## 18. Parameter bounds, selected ingress and refusal examples

**Theorem 18.1 (exact retained reserve and limited call bounds).** On the
encoded continuation of Theorem 17.2, for every $0\le j\le N$,

$$
\begin{aligned}
w(t_j)&\le H_j\le3h_j,\\
K_j&=\max(K_0,H_j)\le\max(K_0,3h_j).
\end{aligned}
\tag{GT.13}
$$

The designated source payload at that boundary has exactly $4K_j-2$
bit cells. The number of freshly designated source payload cells added
since $p$, including the encoded preparation, is exactly
$4(K_j-K_0)$. This is not the arena/scratch or total retained-storage
count. The encoded preparation and first $N$ rounds require at most
$3N+4$ complete outer01 calls; the reference rounds require at most
$3N$. These bounds omit the already completed preparation/acquisition
of $p$ and count no additional acquisition or read calls.

*Proof.* By (GT.5), $n(t_j)\le h_j$. The supplier inequality
$w(t_j)\le3n(t_j)$ and $H_j=\max(h_j,w(t_j))$ give (GT.13).
The maximum with $K_0$ is necessary even if $K_0>3h_j$.
CAP Definition 4.1 designates $L(K)=4K-2$ logical source bit cells.
Every strict Reserve adds exactly $4(J-K)$ such cells and never replaces
or copies an old designated source payload cell into a new one. Since
all selected reserves are nondecreasing and the last is $K_j$, summing
their differences from the initial actual $K_0$ telescopes to the stated
fresh-cell count. Their delimiters, directory records and separate
scratch allocations do not belong to this subtotal.

Proposition 17.1 uses two Rho and at most two maintenance calls. Each
round adds one whole modifier and at most one Reserve and one Raise.
The same latter bound applies to the reference rounds without encoded
preparation. Every counted call is complete, including refused modifiers;
its internal primitive length is not bounded by counting it once.
$\square$

**Proposition 18.2 (exact selected external ingress).** Let $r$ be the
number of Rho requests among the $N$ rounds, let $\mathcal G$ index all
graft requests, and let $\mathcal M$ list the actually performed encoded
Reserve/Raise calls, including those in Proposition 17.1. Write $J$ for
each such call's supplied parameter. The total number of external input
bits at the outer-choice and source-frame IN sites of these selected
encoded calls, measured after $p$, is exactly

$$
I_{\rm selected}
=12+6r+\sum_{j\in\mathcal G}(6w(v_j)+4)
       +\sum_{(\mathrm{kind},J)\in\mathcal M}(2J+8).
\tag{GT.14}
$$

All requests, accepted or refused, occur in this formula. In particular
$|\mathcal M|\le2N+2$ and each such $J\le K_N$. The sum is solely the
specified external ingress, with no bound on total work, tariff or storage.

*Proof.* Each selected call first supplies the two literal outer01 bits.
A Rho source frame is `0010`, contributing four more bits; the two
preparatory Rho calls therefore contribute twelve together. A context
with $m$ leaves has the existing prefix-code payload length $d=3m-1$
from (SW.12). Its source frame has three tag bits, $d+1$ unary length
bits and $d$ payload bits, totaling $6m+2$; its outer choice gives
$6m+4$. Here $m=n(E(v_j))=w(v_j)$ regardless of the eventual guard
outcome. A maintenance source frame is
$\mathrm{tag}\,U(J+1)\,U(J)$, with $3+(J+2)+(J+1)=2J+6$
bits; its outer choice gives $2J+8$. Summing gives (GT.14).
There are at most two maintenance calls per round and two in preparation.
Their parameters are the selected $H_j$ or $K_j$, so monotonicity puts
them below $K_N$. This count does not include descriptor/status work,
ordinary writes of received bits, early operand acquisition, computations
which build these words, row/dependency copies, captured cycle material,
or any output. Each of those keeps its separate original bill.
$\square$

**Proposition 18.3 (mixed refusals and later accepts with preserved initial
reserve).** There is an instance of Theorem 17.2 with
$t_0=\beta$, $h_0=3$, $K_0=12$, and the following seven rounds.
Let $v=\langle\langle\alpha,\alpha\rangle,\alpha\rangle$.
The pair $(a,b)$ in the table is the reference post-round composition.

| $j$ | $h_j$ | Whole request | $\ell_j$ | $d_j$ | Label | Post $(a,b)$ | $H_j$ | $K_j$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | 3 | Left$(v)$ | 4 | 9 | refuse | $(0,1)$ | 3 | 12 |
| 2 | 3 | Right$(\beta)$ | 2 | 6 | accept | $(0,2)$ | 6 | 12 |
| 3 | 3 | Rho | 4 | 10 | refuse | $(0,2)$ | 6 | 12 |
| 4 | 4 | Rho | 4 | 10 | accept | $(2,2)$ | 10 | 12 |
| 5 | 5 | Left$(\alpha)$ | 5 | 12 | accept | $(3,2)$ | 12 | 12 |
| 6 | 5 | Right$(\alpha)$ | 6 | 14 | refuse | $(3,2)$ | 12 | 12 |
| 7 | 6 | Right$(\alpha)$ | 6 | 14 | accept | $(4,2)$ | 14 | 14 |

*Proof.* From the authentic beta boot, Reserve(12), Raise(3) and their
complete returns attain the displayed initial source and parameters.
Its acquired beta syntax remains current through these maintenance
calls. Take all displayed operands and their encodings as actually
acquired early finite material with the backing and permissions of
Assumption 15.3. The initial encoded preparation has $H_0=3$ and reserve
12; its two Rho calls accept. Substitution sends $(a,b)$ to $(b,a+b)$,
while a graft adds its operand's pair. These updates and (GT.11) give
each table entry. The actual CAP guard comparisons give the labels in
both alternatives by Theorem 16.1, and Theorem 17.2 supplies every full
return. The first refusal precedes an acceptance at the same reference
guard; later repeated Rho and Right requests change from refusal to
acceptance when the reference schedule rises. Throughout the first six
rounds the initial reserve 12 is retained although the active encoded
guard is smaller at several cuts. $\square$

**Proposition 18.4 (unscheduled surplus and unbounded refused material).**
The source relation alone, with a larger arbitrary encoded guard, does
not preserve refusal. Also, a bound on the selected guard and number of
complete calls does not bound their context ingress or total work.

*Proof.* At the authentic reference beta/$h=1$ cut, Right$(\alpha)$
refuses: its candidate has two leaves. The encoded preparation has source
$E(\beta)$ with three leaves and guard 3. If one instead completes the
additional lawful Reserve(5), Raise(5), then requests Right$(E(\alpha))$,
its whole candidate has $3+2=5$ leaves and accepts. These are existing
canonical operations and full returned alternatives. The extra raise
violates (GT.6) and the refusal interval (GT.8); it cannot be hidden as
source-preserving maintenance in this relation.

For the second assertion keep the correctly matched encoded source
$E(\beta)$, guard 3 and its fixed reserve. For each $m\ge1$ let $v_m$
be a fixed ordered bracketing of $m$ alpha leaves. The reference at
$h=1$ refuses Left$(v_m)$, and the selected encoded call refuses
Left$(E(v_m))$ without increasing guard or reserve: its candidate has
$3+2m>3$ leaves. There is exactly one modifier call, while its selected
outer/source ingress has $6w(v_m)+4=12m+4$ bits, unbounded in $m$.
All are early acquired finite operands in their respective instances.
The input occurrences themselves are paid, so even this portion of work
has no uniform bound from guard and call count alone. $\square$

**Definition 18.5 (complete resource scope).** The full accounting is
Definition 14.5's vector, including acquisition of current syntax and
counts; encoding, arithmetic and planning; contexts and immutable
backing; copying, unary frame and descriptor construction; maintenance;
all candidate work including refused candidates; primitives, counters,
rows/dependencies and their checks/ACKs; returns, captures, retention and
output. For each actual finite primitive prefix $z$, use CAP Theorem
7.2's own quantities $\nu(z)$, $A_{\rm phys}(z)$ and $b_{\rm ctl}(z)$:

$$
\operatorname{Bill}(z)=
\bigl(\nu(z),2\nu(z),
 S_0+b_{\rm ctl}(z)+8A_{\rm phys}(z)+8\nu(z)\bigr).
\tag{GT.15}
$$

This is the same-run primitive convention, with GENERAL's independently
specified foundation/tariff when that supplier is used. It accounts for
the actual native prefix on which its variables are measured. Any
material preparation or calculation outside that prefix retains its own
charge in the full accounting vector, without an unproved conversion to
CAP ticks. The finite calculation in Definition 16.2 does not install
an actor planner. The old $p$
acquisition/boot prefix and every later actual expense remain included
in the full run even when (GT.14) starts after $p$. The designated
$4K_j-2$ source bits, arena/scratch, retained operand/encoding blocks and
total constructed storage are distinct coordinates. Retired material
and all receipts remain retained. Equations (GT.13)–(GT.14) give no
cross-path equality, total-cost dominance or optimum, operation rate,
throughput, uniform deadline, infinite completion or boot-time common
future maximum.

## 19. Supplier correspondence and scope of the relation

**References 19.1 (mathematical ownership and parameter map).** The
request-dependent guard intervals, their selected monotone composition
and its actual acquired-material completed-cut realization are
repo-derived consequences in §§16–17. Their suppliers are the following
statements with their original hypotheses.

| Supplier | Use in the relation and retained condition |
| --- | --- |
| [ABT](RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BOUNDARY_TRICHOTOMY.md), Theorem 12.1 and §§18–23 | The actual two-step shape inverse and the distinction between current image and global epoch; the request-independent obstruction of Definition 19.1/Theorem 19.3; the fixed-guard interval and fixed-guard positive classes of Theorems 22.2–22.3. Here guards depend on the early acquired individual request and are maintained between whole calls. Neither their obstruction class nor their fixed-guard theorem already supplies this mixed monotone invariant. |
| ABT §§24–32 | Attained varying-capacity original responses, fixed-numeral positive classes, and the precise Presburger/synchronous-word/fixed-matrix representation boundaries. The paid growing syntax and count calculations of (GT.11) do not assume a fixed finite response formula in any of those excluded languages. No such automatic representation is asserted. |
| [ER](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_ENTRY_REFERENCE_AND_GRAFT_ORDER.md), Theorem 9.8 | Fixed two-step homomorphic transport with the exact encoded graft constant, under its own one-graft initializer and ternary menu. Its support/history inverse needs that initialized ancestry-antichain domain. Arbitrary operands and refusals here do not satisfy that history-inverse premise. |
| [CAP](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CAPACITY_COHERENCE_AND_GROWTH.md), §§1–7 | The original nonempty trees, full candidate guard, actual seven-tag frames, continuing source16/$\phi_K$, lawful Reserve/Raise, historical counters/guards, complete rows/dependencies, current admission, checks/ACK and paid returns. In particular Lemma 6.7 includes executed refusal and keeps its complete successor. |
| ARC, Definitions 4.1, 5.1–5.4, Proposition 5.5 and §§12–14 | The actual parked-client outer01/$F^A$/InnerReturn/CaptureCAP consumer and beta-boot preparation. The accepted command/operand chronology and its write frontier remain their own results; no inverse of a refusal history is inferred. |
| [NCE](RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CROSS_EPOCH_RELATIONS.md), §§13–14 | The authentic beta-boot source class and its full finite-return premise. Its acquired-source and original-label scope is retained; the algebraic all-alpha starts do not become operational beta-boot starts. |
| [GenealogicalFiberTransport](../../../D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.lean) and its [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport.scribe.cs) | Source is FreeMagma Bool, true=alpha, false=beta; substitution is its magma homomorphism, composition is the actual leaf pair, and one_step/transport inside fiberMap give the common-tree composition evolution. Probability transport, Catalan fiber counts and cardinality conclusions are not used as source services. |
| [NativeErasedSupportKernels](../../../D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativeErasedSupportKernels.lean) and its [Scribe](../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativeErasedSupportKernels.scribe.cs) | Its actual two-step prefix kernels, with root_reflection, sharp_forward, erased_reflection, erased_reply_presence, erased_support and labeled_iterates, use the same finite trees, false=L/true=R addresses and inclusive radii. Only Corollary 17.3 uses the resulting inverse under its actual current-image and acquired-observation premises. |

**Definition 19.2 (comparison with simulation reference frames).** In
Lynch–Vaandrager, *Forward and Backward Simulations, Part I: Untimed
Systems*, [§3.2](https://groups.csail.mit.edu/tds/papers/Lynch/IC95.pdf), a
forward simulation $f$ from $A$ to $B$ covers initial states and requires,
for every step $s'\mathrel{\smash{\xrightarrow{a}}}s$ and every
$u'\in f[s']$, a finite $B$ execution fragment from $u'$ to some
$u\in f[s]$ with the same external trace $\widehat a$.
The finite-fragment matching discipline is literature-attested.
For the present source projection, the initial pair is $p,\widehat p_0$;
a reference round consists of its guard publication and whole modifier;
its explicitly constructed matching fragment is Definition 16.2's
maintenance followed by the encoded whole modifier. The corresponding
finite endpoint obligation is exactly (GT.6), and the selected modifier
label is preserved by Theorem 16.1.

This correspondence concerns selected macro endpoints and projections.
The actual external traces include different maintenance frames, encoded
operand bits and all original call/return labels. They have not been
shown equal. Thus no forward simulation of the complete original labeled
systems is inferred from the source projection. Any such application
would additionally have to specify and prove the external-alphabet map,
all initial coverage and every actual step/continuation condition; merely
calling maintenance internal would not discharge them.

In Reissig–Weber–Rungger, *Feedback Refinement Relations for the Synthesis
of Symbolic Controllers*, [Definition V.2 and §IV](https://arxiv.org/pdf/1503.03715v3),
the simple systems have the form
$S_i=(X_i,X_i,U_i,U_i,X_i,F_i,\mathrm{id})$, with $U_2\subseteq U_1$.
For a strict relation $Q\subseteq X_1\times X_2$ their conditions are,
for every related $(x_1,x_2)$,

$$
U_{S_2}(x_2)\subseteq U_{S_1}(x_1),\qquad
u\in U_{S_2}(x_2)\Longrightarrow
Q(F_1(x_1,u))\subseteq F_2(x_2,u),
\quad U_S(x)=\{u:F(x,u)\ne\varnothing\}.
\tag{GT.16}
$$

The input $u$ is the same on both sides. Their preceding information
counterexamples distinguish a refinement's dependence on unavailable
concrete state and on history absent from a static concrete controller.
In the present correspondence, the prospective concrete state is an
actual encoded Ready state with its owned backing, the reference state
is its paired source/guard state, and a reference input is a whole
request with its announced guard. Our construction changes that input
into a finite sequence with encoded operands and request-dependent
maintenance. It therefore is not an automatic instance of (GT.16).
Assumption 15.3 makes the needed current syntax/counts and next operand
material explicit; Theorem 17.2 proves only the stated conditional
finite-sequence relation. Neither reference supplies this early material,
a controller, completion, or the claimed source-specific guard inequalities.

**Definition 19.3 (remaining recovery domain).** The relation preserves
actual current source image and the existing modifier label only at the
scheduled matched completed Ready cuts. Complete original responses and
successors, literal reads and their legal menus, failures/refusals,
authorities, row histories and resource coordinates all keep their source
definitions; equality of the selected label is not equality of any of
those complete objects. No original-$Q$ or four-view equivalence, complete
history recovery, source acquisition, new decoder, autonomous planner,
current parked-client caller, physical execution or source bridge follows.

Arbitrary Busy, raw partial-overwrite, malformed/bootstrap/unfinished,
annex and changed-return cuts, arbitrary unscheduled maintenance and
all other lawful original experiments are outside this positive relation,
without being removed from the machine. The original final00 route,
INITIAL target/verifier and absorbing halt remain unchanged. No matched
post-terminal cut or terminal extension is asserted. The actual source
image used by Corollary 17.3 is earned by the completed operation
induction, whereas acquiring its current shape/support and using it
lawfully remain separate paid premises. The broader mutual recovery of
space, continuation/time, boundary and memory retains its other
source-specific acquisition, operation, continuation and resource
obligations.

## 追加锚（本行以下为增补区）

## 20. Late operand content and irreversible guard surplus

**Definition 20.1 (direct transport with late distinguishing material).**
Fix an integer $m\ge2$ and the authentic GENERAL/ARC beta-boot occurrence
of Definition 9.1, ABT Definition 18.1 and NCE Convention 13.1. Retain
$H_{\rm boot}=1$, $\xi$, source16, the continuing $\phi_K$, the acquired
beta seed with its actual origin/epoch, parked original client, occupied
verifier and INITIAL consumer. Complete Reserve$(m+1)$ and Raise$(m+1)$
to reach $p$ with source $\beta$ and $h=K=m+1$. The reference starts at
$p$. Its encoded alternative completes two original Rho calls, reaching
$E(\beta)$ with that same guard/reserve: their candidates have two and
three leaves, both within $m+1$. These are alternative extensions of one
occurrence, without reset, clone or new preparation. CAP Theorems
4.5, 5.2–5.3 and Lemma 6.7, this volume's Proposition 5.5 and GENERAL
Lemma 8.1 give these actual source values and complete returns, as in
Proposition 17.1; only its source preparation is used, not Assumption
15.3's early operand supply.

Reuse ABT Definition 19.2's ordered trees
$P_1(z)=z$, $P_{r+1}(z)=\langle P_r(z),z\rangle$. Compare

$$
W_\gamma=
\bigl(\operatorname{Right}(P_m(\gamma)),
      \operatorname{Right}(\alpha)\bigr),\qquad
\gamma\in\{\alpha,\beta\},
\tag{LI.1}
$$

at the fixed reference guard $m+1$. Each modifier must map to exactly one
complete original Right$(E(v))$, with its whole canonical operand. At
each matched returned cut require only the same accept/executed-refusal
label and encoded logical source $E(t')$ for the reference successor
$t'$. Impose no exact encoded guard/reserve endpoint such as (GT.6).

A single deterministic preparation rule starts at the same encoded
prefix in the two cases. Before and between mapped modifiers it may use
any finite lawful source-preserving read, local or history work and any
paid lawful Reserve/Raise, using all information actually acquired then.
The tested class uses no source-changing repair, replacement encoding or
multi-modifier realization. This restricts the tested correspondence,
not the original apparatus or any of its other lawful menu entries.

The information premise is equality of the rule's **complete usable
observation histories through its final effective first guard choice**.
This includes acquired backing and rows, origins, epochs, current rights,
tokens, clocks/status and certificates, and every usable read or input
outcome of its preparation. No branch-distinguishing operand material,
encoded length or other separating observation is usable there. Request
kinds, reference guards and original operand shapes/sizes may be known
if actually supplied. The first operands have the same ordered shape,
$m$ leaves and original prefix-code length $3m-1$; these equalities alone
do not imply the information premise or install a shape/size service.
Any already owned/readable original operand, encoded length, weight or
other lawful discriminator must be retained; if it separates these
cases, this premise fails.

The effective guard is the authoritative current producer-directory
guard used by the first mapped whole call. Equality must persist through
every opportunity to change it before that call, not just through an
earlier provisional Raise. Thereafter grant complete truthful encoded
ingress, including its possibly distinguishing length and payload, at
all prescribed IN sites with all original charges. CAP Definitions 1.4,
4.6 and 5.1 supply no maintenance callback during Busy ingress; later
complete returns enable further lawful maintenance but no guard decrease.
AIF Definition 2.2's future supply choices are not earlier adapter data.

**Proposition 20.2 (two-round late-content obstruction).** For every
$m\ge2$, every finite-returning rule in Definition 20.1 fails on at least
one displayed word: either its first $W_\beta$ label/source successor is
wrong, or its second $W_\alpha$ label/source successor is wrong. Both
reference words actually release
$(\mathsf{accept},\mathsf{executed\text{-}refusal})$.

*Proof.* The reference first candidate
$t_\gamma=\langle\beta,P_m(\gamma)\rangle$ has $m+1$ leaves and
accepts. Its second candidate $\langle t_\gamma,\alpha\rangle$ has
$m+2$ leaves, so the complete second call refuses and retains
$t_\gamma$. These are canonical nonempty finite operands, including the
refused one, in CAP Definition 1.2's original task domain.

Determinism and the full observation premise force a common final first
guard $G$, including any intervening lawful preparation and maintenance.
Reuse (GT.1)–(GT.3) and CAP's whole-candidate test used in Theorem 16.1:

$$
n(E(\beta))=3,\qquad
n(E(P_m(\alpha)))=2m,\qquad n(E(P_m(\beta)))=3m.
\tag{LI.2}
$$

Thus the first beta-side candidate has $3+3m$ leaves. If $G<3+3m$,
it refuses and keeps $E(\beta)$, whereas the reference accepts and
requires $E(t_\beta)$, whose leaf count is strictly larger. Both the
label and the source requirement fail on that first call.

Otherwise $G\ge3+3m$. The first alpha-side candidate has $3+2m$ leaves,
so it accepts and installs exactly $E(t_\alpha)$ by the supplied
homomorphism. All allowed inter-call work preserves this source. CAP's
actual maintenance rules give $G_2\ge G$ for the guard used by its next
whole call, even after it learns the complete operand and history. But

$$
n\langle E(t_\alpha),E(\alpha)\rangle
 =5+2m\le3+3m\le G\le G_2\qquad(m\ge2).
\tag{LI.3}
$$

The second encoded call therefore accepts instead of refusing. Its
actual source is $\langle E(t_\alpha),E(\alpha)\rangle$, with two more
leaves than $E(t_\alpha)$, so it also fails the required successor
relation. No exact guard endpoint from (GT.6) was used.

For $m=2$, $p$ has guard/reserve 3. Both original first operands have
two leaves and code length 5; the reference candidate counts are 3 then
4, yielding acceptance then executed refusal. The encoded first counts
are 7 and 9. Correct beta-side acceptance forces $G\ge9$; the alpha
side's second candidate has exactly 9 leaves and accepts at any retained
or raised guard. Each word separately is transportable when its early
material is actually supplied: Theorems 16.1 and 17.2 permit respective
first guards $3+2m$ and $3+3m$, held through the second call. The conflict
is the common early choice, not the existence of either separate word.
$\square$

**Corollary 20.3 (necessary early separation for the direct consumer).**
Any deterministic direct whole-graft rule with Definition 20.1's
operations and endpoint requirements that transports all finite words
must lawfully separate the two first operands in (LI.1) before its first
effective irreversible guard choice. Eventual exact material and
retrospective authentication alone cannot replace that distinction.
This requires neither full early syntax, an exact count, nor any
particular certificate format.

*Proof.* Otherwise the two histories satisfy Definition 20.1's equality
through the final choice, and Proposition 20.2 contradicts success on
both. A later read or completed return cannot withdraw the surplus in
(LI.3). An actual early discriminator removes that premise and is not
excluded by this corollary. $\square$

**Convention 20.4 (reuse, costs and remaining recovery obligation).**
This source-specific temporal consequence is repo-derived. ABT
Definition 19.1/Theorem 19.3 exclude one request-independent scalar for
an entire entry menu, with different original sizes and first labels.
Here preparation may depend on actual request observations, and both
equal-size first requests accept. ABT Theorems 22.2–22.3 give the exact
fixed-guard whole-menu interval and its slack-0/1 positive classes.
Here slack is $m\ge2$, only two words are tested, guards may adapt
between calls, and their first rounds alone admit a common guard.
Theorem 16.1 already supplies the inequalities, and Proposition 18.4
already shows a surplus can spoil refusal. The added necessity forces
that surplus from correct service of an indistinguishable alternative;
later truthful material cannot repair it. Deterministic
indistinguishability is a mature method, not an originality claim. The
primary simulation/refinement comparisons and their information limits
remain those of Definition 19.2; neither supplies early native material.
No worldwide or corpus-wide novelty claim is made.

All calls retain the installed outer01/$F^A$ route, actual current
admission and permissions, ReadState and current $\phi_K$ resolution,
complete canonical ingress/validation, whole candidate and guard work
including refusals, response/counters, rows and all dependencies,
receiver checks, final row ACK, source TOK, idle CTL, InnerReturn,
CaptureCAP and next Ready, as in Theorem 17.2. No call overlaps another.
Premature, Busy, malformed or terminal routes cannot replace the paired
completed label/source cuts. The acquired seed, every existing row,
archive/menu, backing, permission and service contract remain intact.
Definition 18.5's full vector charges acquisition, count/encoding/planning,
original/encoded copies and immutable backing, maintenance, accepted and
refused work, primitive receipts/ticks/fees, checks/ACKs, returns/captures,
retention and output. Its CAP Bill applies only to its measured native
prefix; outside material work and GENERAL's independent foundation/tariff
remain separately charged. No cross-path cost equality, optimum, deadline,
throughput or storage bound follows.

Only finitely many preterminal completed Ready calls are considered,
conditional on actual finite supply and termination of reached local
computations. Original final00, INITIAL verification/output and absorbing
halt remain available but uninvoked; no Busy/posthalt entry or physical
completion follows. The remaining task for weakening Assumption 15.3
is a genuinely lawful, timely separating acquisition for the existing
decision path, or a separately proved alternative operation mapping.
No preview service, planner, new owner, sufficient certificate interface,
all-protocol impossibility, full-$Q$ equivalence, four-view completion or
native/diffusion/AURIC source identification is supplied. The broader
same-source mutual-recovery goal retains these acquisition, operation
and resource obligations.

## 追加锚（本行以下为增补区）

## 21. Late raw operands at a tight encoded boundary

**Definition 21.1 (late-material supplied-frame domain).** Let $P$ be the
first actual Ready of Definition 9.1 and NCE Convention 13.1, with source
$\beta$, $H_{\rm boot}=h=K=1$, acquired beta seed and its actual binding,
source occurrence $\xi$, source16 and continuing $\phi_K$, parked original
client, verifier and INITIAL consumer. Use Definition 15.2 with
$t_0=\beta$, $h_0=K_0=1$: every finite $N\ge0$, every actually announced
finite nondecreasing schedule $1=h_0\le\cdots\le h_N$, and every finite
mixed word of whole Rho, Left$(v)$ and Right$(v)$. Each operand is any
nonempty finite ordered alpha/beta tree. There is no common size or depth
bound. The reference continuation keeps exactly its original guard
publications, whole-candidate outcomes $\varepsilon_j$ and successors
$t_j$ of (GT.5).

Retain Assumption 15.3's owned immutable backing, current rights, actual
next reference guard and request kind at each round's authorized
preparation cut. Replace only its advance operand/encoding requirement: a whole raw graft frame is
actually supplied at the existing outer01/$F^A$ IN sites, but the
continuing consumer need not own $v$, its counts, its encoded length or
$E(v)$ before this first call. The raw-frame supplier still supplies the
whole actual operand; that input obligation is retained. The timing claim
concerns the continuing consumer, not earlier possession by the supplier.
The complete return must precede the continuing consumer's computation
using its newly acquired operand. Material already
available in an instance remains available and retained; no discriminator,
row, permission or service is deleted to make this timing premise hold.

The counts initially come from the acquired beta seed, $(a_0,b_0)=(0,1)$.
Their subsequent owned representations and syntax descriptions are paid
derived data, updated only after the actual final outcomes specified
below. This is the seed-and-successor justification of Theorem 17.2,
not a count sensor, a fresh source snapshot, or an inference from the
global accepted-Rho epoch. Every retained description carries its
actual lineage; its present use requires current read permission.

After the complete acquisition return, use Definition 16.2's finite paid
parsing, tree traversal, substitution, arithmetic and comparison on that
owned material. Every resulting maintenance and encoded modifier frame
must subsequently be supplied **anew** at its prescribed original IN
sites. The pointwise finite-input and reached-local-computation premises
of Assumption 1.2 apply to every displayed call and calculation. They give
neither a deadline nor an automatic supplier. Selecting a finite
continuation at this supplied-frame level does not install these
calculations or a bank-to-IN route in the parked client or in $F^A$.
A computed bank word alone is not a later IN occurrence.

**Definition 21.2 (designated tight relation).** Keep $E=\rho^2$,
$n=a+b$ and $w=2a+3b$ from (GT.1). At designated encoded endpoints
$\widehat p_j$ compare with the reference endpoints $p_j$ by

$$
\begin{gathered}
\pi_{\rm src}(p_j)=t_j,\qquad (h,K)(p_j)=(h_j,h_j),\\
\pi_{\rm src}(\widehat p_j)=E(t_j),\qquad
(h,K)(\widehat p_j)=(H_j,K_j)=(w(t_j),w(t_j)).
\end{gathered}
\tag{LA.1}
$$

The minimum-reserve policy in (LA.1) belongs to this construction.
It is a different relation from (GT.6): there is no encoded requirement
$H_j\ge h_j$, and no automatic mirroring of a reference Raise on the
encoded path. Each path keeps its own actual announced guard and task.
The two paths are alternatives of the same $P$, not simultaneous
registers or callable copies.

Here $j=0$ on the encoded path means the fully returned endpoint of
Reserve$(3)$, Raise$(3)$, Rho, Rho. For $j>0$ it means the full return
after round $j$'s designated final modifier. The preceding acquisition
boundary and its returned source-preserving staging boundary are tight
as well. Intermediate maintenance Ready cuts need not satisfy (LA.1);
in particular, after Raise and before an accepting commit the old source
can be strictly smaller than its guard. This is a phase-indexed relation,
not an invariant of every Ready reachable by arbitrary legal choices.

**Proposition 21.3 (source-preserving raw acquisition with an owned
return).** In Definition 21.1's domain, at a designated tight entry with
source $E(t)$ and
$H=K=w(t)$, either original raw graft with any nonempty operand $v$
executes refusal and retains exactly the whole $E(t)$. After its complete
CAP/ARC return, its submitted operand is actual actor-owned readable
material for the next calculation in Definition 21.1. No operand-dependent
guard choice is required before that acquisition.

*Proof.* The original raw candidate has

$$
n\langle v,E(t)\rangle
 =n\langle E(t),v\rangle
 =H+n(v)>H.
\tag{LA.2}
$$

Thus CAP's existing whole-candidate test, including all acquisition,
validation, candidate-generation and guard/MUX work, executes refusal.
CAP Theorem 4.5 reinstates every old logical source bit, hence the
entire ordered $E(t)$, not merely its leaf count. The raw operand may
have any labels and brackets. Only nonemptiness and tightness were
used to select this source-preserving acquisition flight.

Its acquired object is the submitted request, not the unexposed private
candidate. The outer receiver of Definition 5.2 first receives, seals,
describes and imports choice 01. $F^A$ then executes its header Base/setup
and actual raw INs. CAP Definition 4.6 retains the separate sealed
header, unary-length and whole payload blocks on producer ingress13,
with their real descriptors on 17. The original context code is in that
payload; a refusal does not remove its request references.

CAP Definition 6.3's mandatory delivery sends every missing enumerated
request dependency, including header, length and payload, through its
two actual copy stages before the final row ACK. The receiver has its
own constructed intervals on archive28, local descriptors on 29,
actual origin fields, complete seal/status and availability checks.
CAP Theorem 6.4 gives equality to the immutable sender payload while
keeping the distinct owners and physical intervals. Origin matching
does not authorize reading the producer's address.

Wait for both complete row checks and the final row ACK, source-token
TOK and idle CTL, then InnerReturn normalization. Only then perform
the closed-28/29 import and origin-to-local parsing of Definitions
3.1–3.4. Proposition 3.5 identifies the actual delivered request bits.
CaptureCAP appends their IN-site order, row occurrence, origins and
dependencies to $M$, restores the archive heads and reaches Ready by
Proposition 5.5. The operand can now be extracted from the resolved
A-owned, initialized immutable local payload with its actual current
read token. A copied permission flag grants no TOK; an internal
copy-completion TOK is not final row ACK; an unsealed receiver prefix
or a producer-private reference is not usable backing.

This sequence supplies precisely the finite operand on which the later
count/encoding calculation acts. Its capture does not turn archive28
into a private-source snapshot. The continuing consumer's later
calculation uses no operand-dependent information before this completed
join; the producer's earlier ingress, parsing and copy work retain
their actual roles.
The original refusal/copy facts are reused here for this tight
source-specific consumer. $\square$

## 22. Repeated acquisition and selected commit

**Theorem 22.1 (late-material finite mixed continuation).** Under
Definition 21.1, the same authentic occurrence has reference and encoded
alternative finite continuations satisfying (LA.1) for every
$0\le j\le N$. Each designated final encoded modifier has exactly the
reference modifier's original accept/executed-refusal component and
has actual source successor $E$ of its reference successor. The encoded continuation uses
one raw acquisition refusal per graft, one final whole modifier per
round, and only the paid original maintenance described below.
All calls return completely before another begins.

*Proof.* First complete Reserve$(3)$ and Raise$(3)$ from $P$.
Both are strict lawful maintenance and preserve beta, the source
occurrence, old handles and current rights. The next two original Rho
candidates have two and three leaves, respectively, so both accept.
CAP Lemma 6.7 and Proposition 5.5 give a full returned Ready after
each of these four calls. Thus source $E(\beta)$ and $H=K=3=w(\beta)$
are attained, not posited as a new private preparation. The acquired
seed gives the reference pair $(0,1)$; its two-substitution syntax
description is finite paid derived material. This establishes (LA.1)
at zero without a future operand or future guard maximum.

Suppose the last designated endpoint is $E(t)$ with $H=K=w(t)$,
and the retained current reference pair is $(a,b)$. Take the actually
acquired next reference guard $h_j$. For a graft, first perform
Proposition 21.3's whole raw Left$(v)$ or Right$(v)$ at unchanged
$H,K$, and finish its entire owned return. Decode that captured
payload, count its actual leaves by the finite traversal of Definition
16.2, and construct $E(v)$ by two substitutions on its whole syntax.
The construction preserves every ordered branch and label.
Its finite scans, comparison or checking work, copies and immutable
output backing are paid. Set, using those now-acquired counts,

$$
\ell=a+b+a_v+b_v,\qquad
d=H+2a_v+3b_v=H+w(v)>H.
\tag{LA.3}
$$

These are the reused (GT.11) quantities, computed at a later cut.
If $\ell\le h_j$, select Reserve$(d)$, then Raise$(d)$, returning
completely after each, then the same-direction whole encoded graft
Left$(E(v))$ or Right$(E(v))$. Both maintenance calls are strict:
before Reserve, $K=H<d$; after it, $H<d=K$ makes Raise lawful.
They preserve the source and extend the actual address map.
The final candidate has exactly $d$ leaves at guard $d$ and accepts.
By (GT.3)'s ordered-tree homomorphism it is precisely $E(c_{A_j}(t))$.

If $\ell>h_j$, omit both maintenance calls and issue that same whole
encoded graft at the unchanged guard $H$. Its candidate still has
$d>H$ leaves, so it executes refusal and retains $E(t)$. The final
refusing call is actually issued, copied, captured and charged; it is
not replaced by the earlier raw refusal. In either case its label is
$\varepsilon_j$ and the endpoint is tight for $t_j$. On an actual final
acceptance update the owned reference pair to
$(a+a_v,b+b_v)$ and its syntax to the corresponding ordered graft;
on refusal retain $(a,b)$ and $t$. Both descriptions are justified by
the actual branch just proved, not by a hoped-for response.

For an already identified Rho, no operand acquisition is needed.
Compute from the valid retained current pair

$$
\ell=a+2b,\qquad
d=3a+5b=H+\ell>H.
\tag{LA.4}
$$

If $\ell\le h_j$, fully return from Reserve$(d)$ and Raise$(d)$ and
then perform the original whole Rho. Otherwise keep $H,K$ and perform
the original whole Rho directly. Its candidate on $E(t)$ has exactly
$d$ leaves by (GT.3), so its actual label is again $\varepsilon_j$.
On acceptance its source is $\rho(E(t))=E(\rho t)$ and its reference
pair becomes $(b,a+b)$; on refusal source and pair are unchanged.
Thus (LA.1) is restored in both branches. Only accepting final
modifiers strictly increase $H$ and $K$; all refusals preserve them.

For completeness, every actual entry in this construction, including
raw staging, each Reserve, each Raise and every final refusal, uses
its own literal outer01 prelude and $F^A$ frame. The final modifier
frames are Rho $\mathtt{0010}$, or tag $\mathtt{011}$/$\mathtt{100}$
with $U(3w(v)-1)$ and the complete prefix code of $E(v)$.
Raw graft staging instead uses $U(3n(v)-1)$ and the code of $v$.
Maintenance uses its unchanged tag $\mathtt{101}$/$\mathtt{110}$
and $U(d+1)U(d)$. No second provenance operand or new opcode is added.

Each call obtains current source-service admission and executes
ReadState, resolving source operands and destinations through its
actual current $\phi_K$. In particular, code from a previous layout
or guard is not reused as a current gate tape. Its genuine response,
counter/fence work and semantic/unified rows are followed by all
required dependency and row copies, complete receiver checks, final
row ACK, source TOK, idle CTL, InnerReturn, closed-28/29 import,
CaptureCAP, $M$ append, head restoration and Ready. Proposition
21.3 details why this returns the raw operand; CAP Lemma 6.7 and
Proposition 5.5 give the same complete join for maintenance and commit.
No next call begins at a Busy, partial-copy or partial-token cut.

The reference separately performs Definition 15.2's actual Reserve/Raise
publications, then its original whole request. Its guards are
nondecreasing, so $n(t_j)\le h_j$ follows by induction from beta and the
whole-candidate test. The encoded guard need not dominate $h_j$.
We have used (GT.3), (GT.11) and CAP's original test directly, rather
than applying Theorem 16.1 outside its $G\ge\max(H_-,h_j)$ domain.
The statements and domains of §§15–20 remain unchanged.

Every displayed frame and calculation is finite. Definition 21.1
requires actual later supply of the newly determined bits and termination
of the reached calculations, with backing and rights, so the existing
finite-return suppliers apply. Their serial composition is finite for
each finite word. The local cases close an induction on an arbitrary
mixed word, including either direction, all finite operand shapes and
labelings, consecutive refusals, repeated Rho, and a later acceptance
after a reference guard rise. No uniform bound on the operands, number
of rounds or primitive duration was used. $\square$

**Corollary 22.2 (request kind first learned at ingress).** The same result
holds if the next modifier kind is not already available before the
first raw call, provided that every round stages its actual whole raw
modifier and completes the owned return before selection of its final
commit. For a Rho round this adds one real executed refusal.

*Proof.* Grafts are covered by Proposition 21.3. On a tight encoded
source, raw Rho has candidate count $H+(a+2b)>H$ by (LA.4), independently
of any new input operand. It therefore refuses and preserves the source.
Its complete captured frame supplies its actual kind. Apply the
corresponding commit case of Theorem 22.1 after this return; do not update
the reference pair from staging. The same induction applies with one
additional source event for each otherwise unstaged Rho. $\square$

**Definition 22.3 (causal and observational scope).** The acquired
supplier is the existing raw request plus mandatory CAP delivery and ARC
capture. The consumer is the next authentic Ready supplied-frame
continuation of Theorem 17.2, now deciding from completed acquisition,
seed-derived current counts and the acquired reference guard.
The causal order is raw input, source-preserving refusal, complete owned
return, paid parsing/count/encoding, then fresh maintenance/commit input.
AIF Definition 2.2 permits later supplied bits to depend on already
acquired public data; it does not place future choices in an earlier
state or grant another owner access to A's banks. If the matching later
input is withheld or changed, the completion premise fails. Ownership
alone installs no transmitter.

Every staging refusal advances its real source-call count $q$,
semantic count $j_{\rm CAP}$ and all-event count $m$ once, preserves
accepted-modification count $g$ and accepted-Rho epoch $e$, and has its
own complete semantic row, unified row, request references, origins,
receipts, successor and $M$ item. Each maintenance has its own
historical guard/layout fields, response, unified row and $m$ advance,
with no semantic-row advance. Final commits retain their own actual
counter cases and records. None of these events is erased, relabeled
as an unexecuted attempt, or combined into one reference source event.

The paired components are only the designated final modifier label and
the logical-source relation (LA.1). At every intermediate cut, the actual
source, raw state, menu, root-literal and other original read meanings,
rights and complete history remain their original ones. Their equality
across alternatives is not asserted. In particular a newly acquired raw
operand is not a free literal source read. The encoded source stays in
$E[\mathcal T]$ at the designated endpoints; the existing image inverse
and prefix conclusions of Corollary 17.3 apply there only if their
additional current shape/support observations are lawfully acquired and
paid. They create neither those observations nor an inverse source port.

## 23. Attained boundaries and the actual bill

**Proposition 23.1 (surplus boundary and the ARC20 family).** The tight-entry
hypothesis cannot be dropped from Proposition 21.3 in favor of an
arbitrary attained surplus Ready. Under the same current-right,
finite-supply and local-progress premises, every pair (LI.1) has a
separately justified acquisition/commit continuation from its own
specified encoded preparation, preserving the reference's two
designated labels and successors with four visible source calls.

*Proof.* From the same beta-boot $P$, complete Reserve$(4)$, Raise$(4)$,
Rho, Rho. Both substitutions accept and reach $E(\beta)$ with
$H=K=4$. Its raw Right$(\alpha)$ candidate has $3+1=4$ leaves, so it
accepts and changes the source. Thus arbitrary surplus entries do not
supply the general source-preserving acquisition rule.
Also, the intermediate Ready after Raise$(d)$ in an accepting round
has surplus before commit; it is not a new staging entry for the
induction of Theorem 22.1.

For (LI.1), use exactly Definition 20.1's attained $p$ with
$h=K=m+1$ and its two-Rho encoded alternative. That alternative has
source $E(\beta)$ and guard $m+1$. For each $m\ge2$ and
$\gamma\in\{\alpha,\beta\}$ the first raw staging candidate is
Right$(P_m(\gamma))$ and has

$$
3+m>m+1
\tag{LA.5}
$$

leaves, so it refuses even when this particular first entry is not
tight. Complete its owned capture and compute the first encoded target

$$
d_\alpha=3+2m,\qquad d_\beta=3+3m.
\tag{LA.6}
$$

Both exceed the present $H=K=m+1$. Fully returned Reserve and Raise
to the appropriate $d_\gamma$, followed by
Right$(E(P_m(\gamma)))$, accept and give the required whole encoded
source at a tight endpoint. The next raw Right$(\alpha)$ has
$H+1$ leaves and refuses; after capture, final Right$(E(\alpha))$
has $H+2$ leaves and refuses at the same $H$. These are four
distinct source calls, each with its full return, not the two
direct mapped calls of Definition 20.1. At $m=2$ the first raw
count is 5 at guard 3, the first commit counts/guards are 7 and 9,
and the second raw/final counts are respectively 8/9 and 10/11.

The first raw capture distinguishes the operands before the later
effective commit-guard choice. It is therefore not source-preserving
preparation of the restricted direct class: it is an additional actual
source event. Proposition 20.2 and Corollary 20.3 stand on their
unchanged one-whole-graft domain. No later return withdraws an already
published guard; this construction chooses that guard after acquiring
the discriminator. Equation (LA.5) is the separate first-entry
justification for this family, not a license for arbitrary surplus.
$\square$

**Proposition 23.2 (complete calls and selected subtotals).** For the
graft-only staging protocol of Theorem 22.1 let $G$ count the reference
grafts, $r=N-G$ the Rho requests, and $A_{\rm acc}$ the accepting final
modifiers. From $P$ the encoded continuation has exactly

$$
C_{\rm calls}=4+N+G+2A_{\rm acc}\le4+4N
\tag{LA.7}
$$

complete source/maintenance calls. For Corollary 22.2 it has
$4+2N+2A_{\rm acc}$. Let $\mathcal G$ list all graft rounds and
$\mathcal M$ all actual encoded Reserve/Raise calls, including
Reserve$(3)$ and Raise$(3)$. Their exact selected outer-choice and
source-frame external ingress after $P$ is

$$
I_{\rm selected}
=12+6r+
 \sum_{j\in\mathcal G}\bigl(6n(v_j)+6w(v_j)+8\bigr)
 +\sum_{(\mathrm{kind},J)\in\mathcal M}(2J+8).
\tag{LA.8}
$$

The uniform-staging variant adds $6r$ to (LA.8). At a designated
endpoint of either variant,

$$
H_j=K_j=w(t_j)\le3h_j,\qquad
L_{\rm designated}=4H_j-2,\qquad
\Delta L_{P\to\widehat p_j}=4(H_j-1).
\tag{LA.9}
$$

These are call, specified-input and designated-source-payload
coordinates only.

*Proof.* There are four preparation calls, $G$ raw staging calls,
$N$ final modifiers and exactly two strict maintenance calls for
each accepting final modifier, since its $d>H=K$. Refusing finals
use none. This proves (LA.7) and its variant.

Use exactly Proposition 18.2's framing convention: each Rho call
has six outer/source IN bits; each whole graft on an $m$-leaf
operand has $6m+4$; each maintenance parameter $J$ has $2J+8$.
Thus the two preparatory Rho calls give 12, and each graft round
pays both $6n(v)+4$ and $6w(v)+4$, even on final refusal.
Every additional raw Rho stage gives another six. This proves
(LA.8) with $|\mathcal M|=2+2A_{\rm acc}$ and $J\le K_N$.
Repeated equal bit words still require separate actual input occurrences.

The reference source fits $h_j$, so (GT.3) gives
$w(t_j)\le3n(t_j)\le3h_j$. CAP's designated payload has $4K_j-2$
cells. Each strict Reserve adds $4(J-K)$ such cells, so their
nondecreasing differences telescope from the actual reserve 1 at
$P$ to $K_j=H_j$, proving (LA.9). Delimiters, descriptors, scratch,
mailboxes, raw/encoded operands, rows, receipts, archives and retired
material are excluded from this designated-payload subtotal.
Neither (LA.7) nor (LA.9) bounds an arbitrary refused operand's input:
at reference guard 1, take $v=P_m(\alpha)$. The single round
refuses finally at encoded guard 3 for every $m\ge1$, with fixed
call count but graft ingress $18m+8$ in (LA.8). $\square$

**Definition 23.3 (complete resource convention).** Retain every
coordinate of (SW.17) and Definition 18.5:

$$
\begin{aligned}
\mathbf C={}&\mathbf C_{\rm acquire}+\mathbf C_{\rm plan}
+\mathbf C_{\rm context}+\mathbf C_{\rm copy}
+\mathbf C_{\rm ingress}+\mathbf C_{\rm maint}\\
&+\mathbf C_{\rm auto}+\mathbf C_{\rm primitive}
+\mathbf C_{\rm rows/deps}+\mathbf C_{\rm checks/ACK}
+\mathbf C_{\rm returns}+\mathbf C_{\rm retain/output}.
\end{aligned}
\tag{LA.10}
$$

This includes boot and seed acquisition, current count/syntax maintenance,
post-capture parsing, encoding/arithmetic/selection, checking and immutable
backing, raw and encoded resupply, all Reserve/Raise work, refused whole
candidate generation and guard/MUX work, current-map resolution, primitive
counter/fence/receipt work, both journals and dependency copies, complete
checks/ACKs, all InnerReturn/CaptureCAP work, retention and output.
Automatic-mode work, if separately actually used, keeps its own charge;
it does not supply this raw caller with automatic input.

For an actual measured native primitive prefix $z$, (GT.15)'s CAP bill
remains
$\operatorname{Bill}(z)=(\nu(z),2\nu(z),
S_0+b_{\rm ctl}(z)+8A_{\rm phys}(z)+8\nu(z))$.
It is not a conversion of outside-prefix calculations into CAP ticks.
Those calculations and GENERAL's independently specified
foundation/structural tariff remain separately paid. All earlier
acquisition and all later actual expenses stay in the complete run even
where (LA.8) begins after $P$. No equality of cross-path costs,
total-resource dominance, global optimum, timing rate, throughput,
uniform deadline or infinite completion follows from these subtotals.

## 24. The earned timing premise and retained recovery boundary

**Definition 24.1 (supplier and comparison scope).** The source-specific
composition in Proposition 21.3 and Theorem 22.1 is repo-derived:
attain tightness on the authentic beta occurrence, use it for
source-preserving acquisition of the raw whole operand, and restore
it after each selected final commit. Its suppliers remain CAP's
whole-candidate semantics, mandatory request delivery and complete return;
ARC's owned import, $M$ capture and beta-boot continuation; and
(GT.3)/(GT.11)'s counts, finite encoding and ordered homomorphism.
The existing $\rho^2$ image inverse is reused only with Corollary
17.3's independent acquired-observation premise. Forced refusal,
finite computation, copying and the inverse are not newly invented
general results.

The reduction from Assumption 15.3 concerns the time at which the
continuing consumer must possess the operand/encoding. It does not
reduce the complete retained information or discharge later actual
frame supply. The earlier one-final-call route remains useful on its
early-material domain. The present route pays a separate original
source refusal per graft and both raw and encoded input, and uses
a narrower tight-entry condition. Neither route has been proved to
dominate the other on the complete resource vector. ABT's fixed-guard
whole-menu and tight next-Rho results and the acquired signed
Read/ApplyRho/Halt consumers do not themselves supply this repeated
raw-graft acquisition and encoded commit.

The primary comparison frameworks remain Definition 19.2's
Lynch–Vaandrager, *Forward and Backward Simulations, Part I: Untimed
Systems*, [§3.2](https://groups.csail.mit.edu/tds/papers/Lynch/IC95.pdf),
and Reissig–Weber–Rungger, *Feedback Refinement Relations for the
Synthesis of Symbolic Controllers*,
[§IV and Definition V.2](https://arxiv.org/pdf/1503.03715v3).
Their finite-fragment/external-trace and same-input/admissibility
conditions, respectively, are literature-attested. Here the matching
fragment has an extra visible raw refusal and may have different
maintenance and operand bits. It has not been shown to preserve the
complete external trace; it also transforms a reference input into
a sequence of different actual inputs. Neither framework therefore
installs this native interface or supplies a full-system simulation
or feedback controller. No worldwide novelty or new Lean claim is
attached to this ordinary proof.

**Definition 24.2 (remaining source and continuation obligations).**
The positive domain is the designated preterminal finite protocol from
$P$. Other lawful choices remain available with their literal semantics.
Arbitrary surplus maintenance, Busy, malformed, partial-overwrite,
bootstrap/unfinished, changed-return and annex cuts have no positive
extension supplied here. The original final00 handoff, INITIAL
verification/output and absorbing halt remain unchanged and uninvoked
by this induction; no matched posthalt Ready or re-entry is asserted.
The parked client is not an installed planner or autonomous executor.

The new acquisition is specifically of the submitted operand through
the original request channel. It does not provide arbitrary current
source observations, full original-$Q$ equivalence, literal-read
transport, complete state/history/response recovery, a physical
executor, or native/diffusion/AURIC source identification. In particular
results on another source, including finite-spectrum Gram extensions
under their own support/corner hypotheses, supply no native admission,
owned request or input-feed bridge here. The broader recovery of
space, lawful continuation/time, boundary and memory retains its
original source, operation, acquisition, authority and resource
obligations.

## 追加锚（本行以下为增补区）

## 25. A different original-boot guarded-policy apparatus

**Definition 25.1 (versions, public data and the one-use domain).** Keep
the source, preparation, 74 roles, primitive effects and costs of
Definitions 1.1–1.4. Write $E=\rho^2$, $n=a+b$ and $w=2a+3b$, as in
(GT.1). The apparatus in this section has controller version
`GP1`, input version `GP-IN1`, controller-state version `GP-S1` and
actor-to-producer packet version `GP-CALL1`. These are fixed distinct
finite bit tags. Its source dispatcher, native descriptors, unified and
semantic rows retain CAP's versions, including `SEG-U1` and `SEG-J1`.
The GP tags are local control/data tags, not additional source opcodes.

The public initial tape contains a genuinely supplied complete $U(h_{\rm ref})$
with $1\le h_{\rm ref}<\infty$. It is a field of the actual public
GP initial-data block, bound together with $H_{\rm boot}=1$,
$\xi$, prior $\mathcal T_1$, GP1 and the original Stop-table binding.
Its ordinary ingress, writes, framing, descriptor, seal and initial
delivery are executed. In particular $h_{\rm ref}$ is not inferred from
a later row's encoded $h$ field. The GP1 table is independent of this
word's length or value. No future operand, operand count, depth bound,
encoded operand or common future reserve is initialized.

The public GP block has the seven-Frame format
$(\mathtt{GP-PUB1},U(h_{\rm ref}),\mathtt{GP1},\operatorname{enc}(V_{\rm GP}),
\operatorname{enc}(C_{\rm Stop}),\theta_{\rm Stop},U(1))$, with exact
exhaustion. Here $C_{\rm Stop}$ and $\theta_{\rm Stop}$ are the actual
original finite Turing table and initial configuration of Definition
9.1. The GP code encoding is the native row encoding, with no future
data field. The producer retains this initialized immutable public
block on 21 with its actual native descriptor on 17. Its reference is
bound to the actual public initialization copied with the boot/prior
material. CAP6.3's ordinary initial dependency delivery supplies its
actor28 block and actual origin descriptor29 before manifest import.
The separate actual boot binding supplies $\xi$, initial source
interval and prior references after their construction; none of those
future allocation addresses is guessed in the public ingress word.

An eligible preparation is a finite beta-derived preparation of §§21–22,
before outer00, attaining the following pair of designated alternatives
from its first beta Ready:

$$
\begin{aligned}
\pi_{\rm src}(p)&=t,& (h,K)(p)&=(h_-,h_-),&1\le h_-\le h_{\rm ref},\\
\pi_{\rm src}(\widehat p)&=E(t),&
(h,K)(\widehat p)&=(w(t),w(t)).
\end{aligned}
\tag{GP.1}
$$

All preparation calls, supplied words, rights, acquired seed and complete
returns are retained. Thus $n(t)\le h_-\le h_{\rm ref}$. Immediately
after $\widehat p$, supply one actual outer01 raw Left$(v)$ or Right$(v)$,
where $v$ is any nonempty finite ordered alpha/beta tree, and complete
its refusal, delivery, InnerReturn and CaptureCAP to Ready. Then supply
outer00. This is the designated GP1 entry; it has not previously been
used. The operand need not have been acquired by the continuing actor
before its raw ingress. All rights and immutable backing used below
must be current at the cuts where they are read.

The empty reference preparation is allowed: its encoded preparation is
the four actual calls Reserve$(3)$, Raise$(3)$, Rho, Rho of Theorem 22.1,
so $t=\beta$ and (GP.1) is available for every public $h_{\rm ref}\ge1$.
More general eligible preparations keep precisely their actually
attained domain, rather than asserting attainment of every tree.

**Definition 25.2 (literal original-boot construction).** The GP1
controller is a native finite word controller. Its rows are obtained by
Definitions 2.1–2.4's existing compiler, using the finite word operations,
parsers and traversals cited in §§26–28 below. It is not assigned CAP8's
narrower Native operation-packet type. Its code is the literal native
row encoding of CAP Definition 2.3, installed bit by bit in the active
joint original-boot control store, including the entry/send/return rows
of §§26–27. Its immutable public code copy is the GP-description
subfield of the initial public-data field on 69, whose complete field
has its actual descriptor on 68. That same fixed code word is actually
supplied with public initialization and copied through producer21/17
to actor28/29 before the manifest export. Canonical initialization
supplies the identical native row encoding for control installation
and for this public copy, paying both occurrences of its bits.
These are primitive-control rows under PR57.D1, not dynamic gate code
read as an instruction by name. After outer00, port25 holds the actual
sealed GP input and successive `GP-S1` state blocks, and 27 its waiting
packets. Table24 remains exactly Definition 9.1's original finite
Turing Stop table; its original initial configuration is retained too.

For the shared actor word banks use the union of the registers required
by the history graph and this one fixed word program. Number that finite
union by Definition 2.1's hygienic first-occurrence rule. Its size $r_*$
is a syntactic constant. Construct its empty bank by Definition 2.3;
both the history and GP1 rows use this same layout and parity relation.
Their temporary fields are disjoint. A call into CAP has both possible
bank parities as finite control cases and makes no bank assignment.
The history graph with this layout is denoted $G_*$. Its actual capture
description is $\Delta(G_*)$, with its own $L_*$, installation and
description checks as in §4. It is not identified with the old $G$.
The GP1 rows used after outer00 were already installed at original
boot; the later history-version installations do not install a new
policy or change table24. The new joint apparatus has GP1 as an
additional installed phase of the same actor, with the original Stop
client as its fixed terminal continuation.

More explicitly, reserve the fixed native version name $V_{\rm GP}$
for these original-boot rows, including their inlined CAP caller and
return copies. The joint finite control has fixed version/phase cases;
$V_{\rm GP}$'s completed-store flag and literal rows remain resident
while $L_*,G_*$ run. The new $G_*$ outer00 successor is the fixed CTL
edge to $(V_{\rm GP},\mathrm{GPInput})$, after the actual invocation
handoff and loan. Each GP service returns to that version's fixed
GPResponse. All these targets are linked finite labels, not words
obtained from an operand or a request to enter a legacy closed graph.
The primitive-control version cases are installed at the same original
boot; no edge here enables a partial store. The additional GP invocation
slot starts dormant. Outer00's TOK transfers the invocation to it;
its later fixed handback TOK transfers it to the original client slot.
These are finite paid control/token bits, with no additional tape port.

Construct the ordinary boot, one beta private preparation, stationary
seed acquisition, original counters, directory and boot binding as in
CAP Definition 2.4. The public initialization/prior copies include the
actual GP initial-data word containing $U(h_{\rm ref})$. As in
Definition 4.1, park the initialized original Stop client at its pre-loan entry,
with 24/25/27 protected and its work tokens returned. In Definition
4.3's initial manifest use the actual delivered initial-data block for
this variable field: resolve its local origin and copy its bits, instead
of emitting $h_{\rm ref}$ as a literal. The GP-description subfield is
copied with this actual public data, not embedded as a literal in
$G_*$. Earlier original-table/graph descriptions remain fixed literals.
The ten additional roles, capture,
manifest import, saved heads and token/Ready joins are those of §4
with $L_*,G_*,r_*$ and these actual bindings.

All finite-control alternatives, native calls and loops expand by
CAP Definition 2.3 and Definition 2.1. The initial bootstrap therefore
has a fixed finite literal description. Loops over data use constructed
word cursors; tree traversal uses the existing constructed frame stack.
The original table24, GP rows, $L_*,G_*$ and $r_*$ are fixed
independently of $h_{\rm ref}$ and every future $v$. The canonical code
bits supplied at initialization are these fixed descriptions, not
operand-dependent code advice. Neither GP nor $G_*$ contains the GP
description as a literal. Register counting is consequently over the
finite syntactic field-copy program, independently of the later
description-word length; it has no code-length/register-count fixed
point to solve. This construction uses the finite native boot authority
of PR57.D1/CAP2.3 and the word realization of §2; it does not require a
new Turing-table-to-native compiler.

The raw outer01 route remains the complete external-IN $F^A$ of
Definition 4.1. The history route remains its complete acknowledged
route. At outer00, the actual invocation handoff and twelve-port loan
enter the fixed GPInput entry of §26, before the original Stop interpreter.
GPInput saves the old 25/27 configuration before appending GP state
there. There is no subsequent ARC capture
or Ready assertion for this outer00 suffix. The GP1 terminal branch
executes the original proposal $q_1(\beta)=(0,B,1)$ and CAP's unchanged
Halt/snapshot/verifier/receipt/INITIAL consumer route after the explicit
configuration handback in Definition 28.1. This is a different
apparatus chosen at original boot. No edge installs it into Definition
9.1's already running INITIAL-Stop table.

**Theorem 25.3 (boot and parked-prefix correspondence).** The construction
of Definition 25.2 has an actual finite first Ready, with source beta,
$h=K=1$, the acquired beta seed and original INITIAL target/verifier/
consumer. Every eligible preparation and the following raw acquisition
in Definition 25.1 have their actual CAP/ARC returns in this apparatus.
The raw acquisition refuses and leaves the entire $E(t)$ unchanged.

*Proof.* All additional native rows are a finite literal boot installation;
all new initial-data blocks are finite supplied words. CAP's original
validation installs its initial source interval once. No GP row reads
private source16 or bypasses its validation. The proof of Proposition
4.4 applies with the stated finite register union and actual version
descriptions: native field import/export is insensitive to the number
of other fixed fields, the empty prelude constructs exactly $r_*$ empty
fields, and the captured code is exactly the activated $G_*$. The
variable public field is copied from its actual delivered block before
the closed manifest scan. Thus it has its actual value, rather than a
guessed literal. The prelude and manifest need no self-description
constant in either earlier graph.

The original-boot flag for $V_{\rm GP}$ was set only after its complete
literal installation and is not changed by a fresh history-version
installation. The fixed outer00 edge therefore has an actually enabled
target of the right version. The twelve-token induction supplies its
workspace owner and the invocation TOK its actual entry authority.
This proves the version/entry correspondence; equality of names or
use of the same ports is not being used to create that edge.

Before outer00 no route reads or executes the parked policy. The raw
and history routes, source work, channel checks, head restoration and
token joins are the same inlined routines with their actual new-run
bindings. Induct on completed preparation calls using Proposition 5.5
and Theorem 22.1's attained-source argument. The parked-client proof
uses protection of its initialized material and dead shared workspace,
not the Stop instruction's particular next action. The outer00 entry
is explicitly the new fixed native entry, rather than CAP8's table
interpreter. At corresponding completed cuts the source value,
historical guard/reserve, source occurrence and selected source-call
outcomes agree with the specified preparation. Table bytes, initial
data, manifests, native labels, addresses and costs have their new
apparatus values; no equality of whole boot histories is required.

At the last raw acquisition, $n(E(t))=w(t)=h=K$ and $n(v)>0$.
Proposition 21.3 gives the actual source-preserving refusal and complete
owned return. Its argument uses only the unchanged raw caller and source
contracts, so it applies to either direction and every finite $v$ here.
The original target remains INITIAL-$q_1$ of the original beta, not a
target of the now modified source. ∎

## 26. Constructing the policy input from actual acquired records

**Definition 26.1 (local references and the input projection).** At GPInput,
the actor owns archive28 and native descriptor stream29 and has their
current read tokens. Its public initialization, prior and boot binding
are available immutable received blocks there, with complete producer
origins on 21/17. The acquired seed is the actual 26 or 28 block selected
by the boot binding and its actual local descriptor. Header, length,
payload, semantic and unified rows are immutable acquired blocks on 28
with their actual local descriptors on 29. No producer reference is
used as an actor address. CAP descriptor ordinals are one-based; the
word-bank descriptors on 68 remain their separate zero-based grammar.

Let $\mathcal R$ be the ordered projected record obtained from the
complete acquired unified prefix. Each projected event contains the
actual kind, full canonical request and complete named context when
present, genuine response, historical guard/layout and before/after
counters. For a nonmaintenance event its semantic mate is checked
against that unified row. Retain the actual row and dependency origin
references with this projection. Maintenance keeps its own event and
response. Local/terminal kinds, when present in a prefix, retain their
own material and do not become source modifiers. Physical header,
length and payload seps/statuses are excluded from the chronological
wire bits. Projecting these fields does not identify source events
with word-bank assignments or discard the underlying acquired blocks.

The input bit word is a fixed-arity framed tuple

$$
I=\operatorname{Tuple}\bigl(
\mathtt{GP-IN1},\ {\rm Pub},\ {\rm Seed},\ \mathcal R,\
{\rm Origins}\bigr).
\tag{GP.2}
$$

`Pub` contains the actual seven-field `GP-PUB1` block and the actual
public initialization, prior and boot/controller bindings; its
$U(h_{\rm ref})$ is parsed separately from row guards. `Seed`
contains the acquired syntax and its original/local references.
`Origins` enumerates the local references used for the row/dependency
projection. Tuples, lists and references use §3's existing Frame/
ReadFrame, ReadList and complete CAP-reference codecs. Version tags use
their fixed bit encodings, and all arities and trailing exhaustion are
checked. The data in (GP.2) are precisely public initialization and a
projection of an authentic acquired record, with its acquisition
bindings. They contain no source snapshot, private count or future reply.

**Definition 26.2 (the native GPInput graph).** GPInput follows the complete
outer00 invocation handoff and twelve actual TOKs lending the public
work ports to $A$. It starts no helper during that transfer. It first
imports the original closed 25/27 symbol words and saves their head
distances by Definition 3.1's exact native graph, with its two fixed
port cases now 25 and 27. These are actor-owned readable ports at this
entry. The same proof restores both heads. Retain these words,
distances, original configuration/packet bindings and initialized
Stop entry in disjoint persistent bank fields until the terminal
handback. This import precedes every GP append to either port. It
neither changes their old bytes nor accesses another owner's data.
The graph next
uses the complete native descriptor count scan of CAP Definition 6.1
to construct $U(D_*)$ for the closed current descriptor prefix on 29.
It retains this bound before appending any new descriptor. Every search
below is bounded by that copied count, even if later output appends to
29. Each requested native field is obtained by ReadDescriptor's full
origin scan and following-seal test, not by treating an ordinal as a
cell number. ReadDescriptor may scan a longer complete tail on a later
invocation; its requested ordinal is still one of these first $D_*$.

Select the actual public initialization/boot/prior and seed by their
complete bindings, using the actual local-origin resolution of
Definition 3.3 and CAP6.3. At each selection load the real local base,
length, type and status address, require initialized immutable available
material, position by At and read its actual status. Only the fixed
26/28 seed cases and archive28 cases are admitted. The binding's empty
local origin, if any, is resolved by its complete local reference;
it is not matched against every other empty origin. The GP version
and native-description binding must agree with the actual GP1 boot
version; the original Turing-table/initial-configuration bindings must
agree with the actual Stop client. These are distinct code formats.

Scan the first $D_*$ descriptors for acquired `SEG-U1` blocks of this
$\xi$ and boot/prior binding. Bounded-parse them by §3.4/CAP6.3.
Find their maximum old unified label by unary comparison and construct
its successor $m_*$. Then, for $i=0,\ldots,m_*-1$, scan those same
$D_*$ descriptors for the row with old label $i$ and the expected
predecessor. Choose the first available copy with the complete origin;
other copies of that same origin have CAP6.4's equal payload. Require
one continuous prefix beginning at boot, correct before/after fields
and both joined ends. Resolve every enumerated request/control/output
dependency and semantic mate by its complete origin, local availability
and the §3 parsers. Require its actual `SEG-J1` fields and separate
semantic predecessor on nonmaintenance events, and no semantic mate
on maintenance. These are the already supplied receiver tests, used
as finite word tests on the acquired data.

Import the selected native payload fields by §2.2's native field import,
with positioned payload base and its actual length counter as bound;
binary fields do not use a physical sep as an internal Frame delimiter.
Word-bank rebuilds use only 64–68 and never move the native input port.
At each bit use RD, select its literal cons branch before the compiler
can reuse a latch, perform that assignment, and MR the native source.
The terminal counter test and Reverse finish the exact bit word.
The bounded variant is the same native import schema applied to a
bit block instead of a sep-terminated field. The §3 parsers now form
the successive projected fields of (GP.2) with Frame and AppendItem.
No purported permission bit in an imported field executes TOK.

Export the complete bank field $I$ into a fresh block on 25. This join
has the following literal realization. With the pool still at $A$,
measure Base(25) before writing; position the bank field using Field;
dry-count its bits into a distinct public unary work word; reposition
the same immutable bank field. For each counted bit execute
RD(bank,6), Append(25,latch6), MR(bank) and the actual counter advance;
include the terminal test. Parity selects fixed port64 or port65 before
this scan, and no bank assignment runs during either pass. Append the
physical sep and zero status, construct $b+|I|+1$ by Add, and construct
the full ten-field CAP descriptor on 29 by WriteDescriptor. Set the
actual status by At; WR(1); CTL seal. Its type is `GP-IN1`, owner $A$,
port25, initialized=1, mutable=0 and origin empty. Its base is the
measured $b$ and its creation ordinal is the actual new one-based
count. It is not an RCA descriptor or a remote pointer.

Release temporary words only after this block is sealed. Reposition it
through its just constructed CAP descriptor, import its actual bits
back to the designated policy input field by the same bounded native
import, and parse (GP.2). Export a complete `GP-S1` state block on 25
by the identical measured export, with phase `Input`, the local input
reference and actual acquired-row/seed/public bindings. A CTL installs
that completed state version and enters the word policy. The active
bank/parity is its working representation; 25 is its persistent
sealed state representation. No mathematical value of $I$ is installed
by this CTL without those earlier writes and imports. Archive heads
may now have their actual new positions; no later ARC Ready is claimed.

**Theorem 26.3 (actual record-to-controller input).** At the designated entry
of Definition 25.1, GPInput terminates and the consumed input is exactly
(GP.2), made from these actual owned records and public initialization.
In particular its last source request is the actually submitted raw
Left$(v)$ or Right$(v)$, its acquired payload is the actual $v$, and its
recorded response is that call's genuine refusal. The installed state25
contains the complete input binding and every earlier genuine response
through this prefix. It has not received any anticipated computed-call
response.

*Proof.* Theorem 25.3 and the final CaptureCAP supply a complete acquired
prefix with authentic origins. All its request dependencies and semantic
mates arrived before final row ACK. CAP6.4 gives their immutable equality
to their senders, and §3.5 identifies their local grammar and origins.
The closed count $D_*$ is finite. Every bound, ordinal and maximum used
by GPInput is constructed by finite unary scans. Authentic rows supply
exactly the continuous prefix selected by the old-$m$ and predecessor
tests, including all maintenance and nonmaintenance cases. Copy choice
cannot change a payload with the same complete origin.

Each At addresses the selected local constructed interval. The current
read tokens, not a copied descriptor flag, authorize its RD. During a
native import bank rebuilds preserve that source head, so induction on
the actual length counter gives precisely the referenced bits. Field
parsing and Frame inversion yield the stated projection, including the
raw call's complete context. The fixed seed/boot cases resolve the
authentic initial data, so the public unary field read here is the
actual $h_{\rm ref}$. There is no rule replacing it by the historical
encoded guard in a row.

The two-pass export reads one immutable bank field and appends exactly
its counted bits at the measured 25 base. Status is set only after
completion; descriptor construction uses the true base/length/count.
The subsequent length-bounded reimport therefore consumes that actual
sealed block. The same argument applies to the first persistent state
block. All loops have finite closed data bounds; the source token and
private source are untouched. This proves input availability as an
executed connection, rather than a premise that an acquired bank is
already a field on 25. ∎

## 27. Computed packets into the original guarded service and back

**Definition 27.1 (the GP guarded send graph).** A GP1 source-service
output is the fixed-arity tuple

$$
P=\operatorname{Tuple}(\mathtt{GP-CALL1},\ k,\ z,\ c),
\tag{GP.3}
$$

where $k$ is exactly one of CAP's seven three-bit tags, $z$ is its
complete original payload, and $c$ is one of the finitely many GP1
continuation-phase codes. A graft's $z$ is the full named original
context code in its actual order; a maintenance $z$ is the complete
$U(J)$; the other original payload grammars remain unchanged.
The packet contains no claimed source response. The pending state
retains $P$, $c$ and the bindings needed after return.

The word controller writes and seals this packet on 27 by the measured
native export of Definition 26.2, with its actual CAP descriptor on 29.
It also exports the new `GP-S1` pending state to 25 before starting
the channel, whose pool initially remains at sender $A$.
The packet is copied through route49 to a fresh producer
block on 21, with native descriptors on 17, by CAP6.3's complete
two-stage channel and the actual twelve-port loans/returns. Its complete
origin remains the actor packet reference. The sender continuation
waits for the receiver's complete tuple/availability checks and
acknowledgement. CAP6.3 first returns the pool to sender $A$.
The GP sender continuation then executes twelve actual TOKs from
$A$ to the producer and one CTL to the fixed GP dispatch entry.
Only now are all twelve work tokens at the producer.
No source call begins during a partial send or token transfer.

The producer bounded-parses the received tuple, checks its GP version,
finite continuation code and exactly one of the seven tags, and copies
the whole payload into its public word/staging work. It calculates the
payload length by a complete scan. It enters CAP Definition 4.6's
already supplied automatic canonical block constructor: Append/copy
the three literal header bits, the complete $U(|z|)$ and the entire
$z$ into three fresh blocks on 13. Measure each actual Base before
append and execute its sep/status/descriptor/seal operations on 13/17.
Construct the complete three-reference request tuple in its original
order. No source-frame bit in this graph uses IN. In particular a
computed operand is copied from the packet, not compared with a
separately supplied external operand.

At the acknowledged idle source boundary the fixed GP caller kind
takes the actual source-service token, retains its fixed return kind
and enters the same canonical parser/ReadState/selected-service graph
as an original guarded client. All seven cases use the same source
or maintenance bodies, complete row writer and mandatory delivery.
For Rho or a graft there is no intervening automatic safe-growth edge.
The current guard itself decides the whole candidate's accept/refuse
case. Reserve/Raise operate only when explicitly present in $P$.
ReadE, TagRead and the original non-source terminal/local routes
remain available through their own existing entries and types.
Malformed, incomplete, busy and missing-token raw cases retain their
original partial legality; GP packets neither grant such entries nor
replace those cases by refusals. A GP tuple/availability fault has
its finite paid local failure successor and makes no source call.

**Definition 27.2 (the GP return graph).** Each selected service executes
its actual response commitment, applicable counter/fence work, semantic
row if required, unified row and all enumerated dependencies. Missing
actor material is copied through route48 with fresh mailbox/receiver
intervals, actual status/seal/TOK and both workspace loans. The receiver
performs CAP6.3's full joined checks, installs its actual new ends, and
emits the final row ACK after the workspace return. Only then execute
the source-token TOK and idle CTL. Their GP saved continuation is the
fixed label GPResponse, not $F^A$'s next IN or InnerReturn.

At GPResponse lend all twelve work tokens to $A$ and enter its return
reader. The pending 25/27 blocks remained protected during the service.
Scan the local origin descriptors on 29 and acquire the returned new
unified row and its semantic mate/dependencies through the actual
complete CAP receiver relation. Apply the same bounded row checks as
in Definition 26.2, additionally comparing the request references'
resolved bits with the waiting $k,z$ and the actual predecessor with
the saved acquired end. Read the complete genuine response field.
Native field import places that field, row origins and the new joined
ends into the active bank. The continuation $c$ is loaded from the
retained packet; it is not inferred from a hoped-for reply.

Append that response and its actual row reference to the controller's
response list. Export a complete new `GP-S1` block on 25, containing
the input reference, retained request/continuation, complete returned
response and row binding, response-list end and actual successor phase.
All exports have measured bases, complete descriptors and real status/
seal operations. Its final state-install CTL occurs only after that
seal. Return all twelve work tokens to the producer and execute the
fixed caller-return CTL. Only the next actual loan/CTL can run the
next controller phase. Bank heads/latches and new 25/27 versions keep
their actual values; no old snapshot is restored over the source.

The finite successor phases include `AfterReserve`, `AfterRaise` and
`AfterFinal`. Each first examines its installed actual response. A
response inconsistent with its selected phase goes to a retained local
failure state; it never creates an acceptance token or updates counts
as though a different response had arrived. The raw acquisition's
response is already installed with the entire input by GPInput.

**Theorem 27.3 (actual guarded output, complete return and memory).**
Every finite valid packet emitted by this controller at its authorized
source boundary has the original guarded canonical service, full
returned row/dependency relation, final ACK, source-token/idle return
and genuine response installation in state25 described above, under
the retained pointwise progress and current-right premises. No matching
external frame bits are required for this output. The graph retains
the complete seven-tag guarded menu, rather than CAP8's safe-growth
task or its narrower Native packet grammar.

*Proof.* The packet export's bit induction is Definition 26.2's. CAP6.3
then copies that actual immutable packet, including its version and
whole operand, to the producer's own interval. The recipient reads
through its own descriptor on 17. It does not dereference actor27.
The acknowledged send returns the pool to $A$; its explicit following
twelve-token transfer and CTL establish the producer constructor's
entry. CAP4.6 explicitly supplies the automatic-mode
three-block construction by copies/Appends, including real nonempty
port bases, descriptors and status work. Applying it to this parsed
packet gives exactly the requested original frame, without an IN row.
CAP Lemma 4.7 gives each tag its actual selected body and saved return.
The graph's explicit guarded caller kind selects those branches and
contains no CAP8.2 growth-policy join. Thus a finite but too-large
context still reaches its entire original candidate computation and
executed refusal.

CAP Lemma 6.7 and Theorem 6.4 give the actual response, counters, rows,
two-stage copies and joined checks on every accepting and refusing
case. These are the unchanged resident routines. The GP boot changes
only this caller's final saved successor after the source token and
idle restoration. Neither a directory seal nor a copy-completion TOK
can enter GPResponse in place of final row ACK.

The actual postservice archive now supplies the return reader's local
row and response bits. The saved packet/continuation still exist on
protected 25/27. Its origin and predecessor comparisons therefore
identify the row for this execution, rather than an old equal-valued
reply. The bounded import followed by measured export installs exactly
that full field and row binding in the next state25. The subsequent
phase reads these newly installed values. Serial token transfer
establishes both its local authority and its actual caller return.
Finite packets, closed scans and the supplied service termination give
finite completion. This proves the joins by their primitive graphs;
it does not assume an unproved GP input/call/return service. ∎

## 28. The fixed one-use word policy

**Definition 28.1 (finite policy and its persistent phases).** The word
program has the finite phases `Input`, `Select`, `WaitReserve`,
`AfterReserve`, `WaitRaise`, `AfterRaise`, `WaitFinal`, `AfterFinal`,
`Done` and `Stop`, together with distinct finite parse/domain/response
failure phases. Every persistent phase is exported to 25 as `GP-S1`.
Variable trees, counts, request words, row ends and response lists are
bank words and sealed 25/27 blocks, never finite-control indices.
Only fixed literal bit cons, empty/copy/tail, first-bit/empty tests and
the already supplied acyclic word macros occur in its local graphs.

The `GP-S1` payload is a tuple with these fixed fields: version, phase,
local input reference, saved-original-configuration binding, derived
reference tree, raw operand, encoded operand, four leaf counts, current
encoded $h,K$, selected $d$, branch bit, optional waiting-packet reference,
continuation code, complete response list with row references, and the
two acquired journal ends. Unset fields have explicit none tags. The
saved binding includes the actual old 25/27 symbol words and head
distances, their original initialization references and the original
Stop entry. A field can hold a complete framed word or its complete
local immutable block reference; reference fields are resolved with
their actual descriptors and current read tokens. In particular this
is not an unbounded collection of finite-control registers.

At a phase change export this whole tuple, or its complete framed local
reference fields, by Definition 26.2's native graph and install its
sealed reference. On the next actor loan reimport and parse that actual
state block before testing the phase/returned-response fields. The
working bank is thus reestablished from the persistent representation,
not from latches left across a source service. History fields are
separate and are not overwritten by this state reload.

At `Input`, parse the actual (GP.2). Replay its projected original
source record from the acquired beta seed. Whole accepted Rho and
grafts update the derived tree by their existing finite syntax
construction; refusal and read leave it unchanged; maintenance updates
only its derived $h,K$ according to its genuine recorded branch.
Use the complete actual request contexts, historical guards and the
actual recorded outcome, and check that the original guard test agrees.
This is computation on acquired public data, not a read of a private
source or of an unreleased refused candidate. Require the latest
source event to be the immediately preceding raw graft refusal and
retain its actual direction and whole $v$.
Initialize the response list by copying each genuine projected response
and its actual row reference, including this final raw refusal, into
the represented state. Earlier input/response blocks remain immutable.

Let $s$ be the replayed current encoded tree. Apply the existing finite
two-step image parser of ABT Theorem 12.1 to $\operatorname{sh}(s)$,
obtain $t$, and check the complete equality $E(t)=s$. The equality
check prevents an arbitrary labeled tree with the same erased shape
from passing. Require derived $h=K=n(s)=w(t)$ and $n(t)\le h_{\rm ref}$.
The eligible entry guarantees these tests; outside it they are finite
domain failures, not a claim of another Ready. Derive counts by the
existing complete tree traversal, and form $E(v)$ by the existing two
substitutions. Preserve the actual raw operand and all input bindings.

At `Select` compute exactly the reused quantities (LA.3),

$$
\ell=n(t)+n(v),\qquad H=w(t),\qquad d=H+w(v)>H,
\qquad b=[\ell\le h_{\rm ref}].
\tag{GP.4}
$$

If $b=1$, emit Reserve$(d)$ with continuation `AfterReserve` by
(GP.3). After its complete genuine returned greater response is in
25, emit Raise$(d)$ with continuation `AfterRaise`. After that complete
genuine successful response is in 25, emit the original same-direction
Left$(E(v))$ or Right$(E(v))$, with continuation `AfterFinal`.
If $b=0$, emit only that same final encoded graft, at the unchanged
guard/reserve. The waiting and returned phases and all packet/state
exports are real intervening graphs of §27. Neither anticipated
maintenance success nor the bit $b$ itself is a source response.

At `AfterFinal` read the installed genuine final response. On its
accept component update the derived reference syntax to the specified
ordered graft and its pair to $(a+a_v,b+b_v)$; on its refusal component
retain $t,(a,b)$. Require agreement with $b$ before installing `Done`.
Retain the complete actual response and row reference in either case.
Export the resulting state to 25, return the pool, and take a CTL to
the fixed non-ARC policy-return cut $D_{\rm GP}$. At this cut the
producer again owns the twelve words, the source-service token is
idle, and 25/27 contain the actual completed state and packet/response
bindings. The history invocation has been consumed by outer00. There
is no new CaptureCAP, $M$ item or ARC Ready at this cut.

The next local GP1 phase is `Stop`. It is the following explicit
handback, not a native encoding substituted for a Turing table.
Borrow the public pool for $A$. From GPInput's saved actual original
configuration/packet words extract the original finite Stop machine
configuration using its original code/data grammar. The protected
original table24 and all referenced initial blocks still exist.
Use CAP8.1's actual configuration/stack word-copy initialization to
write a fresh active original configuration version on 25 and its
initial empty Native waiting-packet version on 27. Their bits are
copied from those saved words, with the complete original reference
fields; their newly constructed locations have their own descriptors.
Only the live machine-configuration designation changes. The sealed
GP-S1 blocks, response list, original configuration and all earlier
25/27 data remain retained. No source, archive, row or acquired end
is restored to an earlier state.

Restore the table24 head by its original positioning code, return all
twelve work tokens to the producer, execute the identity public-role
CTL and the actual Tail(13), Tail(17) normalization of Definition 4.1,
and execute the fixed GP-to-client invocation-slot TOK. All former
public work words are dead: the complete initial Stop configuration
and empty packet have already been written on 25/27. The original
twelve-token loan and entry CTL now
enter the initialized Stop interpreter at its original label.
This code has exactly the original table and represented initial
machine configuration, so it actually executes its original Stop,
writes/seals $(0,B,1)$ on 31, enumerates the executed original
instruction/output dependencies in its terminal packet, and copies
them through route49 to producer21 as in CAP8.1. The terminal template
identity is that original Turing-table identity, not the GP native
encoding. It then follows CAP6.5–6.7's unchanged terminal route.
No NativeLocal marker was fabricated for the preceding GP primitive
work: CAP6.2a already distinguishes that work from completed semantic
markers. There is no return to $D_{\rm GP}$ after global halt. This
fixed handback is part of the original-boot apparatus; table24 is
never rewritten or replaced.

**Theorem 28.2 (finite realization of this policy).** Definitions
25.2–28.1 specify a fixed finite primitive program on the stated owned
carrier. On every eligible finite input, its local work terminates and
its service output comprises exactly the packets just specified.
Its new response list contains the genuine raw refusal and, in order,
the genuine responses of every computed call actually performed.

*Proof.* The local algorithms are the existing finite parsers,
Frame/list operations, tree traversals, image parser, substitution,
arithmetic and comparison, used inside one finite control graph.
Replay iterates a finite acquired list; every tree traversal descends
through finite syntax with a constructed stack. The image parser's
termination and inverse property are ABT12.1's supplied result, not a
new inverse theorem. Unary comparisons and additions use §2.1's
acyclic expansions. Fixed calls are inlined, data loops retain their
actual cursors, and the finite phase alternatives have the stated
success/failure successors. Definition 2.1's compiler therefore yields
finitely many native rows and the finite constant $r_*$, regardless of
data sizes. Definition 2.4 supplies their represented-bank relation
and paid native execution. Initial native imports and persistent-state
exports have their separate joins in §26; no word assignment claims
to access an unimported old port.

Induct over the actual projected prefix to identify its replayed
tree and guards. The base is the acquired original beta, and CAP's
original whole-candidate semantics gives each update step. All request
contexts are actually acquired. Thus $s$ is the actual current source
value. The attained relation (GP.1) and source-preserving raw refusal
give $s=E(t)$; the supplied inverse and the complete equality check
recover precisely that reference $t$. The current guard/reserve and
the actual public $h_{\rm ref}$ therefore pass the stated tests.
The last captured raw payload gives precisely $v$ and its direction.
No new source observation or hidden size argument was used.

The word program forms complete finite packets from these now
represented words. At most two maintenance packets and one final
packet are emitted. Theorem 27.3 supplies their genuine response
installation before each subsequent phase, so the induction over the
three possible waits identifies the actual response list. Export to
25 and its installation are part of each phase, including `Done`.
All local loops terminate on this finite input; pointwise progress
of the retained source services completes the finite composition.
The generic finite interpretation and controller discipline of
PR57.D5 and CAP8.1 are reused at the level of paid input/output and
persistent returned data. Their Turing/Native packet grammar is not
asserted to be identical to this explicitly expanded native version. ∎

## 29. One earned guarded use and the original INITIAL consumer

**Theorem 29.1 (actual acquired-record guarded use).** There is the one
fixed original-boot apparatus of Definition 25.2 such that, for every
actual finite public $h_{\rm ref}\ge1$, every eligible preparation
(GP.1), every nonempty finite ordered operand $v$ of arbitrary size
and depth, and either actual late raw direction, the designated entry
executes one selected original guarded use after the complete raw
refusal/acquisition, with no matching external bits for any computed
maintenance or final modifier. Retain the original finite raw supply,
canonical initialization, current rights/backing and reached-service
progress premises. Define the reference whole modifier and its outcome
at guard $h_{\rm ref}$ by

$$
\begin{gathered}
c=\langle v,t\rangle\ \hbox{or}\ \langle t,v\rangle,\qquad
\varepsilon=
\begin{cases}\mathsf{accept},& n(c)\le h_{\rm ref},\\
\mathsf{refuse},&n(c)>h_{\rm ref},\end{cases}\\
t'=\begin{cases}c,&\varepsilon=\mathsf{accept},\\
t,&\varepsilon=\mathsf{refuse}.\end{cases}
\end{gathered}
\tag{GP.5}
$$

At the actual completed policy-return cut $D_{\rm GP}$ the designated
final modifier's original label is $\varepsilon$, its actual source
successor is $E(t')$ through the continuing source16/$\phi_K$, and

$$
(h,K)(D_{\rm GP})=(w(t'),w(t')),
\qquad n(\pi_{\rm src}(D_{\rm GP}))=h=K.
\tag{GP.6}
$$

Every actual service used here has its complete return and genuine
response in the declared state25. There is exactly one raw staging
source call and one final encoded source call after $\widehat p$;
two strict maintenance calls occur exactly when $\varepsilon$ accepts.
The raw and final refusing calls remain distinct executed events.

*Proof.* Theorem 25.3 earns the raw acquisition and the authentic Ready
before outer00. GPInput constructs and consumes the actual acquired
input by Theorem 26.3. Theorem 28.2 supplies the fixed finite policy
on those words, and Theorem 27.3 supplies its actual guarded calls and
complete response/state joins. These facts establish the missing
input-to-call-to-return connection before any use of the guard/count
identities.

The semantic selection is precisely the one-step graft case already
proved in Theorem 22.1. Explicitly, if $\ell\le h_{\rm ref}$, then
$K=H<d$ makes Reserve$(d)$ strict and, after it, $h=H<d=K$ makes
Raise$(d)$ lawful. Their real successful responses lead to the next
phases. They preserve the entire $E(t)$ and extend the actual layout
without replacing the source. The final original candidate has $d$
leaves at guard $d$, so the original service accepts. Its actual
ordered candidate is $E(c)$ by (GT.3), and $d=w(c)=w(t')$.
If $\ell>h_{\rm ref}$, no maintenance runs. The final original
candidate still has $d>H$ leaves, so it executes refusal and preserves
the entire $E(t)$. Its endpoint has $h=K=H=w(t)=w(t')$.
These are both outcomes of the actual unchanged guard/MUX body,
not GP1 assignments to source16 or predictions installed as replies.

At every wait the full response/row joins precede the next phase.
The genuine final response therefore selects the corresponding
derived syntax/count update and passes the comparison with $b$.
`Done` is exported, sealed and installed, and all workspace/source
tokens have their stipulated returned owners at $D_{\rm GP}$.
This proves (GP.5)–(GP.6) and the complete memory assertion.

The counterfactual reference path is an alternative finite extension
from the same first beta Ready: use the reference preparation to $p$,
publish $h_{\rm ref}$ by the original Reserve/Raise when needed,
then perform the original whole Left$(v)$ or Right$(v)$. Since
$h_-\le h_{\rm ref}$, this publication is lawful and $t$ fits the
guard. Its actual whole-candidate branch is exactly (GP.5).
The encoded path does not perform that reference publication on its
own source; it reads the public initial datum and chooses its own
explicit guards. Neither path is a live copy of the other's endpoint.
All finite $v$ and both directions were arbitrary. No uniform time,
size, depth or guard bound enters the finite program. Both outcome
branches occur for the same fixed code and public $h_{\rm ref}=2$:
from the empty reference preparation, $v=\alpha$ gives an accepting
final at encoded guard/reserve 5, whereas
$v=\langle\alpha,\alpha\rangle$ gives an executed final refusal at
guard/reserve 3. Either direction has these actual returned executions.
Their packets and genuine state25 responses are supplied by §§26–28,
not additional matching external frame bits. ∎

**Corollary 29.2 (preserved original target and actual terminal use).**
Continue the same run from $D_{\rm GP}$ through its fixed `Stop` suffix.
It reaches the original INITIAL-$q_1(\beta)$ consumer output and global
halt with no new private preparation or altered verifier. This suffix
has its actual terminal row, complete snapshot, both journal ends,
receipt delivery, consumer checks/output/ACK and terminal return.

*Proof.* The original seed acquisition, boot/prior binding and original
source occurrence were preserved throughout. The explicit handback
copies the saved initialized original Stop configuration into its
actual active word representation. The bank compiler preserves the
saved fields through all intervening source services, and no GP
append overwrote the old 25/27 material. The original configuration
copy/stack routines therefore establish the original interpreter's
actual entry, with its unchanged Turing table24 and completed loan.
This is a paid local configuration installation, not an assumption
that arbitrary new 25 bytes are an old valid configuration. Executing
that table gives the proposal $(0,B,1)$ for the actual original beta.
The output is actually written/sealed on 31; its complete dependencies
and terminal control packet are copied to producer21 before Halt
commits. CAP6.3 freezes both complete journal indices only after the
terminal row ACK and builds/copies the actual `SEG-P1` snapshot and
all dependencies. CAP6.5's terminal-instruction check uses the actual
original Turing table and acquired terminal material through PR57.D5's
interpreter. It is not asked to interpret GP native rows as a Turing
table or to invent a NativeLocal event for source-free primitive work.
Every GP call used the original guarded source
body, every maintenance row has its true historical guard/layout,
and the raw/refused calls retain their complete contexts. Thus the
actual initial beta survives the original verifier replay. The
stationary acquired beta prefix distinguishes it from alpha in
$\mathcal T_1$, as in Theorem 9.2's original consumer proof; later
lawful events do not remove the actual surviving beta. The whole
nonempty compatible initial-source fibre therefore has the proposed
INITIAL target. CAP Theorem 6.6 and PR57.T4 give acceptance.

CAP6.5–6.7 then construct and deliver the actual `SEG-R1` receipt
on route51, with complete original binding and both frozen journal
ends. Consumer40 checks its acquired local payloads and expected
bindings, allocates/copies/seals the target on its original work ports,
executes the genuine OUT, ACK and return, before global halt CTL.
All these graphs and their costs remain in this same run. No new
Ready, absorbing-halt re-entry or second policy invocation follows. ∎

## 30. Retained source relation, exact accounting and theorem scope

**Definition 30.1 (retained relation and comparison hypotheses).** The
relation proved here consists of actual beta-boot/parked-prefix
correspondence in Theorem 25.3, the record-to-controller representation
of Theorem 26.3, the actual packet/service/response representation of
Theorem 27.3, and the selected endpoint components

$$
\bigl(\varepsilon,\ t',\ h_{\rm ref}\bigr)
\quad\longleftrightarrow\quad
\bigl(\varepsilon,\ E(t'),\ w(t'),w(t')\bigr).
\tag{GP.7}
$$

The source occurrence is the same original $\xi$ within either
alternative. Its private ingress is not repeated; actual source16
and its path's continuing $\phi_K$ remain the source. Each reserve
extends its old logical address map, retaining old intervals and
their original handle meanings. All old/new origins, descriptors,
read/write rights, rows, source events, counters and actual partially
constructed states are retained. Row equality in a channel identifies
payloads with the same complete origin; it does not identify recipient
addresses, owners or versions. New GP policy state and controller code
are explicitly different from the old fixed Stop apparatus. The
comparison does not equate the alternatives' full responses, histories,
literal root reads, native labels, addresses or costs.

The finite-fragment discipline in Lynch–Vaandrager, *Forward and
Backward Simulations, Part I: Untimed Systems*,
[§3.2](https://groups.csail.mit.edu/tds/papers/Lynch/IC95.pdf), requires
initial coverage and a matching finite fragment with the same external
trace for every related transition. Reissig–Weber–Rungger,
*Feedback Refinement Relations for the Synthesis of Symbolic Controllers*,
[Definition V.2](https://arxiv.org/pdf/1503.03715v3), additionally uses
the same admissible input in its two transition systems. Leroy,
*A Formally Verified Compiler Back-end*,
[§3.7, Definitions 10–13](https://arxiv.org/pdf/0902.2137v3), relates
initial/final states and transitions with matching event traces;
its plus/star diagrams do not erase unmatched visible events.
These literature-attested hypotheses delimit (GP.7). This apparatus
has an extra visible raw refusal, packet/channel work and possibly
different maintenance and encoded context words. No complete external
trace equality or same-input feedback-refinement theorem is inferred.
The new result is the repo-derived source-specific earned connection,
not a new general parser/compiler/composition theorem, worldwide
novelty claim or Lean verification claim.

**Theorem 30.2 (all actual costs and the removed premise).** Let $z$ be
any completed primitive prefix in this apparatus, including all boot,
preparation, acquisition and GP work that precede it. The actual CAP
bill is still

$$
\operatorname{Bill}(z)=
\bigl(\nu(z),\ 2\nu(z),\
S_0+b_{\rm ctl}(z)+8A_{\rm phys}(z)+8\nu(z)\bigr).
\tag{GP.8}
$$

Each new graph has the exact evaluation recurrence of CAP Definition
7.1, applied to its expanded primitive rows at their actual entry
configurations. After $\widehat p$ the source/maintenance call count
through $D_{\rm GP}$ is $2+2[\varepsilon=\mathsf{accept}]$.
Only the first raw frame and the outer choices use externally supplied
bits in this suffix. The number of later matching external IN bits
for computed maintenance/final modifier frames is exactly zero.
Their complete words, packet copies, canonical construction and
returned-response work nevertheless have their full actual costs.

*Proof.* Partition actual primitive occurrences by their actual opcode
and disjoint owner/purpose phase, as in PR57.D9 and CAP7.1. This
includes the original-boot GP rows/table/data, $L_*,G_*$ and $r_*$
initialization, public guard ingress/copy, every retained preparation
and raw acquisition, closed descriptor/row scans, input projection,
25 export/reimport/state installation, replay/count/encoding, packet27
construction, route49 copy, producer canonical construction, original
source/maintenance execution, rows/dependencies/checks, final ACK,
source token/idle, return-reader loans/state exports, retention and
the optional original verifier/consumer suffix. An EX inside a helper
has its actual one occurrence and ordinary constructed-cell coordinate;
it is not charged again as another whole-phase allocation. Every
status, delimiter, descriptor, old bank/stack/state version, gate tape,
candidate, channel block, row and receipt remains constructed.

The recurrence counts one for each such enabled primitive, including
all positioning, loop tests, seal/TOK/CTL and state-install edges.
An IN consumes exactly its actually supplied bit. Definition 27.1's
computed-frame graph has no IN row: its reads are of the actually
acquired producer packet and its constructed public fields. Thus
there is no later external matching-input condition to count or
assume. There is still positive work to emit and copy every bit.
The raw stage, one final call and two optional maintenance calls give
the stated count. Induction on primitive occurrences now gives (GP.8)
by CAP Theorem 7.2; the disjoint phase counts also retain every
coordinate of (LA.10), with planning/internal construction now inside
the actual native run. GENERAL's independently specified structural
tariff stays separate. No equality of cross-path bills follows. ∎

**Definition 30.3 (supplier reuse and residual domain).** The mathematical
suppliers used inside this connection are the acquired-refusal and
selected-commit results of §§21–24, the $E$/count identities of §§15–16,
ABT12's existing finite inverse, the word realization and actual
readers of §§2–3, PR57.D1/D5/D7/D8/T4's primitive/public-policy/
record/consumer contracts, and CAP2–7's seven-tag canonical construction,
guarded source semantics, descriptor/row/channel/return/cost graphs.
CAP8.1–8.3 already supply a positive Native packet/return controller
on their own grammar and safe-growth task. The present GP1 version
reuses their explicit owned-packet, retained continuation and genuine
return discipline; it does not reprove that result or identify its
packets with guarded GP packets by a shared port name. The original
Stop Turing table is retained separately and genuinely resumed by the
handback, keeping CAP6.5's original table interpreter applicable.

The removed premise is exactly later matching external supply of
computed maintenance/modifier frames after raw acquisition in this
one-use domain. Actual public initialization, raw operand supply,
current rights/backing, canonical installed versions, finite reached
work, all costs and the attained tight beta-derived preparation remain.
There is no arbitrary late-guard input, uniform duration, automatic
admission at Busy/partial/halt cuts, repeated ARC closure, repeated
policy-use theorem, full-$Q$/trace/cost equality, physical executor or
alpha/beta-to-diffusion/AURIC/OTF source identity. The selected local
use and original INITIAL consumer leave the broader mutual-recovery
objective with its other original-source obligations.

## 追加锚（本行以下为增补区）
