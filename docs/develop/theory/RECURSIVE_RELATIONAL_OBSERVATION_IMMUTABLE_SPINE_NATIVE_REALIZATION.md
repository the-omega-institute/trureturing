# Recursive relational observation: immutable word spines at the paid native boundary

This volume gives ordinary source-specific definitions and proofs for the
candidate `IS2-immutable-spines-direct-native/v1`. It uses the paid boundary
ML-I and literal primitive boundary ML-P of
[Monotone LAB Indexed Execution](RECURSIVE_RELATIONAL_OBSERVATION_MONOTONE_LAB_INDEXED_EXECUTION.md),
abbreviated ML. It does not establish a completely backed native UJB session.
In particular, its finite native prefix bound is not a sufficient reservation
for one of the complete acquired-input evaluations.

The definitions and proofs are `repo-derived` mathematical prose, without a
fresh Lean check or a claim of originality for persistence or universality.
The implementation source is the private experiment tree's
`rro-lab-execution/native-prerequisite/immutable_spine.py`;
`immutable-spine-results.json` contains its finite results. The implementation
and ordinary mathematical exposition have one author under the repository
reasoning and theory-volume skills; independent acceptance is not asserted.

## 1. The actual domain and the object that is shared

**Definition 1.1 (fixed interfaces).** Retain ML-I's actual initialized owned
objects, original current rights, literal field accesses, reference assignments,
null/equality tests, finite native transition graph, allocation/grant boundary,
finite bit connections and local acknowledgements. Retain the original
stationary observation root and UJB5.2 port separately. Neither this root nor
an original Read reply is represented by an evaluator value token.

The mathematical domains remain every finite bilateral non-erasing B program,
finite input and finite run prefix, including immediate halt and prefixes of
nonhalting computations; and every accepted ML-F arithmetic frame with
$N\ge4$, finite represented rational $0\le a/b\le1$, $b>0$, arbitrary
original-indexed masks/values and a finite cylinder list. Endpoint and
unreduced priors remain valid. An actual cache outside the prior's support
is still an input. An unrepresented arbitrary real is not an input.

**Definition 1.2 (immutable spines).** A word head is null or a reference to
an auxiliary cell with a tail reference and a payload reference. Payloads are
references to two distinct, read-only owned LAB leaves $z,o$, respectively
$\alpha,\beta$. A nonnull tail points to an earlier completed cell. Decode

$$
 D(\mathsf{null})=\varepsilon,\qquad
 D(c)=bD(c.\mathsf{tail}),\quad
 b=\mathbf1_{c.\mathsf{payload}=o}.
 \tag{IS.1}
$$

A published cell's tail and payload never change. A register is a separate
mutable head slot. Different registers may have the same head or shared tails.
All allocated cells, including popped and unreachable cells, remain retained;
this construction performs no garbage collection, reclamation or hash consing.
Heads are actual references. No integer denotes a runtime object or label.

A payload reference shares a read-only value, not a logical tree position.
Spine cells are auxiliary paid material, not several children grafted onto one
LAB tree leaf. Their field operations are supplied by ML-I. Thus this is a
conditional realization using paid memory, not a derivation of memory or a
source port from the two names $\alpha,\beta$.

**Definition 1.3 (source translation).** Keep the bodies, call convention,
scalar representations and combinatorial routines of ML §§10–11. In the
assembler `constructor_ir.Graph`, replace each emitted `clear(r)` expansion
by the instruction $r:=\mathsf{null}$ and each `copy(s,d)` expansion, for
distinct names, by $d:=s$. A self-copy emits nothing. Keep every other
assembler method and every body in `evaluator_program.py` unchanged.

The resulting finite instruction algebra is halt, goto, constant-bit push,
pop, peek, head copy and clear. Push initializes a fresh cell with the old
head and the indicated payload, then publishes its head. Pop reads a nonempty
head's payload and tail and assigns only that register's head; empty pop leaves
it empty. Peek changes no head. Both select the same empty/zero/one successors
as ML-S. No word operation is a runtime arithmetic callback.

**Theorem 1.4 (value correspondence, with the correct cut domain).** For any
finite assembly respecting the original assembler's reserved `__copy` scratch
name, the translated and original programs have equal client-register words
at every corresponding assembler expansion boundary. The removed private
`__copy` register is interpreted as empty at these boundaries.
The assertion applies to every finite prefix of those boundaries, without a
termination premise. It preserves each conditional successor and terminal
Boolean. All original word and arithmetic routine contracts consequently
hold for the translated routines on their complete represented-word domains.

Proof. Acyclicity of completed tails makes (IS.1) well-defined. Initially all
heads are null except the actually loaded input. Head assignment duplicates a
word value without changing either word's cells. Clear installs the empty word
without changing any aliased head. Fresh push creates exactly the specified
one-bit prefix; pop and peek read the same leading symbol, and only pop
changes its selected register. These assertions hold even when two registers
initially have identical heads or overlapping tails. No instruction changes a
published tail or payload.

The original copy expansion has the word effect stated in ML10.2–10.3, including
an unchanged source and an overwritten destination; its clear expansion empties
only the selected register. Thus the replacements have identical word effects.
The private copy scratch is empty at each original copy boundary and is not
read by the client. All other emitted instructions retain their meanings.
Induction over expansion
boundaries proves the claim. A loop or call changes no part of this argument:
its branch reads the same word, so it selects the same next expansion. The
original routine contracts and their termination measures in ML10.3–10.5 then
apply. This is a source transformation, not a claim that the new program
executes the abandoned copy loop's internal cuts. $\square$

**Proposition 1.5 (the changed cost term).** For a source word of $m$ bits,
the original distinct-stack copy emits $3m$ pushes, in addition to its pops,
tests, destination clearing and control. The replacement emits one head copy
and zero pushes. Clear similarly emits no per-bit pops or pushes.

Proof. Transfer to the temporary pushes $m$ bits; restoring the original and
constructing the destination pushes $m$ bits into each. The replacements are
Definition 1.3's literal instructions. Their save-before-publish native paths
below have length independent of $m$. Other reverse transfers, vector scans,
new arithmetic bits and service copies remain executed and paid. No statement
about their share of total time follows from this local calculation. $\square$

## 2. A literal native graph and its internal cuts

**Definition 2.1 (material layout and initial seed).** Reserve a finite chain
of $K$ supplied cells, each with four reference fields, eight bit fields and
its current grant. Every reference and bit is initialized before use. Extract
a cell by testing the actual pool head, retaining it, reading its next link,
advancing the pool head and clearing the extracted next field. A missing grant
or exhausted pool refuses; it does not manufacture a reference or a result.
Unused fields and cells remain charged.

The native seed first extracts a known actual $\alpha$ root with null
parent/left/right/header. Test its null left and right fields. Extract a marker,
set its parent to the root, and publish it as the root's left field. This is
AA20.2's $P_\varepsilon$ template. Test the resulting $\beta$ guard. Extract
another marker, a right child and a route header, all initialized; set the
new marker's parent to the old marker and the right child's parent to the root.
Publish the old marker's left child, root's right child, and root's header in
that order. This is AA20.2's $S_\varepsilon$ template. Its result is
$\langle\beta,\alpha\rangle$, with $o$ the old marker and $z$ the right child.
The header has empty head and tail. Both events have depth zero, so there is
no proper-ancestor append to omit. Five reserve cells are used. These leaves
are never subsequently promoted or split by this evaluator.

**Definition 2.2 (literal lowering).** Every register selector and field
selector in the translated finite program is fixed wiring. Lower a head copy
as read-source-slot, write-destination-slot; clear uses the initialized null
slot. A field read is read-base-slot, retain-address, read-that-literal-field,
write-result-slot. A field write is read-base-slot, retain-address,
read-value-slot, write-that-literal-field. Binary reads/writes have the
corresponding bit latches. Tests are distinct vertices and choose their wired
successor. A push uses Definition 2.1's pool path, writes tail and payload,
then writes the published head. Pop captures the old head, tests null, reads
its payload, reads its tail into the selected head slot, and takes the literal
zero/one successor. Peek omits the head update. Token equality is checked
against both actual tokens; any other payload refuses. Halt writes its Boolean
to the actual `result.ok` bit slot. True selects the computed printer; false
selects a literal BadFrame printer. Both have End/Ack/Return terminal paths.

Before a head-changing source instruction, save that register's old head in
an actual `busy.old` slot. During its private lowering, the native location
identifies the source label and phase. Before the save completes, the register
has not changed. Afterwards `busy.old` recovers its old value even after
publication. All other register heads still have their old values. The
instruction commits at entry to its selected next source label; a private
native successor is not another source instruction.

The native machine has actual retained read-reference, saved-reference,
address and control-reference latches, and binary read/phase/latch state.
A primitive read returns into its retained latch. Code selection, binding,
actual successor-reference read and control-reference assignment are charged.
The labels denote ML-P primitive vertices, not an interpreted word-operation
or an unrepresented Python program counter. The hosted check interpreter
models these same finite vertices; its observer maps do not select a successor.

**Theorem 2.3 (prefix realization and completed-instruction converse).** For
every finite translated instruction graph, every finite input word of length
$L$ and every prefix with $T$ completed source instructions and at most one
unfinished next instruction, the literal graph has legal initialization and
internal prefixes whenever the required current grants and primitive
completions are supplied and

$$
 K\ge5+L+T+1.
 \tag{IS.2}
$$

At source boundaries it has exactly the translated word state. Every internal
prefix has the saved-head, loader, seed or printer interpretation above. Every
completed source instruction has exactly its prescribed successor; refused
or unfinished paths add no completed instruction. The claim includes immediate
halt and finite prefixes of nonhalting source programs.

Proof. Seed legality follows directly from its two checked AA templates. Its
incomplete attachment phases retain the fresh cells and native location, so
an unfinished template is never interpreted as a complete LAB tree. The loader
below uses one distinct cell per bit. Each source push consumes one further
cell; no other source instruction consumes one. Hence at most $5+L+T+1$ cells
have been extracted at any claimed cut. All initial fields and all current
pool links are actual initialized material.

For a source instruction, expand the literal paths in Definition 2.2. Source
capture precedes the destination write, including overlapping operands. A
published spine is never a field-write target. Null pop, both payload branches,
push and assignment therefore have exactly Definition 1.3's effects. A private
path has no internal cycle; its only variable choice is the inspected Boolean
or null value. The saved-head slot recovers the committed old word throughout
publication. At the next source label the new heads give exactly the next
word state. Induction over commits proves forward correspondence and the
converse. A guard failure has not performed its guarded update; any earlier
partial seed or pool effects remain retained in the busy state. No refusal
rolls them back. $\square$

This theorem concerns a supplied finite native graph and reserve. Its generator
is finite for every finite source graph; no hidden source or numeric answer
is used during graph construction. The standalone native installer copies
actual public descriptors and relocates their actual references by ML19–20's
existing `Installer`. The original descriptors, forward links, installer
seed, initialized reserve and targets are all retained. Installation of the
complete fixed UJB candidate has not been executed by the finite checks here.

## 3. Actual loading, computed return and the same-source interface

**Definition 3.1 (loader and printer).** The loader follows an actual finite
input chain with bit field zero and next-reference field one. It reads each
bit, selects $z$ or $o$, extracts one cell and initializes its null tail and
payload. Before publishing any stack register it builds the chain in input
order, linking the previous private tail once. At End, publish its head in
register zero. The input chain is retained and never modified. An incomplete
external frame remains the existing receive handler's waiting state; it is not
an empty accepted arithmetic word.

On successful halt the printer follows the computed register-zero spine. It
emits `01`, traverses the spine emitting one length mark per cell, emits the
zero delimiter, then traverses it again emitting the actual payload bits.
It emits End, obtains local Ack and executes Return in that order. Thus its
output is exactly ML-F `reply(1,w)` for the computed word $w$, not a word read
from a reference evaluator. Output occupancy and acknowledgement backing belong
to the paid connection. No numerical answer is installed in this printer.

**Corollary 3.2 (ordinary all-domain evaluator consequence).** Suppose the
actual accepted ML-F arithmetic chain is the loader's input and its complete
literal execution has sufficient material and primitive completion. On all
Definition 1.1 arithmetic inputs, the computed register-zero output is precisely
ML10.5–11.6's output for UJB16.2, and the printer emits its framed return.
This includes zero evidence and emits conditional ratios only at a positive
normalizer. It has no machine-word bound on arithmetic values, $N$, indices,
array lengths or cylinder counts.

Proof. The loader establishes the same input word, not merely a parsed tuple
with silently normalized fields. Apply Theorem 1.4 to the unchanged routines
and Theorem 2.3 to their literal lowering. ML's existing word/scalar,
combinatorial and output contracts then give the stated result. Token equality
reads one bit of a finite spine, not a 64-bit arithmetic bank. The output scan
has exactly the length and payload in Definition 3.1. $\square$

**Definition 3.3 (particular service cut relation).** The existing service
frontend retains the original port binding, public prior, original-indexed
cache, actual request chain, ordered occurrence-receipt chain and pending
fields. Its `evaluate.begin` cut has `eval.busy=1` and the accepted chain
at `eval.input.refs[1]`. The necessary entry relation for IS2 is

$$
 \mathsf{received}=\mathsf{eval.input.refs[1]},\qquad
 \mathsf{owner}(\mathsf{received})\text{ grants the actual reads},
 \tag{IS.3}
$$

with both sides the same physical chain, or a separately charged actual
bit-for-bit transmission retaining both backings. The actual input contents
must be the acquired frame, including its original indices and represented
prior; a reference answer cannot satisfy (IS.3).

The necessary return relation connects the computed spine and its emitted
`01 V(w)` bits to the same service's output connection, then clears its busy
state only after the actual End/Ack/Return path. Return reaches that service's
entry handler. A later Read must traverse its unchanged original connection,
produce the port's real reply, append a fresh occurrence receipt even for a
repeat, and update the cache at the original index. Close uses that service's
original terminal handler. A law value cannot fill the reply latch.

**Proposition 3.4 (scope of composition with UJB17.1).** If the entry and
return relations of Definition 3.3 and the old service's entire primitive
prefix relation are realized at common cuts, the new evaluator preserves
UJB17.1's conditional laws and the old service's actual stationary Read
continuation on the unchanged source. Without those realized relations,
Corollary 3.2 and a hosted acquisition replay do not establish this conclusion.

Proof. At entry, (IS.3) supplies the actual arithmetic input. The retained cache
and receipt chains are disjoint from the write targets of Definition 2.2;
evaluator aliasing concerns value tokens, not sample or receipt identities.
Corollary 3.2 supplies the computed return. At its acknowledged return cut,
the frontend's original handlers again have the same original root, original
indices, cache and receipt prefix. Apply the already proved original service
correspondence to each subsequent Read, and UJB17.1 to its full indexed law
where its normalizer is positive. Zero evidence retains its designated output.
Induction gives the conditional statement. Neither of its two cut relations
is supplied by equality of numerical answers alone. $\square$

The native IS2/service splice in (IS.3) and the full acknowledged-return
relation are unresolved for this candidate. The finite native checks use a
standalone actually initialized input chain and a computed printer; the
74/73/149-call replays below exercise the existing hosted acquisition path.
No check here performs a Read after a completed IS2 UJB evaluation. The
candidate's allowed primitive set does not yet install the original source
connection or the service's indirect-return bindings.

## 4. A precise reserve census and the missing full-session terms

**Definition 4.1 (one standalone native owner).** Let $F$ be the literal
native vertex count, $R$ the number of one-reference register slots and $B$
the number of one-bit register slots. Count all $K$ reserve cells, $L$ retained
input cells, all code, and the four-reference/eight-bit native latch cell.
The public descriptor blocks have counts

$$
\begin{aligned}
 n&=K+L+F+R+B+1,\\
 r&=4(K+L+F+1)+R,\\
 b&=8(K+L+1)+21F+B.
\end{aligned}
\tag{IS.4}
$$

Each code block has four reference fields and 21 installation bits. Its
selectors are fixed literal wiring after installation. Each public block
also has its retained directory link and a Source descriptor with
block/next/forward links. Let $(O_s,R_s,B_s)$ count the actually installed
initializer seed, including all of its bit-scanning wires. It includes the
unused 32768-bit scanning path of the reused installer. No term is removed
because the candidate itself does not use pages.

**Theorem 4.2 (exact standalone retained census).** With the existing
installer header layout, at its completed installation cut, the native owner
has

$$
\begin{aligned}
 O&=3n+1+O_s,\\
 A&=2r+5n+15+R_s,\\
 C&=2b+2+B_s,\\
 S(w)&=O+wA+C.
\end{aligned}
\tag{IS.5}
$$

Here $A$ is a reference-slot count, $C$ excludes grant bits, and the $O$
term pays one retained grant bit per object. For a fixed adequate reference
width $w$, these counts remain unchanged throughout its standalone execution,
including refusals and its computed printer. Every installation prefix is
bounded by this completed census in the same reserved layout.

Proof. The retained public block and Source descriptor contribute $2n+1$
objects, $r+4n+15$ reference slots and $b+2$ bits, including the initializer
header. The target contributes $n$ objects, $r+n$ reference slots and $b$
bits. Add the seed to obtain (IS.5). Installation allocates each target at
most once and initializes its entire declared layout; the prefix count cannot
exceed that total. Extracting a pool cell does not allocate another object.
Seed, loader, stack execution and printer change only already counted fields.
The native CPU and every old unused or unreachable frame remain in that
layout. Thus counts do not fall at a pop, clear, Return or refusal. $\square$

**Proposition 4.3 (effective prefix bound is not a session certificate).**
Let $Y$ be the returned word length and $T$ the number of executed translated
source instructions. A successful standalone execution is bounded by a
finite effective literal operation vector obtained from its fixed graph and
these integers. For example,

$$
 V_{\rm actions}\le F\bigl(T+2L+2Y+20\bigr)
 \tag{IS.6}
$$

is a conservative bound, apart from separately counted installation and
physical connection completion. Code-label/binding reads, grant tests,
reference/bit latch operations, tests, control and navigation are charged in
that vector; reference-bit work uses the actual width. No $T$ bound for a
complete acquired-input UJB session follows by substituting its input length
into (IS.2) or (IS.6).

Proof. Each source instruction's private lowered path is acyclic and has at
most $F$ vertices. Each input iteration, termination path and each of the two
output traversals has the same finite bound between its loop gates. The seed
and fixed printer prologue/epilogue fit the remaining constant. All field
selectors are fixed and all traversed fields are actual. This proves (IS.6)
by path concatenation. But $T$ is an outcome of the complete translated
execution, whereas a prospective reservation must be fixed before that
execution. A formula conditional on this unknown outcome is not the missing
independent upper bound. $\square$

**Definition 4.4 (the unresolved sufficient envelope).** For a selected
complete chronology $x$, an adequate prospective account requires independently
justified bounds $U_{\rm push}(x)$, $U_{\rm step}(x)$ and $U_{\rm out}(x)$
for the translated evaluator, its actual service, and all unfinished phases.
Then $K\ge5+L+U_{\rm push}(x)$ pays the evaluator extraction demand; service
extractions require their own additional amount if the pool is shared. This
must be combined at the same actual cuts with the inherited source, old jobs,
receipts, cache, input/output, grants, pending fields and cleanup backing.
No retained old job or receipt is identified with an IS2 cell or removed.

Let $\mathcal O(t)$ be these actual owners, including all preparation,
source and target descriptors, initialized unused pool, code, native latches,
frontend/connection/provider, inherited jobs and observer material. Required
host bounds have the form

$$
\begin{aligned}
 H(x)&\ge\max_t H_{\rm actual}(\mathcal O(t),\text{overlap at }t),\\
 W(x)&\ge W_{\rm actual}(\text{preparation, installation, session,
 observers and cleanup}),\\
 H(x)&\le H_{\rm reserved},\qquad W(x)\le W_{\rm backed}.
\end{aligned}
\tag{IS.7}
$$

The quantities are host bytes/work for the chosen host, distinct from the
native bit/operation vector. If a common reference width is used, it must name
all actual simultaneously referenced owners, not just IS2's internal pool.
If widths migrate, old/new overlap and rewriting belong to the same maximum.
The standalone installer's width is not a proved composed-session width.

For the current Python prototype, retained objects include the original and
translated assembly, field graph, literal public blocks, Source descriptors,
relocated targets, initializer wiring, Python lists/maps and observer frozen
sets. Even (IS.5) with an adequate $K$ is not a host upper bound for them.
Likewise, original-source navigation and the service's unary validation,
receipt construction, repeated-index scans and acknowledgement work are not
removed by replacing evaluator copies. UJB16.3's rational-operation estimate
bounds only its stated arithmetic coordinates; it supplies neither these
host bounds nor the translated instruction counts.

For each of the three chronologies below, $U_{\rm push}$,
$U_{\rm step}$, the completed native service relation, and the two host
bounds/reservations in (IS.7) remain unresolved. No complete-run reservation
is supplied. A physical machine's RAM total is not such a reservation.
This is an exact missing term for this class and these inputs, not a proof
that the candidate, a different algorithm, or the full authorized family is
impossible. The old C and FS1 lower bounds keep their original directions and
apply to their unchanged routes; they are not lower bounds for IS2's changed
unexecuted copy expansions.

## 5. B execution, geometry and the information retained for continuation

**Definition 5.1 (separate mutable B material).** Use the existing ML-C
comb/native B installation for the generic bilateral B obligation. Its input,
program, reserve, control, busy cuts and routing are separately paid with
ML §§2–3,18–20's domains and hypotheses. Its tape bits are distinct mutable
LAB positions. In particular an M operation may not promote an IS2 zero token:
that would change every word occurrence referring to it. A joint installation
must include both actual graphs, both reserves and their simultaneous owners
in (IS.7). The compact IS2 evaluator does not substitute for the B graph.
NWMG's mature simulation is reused on its own tape-time domain, with no new
universality claim or conversion of tape time to native work.

**Proposition 5.2 (spatial image and sufficient annotated state).** AA17.3's
support/boundary conversion applies to the actual seed tree
$\langle\beta,\alpha\rangle$ and to the separately realized B trees. For
continuation of the proposed composed service, a sufficient state includes
these trees, all actual spines and head slots, source and code bindings,
native PC/latches, busy old head and phase, current grants/meter, all receipt
occurrences, original-indexed cache and pending connection state. On an actual
realized image with this state, the existing PG response/update and Typed
Residual Resource Boundary §§3,6 suppliers apply on their stated domains.

Proof. The seed is reached by the legal AA templates, so AA's hypotheses hold.
The annotation retains every field tested by the literal successor rules and
every source/service field named by Definition 3.3. Thus equal annotated views
have equal legal actions, responses and updated annotated views, with the
same inherited resource meter. This is precisely the factorization condition
required by those suppliers. The existing reachable ML31.4 example
$W=(R,M)$ on 00 already has the same bare work tree before and after its first
move and different next actions; it remains the required concrete witness for
the separate mutable B component. No redundant geometry-only decoder can
restore that missing head/control state. No minimum-memory or actual serial
history recovery follows. $\square$

## 6. Bound finite evidence and source correspondence

The reproducible private check uses the unchanged original assembler for the
original evaluator and checks its serialized bytes against
`constructor/evaluator.stack.bin`. It then generates, but does not execute
or fully install, the fixed translated evaluator. Its deterministic source
identity is SHA256
`7257d4ad4b5730860ad811d41c3057ea6accdf1c413dbf7af75be206a5b24595`.
The resulting counts are:

| Quantity | Actual generated count |
| --- | ---: |
| Original ML-S source states | 22202 |
| Translated source states | 10983 |
| Translated register names | 360 |
| Head-copy source instructions | 863 |
| Clear source instructions | 208 |
| Push source instructions | 2556 |
| Literal field vertices | 59543 |
| Literal native vertices | 216968 |
| Reference register slots | 381 |
| Binary register slots | 4 |

These are static code counts, not dynamic push counts, material reservations
or a measured total speedup. The native count includes source-boundary entry
vertices, saved-head paths, seed, loader and computed printer. The fixed
installer seed is additional material as required by (IS.5).

The small actual native installations use $K=2048$, with exact alias,
addition and multiplication checks and addition of a 131-bit operand. Empty
input with immediate true and false halt is checked at the actual terminal
bit and its framed output. The
checks inspect every tested native cut for immutable input backing and reject
writes to published frame/token fields. The emitted result is checked
externally against the independent small arithmetic result. Additional checks
exercise an empty pool and a denied current grant at an unchanged native PC.
The expected answer is used only by the checker, never by native execution.
These finite cases neither prove the universal theorems nor establish any
complete UJB consumer or composed-source reservation.

The three source chronologies are exactly the preexisting acquisition schedules,
including the final acquisition-only old-slot probe. They keep every real
occurrence, all four replies, partial slots and original indexed cache values.
Their acquired arithmetic frames have the following unchanged identities:

| Chronology | $N$ | Bits | Calls / operand bits | SHA256 of acquired frame |
| --- | ---: | ---: | --- | --- |
| positive-full | 4 | 387 | 74 / 2176 | `37dfee71eda5a8fbee3d373aab446982f15976785ef965ec2e4a1b6ea98c5402` |
| positive-partial | 4 | 386 | 73 / 2115 | `1a4ae049cf81b1f434398aa05cb8eabcf4d8689f7873f8d75f9ae1e870c34764` |
| null-nine-distinct-left | 9 | 839 | 149 / 9676 | `f5518d034eef5bd00c87ff9d43c5ca878ef9d012f47e04bedcbe45163ee3e29d` |

Replaying this existing hosted acquisition is a source/data binding check.
It does not claim that the candidate's computed-output/Read service cut has
been reached. The exact remaining gap is (IS.3), its acknowledged return and
actual continuation relation, and the prospective bounds/backing of (IS.7).
A larger unbacked evaluator run is not a check of either missing premise.

**Source and literature status.** The native realization, arithmetic consumer
translation and census above are `repo-derived` interface results. ML10–11
supply the exact scalar/UJB application; UJB16.2–17.1 supply the original
once-shared full-injection indexed laws, repeats and null semantics. No law
is rederived by the experiment's runtime. The read-only value-token mapping
never replaces the original source or an authentic reply.

The repository's licensed `D5/S0/Computability/BinaryMachine/StackProgram.lean`
supplies the original five-constructor step convention, with the source and
license stated in ML's bibliography. The copy/clear extension is the explicit
ordinary construction here; no new Lean client is asserted.
[Okasaki, *Purely Functional Data Structures*, thesis, §1.1 and §3.5.2](https://www.cs.cmu.edu/~rwh/students/okasaki.pdf)
attests persistence and common-tail sharing; those general mechanisms are
`literature-attested`. This volume claims no lazy-evaluation or amortized
bound from that text. NWMG and the original AA/ML suppliers retain the exact
scope recorded in the repository's computability bibliography.

C117 at source pin `6b6539921bf3fde0f84f85fdda6c284b5891ae98`, Theorem25.2,
supplies a conditional whole-future positive-generation repair only with its
actual legal words, exact expansions, full record constraints and positive
margin. Those hypotheses do not install an IS2 field read, output connection,
original Read edge or resource reservation. None is transplanted into (IS.3)
or (IS.7). Complete native UJB execution, independent experimental and
reconciliation checks, and acceptance remain unestablished.

## 追加锚（本行以下为增补区）

## 7. A service-bound native entry and return

**Definition 7.1 (the composed immutable-spine service).** Fix the
particular frontend of ML22–24, its actual original port $o$, the public
$N,a,b$, its original-indexed mutable cache and its ordered occurrence
receipts. Retain its receive, validation, Read, receipt, cache-update,
printing and Close paths. The evaluator is the immutable-spine translation
of §§1–3, with its private reference and bit names disjoint from the
frontend's names. Only the actual reserve and the null binding are shared.
The source connection, cache cells and occurrence records are not value tokens.

At the frontend's accepted arithmetic entry, first set its busy bit and
read the head of its actual accepted header:

$$
 h=\mathsf{eval.input.refs[1]},\qquad
 \mathsf{is2.received}:=h.                                      \tag{IS.8}
$$

This is a reference read followed by a register write, not a transmission
of a parsed tuple. The loader follows these very cells. Initialize the
logical stack heads to null by separate register writes; do not clear
any old backing frame. Install a return register whose value is the
actual native location $r_{\rm eval}$. At $r_{\rm eval}$ the first action
clears the busy bit, and its literal successor is the original frontend
return handler. Its successful path reaches the original receive entry.

Before ordinary frontend printing, bind the same return register to the
original frontend return handler. End and Ack retain their original
ordinary-output meaning. A Return requires the acknowledged output phase,
reads the installed return register with current rights, and puts that
actual reference into native control. A native indirect routine return
likewise reads its supplied return register; it does not interpret a
host integer as a code address. Literal code-reference binding and this
indirect reference transfer are the existing ML-P binding/control
interface, lowered to literal native locations. Original-port bit,
End and Ack operations retain their separate connection selection.

The printer reads the computed register-zero spine and uses the same
ordinary output connection as the frontend. A local acknowledged bit,
without the installed return reference and its actual control transfer,
does not meet this definition. Code locations, return slots and their
grants are material in the composed installation.

**Theorem 7.2 (candidate-specific service correspondence).** Suppose the
composed installation of Definition 7.1 is supplied, every tested current
right is present, its declared finite allocations are backed, and the
original input/output/provider operations complete. At each accepted
arithmetic entry, (IS.8) realizes (IS.3) on the same physical chain.
For every accepted arithmetic frame the evaluator's completed output is
its unchanged ML10–11/UJB16.2 result, emitted by Print, End and Ack.
Its actual Return reaches $r_{\rm eval}$ while busy is still one; only
then is busy cleared and the original frontend resumed. A subsequent
Read, including an old original slot, calls $o$ and appends a fresh
occurrence receipt. Close reaches that frontend's terminal handler.

Proof. The accepted header is produced and validated by the original
frontend. The two actions in (IS.8) retain its actual head identity;
every loader field read tests the current grant on that backing. No
input bit is obtained from a numerical reference result. The disjoint
namespace makes every evaluator write target either its own register
or a newly extracted frame. Its source/header reads do not target the
source connection, cache or receipt links. Theorem 2.3 and Corollary 3.2
therefore apply to this actual word.

The printer follows that computed spine, so its length marks and payload
are the computed frame. End precedes Ack. Return reads the installed
reference to $r_{\rm eval}$; the native control write is part of Return,
rather than an observer's replacement of the counter. The busy bit has
no write on this path before $r_{\rm eval}$. Its first write then clears
busy and its successor is the original return handler used by ordinary
frontend answers. This proves the two common-cut relations required
by Proposition 3.4.

The unchanged ML23 paths then transmit the actual operand to $o$,
capture its actual two-bit reply before Ack, and append a new record
header with that operand and reply. Even an equal operand uses a newly
extracted header; it is not identified with a previous equal record.
The classifier's slot cursor walks the original cache spine, so equal
data at indices zero and fifteen do not identify those cells. A
repeated informative reply is checked against its old value; the
original mask/value pair is retained. Constant and absent replies
retain their original behavior. Induction over the finite Read list
proves ordered-record and cache preservation. Close writes the original
closed bit, prints its original terminal frame and returns to the
original closed wait. $\square$

The hypotheses include actual primitive completion and adequate material.
This theorem neither asserts those premises for an unexecuted full
session nor turns arithmetic output into a source reply. It specifies
the entry/return construction for Proposition 3.4; the standalone
graph of §3 retains its stated, narrower scope.

## 8. Public operand widths and a prospective evaluator envelope

**Definition 8.1 (public arithmetic parameters).** For an accepted frame
$x$, let $L=|x|$, $N\ge4$ its sample count, $t$ its cylinder count,
and $0\le a\le b$, $b>0$, its numerator and denominator as represented
before reduction. Set

$$
\begin{aligned}
 r_*&=\min(N,72),&s_*&=\min(N,243),\\
 D&=1944^N(128)_{r_*}(256)_{s_*},\\
 m&=64(N+L+t+2),&Y&=64(t+2)(m+1),\\
 A&=(16N+3)2^{\min(N,243)},\\
 D_0&=L+Y+(N+1)^2+A+m+1024 .
\end{aligned}                                                   \tag{IS.9}
$$

Falling factorials have their ordinary finite-product meaning.
These parameters depend only on public code and received bytes;
$D$ uses the original block caps, not an attained partition.

Let $Q,R$ be the translated source-location and register counts, and
$d$ the number of declared routines including outer main. Unused
declared banks remain in $R$. Define

$$
\begin{aligned}
 B_x&=16^{d+1}(D_0+1),\\
 E_x&=R(B_x+1)+\lceil\log_2 Q\rceil+1,\\
 U_{\rm step}(x)&=2^{E_x},&
 U_{\rm push}(x)&=2^{E_x},&
 U_{\rm out}(x)&=Y .
\end{aligned}                                                   \tag{IS.10}
$$

These loose integers are not runtime measurements, installation offers
or lower bounds.

**Theorem 8.2 (represented-width bound for this evaluator).** At every
translated source-instruction boundary on $x$, every logical register
word has length at most $B_x$. Every completed arithmetic scalar used
outside internal word routines has at most $m$ bits. The computed
unframed register-zero output has length at most $Y$.

Proof. Use the meanings established in ML10–11. Each admitted summand
denominator $1944^N(128)_r(256)_s$ divides $D$: $r\le r_*$,
$s\le s_*$, and an initial falling factorial divides a longer one
with the same initial factor. Summands are nonnegative. ML11.5
identifies the completed sum as an evidence probability, so every
partial sum is at most one. Its reduced numerator and denominator
are at most $D$, with denominator dividing $D$. Null evidence is $0/1$.
Moreover

$$
 \log_2 D<26N,\qquad b<2^{L+1}.                                \tag{IS.11}
$$

The two unreduced mixture contributions have denominators at most $bD$.
Their reduced sum has denominator dividing $bD$ and numerator at most
that denominator. Before reduction the rational-addition cross-products
and sum have at most $52N+2L+5$ bits. A positive-evidence conditional
ratio forms products of two integers bounded by $bD$, obeying the same
allowance. Zero evidence does not form that ratio.

The other scalar bounds do not rely on the probability bound. A
type-map weight is at most $27^{r+s}$ and there are at most
$36^{r+s}$ maps, so its accumulated $J$ is at most $972^{2N}$.
A partial label-assignment count is at most $256^N$. A subset index
and its doubled power have at most $N+2$ bits. Loop indices, degrees,
occupancies and falling-factorial products obey their finite vector
sizes or (IS.11). The increment before a failed loop test and the
borrowed subtraction residue add at most a constant. All are below $m$.

A label-subset array has at most $2^{\min(N,243)}$ entries. Each
entry has at most $8N+1$ payload bits and its ML.17 record at most
$16N+3$ bits. This gives $A$. The seen-edge array has at most $N^2$
zero/one entries. Coordinate, requirement, occupancy and partition
vectors have their declared finite lengths; their record delimiters
and scalar payloads fit $(N+1)^2+m+1024+A$. Remaining input has
length at most $L$. All returned words at the combinatorial boundaries
are bounded by $D_0$, after including the output estimate below.

There are $3(t+1)$ evidence fractions and at most $t$ ratios. A
nonnegative rational with numerator/denominator widths at most $m$
has ML-F length at most $4m+3$, including explicit zero payloads and
sign. Its outer V-word has length at most $8m+7$. The list headers
and positivity bit, including $t=0$, fit the remaining allowance
in $64(t+2)(m+1)$. This proves $Y$ without executing the output.

Internal word temporaries also need a bound. In transfer, normalization
or framing, each temporary is a prefix, suffix or reversal of a supplied
word, with at most its unary marks and delimiter. Ripple arithmetic
uses at most the two argument widths plus carry/borrow; shift-add
multiplication uses at most their sum plus two. Division uses at most
four times the larger argument width plus eight. Get and Put store
the original serialized vector, a reversed record prefix and selected
replacement; an individual temporary is bounded by four vector
lengths plus four scalar widths plus eight. Gcd and reduction call
these routines without enlarging the supplied scalar values. The
eight-bit return word has one pending identifier because the call
graph is acyclic.

One routine layer, excluding deeper calls, therefore enlarges a bound
$z\ge D_0$ on supplied words to at most $16(z+1)$ for an individual
temporary. The loop invariants just described bound each temporary
throughout a loop. Semantic outer results and arrays remain bounded
by $D_0$ after each call. Induction down the acyclic call graph, of
depth at most $d$, bounds all private temporaries by
$16^{d+1}(D_0+1)$. Repeated outer calls reuse their banks, without
increasing that depth. Sharing Copy and Clear add no growth beyond a
supplied head or the empty word. This includes normalization and
dispatch instruction boundaries. $\square$

**Theorem 8.3 (non-retrospective complete evaluator bounds).** On every
accepted $x$, the translated evaluator executes at most
$U_{\rm step}(x)$ source instructions and $U_{\rm push}(x)$ pushes.
These and $U_{\rm out}(x)$ apply to the entire accepted domain,
including null evidence, endpoint/unreduced priors, partial masks
and arbitrary finite cylinder lists.

Proof. There are $2^{B_x+1}-1$ Boolean words of length at most $B_x$,
so the semantic state has at most

$$
 Q(2^{B_x+1}-1)^R\le Q\,2^{R(B_x+1)}<2^{E_x} .                 \tag{IS.12}
$$

ML11.6 and Theorem 1.4 give termination of the deterministic semantic
run. A repeated semantic state before halt would repeat its entire
future, contradicting termination. Hence (IS.12), with the slack in
(IS.10), bounds executed instructions including the terminal one.
Every push is an instruction; Theorem 8.2 bounds output.

Different immutable-frame histories can represent the same semantic
state. The next logical instruction depends only on the words and
source location; those extra identities are charged below. No completed
evaluator run supplies a step count to this argument. $\square$

The no-repetition step is the usual finite-configuration argument,
used inside this source-specific derivation rather than asserted
as a new general theorem; the repository's
[space-bounded configuration account](../../../Library/ConceptDynamics/cook2006pversusnp.md),
Proposition 5, already uses that argument. The represented-width, divisor and
service-reserve application is repo-derived.

## 9. Whole-session material and the host-owner boundary

**Definition 9.1 (finite service chronology and frontend encoding).**
A chronology $z$ specifies finite public initialization, a finite
Read list, an accepted arithmetic frame $x$, a finite subsequent
Read list and Close. The original source is fixed throughout.
Let $q$ count all Reads, $S$ sum their operand lengths, and $I$
count all received bits, including framing, initialization and Close.
Every occurrence is retained; an acquisition-only final probe remains
in the first Read list. Multiple accepted evaluations use sums of
their evaluator bounds and seed/loader allocations, retaining old frames.

For the fixed frontend let $F_0$ count its field locations and $R_0$
its reference and binary registers together. Set

$$
\begin{aligned}
 Z&=L+I+S+15N+t+1024,\qquad B_F=64Z^2,\\
 E_F&=(R_0+4)(32B_F^2+1)+\lceil\log_2F_0\rceil
               +\operatorname{bitlength}(I)+8,\qquad U_F=2^{E_F}.
\end{aligned}                                                   \tag{IS.13}
$$

This frontend encoding retains active requests, public prior, indexed
cache, receipt occurrences/links, temporary words/headers, cursors,
return references, phases and binary latches. Dead retained allocations
are erased only from this semantic cost analysis, never from material
accounting or the actual continuation representation.

**Proposition 9.2 (frontend envelope on this chronology).** Under its
original primitive-completion conditions, the frontend, excluding
evaluator and provider internal transitions, executes fewer than
$U_F$ field actions and extracts fewer than $U_F$ reserve cells.
Total printed bits are at most $7q+2Y+6$.

Proof. ML22–24 give finite receive/validate/Read/print contracts.
A received word or suffix has at most $I$ bits; receipt payloads
together have $2S+3q$ bits and $q$ headers. Cache has $15N$
two-bit entries. Unary conversion for shape and cylinder iteration
has value at most $N$ or $t$. Its doubling scans a fixed snapshot
and grows by at most the resulting unary value. Prior comparison
scans the two actual received payloads. Other words are copies,
framed copies, cursor suffixes or concatenations of these words.

There are $R_0$ named cursors/banks, a fixed number of pending
headers per bank, and at most $I+q$ visible receipt/request components.
Their simultaneously active cells/headers fit $B_F$, including unary,
wrapping and partial-append phases: their linear payload bounds are
multiplied by the fixed bank count, less than $64\cdot1024$, while
$Z\ge1024$. Canonically number active cells, preserving equality,
four reference fields and eight bits. At most $32B_F^2$ bits per
bank, with four additional pending banks, encode these fields,
positions and shapes. $B_F$ also exceeds the fixed code/reference
name count. Thus fewer than $2^{(R_0+4)(32B_F^2+1)}$ encoded states
suffice at each frontend location.

Between successive input signals, evaluator handoffs, provider
completions and suspensions, the semantic frontend is deterministic
and terminates. The non-repetition argument bounds each segment.
Fewer than $32(I+1)$ segments occur, since each request consumes
received bits and has a fixed number of completion cuts. The slack
in (IS.13) covers these segments and boundary actions. Each field
action extracts at most one cell. This analysis first interprets
allocation with an unlimited fresh supply; its extraction bound then
justifies a finite reserve, without assuming that reserve to prove
its own size.

Read prints seven bits, arithmetic at most $2Y+3$, Close three,
and initialization no answer. Their sum gives the output bound.
Waiting charges retained material without an elapsed-time claim.
$\square$

**Theorem 9.3 (sufficient native reserve and retained composed census).**
For one evaluation a sufficient extraction reserve is

$$
 K=5+L+U_{\rm push}(x)+U_F .                                    \tag{IS.14}
$$

Let $F$ count fully composed literal native locations, $R_c$ reference
registers and $B_c$ binary registers. Session input arrives through the
frontend, with no separately preinstalled $L$-cell input shadow.
Excluding the initializer seed, the prepared block counts are

$$
\begin{aligned}
 n&=K+F+R_c+B_c+1,\\
 r&=4(K+F+1)+R_c,&c&=8(K+1)+21F+B_c,\\
 O_C&=3n+1+O_s,& A_C&=2r+5n+15+A_s,&C_C&=2c+2+C_s .
\end{aligned}                                                   \tag{IS.15}
$$

Source shadows, Source descriptors, targets, grants, unused reserve,
initializer wiring and the output-return slot remain retained.
The seed includes its unused wide scan. At fixed adequate reference
width $w$, this owner occupies $O_C+wA_C+C_C$ native bits from
completed installation through acknowledged return and Close;
earlier preparation/installation prefixes are bounded by that layout.

Proof. Seed consumes five cells, loader $L$, and each source push one.
Proposition 9.2 pays frontend extraction, including input, validation,
operand transmission, fresh receipt headers/payloads, pending fields
and Close. Garbage frames or cleared heads return no cells.
This gives (IS.14).

Code and reserve blocks have four references, reference registers one,
native latch four, binary registers none. Their bit shapes are 21,
eight, zero and one respectively; native latch has eight bits.
These give $n,r,c$. Theorem 4.2's descriptor/target calculation gives
the displayed totals. Input cells are already extracted from $K$;
an additional installed $L$ would describe the standalone fixture,
not this composition. Execution changes only counted fields.
$\square$

**Definition 9.4 (common-cut demand, including other owners).** At each
cut from source preparation through cleanup take the union of actual
owned bindings, assigning each binding once. Owners are the composed
graph and public preparation, original source, connection/provider,
input/output peer, initializer/shared wiring, inherited jobs, observers,
and any concurrently installed mutable B component. Shared wiring
is counted once; distinct headers, shadows and targets stay distinct.

Let $(O_j,A_j,C_j)$ upper-bound each owner's census at those cuts,
and $O_*=\sum_jO_j$ with that actual identification. A common
injective naming needs an offered width

$$
 w_*\ge\lceil\log_2(O_*+1)\rceil .                              \tag{IS.16}
$$

Owner-local widths can instead use actual tagged foreign references,
charging both owner and slot bits. A local installer width proves
neither composed representation. Width migration pays old/new overlap
and rewrites. Common native material is bounded by

$$
 S_*(z)=\sum_j(O_j+w_*A_j+C_j)+S_{\rm migration}(z).             \tag{IS.17}
$$

Original source/provider terms are their actual ML25 preparation,
route, navigation and returned-buffer terms. Its $q$ calls examine
at most $S+q$ vertices and navigate at most $S$ links, in addition
to operand/reply buffers, grants, Ack and retained call records.
Source preparation and route words are additional.

In particular, insert the existing original-owner census at
$k=15N$, with $f=1$ when $q>0$ and $f=0$ otherwise:

$$
\begin{aligned}
 D_s&=(5k^2+13k+6)/2,&V_s&=8k+8,&H_s&=3k+3,\\
 O_{\rm src}&=V_s+H_s+D_s,&
 A_{\rm src}&=16+4V_s+2H_s+D_s,&C_{\rm src}&=D_s,\\
 O_{\rm port}&=1+2S+5q+f,&
 A_{\rm port}&=10+2S+7q+2f,&C_{\rm port}&=2S+3q .
\end{aligned}
$$

The port row includes its binding, actual transmitted provider-request
and returned-latch buffers, cleared wire cells retained on the paid
free list, and its free-list header. It excludes the native peer cell
already paid in $K$. The source row includes its original route
headers and side words. Grant bits are one per object, separate
from $C$. For widening arenas the old/new overlap is additional;
these local row widths cannot replace (IS.16).

For the chosen initializer a sufficient operation allowance is

$$
 I_C\le128n+16r+4c+64 .                                        \tag{IS.18}
$$

Both passes have fixed per-block paths, bounded per-reference paths,
and three bit vertices per copied bit; the slack pays tests,
directory, grants, latch and control actions. Seed initialization
and public preparation are separately paid input operations.
The composed controller has the sufficient transition allowance

$$
 V_C\le I_C+
 F\bigl(U_{\rm step}(x)+U_F+2L+2Y+R+64\bigr).                  \tag{IS.19}
$$

Each lowered private path is acyclic with at most $F$ vertices,
$R$ pays initial stack-head resets, input/output loops have the
displayed lengths, and seed/return paths fit the constant.
Add source preparation/provider work, external delivery, rights
delivery, inherited work, observers and cleanup to obtain $V_*(z)$.
Reference transport carries the actual widths; a transition count
does not erase those separate bit-work coordinates.

**Definition 9.5 (host demand and the unsupplied offer).** A host layout
contract $\mathcal H$ supplies upper storage functions for actual
Blocks/reference lists/byte buffers, Source descriptors, code nodes,
lists, tuples, dictionaries, sets, integers/counters, initializer
wires/headers and compiler/library material. It also supplies upper
work for creation, access, resizing, hashing, integer arithmetic,
copying and release. Denote these functions by $h_{\mathcal H}$
and $w_{\mathcal H}$. Host pointer widths and object/container
headers are paid even when a modeled arena uses fewer index bits.

For the actual owner graph define demand expressions using
(IS.14)–(IS.19) as upper cardinalities and operation counts:

$$
\begin{aligned}
 H_{\mathcal H}(z)
 &=\max_u\sum_{\text{objects/buffers/containers owned at }u}
                       h_{\mathcal H}(\text{type, capacity, widths}),\\
 W_{\mathcal H}(z)
 &=\sum_{\text{preparation, installation, native, provider, observer,
                         and cleanup operations}}
                       w_{\mathcal H}(\text{type, widths, capacity}).
\end{aligned}                                                   \tag{IS.20}
$$

The population includes original/translated assembly and labels,
field/native graphs, block/descriptor/target lists/maps, reserve,
initializer state/wires, frozen-frame maps/reference tuples, source
preparer's retained cuts/event/address words, source/connection
identity sets/counters, request/reply buffers, output lists, and
handoff/return observers' retained copies. Counter widths depend
on $V_*$, not just $N$. An observer at every preparation cut pays
every retained observation, not one terminal census. Acknowledgement
and reference clearing do not delete retained containers.
Preparation temporaries, rehashing and width migration use their
actual overlaps in the maximum.

Substitution requires the actual host layout contract and the inherited/
concurrent owner manifest with common-cut capacities/work. No such
full-session contract or actual $(H_{\rm reserved},W_{\rm backed})$
offer is a premise of §§7–8. The remaining inequalities are

$$
 H_{\mathcal H}(z)\le H_{\rm reserved},\qquad
 W_{\mathcal H}(z)\le W_{\rm backed}.                           \tag{IS.21}
$$

Their supplier is the existing host/resource owner of the complete
chronology. Current original-port rights and finite operation
completion belong to the source/connection owner; output occupancy
and Ack completion belong to its actual output peer. None is supplied
by a logical bound, physical RAM total, tiny allocation or retrospective
run count.

This is an uninstantiated host demand expression with named missing
offers, not a concrete proved host upper bound or an exceeded offer.
Even a loose sufficient bound above an offer would not exclude an
implementation; exclusion needs a necessary lower bound in the
same units and owner scope.

**Proposition 9.6 (separate finite mutable B prefixes).** A concurrently
retained ML-C mutable B component adds its program/input/code/reserve,
head/control/busy state and source/target/routing/observer material
in Definitions 9.4–9.5. For input length $\ell$ and a requested
$p$-step B prefix, $C\le\ell+p+1$ instantiated cells and $b_1\le C$
give the existing ML6.2 bound

$$
 D_{\rm route}\le1+\frac{C(C+1)}2+C(C+1).
$$

Controller/navigation and installation retain the ML-C suppliers
at these finite parameters. This includes $p=0$ and every finite
nonhalting prefix, without arbitrary B termination. Mutable B
positions remain distinct from immutable value tokens.

Proof. At most one frontier tape position is reached per completed
move; the extra one permits a pending frontier action. Apply ML6.2
and its prefix/controller account. Common-cut union retains both
components while either executes. A changed shared value token
would alter every alias and violate §1; separate mutable material
avoids that identification. $\square$

## 10. The three unchanged chronologies and the composed actual image

**Proposition 10.1 (public instantiation without a full execution).**
For the fixed translation, $Q=10983$, $R=360$, $d=34$. Retain all
original acquisition calls, including their acquisition-only final
probe, then append post-evaluation $\mathrm{Read}(LL)$ and Close.
The parameters of (IS.9)–(IS.14), with $d_0=D_0+1$, are:

| Frame | $N$ | $L$ | $t$ | acquisition calls / operand bits | total $q/S$ | $I$ | $m$ | $Y$ | $d_0$ |
| --- | ---: | ---: | ---: | --- | --- | ---: | ---: | ---: | ---: |
| positive-full | 4 | 387 | 2 | 74 / 2176 | 75 / 2178 | 5376 | 25280 | 6471936 | 6499725 |
| positive-partial | 4 | 386 | 2 | 73 / 2115 | 74 / 2117 | 5249 | 25216 | 6455552 | 6483276 |
| null-nine-distinct-left | 9 | 839 | 2 | 149 / 9676 | 150 / 9678 | 21507 | 54528 | 13959424 | 14091180 |

In every row,

$$
 B_x=16^{35}d_0,\quad E_x=360(16^{35}d_0+1)+15,\quad
 K=5+L+2^{E_x}+2^{E_F}.                                       \tag{IS.22}
$$

The frontend exponents $E_F$ in row order are
$244562584912076855181626$, $224715089010335365988666$ and
$44666665685474872606720316$. Substitute the same $K$ in (IS.15),
with composed counts $F=225718$, $R_c=604$, $B_c=57$.
The evaluator word and numerical consumer are unchanged; the code
also includes service, explicit resets and actual return binding.

The original-source $(O,A,C)$ rows are $(10064,11727,9393)$ for
both $N=4$ frames and $(47939,51627,46443)$ for $N=9$.
The port/connection rows after the appended Read are respectively
$(4733,4893,4581)$, $(4606,4764,4456)$ and
$(20108,20418,19806)$. These are inserted with (IS.15) into the
same union (IS.17), together with any actual peer, inherited,
observer and mutable-B owners. No inherited-owner census is
inferred from these three rows.

Proof. Initialization uses the represented public prior prefix.
Read on $w$ receives $2|w|+3$ bits, arithmetic $2L+3$, and Close
two. Appended $LL$ adds one call, two operand bits and seven
received bits. These give $I,q,S$ without altering earlier counts.
Each represented prior is $1/3$ and each cylinder count two.
Substitution gives $m,Y,d_0$ and (IS.22). The frontend's fixed
banks/locations and literal composition of Definition 7.1 give
the other counts. These are input/code-derived parameters, not
attained full-run counts or host offers. No acquisition-only check
is relabelled as post-evaluation evidence. $\square$

**Proposition 10.2 (the concrete supplier map).** On Definition 7.1's
actual reachable image retain the frontend's original root/connection,
public data, original-indexed cache and all occurrence receipts;
installed code/output-return reference; immutable spines, tokens and
logical heads; native location/latches, busy old head and phase;
current grants; input/output occupancy, End/Ack state, pending
allocations and meter. Include each retained B component with its
own head/control/routing annotations. Process Geometry3.2–3.5
and the Typed Residual Resource Boundary suppliers apply with
these complete same-source labels and resource responses.
AA17.3 converts the actual guarded work supports and terminal
antichains with the same annotations.

Proof. Each native instruction tests the named actual code/operand
fields, grants or latches, then transfers control by a retained
successor or return reference. Each source call uses the same port;
its actual returned record is retained. Pending phase determines
committed fields and busy-macro data. Consistent fresh-reference
renaming therefore preserves root reads, legality, complete primitive
labels, resource updates and annotated successor. These are the
existing process suppliers' hypotheses on this actual image, rather
than an independently prepared product of summaries.

Seed has its actual guarded AA support/boundary; B conversion keeps
its ML7.2 domain. Neither conversion reconstructs spines, rights or
control after their annotations are erased. The reachable ML31.4
case $W=(R,M)$ on $00$ has the same bare work tree before and
after its first move and a different next action. Retaining disjoint
service/spine material preserves that witness. No bare-tree
sufficiency or actual serial-history recovery follows. $\square$

C117 affine/positive-response repair, inverse-limit and periodic-MPS
suppliers keep their original response, continuity, range,
physical-state and rank hypotheses. No identification of this service
with those carriers is made. They do not supply (IS.8), native
completion, current grants or (IS.21). The new content is this
particular composition and input/code-derived envelope with explicit
owner terms; generic quotients, adaptive continuation and spatial
equivalences are reused.

## 追加锚（本行以下为增补区）

## 11. A loop-derived cost for the unchanged complete evaluator

**Definition 11.1 (source call multiplicities).** Retain the evaluator,
sharing translation and composition of §§1 and 7. Let $b=B_x$ and $Y$
have exactly the meanings in (IS.9)–(IS.10). The complete emitted stack
graph has 10,983 locations, including its return dispatch; put
$q_0=10984$. A routine name below denotes its literal assembler body,
not a host arithmetic operation. Let $m_{fg}$ be the number of syntactic
calls from body $f$ to body $g$, counting both branch bodies and every
literal expansion. The nonempty rows are as follows; omitted entries
are zero and an omitted multiplicity is one.

| $f$ | $g:m_{fg}$ |
| --- | --- |
| main | add:2, addword:7, concat:3, conjoin, encu:2, lt, mixture:2, mul:3, normalizer:2, readcache:2, readu:4, readv |
| addword | concat, encq, encv |
| blocks | add:2, get, lt:2 |
| conjoin | add, eq, get:2, lt, mul, put |
| countlabels | add:18, blocks, div:3, eq:2, get:9, lt:9, mul:4, put:5, sub:4, zeros:4 |
| div | add:2, lt, sub |
| encq | concat, encu:2, reduce |
| encu | encv |
| eq | sub |
| falling | add, lt, mul, sub |
| gcd | div |
| get | popword:2, sub |
| inject | add:11, eq, get:12, incident, lt:6, mul:4, odometer, put:5, sub:2, zeros:6 |
| lt | sub |
| mixture | mul:4, qadd, sub |
| mul | add |
| nextpart | add:5, get:2, lt:4, put:2, sub:2 |
| normalizer | add, blocks:2, countlabels:2, falling:2, inject:2, lt:3, mul:6, nextpart:2, qadd:2, side:2 |
| odometer | add, get, lt:2, put:2, sub |
| put | popword:3, prepend:3, sub |
| qadd | add, mul:3, reduce |
| readcache | add:3, get, lt:2, mul, put:2, zeros |
| readu | readv |
| reduce | div:2, gcd |
| side | add:12, eq, get:4, lt:5, mul:3, put, zeros |
| zeros | sub |

These rows are the expansion of `constructor_ir.Assembler.call`,
`constructor_ir.primitives`, `evaluator_program.define_evaluator` and
`evaluator_program.main` in the
[fixed source](https://github.com/the-omega-institute/trureturing-experiments/tree/0ab58a79e9122c53680491b2f99c1a00dc06f19e/rro-lab-execution).
In particular, `incident` is the fixed public incidence decision tree.
No row calls an ancestor in this table's dependency relation; the
longest invocation chain has eight bodies. Return words still have
their original eight-bit identifiers. This table changes neither
the evaluator nor its admissible input language.

Put

$$
 P=N^N,\qquad M=36^{\min(N,72)}27^{\min(N,243)},\qquad
 H=2^{\min(N,243)}.                                             \tag{IS.23}
$$

The twenty word routines are add, sub, lt, eq, mul, div, gcd, reduce,
qadd, popword, prepend, get, put, zeros, concat, encv, encu, encq,
readv and readu. Assign each of them $\lambda_f=(2b+3)^2$.
Assign the remaining local multipliers by the following table.

| Body $f$ | $\lambda_f$ |
| --- | ---: |
| main | $t+2$ |
| readcache, conjoin | $15N+2$ |
| blocks, falling | $N+2$ |
| nextpart | $(N+2)^2$ |
| side | $16(N+2)^2$ |
| countlabels | $257(H+1)(N+257)^3$ |
| odometer | $2N+2$ |
| incident, mixture, addword | $1$ |
| inject | $(M+1)(2N+2)$ |
| normalizer | $(P+1)^2(N+2)$ |

Define integers, in dependency order, by

$$
 C_f=q_0\lambda_f\left(1+\sum_g m_{fg}C_g\right),\qquad
 T_x=C_{\mathrm{main}}.                                        \tag{IS.24}
$$

This is a finite arithmetic recurrence on public code, $N,L,t$ and
the already proved word bound $b$. It contains no completed-run count,
normalizer value, actual hidden injection or numerical reference answer.

**Theorem 11.2 (complete source cost from the actual loops).** Every
accepted arithmetic frame in Definition 8.1 executes at most $T_x$
stack instructions and at most $T_x$ pushes. Its output bound remains
$Y$. Thus $T_x$ can replace either occurrence of $2^{E_x}$ in the
reserve and operation upper bounds, with all original domains retained.

Proof. First count a body's own locations, contracting each subroutine
invocation to an edge. All consuming word scans have at most $b+1$
iterations by Theorem 8.2. Addition/subtraction consume the two supplied
words; normalization and moves consume a finite temporary. Multiplication
consumes multiplier bits, and division consumes dividend bits. Their
numeric values are not loop lengths. In get/put the index is a valid
serialized-vector position, hence at most $b$; the restored prefix has
at most $b$ records. Zeros receives an actual vector size, also at most
$b$. Readv consumes its represented unary marks and payload. Euclid
has at most $2b+1$ iterations: after two nonterminal remainders the
positive divisor is less than half its earlier value. This is the usual
Euclidean estimate applied to these actual argument words. Calls to
division are counted separately. The word bodies have no remaining
local loop with a larger counter, and no local nesting beyond the
generous square in $(2b+3)^2$.

Readcache and conjoin scan $15N$ positions. Blocks/falling scan $N$.
Nextpart decreases its outer position and scans a prefix of length at
most $N$, then resets a suffix; side uses at most two sample positions
and eight coordinate positions. The corresponding table entries
dominate the visits of each local location, including failed tests.

Countlabels uses at most 256 labels, at most $N$ blocks and eight
coordinates, and a subset table of at most $H$ entries. Its loops are
sample-coordinate, label-block-coordinate, or label-subset-block;
the stated multiplier dominates each location's visits. Its get/put,
division and arithmetic work are subroutine calls, not free operations.
The 72/243 block tests occur before inject. Consequently inject's
odometer has at most $36^r27^s\le M$ settings for source zero and at
most $9^{r+s}\le M$ for source one. Each setting scans at most $2N$
vertices and $N$ sample edges. The degree test and seen-edge array
are paid before enumeration even when they reject the entire term.

The restricted-growth-word enumeration visits at most the number of
partitions of $N$ positions. Assigning each position one of $N$ labels
gives its elementary upper bound $P$; this bound includes partitions
rejected by block caps. The two normalizer partition loops therefore
have at most $P^2$ pairs. Its separate power loop has $N$ iterations.
Main executes its cylinder body $t$ times and retains its initial
evidence computation. Each remaining body has no local loop.

There are fewer than $q_0$ own locations per body. Each call site is
visited at most $q_0\lambda_f$ times, which also bounds its own
instruction total. Induction on the actual acyclic call graph gives
(IS.24), including argument binding, eight-bit call/return handling,
branching and the terminal instruction. Each push is an instruction.
Theorem 8.2 still bounds output. This proof uses loop invariants rather
than the number of possible Boolean-register configurations. $\square$

## 12. The full frontend, local service completion and joint native demand

**Definition 12.1 (frontend scan recurrence).** For Definition 9.1's
complete finite chronology, set

$$
 J=I+S+15N+t+q+L+Y+1024,\qquad f=F_0+1,                        \tag{IS.25}
$$

where $F_0$ is the unchanged frontend's field-location count. Define

$$
\begin{aligned}
 a_{\rm take}&=f,\\
 a_{\rm readv}&=f(J+1)(1+a_{\rm take}),&
 a_{\rm readu}&=f(1+a_{\rm readv}),\\
 a_{\rm unary}&=f(J+1)^2,&
 a_{\rm shape}&=f(J+1)(1+a_{\rm unary}),\\
 a_{\rm prior}&=f(J+1)(1+2a_{\rm readu}),&
 a_{\rm mask}&=f(J+1)(1+a_{\rm take}),\\
 a_{\rm cylinders}&=f(J+1)(1+a_{\rm readu}+a_{\rm unary}
                  +a_{\rm readv}+a_{\rm mask}+a_{\rm take}),\\
 a_{\rm arithmetic}&=f(1+a_{\rm readu}+a_{\rm shape}
                    +a_{\rm prior}+a_{\rm mask}+a_{\rm cylinders}),\\
 a_{\rm classify}&=f(J+1),\\
 A_{\rm cmd}&=f(J+1)^2\left(1+\sum_r a_r\right),&
 T_F&=(I+q+3)A_{\rm cmd} .
\end{aligned}                                                   \tag{IS.26}
$$

The sum is over the ten displayed routine quantities. The quantity
$A_{\rm cmd}$ denotes the top-level command allowance, including receive,
copy/cat/wrap, framed output and the pending input/output latches.
These are field-action counts, not Boolean-stack or host-time counts.

**Theorem 12.2 (whole frontend and local endpoints).** On a complete
valid public chronology, under finite allocation and current-rights
premises, the frontend outside the evaluator and provider executes at
most $T_F$ field actions and extracts at most $T_F$ cells. Every call
to the original local provider and every local End/Ack/Return completes
after finitely many of its own operations. No independent remote Ack
or remote source-completion hypothesis is needed for these endpoints.

Proof. Use the actual routines in `field_service.Service`. Take consumes
one actual input cell or reaches its specified suspended/refusal cut.
Readv scans represented unary marks and their payload; readu additionally
checks the canonical first bit. Unary's outer loop scans a binary word;
each doubling scans the saved tail snapshot, whose resulting unary
length is at most $N$ or the represented cylinder count $t$. Both are
bounded by $J$. Shape's remaining loop appends exactly $15N$ cache
positions. Prior compares original represented payloads, without
cancelling the fraction. Mask scans the shape and selected values.
Cylinders repeats a readv, strict finite mask validation and cursor
restoration for its actual finite count. Thus induction over the
displayed calls gives the first nine allowances. Classify consumes a
finite operand/cache spine and then at most three suffix bits.

Top-level copy/cat/wrap, receipt construction, prediction construction
when requested, and print each scan finite words of length at most
$J$. Their branch-local loops and fixed call sites are bounded by
$f(J+1)^2(1+\sum_r a_r)$. This includes no evaluator instruction.
There are at most $I+q+3$ bit deliveries, complete-command boundaries
and initialization/closing phases to which this generous top allowance
must be assigned. Waiting charges retained material but no elapsed
time. Each field allocation extracts one cell. This proves (IS.26).

For an operand $w$, `OriginalConnection.invoke` projects exactly the
transmitted finite native chain. `OriginalPort.call` constructs and
parses its actual $2|w|+1$-bit wire, then examines at most $|w|+1$
source vertices and follows at most $|w|$ child links. It returns its
actual two-bit latch. Buffer.clear visits only its finite wire, retaining
all cells on the paid free list. Connection.ack clears the occupied
reply latch. These loops require no additional source decision or
unbounded external response. The granted root is the same object on
every invocation; the classifier does not supply a reply.

In `immutable_spine.Direct.tick`, ordinary send appends the computed
bit to the local output list, End sets its ended flag, Ack tests that
flag, and Return tests acknowledgement and reads the actual retained
output-return reference. These are local finite routines. The ordinary
completion is conditional on their actual storage/rights and execution,
not a promise that the runtime can allocate arbitrary finite lists or
will schedule them within a specified time. $\square$

**Theorem 12.3 (loop-derived complete native demand).** For one accepted
evaluation with all its acquisition, return, subsequent Reads and Close,
a sufficient extraction allowance in the unlimited-fresh-cell semantics
is

$$
 K^{\rm loop}=5+L+T_x+T_F .                                    \tag{IS.27}
$$

Insert this same integer in (IS.15). The simultaneous native census
still retains every source block, descriptor, target, grant, unused
reserve, initializer and old immutable frame. A sufficient composed
native-transition allowance is

$$
 V_C^{\rm loop}=128n+16r+4c+64+
 F\left(T_x+T_F+2L+2Y+R+64\right).                            \tag{IS.28}
$$

Source preparation, provider work, external input-latch delivery and
cleanup are separate coordinates, with source and connection censuses
as in Definition 9.4. In particular the receipt payload has exactly
$2S+3q$ bits, provider navigation is at most $S$, and provider vertex
examination is at most $S+q$. There are $I+q+3$ input bit/End signals
for the specified initialization, $q$ Reads, one evaluation and Close;
their native delivery writes three actual latches per signal.

Proof. Combine Theorems 11.2 and 12.2 with the seed/loader/push
extraction proof of Theorem 9.3. Every literal lowering path is bounded
by $F$, including stack resets, the two output scans and actual indirect
return. The installation two-pass bound is unchanged. Provider work
and input delivery do not disappear inside the symbol $F$. Source
preparation has its original $5k+4$ guarded growth events and
$(5k^2+13k+6)/2$ ancestor-route appends at $k=15N$, including its
retained event-address words and the finite route-validation scans.
Their host copying cost is additional to these native events.

The receipt and cache proofs depend on original occurrence indices
and actual replies, including replies outside the positive-law support.
None of their cost estimates assumes positive evidence. The rational
endpoint/unreduced and zero-evidence cases are already included in
Theorems 8.2 and 11.2. A zero denominator for a conditional law omits
only that ratio; it does not replace the source or delete an occurrence.
For several evaluations sum their $T_x$, seed/loader allowances and
output bounds, while retaining all earlier allocations. $\square$

## 13. Actual reference carriers and the object-layout obstruction

**Definition 13.1 (a concrete host data layout).** Consider the CPython
3.12 slotted Block/Source layout of `native_install`, with eight-byte
host pointers, four-reference work/code blocks, and a one-byte work
data buffer. Its reported object payload sizes, in bytes, are

| Component | Bytes |
| --- | ---: |
| slotted Block | 72 |
| slotted Source descriptor | 64 |
| four-element reference list | 88 |
| one-element reference list | 64 |
| empty reference list | 56 |
| one-byte bytearray including its header/buffer | 58 |
| three-byte bytearray including its header/buffer | 60 |
| four-element tuple | 72 |

This is a host object-payload coordinate. Native grant/field bits,
allocator size classes, process mappings and resident pages are different
coordinates. A physical Python reference is a host pointer to its actual
object. A modeled owner-local reference width never compresses that
host pointer. The runtime's signed container-length limit is
$2^{63}-1$, and its nonnegative integer digits carry 30 bits in four
bytes. Counter widths therefore depend on total charged work as well
as data length.

**Proposition 13.2 (reserve payload and physical realization).** Each
additional installed reserve cell in the unchanged Direct layout
retains two distinct Blocks, two distinct four-element reference lists,
two one-byte buffers and a Source descriptor. Its object payload alone
is exactly

$$
 2(72+88+58)+64=500\text{ host bytes}.                         \tag{IS.29}
$$

It adds $(3,13,16)$ to the native $(O,A,C)$ census. It also adds
container entries and preparation/observer material outside (IS.29).
At a common actual-object cut, references to these objects are realized
by their eight-byte carriers, with aliases sharing their pointed-to
object. There is no integer-to-object reconstruction operation.

Proof. Source and target have the same four-reference/eight-bit shape.
The descriptor points to source block, next descriptor and relocated
target. Each Block also has its directory slot, giving eight work
reference slots, two directory slots and three descriptor slots. Source
and target bits contribute sixteen; one grant per modeled object is
in the $O$ coordinate. Adding their separate host object payloads gives
(IS.29). The actual allocation retains both sides, rather than overwriting
the source with a target alias.

Direct's pool source list, translated target list, source-block and
descriptor lists are additional retained host arrays. The source-to-
descriptor map, link slices and relocation temporaries overlap during
preparation. The constructor also retains source/target boundary maps,
register maps and code. Its installer retains the source list, directory,
pending/source/target latches and fixed control graph. A later frozen-word
observer additionally retains its dictionary entries and reference tuples;
clearing a stack head does not release those tuples. These facts explain
why (IS.29) is only one exact additive payload term, not a complete host
upper bound. The layouts use actual object fields and pointers throughout;
grant tests are still required on the operational path. $\square$

**Proposition 13.3 (one simultaneously installed image).** The fixed
composed graph with $K=0$ has $n=226380$ source blocks and the census

$$
 (O_C,A_C,C_C)=(777713,3037783,11648685).                        \tag{IS.30}
$$

An independently installed mutable-B component for program
$W=(R,M,J_2)$, input $00$, reserve 128, at its initialized zero-instruction
prefix has census $(1281587,5224821,18724355)$. Its immutable initializer
wiring may be shared with the composed graph, while its mutable
initializer header, code, tape, head and pending/control state remain
distinct. The same original $k=60$ test-source factory and its uninvoked
connection add $(10064,11727,9393)$ and $(1,10,0)$ respectively.
Their common reference-carrier census, deduplicating shared wiring,
is

$$
 (O_*,A_*,C_*)=(1970961,8175937,28217545).                      \tag{IS.31}
$$

The corresponding fixed 64-bit-reference native-field coordinate is
$553448474$ bits. This coordinate is neither the host object payload
nor the resident size, and $K=0$ supplies no evaluator extraction reserve.

Proof. The initializer contains

$$
 W_s=1+3(1+3+8+21+32768)=98404
$$

immutable wire vertices, including its end vertex and the unused wide
scan. Its own mutable header and 167 installer locations give seed
$(98572,98908,2168397)$. The shared portion is exactly
$(W_s,W_s,22W_s)$; two mutable headers and two installer control graphs
remain distinct. Substituting $K=0,F=225718,R_c=604,B_c=57$ in
(IS.15) gives (IS.30). The independently prepared B program/input and
128-cell reserve use their original native installer; its source census
has 394338 blocks. The same descriptor/target enumeration gives its
displayed census. The B loader has initialized its actual mutable tape;
no B instruction is required for this prefix.

Sum the four owners and subtract only the shared wire portion. This
gives (IS.31), including each owner's grants. Then compute
$O_*+64A_*+C_*$. Python object references and C wire successors have
their actual pointer carriers; the bit-scanning C routine mutates the
header/target bytes, not the shared successor wiring. Thus two actual
initializer headers can use the same immutable wires. This image is a
layout instance, not a computed UJB output or a complete service history.
$\square$

**Definition 13.4 (host terms still needed for a sufficient comparison).**
For this layout the exact term $500K$ must be accompanied by all actual
retained and peak container payloads, temporary slices/maps, hash-table
capacity and rehash overlap, copied source-address/route words, C/ctypes
native buffers and keepalive maps, source/provider buffers and free-list
cells, output/observer copies, interpreter/compiler/library material and
cleanup. Kernel code, mappings, allocator arenas/fragmentation and execution
stack are separate host terms. Their maximum must be taken at common cuts;
the installed-object sum alone is insufficient.

A closed host-work account must also price allocation and release,
container resizing/hashing/probing, arbitrary-width counters, every
source-preparation copy and validation scan, every native interpreter
step and its observer, input/output copying and cleanup in actual host
work units. The native operation allowance (IS.28) provides cardinalities
for this substitution but does not price these runtime operations.
These are construction/runtime derivation obligations, rather than an
indivisible theorem assigned to a host-resource owner.

An actual protected host-byte offer and a backed host-work offer for
these same owners/cuts are different premises. A physical-memory count,
RSS reading, unlimited process limit, finite list allocation or prior
successful component is not such an offer. Owner-local width migration
still pays its overlap unless the chosen actual pointer layout already
carries the references. Only actual retained/shared or offer-coupled
owners enter this union; unrelated machine users do not enter merely
because they exist. No wall-clock conversion follows from the native
or host-work coordinates.

## 14. Three complete-chronology substitutions and the finite B domain

**Proposition 14.1 (the original rows discriminate the new bound).**
Substitute Definition 10.1's unchanged frames, acquisition schedules and
appended post-evaluation Read(LL)/Close in (IS.24)–(IS.28). The exact
source recurrence gives the following bit lengths, where
$\operatorname{bl}(u)=\lfloor\log_2u\rfloor+1$ for positive integers.

| Original frame | acquisition Reads / operand bits | whole $q/S$ | $\operatorname{bl}(T_x)$ | $\operatorname{bl}(K^{\rm loop})$ | $\operatorname{bl}(V_C^{\rm loop})$ |
| --- | --- | --- | ---: | ---: | ---: |
| positive-full | 74 / 2176 | 75 / 2178 | 2094 | 2094 | 2112 |
| positive-partial | 73 / 2115 | 74 / 2117 | 2094 | 2094 | 2112 |
| null-nine-distinct-left | 149 / 9676 | 150 / 9678 | 2149 | 2149 | 2167 |

The frontend field-action upper bounds $T_F$, in row order, are

$$
\begin{aligned}
&5704718395141094332244518336746932279963494449801624,\\
&5507302958271138648414070229466644995972382284536600,\\
&765978059821551433955279764650622238585882639680896000.
\end{aligned}                                                   \tag{IS.32}
$$

The three payloads still have lengths 387, 386 and 839, with the SHA256
identities, in the same order,

```
37dfee71eda5a8fbee3d373aab446982f15976785ef965ec2e4a1b6ea98c5402
1a4ae049cf81b1f434398aa05cb8eabcf4d8689f7873f8d75f9ae1e870c34764
f5518d034eef5bd00c87ff9d43c5ca878ef9d012f47e04bedcbe45163ee3e29d
```

Each row is a complete prospective native-demand substitution. Its
parameters contain neither a protected host-byte offer nor a backed
host-work offer. In all three,
the particular sufficient $K^{\rm loop}$ exceeds $2^{63}-1$, so that
reserving exactly that many entries in one runtime list is not a legal
instantiation of Definition 13.1. This is a failed fit for this upper
reserve and ABI, not a lower bound on necessary reserve and not proof
that these service sessions are impossible. Smaller sufficient bounds
remain a mathematical question for the same representation/evaluator.

The separate B image of Proposition 13.3 can remain installed throughout
each proposed session. In that case add its census to the row's composed
graph, original source and complete connection census, subtracting the
single shared wire contribution. This is one common-cut upper union;
it does not add the B reserve to the evaluator's extraction pool.
For a concrete byte/work comparison the remaining information is:

| Frame | $\operatorname{bl}(500K^{\rm loop})$ in host bytes | complete host upper | same-scope protected byte/work offer | comparison |
| --- | ---: | --- | --- | --- |
| positive-full | 2103 | not supplied by the native census/payload term | none supplied | unsettled; chosen reserve fails the container-length condition |
| positive-partial | 2103 | not supplied by the native census/payload term | none supplied | unsettled; chosen reserve fails the container-length condition |
| null-nine-distinct-left | 2158 | not supplied by the native census/payload term | none supplied | unsettled; chosen reserve fails the container-length condition |

Here $500K^{\rm loop}$ is the exact reserve-payload contribution for
that chosen reserve, not a necessary lower bound on the service's
minimum host demand. Also, a 64-bit pointer carrier can name only a
finite actual object domain; these upper object counts do not establish
that cardinality condition. Changing a logical reference-width symbol
does not enlarge the current host's pointer or container domain.

Proof. Definition 10.1 supplies $N,L,t,I,q,S,m,Y,D_0$ without a numerical
evaluator run. Here $b=16^{35}(D_0+1)$, $q_0=10984$, and (IS.24)'s
call matrix has depth eight. Evaluate that finite integer recurrence
and then (IS.26)–(IS.28). The resulting integer bit lengths and (IS.32)
are as displayed. The source/connection terms remain the exact rows
of Proposition 10.1; the output and fresh receipt terms are those of
Theorem 12.3. Appending a real Read is not a reinterpretation of any
acquisition probe. The comparison with the signed container-length
limit concerns the chosen allocation expression only. $\square$

**Proposition 14.2 (separate mutable B and unreduced class coverage).**
The native logical bounds above cover every accepted represented
evaluator input, not only the three substitutions. In a product with
an actually installed mutable B supplier, let $a$ be its finite program
length, $\ell$ its supplied input length and $p$ its requested finite
instruction prefix. Put

$$
 C=\ell+p+1,\qquad
 D_B=1+\frac{C(C+1)}2+C(C+1),\qquad
 K_B=a+\ell+6+4C+D_B.                                        \tag{IS.33}
$$

This is a sufficient cell allowance for its program/input plus the
ML-C work tree/routing upper census. At each common cut add the
actual installed B source/code/control/descriptor/target/observer terms,
deduplicating only physically shared immutable material. The evaluator's
immutable tokens may not represent mutable B positions.

For the fixed `b_graph` and original native installer used in
Proposition 13.3, those installed native terms have the explicit affine
form, for any adequate chosen pool $u$,

$$
\begin{aligned}
 n_B(u)&=u+394210,\\
 O_B(u)&=3u+1281203,\\
 A_B(u)&=13u+5223157,\\
 C_B(u)&=16u+18722307 .
\end{aligned}                                                   \tag{IS.34}
$$

The constants retain that installer's unused selectors and wide
initializer scan. Let $G_B=394210$. In addition to its two-pass
installation allowance, a sufficient native execution allowance for
initialization and the requested prefix is

$$
 V_B=(G_B+1)^2(\ell+p+2)(C+3)^2.                              \tag{IS.35}
$$

External resume signals and host preparation/observer work remain
separate coordinates. These formulas require the actual corresponding
B installation, rather than identifying immutable evaluator frames
with a mutable tape or assuming its program/input for free.

Proof. Reuse ML6.2 and the finite-prefix correspondence ML31.2, together
with Proposition 9.6. The work tree has at most $5+3C$ vertices, $1+C$
headers and $D_B$ route cells. Program/input occupy $a+\ell$ additional
cells; their sum gives (IS.33). Retain the original separate B graph,
head, program counter and busy phase even when either component waits.
The statement includes $p=0$, an empty/immediately halting program,
and every finite prefix of a nonhalting program. No B termination
assumption or fixed reserve for all prefixes is introduced. A concrete
joint native installation such as Proposition 13.3 supplies a member
of this product; its fixed 128-cell B reserve does not supply all $p$.

In that fixed B source layout the program and finite input occupy
already counted pool cells. Changing their finite contents does not
change any block shape. Each additional pool cell adds a source block,
descriptor and target with the $(3,13,16)$ increment of Proposition
13.2. The fixed field graph, generic native control, reference/bit
registers and initializer give the constants in (IS.34) by the same
descriptor/target enumeration. The $u=128$ substitution is the census
in Proposition 13.3. Both its field graph and native finite-control
graph have fewer than $G_B+1$ locations. A growth-maintenance traversal
follows at most $C+2$ proper ancestors. Each loader iteration or B
macro has fixed remaining control and at most that finite traversal.
There are at most $\ell+p+2$ loader/macro groups, with slack for an
empty input and terminal/suspended prefix. Bounding each local
traversal by the square $(C+3)^2$ and each field/native path by
$(G_B+1)^2$ gives (IS.35), including repeated marking and both head
directions. It asserts neither eventual halting nor an elapsed-time
bound.

For the evaluator, $N\ge4$ is arbitrary, represented prior endpoints
and unreduced numerator/denominator words remain inputs, and $t$ may
be zero or any finite count. Masks, selected values and finite cylinders
are charged by their actual represented lengths. Countlabels and inject
retain the once-shared full injections and original sample indices;
the call bound does not independently optimize their marginals. Actual
outside-support replies, repeated/partial slots and every occurrence
receipt keep their original service semantics. Thus no domain is
replaced by these three applications or by the zero-prefix layout image.
$\square$

The loop recurrence, simultaneous descriptor/target layout, concrete
reference carriers and host-payload decomposition are repo-derived
applications to this particular IS2 source. The Euclidean estimate,
partition counting bound and existing ML/IS suppliers are used only
as intermediate results. No new kernel-verified declaration, universal
physical memory, host scheduling promise, fixed-time completion or
unconditional space/time/boundary/memory recovery follows. The
remaining full host-demand and actual-offer premises in Definition 13.4
are independent of the established native loop bounds and local
service-completion implication.

## 追加锚（本行以下为增补区）

## 15. Guarded scalar and record costs for the same three frames

**Definition 15.1 (the refined cases and their unchanged fallback).**
Use exactly the source, sharing translation, composition, represented
frames and complete message sequences of Proposition 10.1. A message
is delivered bit by bit and sealed once, after its complete valid
payload. Its arithmetic command contains the actually acquired indexed
cache, not a numerical answer. Denote the two costs of a routine by
an ordered pair: executed stack instructions and executed literal
pushes. Copies of a published head and clearing a logical register
have zero pushes. An extracted cell is never returned to this pool.

The refinement below applies to these represented masks and their
represented cylinders. All other cases retain §§8–12 as sufficient
suppliers. In particular it introduces no restriction on $N\ge4$,
unreduced or endpoint priors, finite cylinders including zero, null
evidence, actual outside-support replies, original indices, shared
injections, partial slots or repeated occurrences. The separate mutable
B supplier remains Proposition 14.2 on its whole finite-prefix domain.

**Theorem 15.2 (guards before enumeration).** For every valid normalizer
invocation generated by the three frames, including their cylinders,
the following bounds hold before their use in a cost substitution.

| Frame restriction | left partitions | right partitions visited | $(r,s)$ when an inject call is reached | settings per inject call |
| --- | ---: | ---: | --- | ---: |
| positive-full | 1 | 1 | $(1,1)$ | at most $36\cdot27=972$ |
| positive-partial | 1 | at most 15 | $r=1$, $s\le2$ | at most $36\cdot27^2=26244$ |
| null-nine-distinct-left | 1 | 1 | $(9,1)$ before the degree guard | 0 |

For the partial row, every countlabels invocation has at most sixteen
subset records, and at most two labels enter its subset-update branch.
An empty-event cylinder returns before side, rather than taking any
of these enumeration paths.

Proof. The full row represents four identical fully observed left and
right labels. Side scans all their coordinates and assigns the unique
equality partition on each side. It does not enumerate other partitions.
The nonempty represented cylinder agrees with that complete restriction;
the other cylinder has the explicit conflict flag. The flag sets valid
to zero before normalizer's initial return test.

In the partial row every left label and the first seven coordinates of
every right label are zero and observed. The first three right labels
also have their last coordinate observed as zero. The last sample is
the only missing last coordinate. Side therefore fixes the left
partition, but reports an incomplete right side for the evidence call.
Nextpart still visits all fifteen restricted-growth partitions of four
positions. A block containing a fully observed sample can receive only
the all-zero label. A block containing only the fourth sample can
receive either that label or the label differing in its last bit.
Consequently at most two of the 256 labels have any allowed block.
Distinct blocks must receive distinct labels in countlabels' injection
count. A positive count thus requires $s\le2$; this is a consequence
of the represented restrictions and the countlabels invariant, not a
reference value of a normalizer. All fifteen preliminary counts and
their rejected terms remain charged. The complete cylinder either
fills the missing coordinate consistently, or the explicit empty-event
flag returns immediately; neither enlarges these bounds.

In the nine-sample row the fully observed seven-bit left labels encode
the nine different sample numbers. The right labels are fully observed
and identical. Side gives nine left blocks and one right block. The
seen-edge scan therefore encounters nine distinct pairs incident to
that right block. Its degree becomes nine; the literal comparison
$8<9$ sets ok to zero. Inject finishes its occurrence scan and returns
at its existing degree guard, before initializing any map odometer.
This holds for both source choices. It does not rely on a computed
zero normalizer. The agreeing cylinder preserves the same argument.

Finally, for the first two rows source-zero maps have respectively
$36^r27^s$ settings. The source-one alternatives have $9^{r+s}$,
which are bounded by the displayed numbers. A zero weight inside
either enumeration does not skip vertex, edge or odometer operations.
Both complete enumerations remain in the bound. $\square$

**Definition 15.3 (two-coordinate body recurrence).** Let $h$ be the
larger width of the represented prior numerator and denominator, with
zero represented by one bit. For these three frames $h=2$ and $t=2$.
Put

$$
 m_0=64N+4h+64,\quad w=4m_0+8,\quad e=8N+2,\quad
 v=\max(15N,36,N^2,H,2N),                                    \tag{IS.36}
$$

where $H=16$ for positive-partial and $H=1$ otherwise. Here $e$ is
an individual serialized record's natural-number payload width, $v$
is a vector's record count, and $w$ bounds scalar routine scans.
These are different from a vector's bit length or the output length
$Y$ in (IS.9). Write $M=972,26244,0$ and $P=1,15,1$ in row order.

For each body $f$, let $a_f$ count its syntactic instruction sites
and $p_f$ its syntactic push sites in the SharingGraph expansion.
Calls contribute their literal argument binding, eight return pushes
and continuation transfers to their caller's sites. The callee body
is counted separately. Include twelve extra instruction sites and no
push sites for a callee's exit and eight-bit dispatch; include the
single terminal instruction for main. Thus unreachable syntactic
branches can only enlarge these site counts. The fixed counts are:

| Body | $a_f$ | $p_f$ |
| --- | ---: | ---: |
| add | 71 | 20 |
| sub | 70 | 19 |
| lt | 25 | 8 |
| eq | 33 | 9 |
| mul | 32 | 9 |
| div | 95 | 41 |
| gcd | 30 | 8 |
| reduce | 50 | 24 |
| qadd | 73 | 40 |
| popword | 25 | 4 |
| prepend | 26 | 7 |
| get | 52 | 25 |
| put | 103 | 57 |
| zeros | 30 | 10 |
| concat | 23 | 4 |
| encv | 32 | 9 |
| encu | 31 | 11 |
| encq | 60 | 33 |
| readv | 29 | 5 |
| readu | 45 | 14 |
| readcache | 158 | 89 |
| conjoin | 113 | 62 |
| blocks | 81 | 42 |
| nextpart | 222 | 128 |
| side | 388 | 237 |
| countlabels | 809 | 498 |
| falling | 70 | 34 |
| odometer | 114 | 59 |
| incident | 4111 | 1 |
| inject | 705 | 446 |
| normalizer | 457 | 281 |
| mixture | 88 | 48 |
| addword | 47 | 24 |
| main | 420 | 250 |

Use the call multiplicities $m_{fg}$ in Definition 11.1, with these
proved deletions only: normalizer's countlabels and nextpart
multiplicities are one in the partial row and zero in the other two;
the null row's inject-to-incident, inject-to-eq and inject-to-odometer
multiplicities are zero. Other multiplicities are unchanged. Set

| Body | local site-visit multiplier $\lambda_f$ |
| --- | --- |
| add, sub, mul, div, encu, encv, readu | $w+2$ |
| gcd | $2w+3$ |
| popword, prepend | $e+2$ |
| get, put, zeros | $v+2$ |
| concat | $Y+2$ |
| readv | $L+2$ |
| main | $t+2$ |
| readcache, conjoin | $15N+2$ |
| blocks, falling | $N+2$ |
| nextpart | $(N+2)^2$ |
| side | $16(N+2)^2$ |
| countlabels | $\max(257\cdot9(N+1),2(H+1)(N+1))$ |
| odometer | $2N+2$ |
| inject | $(M+1)(2N+2)$ |
| normalizer | $\max(N+2,P+1)$ |
| lt, eq, reduce, qadd, encq, incident, mixture, addword | $1$ |

In the same acyclic dependency order as Definition 11.1 define

$$
 (S_f,A_f)=\lambda_f\left((a_f,p_f)+
                   \sum_g m_{fg}(S_g,A_g)\right),\qquad
 S_x=S_{\rm main},\quad A_x=A_{\rm main}.                     \tag{IS.37}
$$

The site multiplier is applied once per body. The number of a body's
sites is not an additional multiplier on each child cost.

**Theorem 15.4 (typed loop and allocation certificate).** The accepted
evaluation on each of the three unchanged frames executes at most
$S_x$ stack instructions and $A_x$ pushes. Its output still has length
at most $Y$. The recurrence contains no observed evaluation length,
hidden injection, expected numerical answer or reference output.

Proof. The denominator-divisibility and partial-sum arguments of
Theorem 8.2 use $\log_2D<26N$. Replacing its coarse represented-width
estimate $L$ by the actual prior width $h$ bounds rational addition's
cross-products and sum by $52N+2h+5$ bits. Ratios are formed only
when their actual normalizer is positive. The bound $m_0$ exceeds
these widths, the map-count width $20N+1$, the label-count width
$8N+1$, the power and falling-factorial widths, and all loop indices
in these cases. It also bounds a raw normalizer numerator before
reduction: the product of the map-count and the two label counts
has fewer than $36N+2$ bits. No prior cancellation supplies $h$.

Inside shift-add multiplication, the shifted multiplicand has at most
the sum of the original argument widths plus one, including its last
shift. Ripple arithmetic adds at most one carry bit. Division consumes
dividend bits, keeps a remainder below twice its positive divisor
before a subtract, and a quotient no wider than its dividend. Euclid
does not enlarge those inputs. Its standard two-remainder halving
argument gives at most $2w+1$ nonterminal iterations. The slack in
$w=4m_0+8$ consequently bounds every scalar scan, normalization and
temporary move in these bodies. In particular readu's moves are
charged; argument aliasing does not turn its explicit moves into
constant-time operations.

The serialized vectors are cache positions, requirements, partitions,
seen edges, degrees, type occupancies, maps, and countlabels subset
tables. Their record counts are bounded by $v$. Every record payload
is at most $e$: subset counts are at most $256^N$, and all other
entries are smaller coordinates, labels, degrees or bits. This
statement also covers intermediate nonnegative subset partial sums.
The reversed prefix in put has at most $v$ records; its individual
records do not acquire the width of the entire prefix. Thus each
popword/prepend site is visited at most $e+2$ times, and each
get/put/zeros site at most $v+2$ times per invocation. The latter
still pays its child word operations through (IS.37).

Readv scans a represented suffix or cylinder of length at most $L$.
Encv's inputs are scalar encodings or one encoded rational of length
at most $4m_0+3<w$; its resulting unary framing is not an extra
outer-loop factor. Concat moves complete output prefixes/suffixes,
bounded by the already proved $Y$. Their explicit moves still push
new frames even when their caller bindings share heads.

For the combinatorial routines use Theorem 15.2. Countlabels scans
all 256 labels. Its label/block/coordinate sites have at most
$256\cdot N\cdot8$ visits; its subset/block sites have at most
$2(H-1)N$ visits because only two labels reach that branch. The
displayed maximum, with slack for terminal tests, covers both and
the preliminary scans. The normalizer has one left partition, at
most $P$ right partitions and its separate $N$-step power loop.
The other local loops have exactly the sample/coordinate, decreasing
position or map-setting bounds displayed above. In the degree-rejected
row, all preliminary inject sites are paid; the three deleted child
edges occur only after the rejecting return.

Every own instruction site is visited at most its $\lambda_f$;
every syntactic child call site has the same bound. Argument, exit
and return-dispatch sites are included. Induction on the unchanged
acyclic call graph proves (IS.37), separately in both coordinates.
Shared tails yield no repeated allocation credit: only executing a
literal push adds a frame, and every such push is charged even if
its frame later becomes unreachable from logical heads. $\square$

## 16. Exact frontend extractions on the complete message sequences

**Definition 16.1 (message and cylinder lengths).** Let $h_N,h_a,h_b,h_t$
be the represented unsigned payload widths, and $c_j$ the length of
the $j$th represented cylinder, including its conflict flag. Let $u$
count cylinders whose flag permits a mask. There are $q+3$ complete
messages: initialization, all $q$ Reads, one evaluation and Close.
Here $q$ includes the genuinely appended post-evaluation Read. Put

$$
\begin{aligned}
 E_{\rm init}&=16N+2(h_N+h_a+h_b)+5,\\
 E_{\rm val}&=2L+31N+t+2(h_N+h_a+h_b+h_t)+9
                  +\sum_j(2c_j+1)+u(15N+1),\\
 A_F&=I+(q+3)+2+E_{\rm init}+E_{\rm val}+5S+14q+4,\\
 S_F&=16(F_0+1)(A_F+q+4).                                    \tag{IS.38}
\end{aligned}
$$

Here $A_F$ is an extraction count and $S_F$ a field-action allowance.
Neither is the evaluator instruction coordinate $S_x$.

**Theorem 16.2 (frontend allocation identity).** For these complete
valid messages the frontend extracts exactly $A_F$ cells and executes
at most $S_F$ field actions, excluding evaluator and provider internals.
No earlier request, transient parser word, partial record or old answer
is reclaimed in this count.

Proof. Incoming bits allocate $I$ request cells; their $q+3$ request
headers and the initial receipts/port headers add $q+5$. Each readv
of a payload of length $d$ allocates one header, $d$ unary marks and
$d$ result cells. Unsigned validation adds no cell. Unary conversion
starts with one header and grows monotonically to exactly its final
integer value; all doubling appends remain in that same chain.
Shape therefore adds $N+1+15N+1=16N+2$ cells. Together with the
three unsigned reads this proves $E_{\rm init}$.

Evaluation first captures its length-$L$ frame by readv, then validates
N, shape, the two prior words, a $15N$-entry mask, and the cylinder
count. Cylinder-count unary conversion allocates $t+1$ cells. Each
cylinder is captured by readv; each mask-bearing one additionally
allocates its fresh $15N+1$ paired word. This is exactly $E_{\rm val}$.
The evaluator's subsequent loader and seed are separate below.

A Read of operand length $d$ allocates $2d+1$ for its captured word,
$d+1$ for the actual transmitted word, $2d+4$ for its fresh receipt
including header, V-framing and actual two reply bits, and eight for
its seven-bit answer and header. Their sum is $5d+14$. Classification,
reply checking and writing the original cache slot add no allocation.
Repeated Reads still allocate distinct receipt headers. Close adds
its three-bit answer and header, giving the final four. The composed
evaluation returns directly through its bound output-return reference;
it does not allocate an additional frontend answer word. Summing gives
the identity in (IS.38).

For the field-action bound, each ordinary parser/chain loop advances
over received cells, freshly allocated marks/words, or the shape it
has already allocated. Shape and unary loops have their monotone
append counts just proved. Receipt wrapping and transmitted-word scans
advance over the captured operand. Prior comparison advances over its
captured words; classification advances over the operand and at most
three suffix bits. Mask scans are over allocated shape/mask words.
Nested cylinder validation advances over its captured cylinder words,
which are already included in $E_{\rm val}$. These are consuming
chains, not a numerical-value bound on an arbitrary word.

A shared take site can consume the request, captured arithmetic frame
and captured cylinder payload successively; these three parsing levels
are bounded by their respective input/allocated-word counts. Including
entry/exit tests, input waiting/resume and print/return branches, each
fixed frontend location is visited at most $16(A_F+q+4)$ times.
More explicitly, receive has at most $2(I+q+3)+1$ visits. Total take
invocations are at most $I+L+\sum_jc_j\le A_F$. Each readv mark or
payload loop advances over the cells counted in its own extraction
term. Unary's double-loop visits are bounded by its final appended
tokens plus its binary-input visits; mask/shape loops by their paid
shape/mask entries; prior by captured prior bits; classification and
port/receipt scans by $S+q$; and answer printing by $7q+3$. All are
bounded by $4(A_F+q+4)$, so the displayed factor sixteen also covers
their fixed entry, return and suspension tests without multiplying
parent and child scan lengths.
The once-sealed complete messages do not enter need.more or prediction
construction. Multiplying by $F_0+1$ proves $S_F$ with slack. This
argument makes no claim about malformed, repeatedly sealed or other
message patterns, for which the existing supplier remains available.
$\square$

**Theorem 16.3 (joint prospective native demand).** The unchanged
composed image has the sufficient reserve and native-transition bounds

$$
\begin{aligned}
 K^\sharp&=5+L+A_x+A_F,\\
 n^\sharp&=K^\sharp+226380,\\
 I_C^\sharp&=128n^\sharp+16(4K^\sharp+903480)
                       +4(8K^\sharp+4740143)+64,\\
 V_{\rm exec}^\sharp&=128(S_x+L+2Y+360+64)+5S_F .              \tag{IS.39}
\end{aligned}
$$

Its simultaneous native census is

$$
 (O_C,A_C,C_C)=(3K^\sharp+777713,
                13K^\sharp+3037783,16K^\sharp+11648685).        \tag{IS.40}
$$

Proof. Five seed extractions and $L$ loader extractions are distinct
from all evaluator pushes and all frontend extractions. No pop,
clear, head copy or reset replenishes this supply. Apply the existing
retained-layout calculation (IS.15) to their sum. The installer bound
is (IS.18) at this same reserve, with all source shadows, targets,
descriptors and unused cells retained.

In the literal Direct lowering a field action uses its entry and at
most four further native locations. A stack-instruction path has fewer
than 24 field actions; a loader iteration has fewer than 24; the two
output scans fit the displayed $2Y$ allowance at factor 128. Fixed
seed, reset, bind, End/Ack/indirect Return and terminal paths fit the
remaining constant and 360 resets. Thus 128 per displayed evaluator
unit and five per frontend field action suffice. Input latch delivery,
provider work and host observer/preparation work are separate. The
result concerns native transitions, not host instructions or time.
$\square$

## 17. Common cuts, observer costs and explicit unpriced host terms

**Definition 17.1 (the actual consumer and cuts).** The consumer is
the fixed composition of Definition 7.1 in Direct with empty initial
received data, connected to one OriginalConnection and one fresh
instance of the authorized original test-source factory. The root,
port and connection remain the same throughout initialization,
acquisition, acquired-cache framing, computed evaluator output and
its actual indirect Return, then Read(LL), fresh receipt and Close.
The observer is ServiceDirect.observe; its feed/deliver/drive behavior
retains Direct.run's output join on every invocation. A separately
installed mutable B owner remains reachable throughout. Denote its
actually chosen reserve by $u_B$, with §14's own installation, head,
control and busy state. The original fixed retained instance uses
$u_B=128$; this is not a reserve for all finite prefixes.

Take common cuts before/during source and code preparation, during
compiler invocation and library loading, during descriptor construction
and both installation passes, at every native operation and observer
callback, at input/provider/output boundaries, and during terminal
release. At each cut the population is the identity union of actual
retained objects and actual temporary allocations at that cut. Physical
aliases are counted once, but an old buffer overlapping its replacement
is a second allocation. Let $\mathcal R(c)$ be the multiset of actual
allocator requests still retained at cut $c$, including container backing
and runtime/native buffers. Objects with the same owner-local index
but different actual allocations remain distinct.

**Theorem 17.2 (observer and copying obligations at those cuts).** Put
$D_s=I+q+3$ and $O=7q+2Y+6$. The consumer has the following additional
prospective host quantities, none of which is a pool extraction:

| Actual routine or retained owner | Required count or common-cut population |
| --- | --- |
| Direct.run called by initial drive and every signal | $D_s+1$ whole-output joins; at most $(D_s+1)O$ characters copied and an $O$-character temporary per join |
| Direct.tick received-input check | empty received list in this service instance, but the assertion, generator and empty join still occur every tick |
| Direct.tick boundary and immutability checks | at most $V_{\rm exec}^\sharp$ boundary-map lookups and observer calls, and at most that many frozen-map membership checks; hash/probe work depends on the actual table capacities |
| ServiceDirect.observe at evaluator instruction boundaries | at most $S_x+2$ boundaries, each scanning all 604 register names and up to 360 stack heads |
| first-time freezing of spines | at most $L+A_x$ distinct cell insertions; a shared already frozen tail stops the scan |
| frozen dictionary including handed-off input | at most $2L+A_x+5$ entries and four-reference tuples, including $L$ raw frontend input cells |
| repeated root/token freezing | up to $5(S_x+2)$ new tuple allocations and replacements, even for existing keys |
| handoff observer | one length-$L$ cell list, one transient length-$L$ tuple dictionary, retained length-$L$ bit string and metadata |
| computed-return observer | one retained prefix-output copy of length at most $O$ and metadata |
| terminal computed-output projection | one output-pointer slice and computed-frame join of length at most $O$, followed by Reader/parse_reply slices including the retained computed payload; at most $O$ pointers and $3O$ character payloads beyond the ordinary output list |
| concrete terminal receipt checks | two receipt traversals, at most $2(2S+3q)$ payload bits plus headers, two lists of occurrence IDs and decoded words; their overlap is retained until comparison finishes |
| cache checks and acquired-cache framing | paired $15N$-entry views, attained indexed tuples, represented frame and command strings, including the original raw input and overlapping slices |

Proof. Direct.run joins its whole accumulated output even when its
caller ignores the return value. Output is monotone and bounded by
$O$, so the first row follows without a completed evaluation. Direct's
initial received list is empty; the acquired frame reaches is2.received
through the frontend instead. The composed observer, not the base
unprefixed q-label test, freezes the is2 stack banks.

On a first visit to an unfrozen cell the observer inserts its tuple
before following its tail. Subsequent aliases find that same dictionary
key and stop. Thus the total novel-spine traversal is at most $L+A_x$;
it is not that number times the number of aliases. Head tests and
register-name scans still recur at every boundary. The handoff freezes
the $L$ distinct frontend input cells too, in addition to the loader's
$L$ new spine cells. Five root/token entries are assigned at every
boundary. Their previous tuples can overlap the replacement tuple;
their allocator requests and release work do not disappear when the
dictionary entry is overwritten. The remaining rows are the literal
list, dictionary, slicing, join and receipt/cache traversals of the
same consumer. The received reply is never derived from these views.
$\square$

**Definition 17.3 (priced core and source-located residual inequalities).**
The exact reserve object payload is $500K^\sharp$ bytes from Proposition
13.2. At a fully installed cut all those source Blocks, target Blocks,
their reference lists and buffers, and Source descriptors still coexist.
Additional retained and overlapping requests are as follows.

| Source owner | Retained requests and simultaneous transient requests still to price |
| --- | --- |
| Direct constructor | source-block and descriptor lists of length $n^\sharp$; source and target pool lists of length $K^\sharp$; native list of length 225718; source/target boundary maps of length 62069; source and target register maps of sizes 604 and 57; source-to-descriptor map of length $n^\sharp$; source, descriptor and pool link slices; relocation lists and source/target map overlap |
| fixed program preparation | shared-assembler raw program, pruned program, field and composed graphs, labels, pruning sets/sorted lists/index maps and clone maps; live function/code/module material; temporary assembler banks and call tables; these precede and can overlap installed material |
| BitKernel and Installer | compiler process with source/object/shared-library buffers and loaded mappings; shared immutable wires including the unused width-32768 bank; actual ctypes arrays, pointer wrappers and keepalive dictionaries; separate mutable headers and installer controls; source_array and target_array views/keepalives at rebind, copied data and pending target |
| retained B owner | its own source/target/descriptors, pool, code/control/register maps, mutable initializer header, head/PC/busy/pending and observer objects; only actual common immutable wires/library are shared |
| source preparer | $8k+8$ source vertices, $3k+3$ route headers, $d_k=(5k^2+13k+6)/2$ route cells, arena object list/identity set/field dictionaries/counters, owned set, $5k+4$ event/address pairs; address lists/strings and route-validation maps/prefix strings overlap |
| OriginalConnection and OriginalPort | binding, all retained request/reply/free-list cells and headers of (IS.17); object/identity containers and counters; call tuples and original operands; invoke's operand list/join, V-wire strings, Buffer.cells list, Reader slices and two-bit latch; Buffer.clear retains cells on its free list |
| runtime and observer | output-character objects and list capacity, all quantities in Theorem 17.2, counter and index integers, comparison/hash temporaries, Python/C execution stack, garbage-collection work and retained arenas, interpreter/library mappings and terminal-release overlap |

Here $k=15N$. The source factory's address depth is at most $k+4$.
Its retained event-address characters are at most $(5k+4)(k+4)$.
Prefix extraction during route validation copies at most
$(5k+4)(k+4)^2$ characters; successive concatenations of route words
are bounded by $2d_k^2$ copied characters for expected and actual
route reconstruction together. These are additional host-work
cardinalities, not free implementations of the $d_k$ route events.

For each request size $b$, let $\alpha(b)$ be an upper allocation
charge for the applicable actual allocator, including alignment and
allocator-owned retained backing. It must account separately for old
and new list/table backing while resizing. Let $U(c)$ price the
unattributed runtime/compiler/stack/mapping requests at that same cut.
These author-owned pricing obligations have the explicit form

$$
\begin{aligned}
 H_{\rm complete}&\ge
   \max_c\left(\sum_{b\in\mathcal R(c)}\alpha(b)+U(c)\right),\\
 W_{\rm complete}&\ge W_{\rm assemble}+W_{\rm source}
       +W_{\rm compile}+W_{\rm install}+W_B
       +W_{\rm ticks}+W_{\rm provider}+W_{\rm input/output}
       +W_{\rm observe}+W_{\rm release}.                      \tag{IS.41}
\end{aligned}
$$

Every $W$ term prices the corresponding inventory row's actual
allocation, release, copying, hashing/probing, resizing and integer
operations. For example $W_{\rm input/output}$ includes
$(D_s+1)O$ character visits from the run joins, and $W_{\rm observe}$
includes $604(S_x+2)$ name visits, $360(S_x+2)+L+A_x$ spine-head/
novel-cell visits and $5(S_x+2)$ tuple replacements. These counts
must be multiplied by upper costs for the actual runtime operations;
they are not themselves host-work prices. Counter width is bounded
from total charged events, rather than from $N$: if $E$ bounds the
charged event/counter increments in this inventory, its digit demand
is at most $1+\lceil\operatorname{bl}(E+1)/30\rceil$ four-byte
digits on the specified ABI. Any additional diagnostic observer adds
its own requests and increments to $E$ before this substitution.

CPython 3.12.13's list_resize uses capacity no greater than
$\ell+\lfloor\ell/8\rfloor+6$ for the append-built lists here, but
may retain the old buffer during realloc. Its allocation-size test
is on capacity times pointer size. Dictresize allocates new keys
while old keys/values remain live. These source facts explain why
shallow object sizes and final logical lengths alone do not instantiate
(IS.41). They do not provide an allocator-fragmentation, compiler,
runtime-stack, garbage-collection or hash-probe work bound for this
installed build. Those prices, the exact retained B/kernel owner
manifest and the release policy remain explicit residuals for all
three rows. They are local construction/pricing duties, not requests
for an external source or Ack to finish.

**Theorem 17.4 (ABI and resource-offer boundary).** A realization of
(IS.39) in this fixed layout must additionally satisfy, for every
simultaneously allocated container and actual reference domain,

$$
\begin{aligned}
 \ell&\le2^{63}-1,\qquad
 8\,\operatorname{capacity}_{\rm list}(\ell)\le2^{63}-1,\\
 \#\{\text{distinct actual referenced objects at }c\}&\le2^{64},\\
 H_{\rm complete}&\le H_{\rm reserved},\qquad
 W_{\rm complete}\le W_{\rm backed}.                          \tag{IS.42}
\end{aligned}
$$

The analogous checked byte/index-size conditions apply to dictionary,
set, tuple, bytearray and ctypes allocations. C initializer calls must
use their actual unsigned-64-bit limits; modular counter differences
require a per-call increment below $2^{64}$. This does not truncate
the Python evaluator's arbitrary-width scalar words or counters.

Proof. The list tests are its signed-length and pointer-array byte
tests on this ABI. A 64-bit reference carrier cannot inject a larger
simultaneous object domain into its possible names. Actual ctypes
pointers must address their kept-alive arrays; changing a symbolic
model reference width supplies no new pointer representation. The
last two inequalities compare demand and offers for precisely the
same retained/shared owners and cuts. No offer is entailed by (IS.41),
an RSS observation, a successful allocation, an execution cap or the
total installed physical memory. Failure of one chosen sufficient
reserve or price to satisfy (IS.42) proves no necessary lower bound
on another faithful execution. $\square$

## 18. The three substitutions and their exact remaining boundary

**Proposition 18.1 (refined full-message substitutions).** All three
inputs have the lengths, hashes and acquisition schedules of
Proposition 14.1. Their complete substitutions into (IS.36)–(IS.39)
are:

| Frame | $I,q,S$ | $w,e,v,H,M,P$ | $E_{\rm init},E_{\rm val},A_F$ |
| --- | --- | --- | --- |
| positive-full | $5376,75,2178$ | $1320,34,60,1,972,1$ | $81,1232,18713$ |
| positive-partial | $5249,74,2117$ | $1320,34,60,16,26244,15$ | $81,1230,18264$ |
| null-nine-distinct-left | $21507,150,9678$ | $2600,74,135,1,0,1$ | $163,2668,74987$ |

In the same order the cylinder lengths are $(121,1),(121,1),(271,1)$;
each row has one mask-bearing cylinder. The prior payload widths are
$(1,2)$, without reduction. Source, connection and shared-wire censuses
remain those of §§10 and 13. Add the separately retained B census and
subtract its physically shared immutable wiring exactly once. In
particular this refinement never adds its mutable pool to $K^\sharp$.

The resulting instruction/push/reserve numbers and frontend work are:

| Frame | $S_x$ | $A_x$ | $S_F$ | $K^\sharp$ |
| --- | ---: | ---: | ---: | ---: |
| positive-full | 958573387946884 | 265424734369056 | 650654208 | 265424734388161 |
| positive-partial | 58503114650468336 | 16197911821800220 | 635073408 | 16197911821818875 |
| null-nine-distinct-left | 2663360054441964 | 738876698045112 | 2601681984 | 738876698120943 |

Here $F_0=2163$. The respective $V_{\rm exec}^\sharp$ bounds are
$122697398567391616$, $7488398680088039040$ and
$340910103550755520$ native transitions, before adding the separately
displayed installation/provider/delivery coordinates. The exact reserve
object-payload terms $500K^\sharp$ are:

| Frame | $\operatorname{bl}(K^\sharp)$ | reserve payload bytes | status of this substitution |
| --- | ---: | ---: | --- |
| positive-full | 48 | 132712367194080500 | list length/array-byte and native-census object-count tests below hold; complete host prices/offers absent |
| positive-partial | 54 | 8098955910909437500 | same tested conditions hold; complete host prices/offers absent |
| null-nine-distinct-left | 50 | 369438349060471500 | same tested conditions hold; complete host prices/offers absent |

For these chosen reserves, $K^\sharp+226380$ and the append-capacity
upper bound for its eight-byte-pointer lists satisfy the signed-length
and byte-size tests in (IS.42). Adding the original source, connection
and fixed retained B census, with one shared-wire subtraction, also
gives an object count below $2^{64}$. These particular tests eliminate
the previous chosen reserve's immediate list-length obstruction.
They do not certify allocator address ranges, all dictionary/set/ctypes
capacities or an available physical/virtual allocation. Even the exact
native-census count excludes runtime wrapper/container objects; their
actual pointer domain still requires (IS.42). The exact
payload term is an upper-reserve contribution, not a necessary lower
bound on the bytes needed by the same session with a smaller reserve.

Proof. The source frames are the represented full-zero and partial-zero
restrictions, or nine represented distinct left labels, with the
agreeing and empty-event cylinders just used in Theorem 15.2. Count
the unchanged messages, including their acquisition-only final probe,
and then the separate seven received bits of Read(LL) and two of
Close. Substitute their unsigned and cylinder lengths into (IS.38)
and the guarded multiplicities into (IS.37). Every quantity is a
finite integer derived before evaluation. The common-cut union is
(IS.17), with exactly the same source/provider and mutable-B terms;
the payload term $500K^\sharp$ follows at this same reserve. $\square$

**Proposition 18.2 (scope of the sufficient certificate).** The sharper
extraction and instruction certificate and the original-domain fallback
can be used together. They neither complete a host-price comparison
nor establish physical impossibility for any of the three sessions.
In particular (IS.41)'s outstanding prices and (IS.42)'s actual
same-scope byte/work offers are separate obligations for every row.

Proof. Theorem 15.2 proves the refinements' guards on actual represented
restrictions before substituting them. Theorems 15.4 and 16.2 bound
all allocation-producing loops in that branch; other branches retain
their previous suppliers. Every historic extraction and occurrence
is retained in the composed native and host accounts. The host
inventory includes frontend/parser, per-tick observer, whole-output
rescan, source/target preparation overlap and local provider/return
completion, rather than transferring these to a resource-offer owner.
No adequate values for the remaining author-owned prices or external
scoped offers are assumptions of this certificate. Thus an adequate
complete comparison has not been derived. The inequalities are
sufficient-demand tests and imply no claim about minimum demand.
$\square$

The new content is the source-specific guard/typed-record composition,
exact frontend extraction identity and observer/common-cut application.
The Euclidean iteration estimate, compositional counting and amortized
reuse principles are intermediate mathematics; the existing
[Tarjan note](../../../Library/Computability/tarjan1985amortized.md)
supplies the latter's literature context. The Python container facts
are the list_resize and dictresize definitions in the
[CPython 3.12.13 source](https://github.com/python/cpython/tree/v3.12.13/Objects).
The fixed mathematical routines are those of the private source pin
$9a028468adbb425d7595004c9472055b10222d5f$, with the parameter/label
correspondence stated above. These are repo-derived ordinary proofs
and source correspondences. C117 §§32–33, four-path IV §§52–53 and
the readable-history/visible-quotient suppliers keep their own exact
premises; none supplies a price, execution, grant or receipt deletion
for (IS.41)–(IS.42).

## 追加锚（本行以下为增补区）

## 19. A guarded star consumer of the actual indexed partitions

**Definition 19.1 (the changed consumer and its domain).** Keep ML-F,
UJB15–17 and Definitions 1.1, 7.1 and 17.1, including every finite
represented input with $N\ge4$, $0\le a/b\le1$, $b>0$, and the
original-indexed cache and finite cylinder list. The numerator and
denominator of the prior are the received words, without cancellation.
The only production body changed here is `evaluator_program.inject`.
Its inputs remain the actual current restricted-growth partitions
$p,q$ and their block counts $r,s$, the actual $N$, and the source
selector supplied by normalizer. In particular every block occurs.
The source selectors admitted by that caller are precisely $0,1$.

Retain the occurrence scan, its distinct-edge `seen` table, both degree
arrays and its rejecting return, and the existing source-specific type
and capacity assignments. After those assignments, before `mapsize`,
`map`, `more` or any type occupancy is initialized, execute:

1. Test $r=1$. If true, call the represented `falling(27,s)` and
   `mul(72,result)`, publish that computed word as $J$, and return.
2. Otherwise test $s=1$. If true, call `falling(8,r)` and
   `mul(243,result)`, publish $J$, and return.
3. Otherwise enter the existing complete general inject body.

The first branch owns the overlap $r=s=1$. These are calls to the
existing bit-stack routines, lowered by the existing IS2 path; no
host integer or probability callback supplies their return. `inject.general`
and the two star labels are source addresses, without runtime actions.
The tests run afresh for every inject call. Neither a frame fingerprint,
a previous normalizer result nor a cache-wide classification selects them.
The caller's $r\le72$, $s\le243$, positive $L_p,R_q$ and valid-conjunction
checks retain their original positions. No active-row projection or
four-edge inversion is part of this construction.

**Theorem 19.2 (ordinary source, guard and arithmetic correspondence).**
For every invocation in Definition 19.1 the changed routine returns the
same exact $J_i(H_{p,q})$ as UJB15.3, on each literal source. Its general
branch has the original domain. A repeated sample incidence does not
change this count or authorize a change to $N$.

Proof. UJB15's literal $G_0$ has 36 left types of capacity two and
27 right types of capacity nine; its incidence relation is the fixed
line/point relation with three point neighbors per line type and four
line neighbors per point type. Thus its actual literal populations
are $72,243$ and its degrees are $27,8$. The supplied $G_1$ is nine
components $K_{8,27}$ and has the same populations and degrees. Each
is simple and has 1944 edges. These are the original source identities,
not new combinatorial suppliers.

The unchanged occurrence scan increments a degree only on the first
occurrence of a pair $(p_j,q_j)$. After its first $j$ samples, `seen`
is exactly the set of pairs in that prefix and the degree arrays are
its two incidence degrees. Induction follows directly from get/test/put
and the two increments. A degree above 27 on the left or above eight
on the right makes every injective literal realization impossible.
Returning zero there is consequently sound, including repeated and
out-of-support inputs.

If $r=1$, surjectivity of $q$ implies that the distinct constraint graph
is the entire distinguished star $\{0\}\times[s]$. Choose its actual
left center in 72 ways. The distinguished leaves must be different
literal neighbors, so the supplied count is $72(27)_s$. If $s=1$,
choose its actual right center in 243 ways and obtain $243(8)_r$.
At $r=s=1$ both give 1944; the deterministic first branch is sound.
The same argument includes the degree endpoints and zero beyond them.
The existing guards can return those zero cases earlier.

The falling routine's loop invariant after $k$ factors is the product
of the first $k$ nonnegative factors $\max(c-j,0)$. Its existing
subtraction borrow test prevents an underflow word from entering the
product. At the zero factor the product becomes zero and remains so.
The existing canonical multiplication computes that natural product
at arbitrary finite width. Their established ML/IS2 contracts therefore
produce these exact counts from the represented arguments. No type map
is initialized on either star path. In the remaining branch the old
capacity products, every occurrence test and complete odometer are
unchanged, so UJB15.3 applies verbatim. Repeated occurrences constrain
an already required edge; they remain separate sample positions in
the probability law. $\square$

**Theorem 19.3 (all legal native cuts and the service continuation).**
Under the initialized owned-material, current-rights and sufficient
finite reserve premises of ML-I/ML-P and §2, the changed routine has
that same native correspondence at every legal finite prefix,
including pending arithmetic and return prefixes. At a completed
inject call its caller-visible words and continuation agree with the
old specification. This is a conditional statement about the supplied
material, not a reservation for an entire session.

Proof. Reuse Theorem 1.4 and §2's literal lowering for eq, falling,
mul, their calls and the unchanged remaining routines. An argument
binding copies an actual immutable head; the eight-bit return stack
names a compiled continuation. Each arithmetic push extracts and
initializes a fresh granted cell before publishing its head. All
intermediate heads decode as the corresponding current stack words;
private partial products, the literal PC, saved operands and busy
state remain part of the configuration. The earlier termination
measures apply to the finite falling loop and each multiplication.
Nothing requires an unfinished product to decode as a returned $J$.

At every primitive prefix the existing grant, allocation, frozen-tail
and successor invariants still apply. Denied rights or missing reserve
material cause the existing refusal, without an invented result or a
jump to a successful continuation. This assertion includes prefixes
that stop before a return and prefixes inside a nonhalting outer
computation. It does not identify the old map enumerator's internal
PC with the new arithmetic PC. Their relation is at completed routine
boundaries; Theorem 19.2 supplies the value equality there.

Only the existing caller-visible $J$ is consumed after inject. Its
scratch words do not select a source reply or service return. Composition
still receives the frontend's actual `eval.input` chain in
`is2.received`, binds `output.return` to the compiled returned node,
and uses the original End/Ack/indirect Return path. The returned node
clears `eval.busy` and continues to the same service return handler.
OriginalConnection, OriginalPort, cache indices, pending actual Read,
all receipt occurrence objects and Close remain unchanged. Source and
mutable B owners are separate from this arithmetic work material.
Thus the existing same-source continuation proof applies to the
changed completed evaluator output as well. It neither predicts an
actual Read reply nor executes an outstanding original session.
$\square$

**Theorem 19.4 (absolute laws, cylinders and positive-only ratios).**
On every admitted ML-F frame, including zero evidence, the changed
complete evaluator has exactly the old absolute outputs and encoded
return. For every current restriction $D$ it computes

$$
 Z_i(D)=\frac1{1944^N}\sum_{p,q}
       \frac{J_i(H_{p,q})L_p(D)R_q(D)}{(128)_r(256)_s},\qquad
 Z(D)=\frac{b-a}{b}Z_0(D)+\frac ab Z_1(D).                 \tag{IS.43}
$$

For every represented cylinder $C$, the same statement holds at
$D\wedge C$. Conditional ratios are returned exactly when $Z(D)>0$.

Proof. Normalizer still derives the partitions from the actual
restriction on each invocation, including every conjunction. It keeps
all original label intersections, zero label counts, source capacities,
128/256 falling denominators and the actual factor $1944^N$.
Theorem 19.2 replaces each $J_i$ by an equal integer before the same
multiply and qadd. Hence every term and every partial sum is equal.
The existing rational reduction and framing routines consequently
return the same canonical rational words and output bits.

Conflicting coordinate constraints or the explicit empty-event flag
retain valid=0 and the early zero normalizer return. Partial slots,
unread positions, repeated incidences and old sample indices keep
their original restrictions; the shared full injections have exactly
the extension factors of UJB16.2. The represented prior words are
passed unchanged to the old mixture routine, including endpoints and
unreduced words. If the actual mixture numerator is zero the old ratio
absence bit remains zero. Otherwise the same positive denominator
and cross-products give $Z(D\wedge C)/Z(D)$. No ratio at a null
conditioning event is introduced. This termwise equality establishes
the whole original domain, beyond the finite component checks.
$\square$

## 20. The changed image and its common-cut populations

**Definition 20.1 (literal binding).** The complete changed production
image is the fixed composition generated by ep.build, SharingGraph,
prune, field_graph and compose. Its stack SHA-256 is
`ff8ea0ad5ffe02bbc1bbc59240170407ef17702a0472f15f6be83b398c443afc`;
its composed field fingerprint is
`326af82c315be2e1fb83cf6df5bcffdbb75888543473a3d3261f7d3d4a8d8d30`.
It has 11143 reachable stack states, 361 stack registers, 63182 field
nodes, 229773 native code vertices, 605 reference registers and 57
bit registers. The source result register is `inject.J`, stack index 284.

The field indices of `is2.start`, `is2.print`, `is2.returned`,
`service.return` and `evaluate.begin` are respectively
$2163,62776,62818,1445,2156$. ChronologyDirect checks this fingerprint
and those actual entry identities. It also checks that the returned
node is the literal `put(eval.busy,0)` with both successors equal to
`service.return`, and retains the actual `output.return`, `is2.received`
and `eval.input` registers. Compose's bind points at that node, and
Direct's installed relocation translates the reference to its actual
native entry. No stale installed address is copied between images.

**Proposition 20.2 (changed retained layout).** With the same complete
message schedule, no initial Direct received bits, and reserve $K$,
the changed production construction has

$$
\begin{aligned}
 n'&=K+230436,& R'&=4K+919701,& B'&=8K+4825298,\\
 O'_C&=3K+789881,& A'_C&=13K+3090505,& C'_C&=16K+11818995.
                                                               \tag{IS.44}
\end{aligned}
$$

The installation demand bound is

$$
 I'_{\rm install}\le128n'+16R'+4B'+64.                        \tag{IS.45}
$$

Proof. Apply the actual layout identities (IS.15) and (IS.18) with
$F=229773$, $R=605$, $B=57$; the initializer and shared wire banks
are unchanged. Thus $n'=K+F+R+B+1$, the source reference count is
$4(K+F+1)+R$, and the source bit count is $8(K+1)+21F+B$.
The unchanged initializer seed contributes $(98572,98908,2168397)$
objects, reference slots and bits. The two installed copies and the
retained descriptors give (IS.44). This counts unused reserve cells,
source shadows, code targets and every descriptor simultaneously.

At the same $K$, the new code has 4055 additional native vertices,
one additional reference register and no additional bit register.
The increases in $(n,R,B)$ are $(4056,16221,85155)$, and the increases
in $(O_C,A_C,C_C)$ are $(12168,52722,170310)$. The installer bound
increases by 1119324 transitions at that common reserve. This last
number is a bound delta, not an executed installation count.
The original source, connection, separately retained mutable B owner,
and one subtraction for physically shared immutable wires retain
exactly §§10, 13 and 17's identities at the common cuts. $\square$

All earlier source proofs, installed censuses and finite checks retain
their stated image pins. Their general lowering and counting identities
are reused here; their old numerical image census or installation
measurements do not certify this changed image.

## 21. Complete-message demand after the local substitution

**Proposition 21.1 (prospective demand, with the remaining costs).**
Retain Theorem 15.2's source-derived normalizer call shapes and the
same three messages, priors, cylinders and acquisition schedules.
In (IS.37), only inject's own sites change to $(809,520)$; its new
syntactic child multiplicities are

| Child of inject | add | eq | falling | get | incident | lt | mul | odometer | put | sub | zeros |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| multiplicity | 11 | 3 | 2 | 12 | 1 | 6 | 6 | 1 | 5 | 2 | 6 |

Use $\lambda_{\rm inject}=2N+2$ for these three message shapes.
Set its incident and odometer edges to zero. In the null-nine row
also keep its eq edge zero, because the earlier degree return precedes
both new tests. Other own sites, local multipliers and the previous
proved normalizer-edge deletions remain those of Definition 15.3.
The retained syntactic fallback sites and other child multiplicities
overcharge these paths and hence remain safe upper bounds. Denote
the resulting costs by $(S'_x,A'_x)$.

Keep the exact frontend extraction count $A_F$, frontend action bound
$S_F$, message lengths, source/connection counts and output bound $Y$
of §§16–18. Set

$$
\begin{aligned}
 K'&=5+L+A_F+A'_x,\\
 V'_{\rm exec}&=128(S'_x+L+2Y+361+64)+5S_F.                 \tag{IS.46}
\end{aligned}
$$

At that same reserve use (IS.44)–(IS.45), retain $500K'$ as the exact
reserve object-payload contribution, and use the common-cut host
inventory (IS.41)–(IS.42). Its recurring name and head scans now cost
$605(S'_x+2)$ and $361(S'_x+2)$ visits; distinct new spine traversals
are at most $L+A'_x$, and its retained freezing dictionary has at most
$2L+A'_x+5$ entries. Five root/token tuple replacements still recur.
Every frontend, provider, delivery, output join, runtime, allocator,
compiler, inherited-owner and release term remains in that account.

Proof. Every positive-frame surviving inject call has $r=1,s\le2$ by
Theorem 15.2; this remains true for its valid represented cylinders.
Its old settings loop is therefore absent. Every retained preliminary
occurrence and new arithmetic site is bounded by $2N+2$ visits,
with the falling loop separately charged through its callee costs.
This multiplier also covers the degree-rejected nine-sample call.
Apply the same acyclic two-coordinate induction as Theorem 15.4.
The new falling operands have smaller widths than that proof's
scalar bound, so none of its record or scalar estimates is weakened.
The source constants, sixteen-entry partial countlabels tables and
all preliminary rejected partitions remain charged. Then apply the
same extraction and common-cut arguments, with 361 resets and the
new image populations. $\square$

The null-nine frame already degree-prunes, so it has no map enumeration
saving. Counting unreachable new sites can enlarge its sufficient
certificate. For the positive rows the removed executed loops are
real, but the displayed reserve and execution certificates are only
sufficient demands. Their change is not a measurement of minimum
storage, host time, a complete-session speedup or physical feasibility.
In particular changing this consumer does not instantiate the
allocator/compiler/runtime prices, retained B manifestation and
same-scope offers still absent from (IS.41)–(IS.42).

## 追加锚（本行以下为增补区）

## 22. Source-derived whole-message substitutions and their limits

The source-only recurrence of Proposition 21.1 gives the following
sufficient quantities for the changed complete production image.
These are prospective source calculations, with zero complete
production installations or evaluator executions.

| Frame | $S'_x$ | $A'_x$ | $K'$ | $500K'$ bytes |
| --- | ---: | ---: | ---: | ---: |
| positive-full | 197318401152964 | 54686262652896 | 54686262672001 | 27343131336000500 |
| positive-partial | 3589096854758896 | 995388032623900 | 995388032642555 | 497694016321277500 |
| null-nine-distinct-left | 2704019037395564 | 750329641444152 | 750329641519983 | 375164820759991500 |

| Frame | installation upper bound | execution upper bound |
| --- | ---: | ---: |
| positive-full | 12249722902040504 | 25256760257769984 |
| positive-partial | 222966919375444600 | 459404402237230848 |
| null-nine-distinct-left | 168073839763988472 | 346114453368816448 |

For the common-cut native object/reference/bit union including the
original source, connection and retained $u_B=128$ B owner, with the
single shared-wire subtraction, the resulting populations are:

| Frame | objects | reference slots | bit fields |
| --- | ---: | ---: | ---: |
| positive-full | 164058790003864 | 710921422969555 | 874980231144452 |
| positive-partial | 2986164099915399 | 12940044432586628 | 15926208550673191 |
| null-nine-distinct-left | 2250988926601060 | 9754285348048746 | 12005274292764439 |

These counts exclude the separately listed runtime wrapper/container
requests exactly as §17 does; they are not a complete host-memory
price. The $u_B=128$ instance is the inherited retained owner for
this comparison, not a reserve for every finite B prefix. The actual
owner manifest, physical sharing and runtime prices still require
same-cut evidence before a full run.

The positive rows have smaller sufficient reserve and transition
coordinates than §18's original image. The largest displayed reserve
and execution demand is still positive-partial. Thus the limiting
message and reserve/execution coordinates have not disappeared; their
sufficient values changed. The null-nine sufficient values increase
because the syntactic certificate charges added sites that its degree
return never executes. It obtains no enumeration saving. None of
these comparisons establishes a strict reduction of actual complete
host work, full resource feasibility or an available offer. All the
unpriced coordinates in (IS.41) remain, as do (IS.42)'s offers and
ABI obligations. A smaller sufficient $K$ alone does not settle this
consumer's worth criterion.

## 23. Finite native evidence and the unresolved star return

The reusable private experiment program is
`rro-lab-execution/native-prerequisite/guarded_star_component.py`;
`guarded-star-component-results.json` binds its source and data bytes.
Its production-image construction is source-only. Its executing driver
is a separate component: first read the actual original frame's prior
and acquired cache, derive its partitions by the existing side/blocks
routines, then call the unchanged-signature guarded inject. Further
public component arguments exercise both orientations, repeated
incidences, degree endpoints, overdegree, native conjunction conflict
and a nonstar conjunction. Expected counts are read only by the
checking observer after a returned word; they never supply a runtime
word or a Read reply.

The component compiles only the routine closure it uses. It retains
exactly the production inject prefix through `inject.general`; that
cut has a rejecting terminal in the component and the full original
enumerator in production. A reached component cut would therefore
be a stopped fallback-entry prefix, not completed fallback execution.
No such cut was reached in the bounded result below.

The component's distinct field fingerprint is
`bd9abc7d8c0ffd455537a875c25af8b20beb848d4663adb79892535329f6969b`.
It has 4824 stack states, 36683 field nodes, 133198 native code
vertices, 406 reference registers and 57 bit registers. Its single
actual installed owner used a supplied 140000-cell reserve. All
273662 source blocks and their installed relocations were verified.
Its actual retained native census was 919559 objects, 3653637
reference slots and 10002845 bit fields at reference width 20,
including source shadows, descriptors, the initializer and shared
wire banks. These are component populations, not (IS.44)'s complete
production-image populations.

The one bounded batch returned exit 1 with these executed readings:

| Reading | Result |
| --- | ---: |
| actual installation transitions | 23887951 |
| actual subsequent native transitions | 10386962 |
| aggregate native transitions, including installation | 34274913 |
| original source calls / fresh acquisition receipt occurrences | 74 / 74 |
| native transitions before the component request | 1187381 |
| initialized reserve cells consumed at termination | 140000 |
| completed native star returns | 0 |
| reached general-entry prefixes | 0 |
| measured batch seconds | 67.18984474998433 |
| self peak resident bytes | 312410112 |
| compiler-child peak resident bytes | 43417600 |
| conservative sum of the two resident peaks | 355827712 |

The acquired cache matched the original positive-full frame with
SHA-256 `37dfee71eda5a8fbee3d373aab446982f15976785ef965ec2e4a1b6ea98c5402`.
Its 74 authentic receipt occurrence identities were distinct. The
source preparer, original provider, frontend, actual acquired-cache
framing, compiler and input delivery were executed and retained;
they were not numerical evidence oracles. Their work remains distinct
from native transitions: the provider/source hosted operations and
compiler/runtime costs are not priced by that transition count.
The source census was 10064 objects, 11727 reference slots and
9393 bit fields; the connection census was 4724 objects, 4882
reference slots and 4574 bit fields. No mutable B instance was
installed for this isolated component batch; its whole-session term
in §§20–22 remains prospective and separately required.

The batch terminated with a native fault, exhausted supplied pool and
no completed case. It did not retain the terminal fault label or exact
pending arithmetic location, so that location is unverified. Its 12
planned cases remain uncompleted: acquired $r=s=1$ on each source,
repeated-incidence $r=1,s=2$ and $r=2,s=1$ on each source,
$s=27,28$ at $r=1$, $r=8,9$ at $s=1$, a conjunction conflict,
and the nonstar-conjunction prefix. Receipt preservation after this
failed component, computed End/Ack/Return, post-evaluation old-slot
Read and Close were not checked. No full original evaluator or
chronology ran. The allowance was not renewed and no reserve was
expanded.

Consequently the required actually computed native star return and
strict native work-removal comparison remain unresolved. The new
ordinary source/guard/arithmetic and all-cut construction in §19 is
conditional; the finite batch does not certify its completed consumer.
The next necessary evidence is a genuinely backed acquisition-to-star
return prefix with all new guard/arithmetic costs charged, followed
by the remaining planned cases and complete-session cost comparison
under a separately authorized allowance. The failed fixed reserve
does not prove that another faithful execution is impossible.

The supplied star count identities and original degree/source
identities are reused from [UJB15–17](RECURSIVE_RELATIONAL_OBSERVATION_UNIFIED_JOINT_LAW_BRIDGE.md)
and the original supplier sources. The arithmetic and lowering
contracts are those of [ML](RECURSIVE_RELATIONAL_OBSERVATION_MONOTONE_LAB_INDEXED_EXECUTION.md)
and §§1–2; persistence and amortized-counting context remains the
existing [Tarjan note](../../../Library/Computability/tarjan1985amortized.md).
The existing NWMG literature correspondence keeps its original
scope. The contribution here is the concrete changed consumer,
ordinary native correspondence and changed-image accounting, with
its explicit failed execution boundary. It is repo-derived ordinary
mathematics and implementation, without a fresh Lean verification,
world-originality claim, independent acceptance or completion of any
of the six original outcomes. The continuing research goal remains
unchanged and active.

## 追加锚（本行以下为增补区）
