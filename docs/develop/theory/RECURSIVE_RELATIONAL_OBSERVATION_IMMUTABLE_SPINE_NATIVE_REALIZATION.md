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
