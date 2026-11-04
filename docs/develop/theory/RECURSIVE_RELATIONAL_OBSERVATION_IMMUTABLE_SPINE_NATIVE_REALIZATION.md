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
