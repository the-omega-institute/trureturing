# Native adaptive selection, exact source fibers and acquired stamp recovery

This volume treats the possible common sources and histories of a fully
specified returned boundary of an internal observer. The observer may choose
cuts, addresses and comparisons from acquired data, retry, perform unbounded
finite computation, and forget intermediate descriptions. The selection
rule remains part of the interpretation of its output.

These are ordinary mathematical arguments, not Lean kernel verification.
New deductions are `repo-derived`. Source and literature boundaries are
stated in Sections 2 and 10.

## 1. One source, one program and three different fibers

**Definition 1.1 (native domain and distinguished origin).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle x,y\rangle=\langle\rho x,\rho y\rangle.
\tag{NASF.1}
$$

These are all nonempty finite ordered full trees. Fix an invocation event
$\iota$ and write $u=U_\iota$. Invocation is before the first observer
transition and has no protection against subsequent writer updates. One
independent writer can apply $\rho$ to this same register and root before
any observer event, including its first event, local computation steps,
validation Reads and the separate Return. No other source change is legal.
The observer itself does not issue updates in the contract below.

A Read takes a fully materialized finite word $p$ over $L,R$ and returns
$r_U(p)\in\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$. It does
not return a subtree, source identity, size, epoch, equality or snapshot.
There is no reset, rational or infinite tree, source-specific advice,
clock port, scheduler observation or hidden source telemetry. There is
no common source-size bound.

**Definition 1.2 (effective observer and complete handoff).** Fix finite
public parameters $a$ and one deterministic effective finite program $P$.
Its initial accessible configuration $c_a$ is independent of $u$. Use a
finite-string machine implementation: its next microstep is effectively
computable from its accessible configuration, and is a local transition,
a Read with four continuations, or Return. Address construction, allocation,
comparison, arithmetic and cleanup expand into local microsteps. An
unbounded local calculation is an unbounded sequence of such steps, not
a total oracle for the next external action. Configurations have finite
encodings, with no uniform length bound. Capture roles are fixed by the
code or effectively checked finite-history annotations, not selected by
a source oracle.

At Return, $b$ denotes the entire accessible state, canonically encoded:
rows, cuts, addresses, relation signs, references, stamps, code and control,
all readable counters, lengths, capacities and allocation distinctions,
outputs, transcripts, archives and permissions. Fixed public components
need not be transmitted anew, but are fixed when comparing executions.
An accessible archive or source-dependent timing field belongs to $b$.
A complete access cut can revoke old descriptions; it cannot revoke the
public rule by which $P$ selected $b$.

Our cleaned constructions use the finite-sequence storage contract of
[CWS, Definition 2.1][CWS] and [CAB, Definition 1.3][CAB]: fixed output-region
identities, canonical extents determined by output bytes, paid clearing
and retraction of nonoutput regions, and reset control and heads. There
is no retained failure counter or earlier publication. This is an access
contract, not a physical-erasure theorem for an arbitrary allocator.

**Definition 1.3 (histories and correctness).** A finite active raw history
$h$ starts at $\iota$, retains every observer microstep and Read/reply,
every writer update, all designated capture events, cleanup and Return.
The source at an observer event $s$ is

$$
U_s=\rho^{e_s}u,
\tag{NASF.2}
$$

where $e_s$ counts all preceding updates after invocation. These counts
are mathematical annotations, not observer inputs. Idle waiting, physical
durations and unobservable writer bookkeeping are outside this active
word; histories that retain them have the corresponding projection onto
this word. Every finite prefix contains finitely many events.

Record soundness means that every record on every returning legal history
is true at its designated actual capture/validation event. Universal
finite-interference liveness means: for every $u$ and every schedule with
finitely many writer updates during the pending call, if every pending
observer microstep eventually executes, the call returns. The number and
placement of updates are unknown. There is no requirement to return under
infinite interference, and no source-independent runtime bound is assumed.

For fixed $P,a,b$ define

$$
\begin{aligned}
\mathcal H_{P,b}&=\{(u,h):h\text{ is a legal finite execution of }P
                         \text{ returning the entire }b\},\\
\mathcal J_{P,b}&=\{(u,\mathbf e):\exists h\ (u,h)\in\mathcal H_{P,b},
                 \ \mathbf e\text{ lists its designated event counts}\},\\
\mathcal S_{P,b}&=\{u:\exists h\ (u,h)\in\mathcal H_{P,b}\}.
\end{aligned}
\tag{NASF.3}
$$

For variable numbers of captures use the disjoint union of finite tuples,
including their event roles and order. Return has its own count whenever
included. These are raw-history, source/epoch and source fibers. They are
existential possible-execution notions. Membership does not say that every
scheduler produces $b$, or that a witnessing schedule is the actual past.

**Definition 1.4 (record semantics without selection).** For a finite
prefix-free cut $Q$, the complete row $R_Q(t)$ retains the literal exterior,
every reached hole with its full address, blockers for absent cut words,
and the complete equality/disequality partition of the hidden subtrees.
The empty cut retains $t$; the root cut retains one constant hole and a
singleton partition. A signed comparison requires both addressed operands
to have been reached and actually acquired at their indicated events.
An absent operand has a distinct invalid outcome, never a negative sign.

Let $\mathcal D_b$ be the set of common-source/event tuples satisfying
all displayed row, literal, signed-relation and explicit stamp predicates
in $b$, with chronology. It uses one $u$ throughout. It includes explicit
supplemental meanings but does not silently insert $P$'s discarded branch
tests. Soundness gives the appropriate projection of
$\mathcal J_{P,b}\subseteq\mathcal D_b$. Equality requires a converse:
every candidate in $\mathcal D_b$ must lift to $P$ with exactly the whole
state $b$. Constancy among histories already known to return $b$ does
not prove this converse.

## 2. Exact supplied interfaces and the remaining question

**Citation 2.1 (acquisition and records).** [ARH, Assumption 1.3][ARH]
requires the exact source fiber as a premise, explicitly including
source-dependent choices and all accessible state. Its Proposition 2.1
constructs both directions for public finite coordinate lists and a fixed
serial epoch schedule. It does not discharge that premise for arbitrary
adaptive concurrent programs. Its guarded endpoints can be any actually
reached addressed subtrees. [NCE, Definition 1.2][NCE] instead requires
signed endpoints to be reached holes of the supplied complete rows.

[CNA, Theorems 2.2, 3.3, 4.2 and 5.2][CNA] supplies genuine concurrent whole-tree
capture, equal-leaf validation, safety on returning histories and termination
under unknown finite interference. [CWS, Definition 2.4 and Theorems
3.3–4.4][CWS] supplies complete-row acquisition RA using rereading workspace.
[CAB, Theorem 2.2][CAB] supplies RA$\ell$ and an authentic stamp at its
final validation Read $v$:

$$
\ell(\alpha)=0,\quad\ell(\beta)=1,\quad
\ell(\langle x,y\rangle)=1+\ell(x),\qquad
\ell(\rho^j t)=\ell(t)+j.
\tag{NASF.4}
$$

Thus it can return $(R_Q(U_v),\ell(U_v))$ with no extra Read beyond the
same RA capture. In particular $Q=\varnothing$ provides a paid entire
description of $U_v$. These descriptions are acquired finite data, not
cloned source registers. [AAR, Definitions 1.3–1.4 and Proposition 2.3][AAR]
keeps the acquired reference, calibration and complete-state obligations.
None of these suppliers identifies an unprotected invocation source just
by rebasing coordinates at the first validation.

When composing captures below, inline their finite programs as private
subroutines of one invocation. Replace each subroutine success exit by
the caller continuation, transferring its acquired output into the
caller's paid finite region. Other caller regions stay inaccessible to
the capture routine and unchanged by its cleanup. Only the outer program
performs the final external Return. Thus two captures do not presume
reentry after an absorbing halt, and no intermediate private output is
an unaccounted public archive. The all-source safety and liveness proofs
apply to each suffix from its actual finite starting register; unknown
writer updates remain legal between every expanded local step.

**Citation 2.2 (abstract control and effective implementations).** The
following are reused with their exact restrictions; private proofs and
corresponding Scribes preserve the indicated boundaries.

| Supplier | Exact reusable content and limit |
| --- | --- |
| [Process Geometry, Definition 19.6 and Theorems 19.7–19.8, 20.2][PG] | Common reachable records, control, actual report updates and complete selected responses govern adaptive continuation. Theorem 20.2 gives abstract full-behavior repair without finiteness; finite stabilization in 19.8 needs its stated finite carrier or uniform external-record contract. Neither supplies an effective native acquisition inverse. |
| [ControlledBehaviorUniversality][CBU], `controlled_behavior_universal_property`; private `run_word_intertwines`; [Scribe][CBU-S] | Finite controlled realizations factor through complete behavior, with transition and readout equations. This is a quotient/minimality supplier, not an effective acquisition inverse. |
| [ActualCompletionAcquisitionCut][ACA], `acquisition_provenance_contract`; private `verify_acquisition_cut`, `route_acquisition_cut`; [Scribe][ACA-S] | On actual prefixes, the complete route and selected first mismatch precede acquisition on the same stationary source; the ordered cache persists. An acquisition-local phase name does not erase the earlier route. The installed native clause also retains `Allowed N U`. |
| [NativeSerialMachine][NSM], `operational_replay`, `replay_deterministic`; [Scribe][NSM-S] | A supplied actual serial `Run` gives finite replay with control and chronological local/update/read events, not independent-writer inverse existence. |
| [NativeSerialEffective][NSE], `original_service_simulation`, `original_code_service_simulation`, `effective_service_inclusion`; [Scribe][NSE-S] | Partial-recursive selectors have the stated serial simulation. Certified controller-owned epochs are not hidden independent-writer counts. Our effective outputs are finite encodings, not arbitrary noneffective semantic output maps. |
| [NativeEffectiveSourceProducer][NEP], `effective_source_producer`; private `original_stationary`; [Scribe][NEP-S] | One source-independent numeric selector acquires a stationary epoch-zero source. Its proof-side `sourceDecoder` is not a runtime source port. |
| [NativeSourceSelectorCode][NSC], `tick_code_correct`, `workspace_code_correct_of_tick`, `selector_code_correct`; [Scribe][NSC-S] | Closed code and exact partial-value correspondence implement that numeric selector. Neither the code nor its private first-return proof adds independent-writer acquisition. |
| [IntrinsicSubstitutionCoordinates][ISC], `no_alpha`, `pair_image`, `intrinsic_coordinates`; private `substitution_injective`, `primitive_index`, `normal_root`; [Scribe][ISC-S] | Finite actual trees have unique primitive-ray coordinates. These are source-coordinate results, not freely supplied source identities or clocks. |

[NCE, Definition 4.1, Theorem 4.2 and Corollary 4.3][NCE] supplies decision
and finite witnesses for finite Boolean combinations of native constructor
equations with shared existential tree variables and nonnegative affine
$\rho$ powers. Its parameters are natural numbers; there is no free unknown
tree parameter, variable address or arbitrary program predicate. Witness
replacement preserves affine parameter values but can replace the source.
Section 3 keeps every source in its correspondence; NCE is used only after
an admissible existential or ground substitution when decision is claimed.

The remaining interface is a two-sided effective description for arbitrary
adaptive programs, together with its representation and recovery limits.
An abstract inverse image, another traversal or another clock recurrence
would not supply it.

## 3. Effective native constraints for every finite execution

**Definition 3.1 (observer skeleton).** A skeleton $\tau$ is a finite
source-blind execution of the microstep program from $c_a$ to Return.
At each Read supply one of the four possible replies; compute the address
and every subsequent local state by the actual program. Keep all local
steps, retry decisions, descriptions, selected cuts, validations, cleanup
and the final accessible encoding. Enumerate finite skeletons by
breadth-first exploration of microsteps, branching four ways only at a
Read. Retain in $\mathcal L_{P,b}$ exactly those terminal skeletons whose
whole accessible state is $b$.

The enumeration is effective even if hypothetical reply paths compute
forever: it never waits for an unbounded source-free segment to finish
before advancing other finite prefixes. This is not a finite decision-tree
restriction. Addresses are concrete finite words on each skeleton, with
no common length or number bound across skeletons.

For $s$ observer events in $\tau$, including Return, introduce
$0\le e_1\le\cdots\le e_s$ and $e_0=0$. Insert $e_i-e_{i-1}$
writer updates immediately before observer event $i$. Write
$\operatorname{expand}(u,\tau,\mathbf e)$ for the resulting active
word with register states determined by (NASF.2). This insertion is a
replay schedule to be proved legal, not a claim about the actual schedule.

**Lemma 3.2 (literal navigation as finite native constraints).** Given a
concrete word $p$, a tree expression $V$, and a reply $c$, the condition
$r_V(p)=c$ has an effective finite existential-tree formula using only
native constructors and equality. So does the condition that $p$ is
reached with whole subtree $X$.

Proof. Construct a path context $D_p(Z;\mathbf y)$ by putting $Z$ at
$p$, a fresh sibling variable at every ancestor, and the required ordered
pairs along the path. For the empty word it is $Z$. Then

$$
\begin{aligned}
V|_p=X\text{ and }p\in\operatorname{Pos}(V)
 &\Longleftrightarrow\exists\mathbf y\ V=D_p(X;\mathbf y),\\
r_V(p)=\alpha
 &\Longleftrightarrow\exists\mathbf y\ V=D_p(\alpha;\mathbf y),\\
r_V(p)=\beta
 &\Longleftrightarrow\exists\mathbf y\ V=D_p(\beta;\mathbf y),\\
r_V(p)=\mathsf{branch}
 &\Longleftrightarrow\exists\mathbf y,x,z\
                      V=D_p(\langle x,z\rangle;\mathbf y).
\end{aligned}
\tag{NASF.5}
$$

The inverse reads the actual sibling subtrees along that path. For absence,
take the finite disjunction over strict prefixes $q$ of $p$ and both
leaf labels $\lambda$ of $V=D_q(\lambda;\mathbf y)$. A missing address
in a full tree encounters a first leaf at such a prefix; a leaf there
blocks the remaining nonempty suffix. For $p=\varepsilon$ this disjunction
is false. The witnesses reconstruct exactly $V$, preserving the same
tree in both directions. $\square$

**Definition 3.3 (skeleton constraint).** For each Read at event $i$ of
$\tau$ with literal $p_i$ and reply $c_i$, use Lemma 3.2 with
$V=\rho^{e_i}u$. Conjoin these conditions and chronology to obtain
$C_\tau(u,\mathbf e)$. All auxiliary tree variables are existential.
The distinguished $u$ is the same tree in every occurrence.

Optionally attach a delivered complete row at event $i$ using
$\rho^{e_i}u=C[(x_{[p]})_p]$ and all cross-class disequalities. Attach a
comparison between arbitrary reached addresses using two path contexts
and the stated equality or disequality of their endpoint variables.
An absent endpoint is never made unequal by assigning a default tree.
For record-sound $P$, these additional predicates are consequences on
returning skeletons, so do not change their fibers. Their truth must
still follow from the acquisition proof; the compiler does not certify
a dishonest producer by adding its claims.

**Theorem 3.4 (exact adaptive execution and native-constraint correspondence).**
For every effective $P$ of Definition 1.2, without a liveness assumption,
every $u$, every $\tau\in\mathcal L_{P,b}$ and every chronological
$\mathbf e$,

$$
C_\tau(u,\mathbf e)
\quad\Longleftrightarrow\quad
\operatorname{expand}(u,\tau,\mathbf e)
\text{ is a legal execution returning the entire }b.
\tag{NASF.6}
$$

Every $(u,h)\in\mathcal H_{P,b}$ arises this way. Therefore

$$
\mathcal S_{P,b}
 =\bigcup_{\tau\in\mathcal L_{P,b}}
   \{u:\exists\mathbf e\ C_\tau(u,\mathbf e)\},
\tag{NASF.7}
$$

and retaining the designated coordinates of $\mathbf e$ gives exactly
$\mathcal J_{P,b}$. Retaining the expanded word gives the full active
raw-history relation. This is an effective countable family of finite
native constraints with unknown unbounded epochs, not a finite formula.

Proof. Erase writer updates from a legal returning history. The observer
starts in $c_a$. Each local transition is the public program's transition,
and each Read has one of the four supplied replies, so the erased word
is enumerated. Every actual local state is preserved, including retained
allocation or output distinctions; its terminal state is exactly $b$.
The actual counts are chronological. Equation (NASF.2) gives each Read
condition; Lemma 3.2 supplies subtrees of these same actual iterates as
witnesses. Thus $C_\tau$ holds without replacing $u$.

Conversely fix a satisfying $u,\mathbf e$. Start the one register at
$u$ and the observer at $c_a$. Before event $i$ execute the indicated
finite burst. Induct on $i$. Its register is $\rho^{e_i}u$ and observer
state agrees with the skeleton because all earlier replies and local
steps agree. At a Read, its materialized address is exactly $p_i$, even
if computed by arbitrary earlier adaptive code. Lemma 3.2 and $C_\tau$
give the actual reply $c_i$. A local step changes only observer state.
The same induction covers failed validations, retries, selected operands,
successful validations and cleanup. At Return it gives the entire $b$,
not just its rows. All bursts and steps are finite, so this is a legal
finite history, extendible with a halted writer.

Erasure and insertion recover the original active word, including update
placement relative to every local step and Return. A richer history with
idle waiting or writer housekeeping projects to this word; this theorem
does not recover those actual additional values. Projecting now proves
(NASF.7) and the assertion about $\mathcal J_{P,b}$. $\square$

**Corollary 3.5 (effective scope of an individual branch).** For a fixed
$\tau$ and supplied concrete finite candidate $u_*$, the existence of
$\mathbf e$ satisfying $C_\tau(u_*,\mathbf e)$ is decidable using NCE;
its epoch support has the supplied finite affine description. The same
holds if the source is existentially quantified. Neither assertion
parametrizes every source by NCE's selected witness templates.

Proof. Substitute the finite constructor term $u_*$ everywhere, or
quantify the one shared $u$. Path contexts contain finite constructors
and shared existential tree variables; each exponent is a natural
coordinate $e_i$. Chronology is affine and absence is a finite disjunction.
The result is literally [NCE, Definition 4.1][NCE], so Theorem 4.2 and
Corollary 4.3 apply. A substituted $u_*$ is a ground term, not a free
unknown tree parameter, and cannot change under witness replacement.
Unbounded skeleton enumeration remains outside that finite grammar.
$\square$

**Corollary 3.6 (enumeration is not authentication).** $\mathcal H_{P,b}$
and $\mathcal S_{P,b}$ are computably enumerable. A source/epoch tuple
with finitely specified designated roles is also semidecidable by
finite-witness enumeration. Alternatively simulate all finite active
words on enumerated finite sources and check the whole boundary.
Enumeration supplies no negative membership decision. A witness gives
an alternative possible execution, not authentication that a handed-in
record was acquired. Every branch uses the same public program.

## 4. Native selection survives complete cleanup

**Proposition 4.1 (a selected root row identifies the invocation source).**
There is an all-source record-sound producer with universal
finite-interference liveness whose completely cleaned root-row output
has source support exactly $\{\alpha\}$, although that row alone admits
every finite source.

Proof. First Read $\varepsilon$. If the reply is alpha choose
$Q=\{\varepsilon\}$; otherwise choose $Q=\{L,R\}$. Execute the supplied
RA capture on that selected cut. Retain only the selected cut and its
complete row, with common ready control and permissions; perform the
complete cleanup. The initial reply, branch latch, guard and attempt
state are inaccessible. Once the actual reply selects its finite cut,
RA's all-cut proof applies from the current register. Thus safety and
liveness hold under arbitrary legal interleavings.

Let $b$ be the root cut and its constant row. Reaching this cut requires
that the first Read saw alpha. By `no_alpha` in [ISC], no positive iterate
has root alpha; a tree with that root is alpha itself. Hence $u=\alpha$
and there were zero updates before this first Read. Conversely a
quiescent invocation on alpha returns $b$. More generally, insert any
$j\ge0$ updates after the first Read and before a quiescent RA capture.
Its validation source is $T_j=\rho^j\alpha$, with the same whole $b$.

The concrete quiescent pair is: alpha gives first reply alpha and returns
the root row; beta gives first reply beta and returns the two-address cut
with literal exterior beta and both blocking guards. Beta satisfies the
proposed root-row semantics at every epoch but cannot return $b$ under
this program at any schedule. The cut already reveals the selected
branch. A redundant saved branch transcript is unnecessary. $\square$

The first-validation rebase $t=U_v$ gives only
$t\in\{T_j:j\ge0\}$, not arbitrary $t\in\mathcal T$. The first Read
preceded that validation. Relabelling $v$ as relative epoch zero cannot
remove its restriction. This does not strengthen CAB's origin claim:
the information comes from this program's earlier Read and selected output.

**Proposition 4.2 (selection recovers a lag that the same signs do not).**
A universally live producer can return a completely cleaned pair of root
rows and a negative root comparison that determines capture lag exactly
one, although those record predicates alone admit every positive lag.

Proof. Perform two consecutive RA$\ell$ captures with empty cuts,
retaining paid full descriptions $t_0,t_1$ and stamps $k_0,k_1$ until
both validations $v_0,v_1$. If $k_1-k_0=1$, select root cuts for both
final rows. Otherwise select a root cut for the first and an empty cut
for the second. In either case compute the actual signed comparison of
the reached roots from their paid descriptions. These are ARH-legal
endpoints; on the designated branch they are also NCE holes. Return
only the selected cuts, rows, sign and canonical common state, revoking
descriptions, stamps and intermediate controls. For the alternative
empty second cut its literal whole tree remains part of that output.

Let $b$ be two root rows with negative sign. CAB gives
$k_1-k_0=e_{v_1}-e_{v_0}$ on every returning history, so $b$ forces lag
one. Positive lag makes roots different because $\ell$ strictly advances.
Every source admits this branch: keep the first capture quiescent, apply
one update before the second, then keep it quiescent. The two captures
and finite subsequent computations terminate under every progressing
finite-interference schedule.

For a finite paired-history falsifier use invocation alpha. Quiescent
first capture gives $t_0=\alpha$. One intervening update gives
$t_1=\beta$ and output $b$; two give
$t_1=\langle\beta,\alpha\rangle$ and the alternative empty second cut.
The candidate $(\alpha,0,2)$ satisfies both root rows and the negative
comparison, but no execution with those counts returns $b$. Every
positive lag satisfies the record predicates on alpha. Thus truthful
records alone do not establish the converse. The cut pattern and known
selection rule already retain the exact-lag restriction. $\square$

For explicit raw Read witnesses in Proposition 4.2, suppress only the
finite local steps needed to construct operands and descriptions. The
first empty-cut capture on alpha has Read list
$(\varepsilon,\alpha),(\varepsilon,\alpha),(\varepsilon,\alpha)$:
guard, exterior body, validation. With one intervening update, the second
list is the same three root Reads with beta replies. With two updates,
the second list is

$$
(\varepsilon,\mathsf{branch}),\ (L,\beta),(\varepsilon,\mathsf{branch}),\ (L,\beta),\ (R,\alpha),\ (L,\beta).
$$

The first two Reads find the guard; the next three acquire the literal
empty-cut exterior; the last validates. The left stamp is respectively
one or two. Actual comparison of the two acquired descriptions, cut
selection, clearing and the separate Return finish each history. Their
full microstep expansions are legal with the writer halted outside the
indicated burst. Thus this pair uses six versus nine total Reads, with
all literal operands explicitly materialized; these are hand-derived
finite witnesses, not an empirical batch.

These are actual finite native histories, with no disconnected advice
worlds. Short signs do not pay for the comparisons. Erased data were
acquired, used and cleaned before handoff.

## 5. Exact expressive power of cleaned possible-source outputs

**Definition 5.1 (backward closure under advancement).** A set
$A\subseteq\mathcal T$ is backward closed if

$$
\forall u\in\mathcal T\ \forall j\ge0,\qquad
\rho^j u\in A\ \Longrightarrow\ u\in A.
\tag{NASF.8}
$$

Computable enumerability uses a fixed effective finite-tree syntax.
This is closure toward earlier sources, not forward orbit invariance.
Programs and public parameters are fixed independently of the source.

**Theorem 5.2 (classification with universal finite-interference liveness).**
As $P$ and a designated finite cleaned boundary $b$ vary, the possible
source sets $\mathcal S_{P,b}$ are exactly the computably enumerable
backward-closed subsets of $\mathcal T$, even when producers must be
record-sound on every returning history and terminate on every source
under every progressing finite-interference schedule. If $b$ must be
actually attained, they are exactly the nonempty such subsets.

Proof of necessity. Corollary 3.6 supplies computable enumerability.
If an execution from $\rho^j u$ returns $b$, start instead at $u$, insert
$j$ writer updates before the first observer event, then execute the same
subsequent interleaving. The observer still has $c_a$ and the register is
now precisely the earlier run's invocation tree. Induction preserves
every Read, local state, permission and final byte of $b$. This is a
finite legal schedule, proving (NASF.8). It uses unprotected entry and
source-independent initialization, not liveness. Attainment gives a
source witness.

Proof of sufficiency. Fix an effective enumerator of $A$. Let $E(q)$
be the finite list of completed tree encodings emitted in its first $q$
machine steps. This is a total finite simulation; an unfinished encoding
is not an emitted tree. No decision procedure for $A$ is assumed.
Construct this one finite observer:

1. Use RA$\ell$ with empty cut to acquire a full description $t=U_v$.
   Keep $t$ across the next capture.
2. Use RA$\ell$ with root cut to acquire its row and $k=\ell(U_w)$
   at a later validation $w$.
3. Simulate the enumerator for exactly $k$ steps. Select tag `yes` iff
   $t$ equals a tree in $E(k)$; otherwise select `no`. Accompany either
   tag by the acquired root row of $U_w$.
4. Retain only the tag, root cut, constant row and canonical common
   state. Clear and retract $t$, $k$, enumerator tape, guards, counters,
   reply latches and all remaining nonoutput regions before Return.

Only paid native Reads in the supplied captures and effective computation
on acquired finite data are used. This program never waits for a writer
update or an enumeration success. Under every progressing finite-interference
schedule both captures terminate, $k$ is finite, finite simulation and
comparison finish, and cleanup finishes. Every returned row is true at $w$.

Let $b$ be the fixed `yes` boundary. If returned, $t\in A$ and
$t=\rho^{e_v}u$, so backward closure gives $u\in A$. Conversely, if
$u\in A$, choose an enumeration stage $q$ that emits it. Keep the first
capture quiescent from invocation, so $t=u$. Insert $j$ updates between
captures with $\ell(u)+j\ge q$, then keep the second capture quiescent.
Its authentic stamp is $k=\ell(u)+j$, so simulation sees $u$ and returns
exactly $b$. The writer can halt thereafter. This proves both inclusions
without source-size advice, a schedule bound, source-specific installation
or a free clock. If $A$ is empty, `yes` is unattained; otherwise any member
gives an actual finite witness. $\square$

The existence direction chooses one enabling schedule. It does not say
all schedules return `yes` on members of $A$: a short quiescent second
capture can give too small a budget and return `no`. All these schedules
still terminate, and all returned rows are sound. Universal liveness and
existential possible-output support are distinct quantifiers.

## 6. One fixed total producer with undecidable source membership

**Definition 6.1 (primitive finite source codes).** Put

$$
D_0=\alpha,\qquad D_{e+1}=\langle\beta,D_e\rangle,
\qquad E_e=\langle\alpha,D_e\rangle.
\tag{NASF.9}
$$

These $E_e$ are pairwise distinct, effectively constructible and recognizable
by a finite syntax scan recovering the right-comb length $e$. All satisfy
$\ell(E_e)=1$ and have $2e+3$ nodes. Each is primitive: `pair_image` in
[ISC] says a pair in the image is either $\langle\beta,\alpha\rangle$
or has both children in the image; `no_alpha` excludes its left child.
Thus the existing primitive-coordinate result gives

$$
\rho^j u=E_e\quad\Longrightarrow\quad j=0\ \land\ u=E_e.
\tag{NASF.10}
$$

This use of source coordinates supplies no new source port or live decoder.

**Theorem 6.2 (fixed live producer, exact counts and undecidable fiber).**
Fix an effective enumeration of finite machine programs containing a known
$M_0$ that halts within one step on blank input. There are one fixed
producer $P_*$ and one actually attained cleaned output $b_*$ satisfying
record soundness and universal finite-interference liveness such that

$$
\mathcal S_{P_*,b_*}
 =\{E_e:M_e\text{ halts on blank input}\}.
\tag{NASF.11}
$$

Concrete-source membership in this single fixed fiber is undecidable.
More precisely, if $a,b,r$ count updates at first validation, second
validation and Return, respectively, its accepting projection is exactly

$$
\{(E_e,0,j,r):0\le j\le r,\ M_e\text{ halts within }1+j
                                      \text{ simulated steps}\}.
\tag{NASF.12}
$$

Proof. Use the same two paid captures as Theorem 5.2. After the second,
recognize whether the first acquired tree $t$ is an $E_e$. If not, select
`no`. If it is, simulate $M_e$ for exactly the second stamp $k$ steps and
select `yes` iff it halts within that bound. Retain the tag and second
root row; perform the same complete cleanup. This is one program for
all sources, not an installed program chosen from the hidden index.
Finite captures and bounded simulation give universal liveness even
when $M_e$ never halts.

In an accepting run $t=\rho^a u=E_e$, so (NASF.10) forces $a=0$ and
$u=E_e$. At the second validation $b=j$, CAB gives
$k=\ell(E_e)+j=1+j$. Acceptance is exactly the bounded halting condition
in (NASF.12), and chronology requires $r\ge j$.

Conversely, for a tuple on the right of (NASF.12), keep the first capture
quiescent on $E_e$, insert $j$ updates before the second capture, keep it
quiescent, then insert $r-j$ updates after validation and before Return.
Source-free simulation and cleanup are unaffected by that last burst.
The program accepts with the entire $b_*$. This proves (NASF.12), including
its separate Return count. Since $1+j$ can exceed any finite halting time,
(NASF.11) follows. $E_0$ with no updates witnesses actual attainment.

A decision procedure for $u\in\mathcal S_{P_*,b_*}$ would decide blank-input
halting by constructing $E_e$ and making one membership query. For the
computability premise, Turing's Section 8, p. 248 [TURING] proves that no
machine decides whether arbitrary supplied machine code ever prints a
designated symbol. Transform that code effectively into a blank-input
machine which simulates it and halts at its first designated-symbol event.
A halting decider would decide the printing problem. The native reduction
is the paid producer and exact common-source/count equivalence (NASF.12),
not the undecidability citation by itself. $\square$

**Corollary 6.3 (no finite NCE compilation for all adaptive outputs).**
There is no general effective translation of arbitrary $P,b$ into a finite
NCE-language source-fiber representation whose concrete-source specialization
decides membership exactly. The fixed fiber of Theorem 6.2 admits no single
finite representation of that kind at all.

Proof. Suppose a finite expression schema has one designated source slot
$u$, finitely many existential tree and natural epoch variables, native
constructors, affine nonnegative powers and affine guards as in NCE, and
represents (NASF.11) exactly. The source slot is a proposed representation
interface, not a free-tree-parameter theorem already supplied by NCE.
Substitute the concrete term $E_e$ into it. This is now exactly [NCE,
Definition 4.1][NCE], with all other trees existential. Theorem 4.2 eliminates
those trees and Corollary 4.3 decides existence of the remaining natural
parameters. That would decide (NASF.11), contradicting Theorem 6.2. The
same holds for finite unions. This argument uses actual concrete-source
substitution, not a supposed source-preserving parametrization by NCE's
replaceable witnesses. $\square$

The obstruction leaves intact the countable representation of Theorem 3.4,
each individual branch decision, languages containing arbitrary program
predicates, and restricted selector families proved separately. It rules
out using the finite row/sign language as a universal finite solver for
the full adaptive domain.

## 7. Authentic terminal stamps restore candidate-source decisions

**Assumption 7.1 (terminal advancing stamp promise).** Fix an effective
$P$ with universal finite-interference liveness on every finite source.
For the returned states under consideration, the full $b$ contains a
natural $K$, authentic by the producer's correctness proof, with
$K=\ell(U_v)$ at a designated final source-observation event $v$.
All subsequent observer computation through the separate Return is a
source-free effective suffix: no further Read, source-dependent timing,
allocator telemetry, ambient source query or scheduler observation can
influence it. Compare the complete accessible boundary, including all
permissions and metadata. Authenticity and totality are promises; the
algorithm below does not decide whether arbitrary code satisfies them.
CAB's last guard Read followed by its declared encoding and cleanup is
one supplied implementation of the final-observation condition.

Earlier observations, retries and captures are unrestricted. The writer
can make arbitrarily many additional updates after $v$; the observer
neither learns nor implicitly records them. A copied numeral without
certification at this final observation is not this promise.

**Lemma 7.2 (finite exploration under a total-update cap).** Fix a concrete
finite source $u$, a natural $M$, and an effective observer satisfying the
liveness premise. There is a terminating algorithm enumerating every
finite active execution from $u$ with at most $M$ writer updates through
Return, including its entire boundary and event annotations. No runtime
bound or totality decision is supplied to the algorithm.

Proof. Explore the rooted tree of concrete configurations and a spent-update
counter. At each nonterminal node there are at most two successors:
execute the unique next observer microstep, evaluating a Read on the
current concrete tree if necessary; or perform one writer update if the
counter is below $M$. Return is an observer event ending that branch.
There is no idle-stutter successor. Every successor is effectively
computable on finite data. Keep histories separate when nodes coincide
if their annotations are requested.

If this finitely branching tree had infinitely many nodes, a node with
infinitely many descendants would have a child with infinitely many
descendants; choosing such children repeatedly gives an infinite path.
It has at most $M$ writer updates, hence eventually only observer steps.
Every pending observer transition occurs after finitely many intervening
events, so this is a progressing finite-interference execution without
Return, contradicting liveness. The tree therefore has finitely many
nodes. Breadth-first exploration empties its queue and yields the complete
finite list. This proves termination under the promise without computing
tree height in advance or deciding the promise. $\square$

**Theorem 7.3 (terminating concrete-source membership with a terminal stamp).**
Under Assumption 7.1, membership $u_*\in\mathcal S_{P,b}$ is decidable
for every supplied concrete finite source $u_*$. Compute
$M=K-\ell(u_*)$; reject if negative; otherwise perform Lemma 7.2 with
cap $M$ and accept exactly when one terminal boundary is literally the
entire $b$.

Proof of completeness. For any actual run from $u_*$ returning $b$,

$$
K=\ell(U_v)=\ell(u_*)+e_v,
\qquad e_v=M.
\tag{NASF.13}
$$

Every prevalidation event, including the first observation and all failed
attempts, has count at most $M$. Keep every observer step and every writer
update through $v$. Delete only writer updates strictly after $v$, retaining
all observer computation through Return. By the source-free suffix promise,
induction preserves its whole accessible state, including cleanup. The
Return boundary is still $b$, although its actual Return register can
differ. This normalized execution has at most $M$ total updates and is
enumerated by Lemma 7.2. No pre-first-validation condition was dropped.

Proof of soundness. Every enumerated execution is a real legal history
from $u_*$. Equality of its entire boundary to $b$ gives a witness of
membership. Authenticity further forces its final observation count to
be $M$; other returned boundaries need not have that count. Liveness
ensures that exploration terminates on negative candidates too. $\square$

**Corollary 7.4 (the cap and its limits).** For a fixed hypothetical source,
the normalized search also decides any decidable condition on the finite
pre-$v$ active history and its capture counts, by filtering the finite
list. In particular it enumerates all possible pre-$v$ lag values for
that source and boundary. It does not enumerate every actual raw history
with its unbounded post-$v$ writer tail.

The cap bounds updates through $v$, not source size, Return epoch or a
uniform computation cost. The $E_e$ all have $\ell=1$ and unbounded size.
Arbitrary updates after $v$ preserve $b$ under the suffix promise, making
the Return count unbounded. Even with a small fixed stamp and no updates,
a program can do arbitrarily long finite local work before Return.
Lemma 7.2 gives a finite tree for each fixed code, source and cap, not a
bound depending only on $K$, not a uniform bound over all candidates,
and not a test of universal liveness.

A finite candidate supplied as syntax can be simulated offline. Passing
the unknown live source to this procedure first requires paid acquisition.
The theorem supplies no free live membership port, all-source emptiness
decision or target-constancy decision. In particular $\ell(u_*)$ is
computed from the candidate, not read freely from the register.

**Proposition 7.5 (an earlier authentic stamp is insufficient).** Replacing
Assumption 7.1 by a stamp at an earlier capture does not ensure decidable
source membership, even with universal finite-interference liveness.

Proof. Modify $P_*$ to retain its first capture's stamp beside its
accepting output while still erasing the second stamp. On every accepting
run the first tree is $E_e$, with stamp one. Thus the same fixed accepting
boundary now contains an authentic $K=1$, but its source support remains
(NASF.11). The later second capture supplies unbounded budget $1+j$.
An alleged cap $K-\ell(E_e)=0$ would discard accepting runs that need
$j>0$. The stamp is authentic but is not at the last source observation.
$\square$

Instead retaining $K$ from $P_*$'s already-final CAB capture gives a
family of different boundaries. At fixed $K\ge1$, their accepting
support is exactly $\{E_e:M_e\text{ halts within }K\text{ steps}\}$
by (NASF.12), hence decidable as Theorem 7.3 predicts. Erasing $K$ takes
the unbounded union and recovers the undecidable support.

## 8. Recovery and lawful continuation on the exact fiber

**Application 8.1 (task sufficiency uses the actual relation).** Let $b$
be attained and $F(u,h)$ be a desired source/history quantity. A passive
value is determined by the known program, parameters and $b$ exactly
when $F$ is constant on $\mathcal H_{P,b}$. For tuple quantities use
$\mathcal J_{P,b}$; for source-only quantities use $\mathcal S_{P,b}$.
This is the supplied factor-through-fibers criterion of [PG], not new
quotient theory. The actual acquisition promise places the real history
in that fiber. Proposition 4.2 recovers lag one where the enlarged
record-only set would report all positive lags. Proposition 4.1 recovers
invocation alpha without a separately retained first reply.

For a computable finite-encoded target and an attained boundary,
constancy as an additional proved promise also gives effective recovery:
enumerate finite native witnesses by Corollary 3.6 until one returns
$b$, compute its target, and use constancy. The witness need not be the
actual source or schedule. This does not decide constancy, authenticate
a copied output or reconstruct arbitrary past microsteps. A singleton
source projection identifies the source under the acquisition promise;
it remains distinct from a certificate of physical provenance.

**Application 8.2 (minimal sufficient retained distinctions).** For a
specified future task family, retaining entire source descriptions is
not always necessary. The relevant equivalence compares required outputs
and, for actions, legal domains, reports, successor summaries and control
updates on actual reachable configurations. [PG, Theorems 19.7–19.8 and 20.2]
and [CBU] already supply continuation and minimality principles within
their stated carriers. Their use here requires the selection-aware fiber,
not a product of marginal row fibers.

Known code and a selected cut can already imply a discarded predicate;
Propositions 4.1–4.2 show why demanding a duplicate branch transcript
would overstate necessary retention. An unlisted readable archive instead
enlarges $b$ and changes its fiber. Complete cleanup removes access to
data; it does not make all record-compatible sources reachable by the
selection rule. Minimality is relative to the task/permission contract,
not a universal smallest bit string.

**Application 8.3 (a supplied serial service can consume an enumerable fiber).**
This is a conditional reuse of [ARH, (ARH.2.3)][ARH]. Besides attained
$b$, suppose a service is lawfully invoked on the same source at a
certified known total epoch $N$ from $\iota$, with complete common
service state determined by $P,a,b,N$. During the service the source is
stationary except for its own permitted serial pure updates. Its entire
compatible invocation-source set $U$ must be specified exactly, including
the $N$-entry restriction. If $U$ is obtained from Theorem 3.4 with an
effective finite entry contract, it is computably enumerable. Assume
$U\ne\varnothing$.

For recovery of the entire original $R_Q(u)$, the supplied criterion is

$$
\exists h\ \forall u,v\in U,\qquad
\left[\forall |p|\le h\ r_u(p)=r_v(p)\right]
       \Longrightarrow R_Q(u)=R_Q(v).
\tag{NASF.14}
$$

Given such an $h$, use the existing delayed original-prefix reader at
known epoch $N$, with at most $2(2^{h+1}-1)$ new Reads and maximum
length $h+\lceil N/2\rceil$. Enumerate source witnesses for $U$ until
one matches the recovered original replies, then output its complete
row. The actual source ensures termination; (NASF.14) ensures the answer.
If using individual membership semidecisions instead of an enumerator,
dovetail them rather than wait sequentially on a negative candidate.
Decidable membership from Theorem 7.3 helps when available but is not
necessary for this promised nonempty search.

The reverse direction from a uniform finite-read source-total serial
service to (NASF.14) is ARH's finite reply-tree and address-locality
argument on $U$. No new traversal or budget-extraction algorithm is
asserted. Acquisition may have unknown interference; certified later
entry and serial permission are additional premises. A terminal stamp
alone does not give $N$, since $\ell(u)$ is unknown and updates after
validation are unrestricted. An absorbing Return grants no new invocation
or source permission by itself.

**Application 8.4 (relative time and distinct recovery obligations).** With
two retained authentic stamps, CAB already recovers the update lag by
subtraction. Without them, selection can determine a lag, as in Proposition
4.2; otherwise constancy must be checked on the full joint relation.
Theorem 7.3 decides supplied-candidate membership and, with that candidate
fixed, finitely explores prevalidation lag alternatives. It does not
decide whether all unknown sources give the same lag. Shared source
existence, identifying a source, recovering relative update counts,
authenticating the actual past and executing a legal future service are
different obligations. None identifies physical duration or establishes
physical spacetime.

## 9. Paid resources, finite falsifiers and the remaining frontier

**Definition 9.1 (separate resource coordinates).** For actual submitted
words $p_i$, keep

$$
T=\#\text{Reads},\qquad A=\sum_i|p_i|,\qquad
Q=\max(\{0\}\cup\{|p_i|\}),
\tag{NASF.15}
$$

separate from whole-tree and subtree comparisons, address construction,
local simulation/arithmetic, workspace, acquired operand payload,
inter-capture memory, final payload, validation failures, writer work
and cleanup. Binary counters cost their bit lengths; each literal delivery
costs its length. An offline proof/search history is not a free live
observer transcript.

Theorems 5.2 and 6.2 use two real captures. The first empty-cut capture
pays for its whole tree and retains that description across the second.
Enumeration comparisons and recognizing $E_e$ use that paid description.
The root capture pays guard search and validation; its stamp is acquired,
not chosen as external fuel. A $k$-step abstract simulation requires its
finite implementation work and workspace, not one unit because $k$ has
a binary encoding. Each failed attempt and discarded candidate is charged.
Finite interference makes total cost finite on each execution without
a common all-source/schedule bound. Constant final payload refunds none
of this work or memory.

Retaining the stamp from the same final RA$\ell$ capture adds zero Reads
and address traffic by CAB; encoding, framing and local computation remain
paid. CAB's gamma code for $K+1$ has
$2\lfloor\log_2(K+1)\rfloor+1$ payload bits. If later source observations
follow that capture, acquiring a new terminal stamp is a different
operation: it adds guard/body/validation traffic, possible failures,
workspace and cleanup, and may be delayed by unknown finite interference.
The added capture must leave a genuinely source-free suffix. Timing or
allocator telemetry cannot be hidden in that phrase.

**Proposition 9.2 (decisive finite falsifiers).** These concrete finite
cases refute the indicated overclaims without an empirical batch:

- Invocation beta satisfies Proposition 4.1's displayed root row but has
  no same-program lift to that complete output.
- $(\alpha,0,2)$ satisfies Proposition 4.2's root rows and negative link
  but has no same-program lift with those capture counts.
- An absent endpoint is rejected by (NASF.5) for either signed relation;
  an invented default subtree cannot supply a negative observation.
- In an accepting run of Theorem 6.2 insert one writer update after final
  validation and before Return. The whole boundary is unchanged but
  Return source/count changes. A validation stamp is not a Return bound.

The missing conditions are selection, exact capture lag, reachedness and
the separate Return event. None disputes truthful records at validation.

**Problem 9.3 (broader mathematical residual).**

The full adaptive domain has the countable representation and precise
finite-representation obstruction above. Restricted selector classes,
including automata-based selectors, may have stronger effective descriptions;
no additional such family is proved here. NCE witness selection does not
supply source-preserving finite parametrizations of all signed fibers.
Optimal read, literal-address, workspace, inter-capture and final-retention
tradeoffs remain separate. The broader RRO objective of mutual recovery
of spatial cuts, internal time, boundary and memory remains open beyond
these interfaces; this finite author result does not complete it.

## 10. Sources, proof status and exact contribution

**References 10.1 (primary literature and matched quantifiers).**

| Primary source | Verified scope and use |
| --- | --- |
| James C. King, *Symbolic Execution and Program Testing*, CACM 19(7), 385–394, DOI [10.1145/360248.360252][KING-DOI]; [IBM primary abstract][KING] | `literature-attested` for symbolic inputs and branch-sensitive symbolic execution. Only the primary abstract is used; no inaccessible full-text theorem is a premise. Native count, same-source and whole-boundary correspondence is proved in Section 3. |
| E. W. Dijkstra, [EWD418, Section 3][EWD418], and [EWD472, Section 3][EWD472], *Guarded commands, non-determinacy and formal derivation of programs*, CACM 18(8), 453–457 | Primary transcriptions define $wp(S,R)$ by guaranteed proper termination satisfying $R$. This universal total-correctness quantifier is not existential possible-output support. They support the distinction, not an unproved equality with (NASF.3). |
| A. M. Turing, *On Computable Numbers, with an Application to the Entscheidungsproblem*, Proceedings of the London Mathematical Society, series 2, 42, 230–265, [primary paper scan][TURING], Section 8, especially p. 248 | `literature-attested` impossibility of deciding whether a supplied machine ever prints a designated symbol. The effective printing-to-halting transformation and paid native source/count reduction are given in Theorem 6.2. Circle-freeness is not equated with halting. |

Lemma 7.2 proves the finite-branching argument by the infinite-descendant
construction. No unverified fairness, finite-state model-checking,
database-provenance theorem or enlarged term-language solver is assumed.
No unread publisher text is a premise.

**References 10.2 (new versus reused content).** The new interface is the
native skeleton-constraint compilation and reverse replay preserving all
accessible state (Theorem 3.4); cleaned native selection counterexamples
(Propositions 4.1–4.2); exact computably enumerable backward-closed support
classification despite universal finite-interference liveness (Theorem 5.2);
one fixed total producer admitting an exact source/count characterization
with undecidable source projection, and the resulting finite-language
obstruction (Theorem 6.2 and Corollary 6.3);
and terminal-stamp candidate decision preserving prevalidation restrictions
while normalizing the postvalidation suffix (Theorem 7.3).
For supplied source and counts, (NASF.12) is decidable by bounded simulation;
undecidability concerns the source projection (NASF.11).

Lemma 3.2 expands finite navigation only to discharge the native grammar
correspondence. Traversal, complete-row acquisition, whole-tree comparison,
primitive coordinates, stamp advancement, finite affine existence,
generic quotient minimality and fixed-schedule service theory retain the
suppliers in Section 2. Section 8 gives applications with explicit additional
continuation premises, not new generic quotient results. The inspected
native D5/Scribe and RRO suppliers do not state the support classification,
fixed total-producer undecidability or terminal-stamp decision proved here.
This is a scoped repository comparison, not worldwide originality evidence.
No `suspected-novel` claim is made.

**References 10.3 (proof status and scope).** New results have ordinary
written proofs, not Lean kernel verification. Conditional algorithms retain
their correctness and liveness promises; the broad research residual is
stated in Problem 9.3.

[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[CNA]: RECURSIVE_RELATIONAL_OBSERVATION_CONCURRENT_NATIVE_CUT_ACQUISITION.md
[CWS]: RECURSIVE_RELATIONAL_OBSERVATION_CONCURRENT_NATIVE_CUT_WORKSPACE.md
[CAB]: RECURSIVE_RELATIONAL_OBSERVATION_CONCURRENT_ACQUIRED_CLOCK_BRIDGES.md
[AAR]: RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md
[NCE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CROSS_EPOCH_RELATIONS.md
[PG]: RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md
[CBU]: ../../../D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean
[CBU-S]: ../../../Blueprint/D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.scribe.cs
[ACA]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionAcquisitionCut.lean
[ACA-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/ActualCompletionAcquisitionCut.scribe.cs
[NSM]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.lean
[NSM-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.scribe.cs
[NSE]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.lean
[NSE-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialEffective.scribe.cs
[NEP]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.lean
[NEP-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeEffectiveSourceProducer.scribe.cs
[NSC]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.lean
[NSC-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/NativeSourceSelectorCode.scribe.cs
[ISC]: ../../../D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.lean
[ISC-S]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/SourceCoordinates/IntrinsicSubstitutionCoordinates.scribe.cs
[KING]: https://research.ibm.com/publications/symbolic-execution-and-program-testing
[KING-DOI]: https://doi.org/10.1145/360248.360252
[EWD418]: https://www.cs.utexas.edu/~EWD/transcriptions/EWD04xx/EWD418.html
[EWD472]: https://www.cs.utexas.edu/~EWD/transcriptions/EWD04xx/EWD472.html
[TURING]: https://www.cs.virginia.edu/~robins/Turing_Paper_1936.pdf

## 追加锚（本行以下为增补区）
