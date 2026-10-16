# Recursive relational observation: native preparation history recovery

> **Reading contract.** This is ordinary mathematical reference input, not
> Lean kernel evidence. Numbered claims follow the `generic-v1` theory
> convention. Published bytes are preserved; extensions begin after the
> terminal append anchor and end with another append anchor. Repository
> suppliers below refer to commit
> `5fe79351d430d929eb588422fdf31364c82d9363`.

## 1. The history task and its unchanged source

**Convention 1.1 (status, provenance and contribution).** The deductions
in this volume are `repo-derived` ordinary proofs. One Codex CLI author
uses `formal-thinking-and-answer` and `theory-volume-template` under a
theory-only contract, with inherited repository context. Neither
independent review, mathematical priority nor formal certification is
asserted. The new result counts actual preparation transcripts required
by the original late-target task, and then prices recovering their
content from a compressed acquired export. Existing preparation-call
optima, prediction factors and common-table pooling bounds are suppliers.

**Definition 1.2 (stationary original interface).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad h(\alpha)=h(\beta)=0,
\qquad h(\langle u,v\rangle)=1+\max(h(u),h(v)).
$$

Pairing is free and ordered, and the two leaf labels are distinct. Set

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle u,v\rangle=\langle\rho u,\rho v\rangle.
$$

For public $D\ge2$, the complete original family and target menu are

$$
\mathcal F_D=\{\langle\alpha,v\rangle:h(v)\le D\},\qquad
\mathcal P_D=\{Rq:|q|\le D-1\}.
\tag{NPH.1}
$$

Every finite word $w$ over $L,R$, including the empty word
$\varepsilon$, is a legal original-root Read. Its reply $r_t(w)$ is
$\alpha$, $\beta$, $\mathsf{branch}$ or $\mathsf{absent}$, according
as the address reaches that leaf label, a pair, or passes a leaf. An
absent reply is a completed observation. One actual $t$ remains
stationary throughout every phase in this volume. The tree
$\rho^kt$ is a prediction target, not an executed register update.

**Assumption 1.3 (complete preparation and late-reader contract).** Fix
one deterministic effective pair $A$. Its preparation starts from
public $D$ and common source-independent installed data, before any
target is given. Source information enters only through paid Reads. It
terminates on every $t\in\mathcal F_D$ and exports $E_A(t)$. Every
accessible surviving source distinction belongs to this complete finite
name: control, selectors, buffers, lengths, allocation, handles,
counters and accessible timing. Other accessible fields factor through
this name and public inputs. Handoff, isolation, lawful entry, source
continuity and authentication are explicit separately paid services;
inaccessible preparation material is not a reader input.

After export an arbitrary public source-independent
$p\in\mathcal P_D$ arrives. Using only the complete name and public
inputs, the reader selects zero Reads or one arbitrary original-root
Read, before its reply and before any authentic count. Its final
predictor satisfies

$$
\operatorname{Dec}(Z,D,p,k)=r_{\rho^kt}(p)
\quad\text{for every }t\in\mathcal F_D,
\ p\in\mathcal P_D,\ k\ge0,
\tag{NPH.2}
$$

with no further Read. All competitors and variable shapes in
$\mathcal F_D$ remain in scope, including arbitrary correlated export
fibers. This is [PPF, Assumption 1.3][PPF], not an additional task
promise.

**Definition 1.4 (actual preparation transcript).** Write

$$
\tau_A(t)=((w_1,r_t(w_1)),\ldots,(w_n,r_t(w_n))),\qquad
\mathcal H_A(D)=\{\tau_A(t):t\in\mathcal F_D\}.
\tag{NPH.3}
$$

The order is execution order; repeated, empty, constant and absent
Reads are included. This target specifies address/reply content, not
physical timestamps, intervening computation steps, external events or
signed receipts. The transcript is a mathematical function of the
actual run. A callable archive of it is a further storage/access
service. Preparation pays $n$ calls, $\sum_j|w_j|$ submitted letters
and $\max(\{0\}\cup\{|w_j|\})$ peak submitted length. Distinct
addresses and actual invocations are different charges.
The history task's equivalence is exactly equality of $\tau_A(t)$.

## 2. Credited prediction information and a local decision quantity

**Convention 2.1 (the supplied all-count factor).** Use [AAR,
Definition 12.2, Theorem 12.3 and Proposition 13.3][AAR], also stated
in [PPF, Convention 2.1][PPF]. Write
$s(w)=\#L(w)+2\#R(w)$ and $e(\alpha)=0,e(\beta)=1$. If $q$
ends at an original branch, put $\Gamma_q(u)=(0,0)$. Otherwise let
$a$ be the first original blocking leaf, of label $\ell$, and write
$q=ar$. Then

$$
\Gamma_q(u)=
\begin{cases}
(2-e(\ell),1-e(\ell)),&r=\varepsilon,\\
(s(r)+2-e(\ell),\mathbf1_{r\text{ ends in }R}),&r\ne\varepsilon.
\end{cases}
\tag{NPH.4}
$$

Its supplied decoder is

$$
\operatorname{Pred}((b,c),k)=
\begin{cases}
\mathsf{branch},&k\ge b,\\
\beta,&b\ge1\text{ and }k=b-1,\\
\alpha,&c=1\text{ and }k=b-2,\\
\mathsf{absent},&\text{otherwise}.
\end{cases}
\tag{NPH.5}
$$

On attained factors this equals $r_{\rho^ku}(q)$ for every $k\ge0$.
Conversely the entire trajectory recovers $b$ as its first branch
count and $c$ by whether an alpha stage occurs. Thus distinct factors
are distinct complete prediction trajectories. No actual chronology is
reconstructed by this supplier.

**Definition 2.2 (eleven realized local trees).** Put

$$
C=\langle\alpha,\alpha\rangle,\qquad
S_1=\{\alpha,\beta,C\},\qquad
U=\{\alpha,\beta\}\sqcup
\{\langle x,y\rangle:x,y\in S_1\}.
\tag{NPH.6}
$$

These are eleven actual trees of height at most two, namely the
credited canonical $S_2$ of [CBN, Definition 1.4][CBN]. A nonempty
$B\subseteq U$ is *locally admissible* if, for each
$q\in\{\varepsilon,L,R\}$, $\Gamma_q$ on $B$ is constant or is a
function of one literal reply $r_u(w)$ on $B$, for some finite word
$w$ chosen before the reply and every $k$. The witness may depend on
$B,q$, and may be off-target.

Let $c(B)$ be the minimum number of nonempty terminal leaves of a
finite local Read decision tree whose terminal cells are locally
admissible. The tree uses only truthful literal tests on $u\in B$.
It is a proof quantity, not an installed optimal-strategy oracle.

**Lemma 2.3 (local terminal cost and its splitting inequality).** Every
nonempty $B\subseteq U$ has finite $c(B)$; $c(B)=1$ exactly when
$B$ is locally admissible. For every word $w$, with nonempty cells
$B_y=\{u\in B:r_u(w)=y\}$,

$$
c(B)\le\sum_{y:B_y\ne\varnothing}c(B_y).
\tag{NPH.7}
$$

Proof. Read the local root. Its leaf cells are singletons. On its pair
cell the root factor is constantly $(0,0)$, while either child target
is solved by reading that child: its present alpha, beta and branch
replies give respectively $(2,1),(1,0),(0,0)$. The same construction
restricted to $B$ has at most three nonempty terminal leaves. Thus
the minimum exists as a positive integer. An admissible set needs no
preparatory test. Conversely a decision tree with one nonempty
terminal leaf places all of $B$ in its one admissible terminal cell.
Finally, query $w$ first and append a minimizing tree for each
nonempty reply cell. The resulting leaf count is the right side of
(NPH.7). $\square$

**Lemma 2.4 (the local multiplicative unit).** One has $c(U)=3$.

Proof. The root construction of Lemma 2.3 proves the upper bound.
For the lower bound, consider the first test with more than one
attained reply in any admissible-terminal decision tree on $U$.
Earlier constant tests do not reduce $U$. Such a test must occur:
the set $U$ is not admissible, as follows from the four-tree witnesses
below, which are already nonadmissible subsets.

The empty word has three attained replies, and each word of length
one has four. Either choice therefore requires at least three
nonempty terminal leaves. Each word of length two has just alpha and
absent replies. For a word starting with $L$, its absent cell contains

$$
B_L=\{\alpha,\beta,
\langle\alpha,\alpha\rangle,
\langle\beta,\alpha\rangle\}.
$$

At target $L$, their factors in this order are

$$
(3,0),\ (2,0),\ (2,1),\ (1,0).
\tag{NPH.8}
$$

All four are distinct. No local literal separates them: the root
and $L$ each have at most three reply values, $R$ has at most two,
and every longer word is constantly absent. Hence $B_L$, and thus
the absent cell containing it, is nonadmissible. That cell needs at
least two terminal leaves; the other attained cell needs at least
one.

For a length-two word starting with $R$, use instead

$$
B_R=\{\alpha,\beta,
\langle\alpha,\alpha\rangle,
\langle\alpha,\beta\rangle\}.
$$

At target $R$ the four factors are
$(4,1),(3,1),(2,1),(1,0)$. Again the root and $R$ have at most
three replies, $L$ at most two, and longer words are absent. This
is the same nonadmissibility argument on that actual cell. All words
of length at least three are constantly absent on $U$, so cannot be
the first informative test. These cases exhaust every literal word
and prove the lower bound. $\square$

## 3. Preparation transcripts on the full original family

**Definition 3.1 (a realized scaffold subfamily).** Fix
$d=D-2$ and $Q=2^d$. For a tuple
$\mathbf u=(u_a)_{a\in\{L,R\}^d}\in U^Q$, let
$v(\mathbf u)$ be the perfect ordered scaffold of depth $d$ whose
leaf at address $a$ is replaced by $u_a$, and set
$t(\mathbf u)=\langle\alpha,v(\mathbf u)\rangle$.
For $d=0$ this means $v(\mathbf u)=u_\varepsilon$.
All these distinct sources lie in $\mathcal F_D$. Their coordinate
cones consist of the original words $Raw$. They are pairwise
disjoint; every nonconstant literal on this family enters exactly one
cone. Above those cones every reached scaffold node is a fixed branch;
the left wrapper and all its descendants give fixed replies as well.

**Lemma 3.2 (rectangles of actual preparation transcripts).** Restrict
any preparer satisfying Assumption 1.3 to the sources of Definition
3.1. At every attained transcript prefix its remaining tuples form a
nonempty product $\prod_a B_a$, with $B_a\subseteq U$. At a
terminal prefix, every $B_a$ is locally admissible.

Proof. Initially every $B_a=U$. A literal outside the coordinate
cones has a fixed reply on the family. A literal $Raw$ tests only
$r_{u_a}(w)$, so conditioning on its reply replaces only $B_a$ by
one nonempty reply cell. The next query is fixed by the shared
transcript and common program. Induction proves the product assertion
under arbitrary interleaving, off-target queries, repeats, internal
work and source-dependent stopping.

At a terminal transcript, the export is identical on this whole
product: the program has common initial inputs and has received
identical replies. Fix $a$ and $q\in\{\varepsilon,L,R\}$.
The global target $Raq$ has length at most $D$ and is permitted.
Homomorphic substitution on the scaffold gives

$$
r_{\rho^kt(\mathbf u)}(Raq)=r_{\rho^ku_a}(q)
\quad(k\ge0).
\tag{NPH.9}
$$

The late reader therefore must determine $\Gamma_q(u_a)$ on the
whole terminal product, by Convention 2.1. Its chosen late word is
fixed by the shared export and this target. If it enters cone $a$,
its single reply is one local literal on $B_a$. If it enters another
cone or is constant on the scaffold family, fix all other
coordinates: the reply is then independent of $u_a$, forcing
$\Gamma_q$ to be constant on $B_a$. Choosing zero Reads also
forces constancy. This proves admissibility for every local target.
No rectangularity is asserted for an export fiber, which can be an
arbitrary union of terminal transcript cells. $\square$

**Theorem 3.3 (original preparation-history alphabet).** For every
$D\ge2$ and every correct pair $A$ of Assumption 1.3,

$$
|\mathcal H_A(D)|\ge3^{2^{D-2}}.
\tag{NPH.10}
$$

The same lower bound holds for pairs required to work only on the
realized scaffold subfamily $U^Q$, while serving every original target
and every later $k$. On that restricted promise it is sharp: one
effective native preparer has exactly $3^Q$ transcripts and complete
retained names, uses $Q$ preparation Reads, exactly $(D-1)Q$
submitted letters and peak length $D-1$, and its retained name
recovers its preparation transcript. No full-family equality for the
minimum transcript alphabet is asserted.

Proof of the lower bound. Give an attained prefix cell
$\prod_a B_a$ potential $\prod_a c(B_a)$. If the next query enters
cone $a$, the sum of its child potentials is at least the parent
potential by (NPH.7); a constant query preserves the potential. Every
terminal potential is one by Lemma 3.2. The restricted source set is
finite, and preparation terminates on every member. Its execution
tree is therefore finite: the maximum of these finitely many actual
finite run lengths is finite. Backward induction bounds its number
of terminal transcripts below by its initial potential
$c(U)^Q=3^Q$. The transcript set on the full family contains that
restricted transcript set, proving (NPH.10).

Proof of restricted attainment. In a fixed public address order,
Read each full word $Ra$ for $|a|=d$. Retain only the vector of
these $Q$ root replies. All three possibilities alpha, beta and
branch are independently attained at every cone, so the complete
retained alphabet and actual transcript alphabet each have exactly
$3^Q$ values. Fixed query order makes the transcript recoverable
from that vector. Complete handoff/isolation removes all other
accessible preparation dependence.

For a late target $Rq$, if $|q|<d$, its endpoint is a known
scaffold branch and its entire trajectory is branch. Otherwise write
$q=ar$ with $|a|=d$ and $|r|\le1$. If the retained cone root is a
leaf, its label and this suffix determine its entire trajectory by
(NPH.4). If the retained cone root is branch and $r$ is empty, the
trajectory is branch. If it is branch and $|r|=1$, Read the one
original word $Rar$; its alpha, beta or branch reply gives
$(2,1),(1,0),(0,0)$ respectively. In each case the selected Read
precedes its reply and every $k$, and (NPH.5) answers all later
counts without another Read. This serves all original targets on
the restricted promise. Each preparation word $Ra$ has length
$D-1$, giving the stated simultaneous charges. $\square$

The restriction in the attainment statement is essential. At a fixed
scaffold location an arbitrary full-family subtree need not belong to
$U$. The full-family lower bound was proved by restriction; the
restricted upper construction does not assert correctness on those
additional sources.

## 4. The additional price of recovering the earlier content

**Assumption 4.1 (history-recovery extension).** After the complete
export of a specified public preparer $A$, a deterministic recovery
procedure receives only that name and common public inputs. It may
make further charged adaptive original-root Reads of the same
stationary source and must output exactly $\tau_A(t)$ for every
$t\in\mathcal F_D$. Inaccessible old buffers and histories are not
inputs. Any extra retained field is counted jointly with the export.
This is an additional task, separate from (NPH.2). Public targets or
count inputs, if present, can be fixed to the same allowed values on
every source; they provide no source-dependent advice.

**Theorem 4.2 (necessary acquired alphabet and fresh-Read tradeoff).**
Let $m=|E_A[\mathcal F_D]|$. If a recovery procedure of Assumption
4.1 uses at most $q$ new Reads on every source, then

$$
m4^q\ge3^{2^{D-2}},\qquad
q\ge\max\left(0,
\left\lceil\frac{2^{D-2}\log_2 3-\log_2 m}{2}\right\rceil\right).
\tag{NPH.11}
$$

More generally, if an additional accessible retained field has at most
$K$ possibilities for each export value, then necessarily

$$
mK4^q\ge3^{2^{D-2}}.
\tag{NPH.12}
$$

These are necessary conditions, not sufficiency claims or total
observer-memory estimates.

Proof. For each entry name, the new actual executions form a
decision tree of depth at most $q$ and branching at most four.
Even with early stopping it has at most $4^q$ terminal leaves.
Addresses, stopping, internal control and the final output are
functions of the entry, the acquired replies and public inputs; they
provide no additional independent distinctions. One terminal leaf
cannot correctly output two different earlier preparation transcripts.
Summing over all $m$ entries and applying Theorem 3.3 proves the
first inequality. Taking logarithms gives the second. With the
supplemental field the actual joint entry image has size at most
$mK$, whether or not its fields are correlated, giving (NPH.12).
$\square$

**Theorem 4.3 (paid content replay from the same actual source).** For
every fixed public $D\ge2$ and deterministic effective preparer $A$
of Assumption 1.3, there is a history-recovery extension using at most

$$
2^D\text{ new calls},\qquad
(D+1)2^D\text{ submitted letters},\qquad
D+1\text{ peak submitted length}.
\tag{NPH.13}
$$

It reconstructs the address/reply sequence content (NPH.3). The
statement does not grant authentic past-event receipts, recover
external timing or bound storage, output size or local simulation
work.

Proof. Ignore the compressed export and run the credited procedure
$\operatorname{Acquire}(R,D)$ of [PPF, Lemma 4.1][PPF] on the
same original $t$. Its actually acquired replies determine the whole
relative depth-$D$ table of $v$. Since $h(v)\le D$, every reached
node at depth $D$ is a leaf; recursive parsing of that table
reconstructs all of $v$, hence the original $t$. The supplier's
call, letter and peak bounds are exactly (NPH.13).

Now simulate the specified public preparation program from its common
initial state, supplying $r_t(w)$ from the reconstructed tree to
each of its simulated requests. Induction on the original execution
shows identical submitted words, replies, internal state and stop.
The simulation terminates because $A$ terminates on that source,
and emits exactly $\tau_A(t)$. These local simulated requests are
not additional source calls. The actual new acquisition requests
remain new events and are charged; they do not become earlier
events. $\square$

**Corollary 4.4 (exponential fresh-Read order after optimal naming).**
Reuse the original alphabet optimum $M_1(D)$, its effective acquired
realization from [PPF, Theorem 5.1][PPF], and the credited limit and
strict upper bound

$$
\lambda=\lim_{D\to\infty}2^{-D}\log_2 M_1(D)<\frac3{16}
\tag{NPH.14}
$$

from [FMR, Theorem 3.3][FMR] and [D3, Theorem 4.1][D3]. For any
family of exact history-recovery extensions starting only from
optimal original exports, with worst new-call bound $q(D)$,

$$
\liminf_{D\to\infty}\frac{q(D)}{2^D}
\ge\frac{\log_2 3}{8}-\frac\lambda2
>\frac{\log_2 3}{8}-\frac3{32}>0.
\tag{NPH.15}
$$

For any specified family of effective optimal preparers, the minimum
worst new-call cost of content recovery is therefore
$\Theta(2^D)$, when local work, storage and final output are allowed
to grow and are charged separately.

Proof. Substitute $m=M_1(D)$ in (NPH.11), divide by $2^D$ and
take the lower limit, using (NPH.14). The last constant is positive
because $\log_2 3>1>3/4$. Theorem 4.3 gives a uniform upper
bound $2^D$ for each specified effective preparer. No sharp leading
constant follows. $\square$

At $D=3$, Theorem 3.3 gives at least nine actual preparation
transcripts, whereas [D3, Theorem 2.3][D3] gives $M_1(3)=4$.
Thus no optimal four-name export alone recovers that earlier sequence.
Equation (NPH.15) also excludes recovery with just one new Read from
optimal exports for all sufficiently large $D$. The depth-three
comparison alone does not exclude one new Read, since $4\cdot4$
exceeds nine. These statements do not contradict the original feasible
one-request prediction service.

## 5. Event authenticity, common realization and four-view limits

**Definition 5.1 (one actual history image).** For the interface in
this volume, an execution prefix consists of the one stationary
source, its authenticated original-root reference and permissions
supplied by the access contract, its current preparation/recovery
control and work, and the ordered Reads actually completed. The
source/epoch/type tags of these fields belong to that same execution.
The history domain is the set of prefixes generated by these
programs and truthful replies. Their joint image is the image of
this one domain, never the product of separate field images.

A Read event has full label $(w,r_t(w))$. Its source-register
successor is still $t$; control and work take the declared
deterministic successor. If an archive writer is installed, the same
event appends that label to the archive and the writer/storage cost
is additional. With no such service the mathematical history is not
an accessible operational record. The actual-call and transcript
arguments above require no free archive.

**Proposition 5.2 (content reconstruction cannot supply an omitted
past-event distinction).** Suppose an enriched history task permits
two actual histories with the same stationary source, same complete
recovery entry and public inputs, but different required past-event
receipts or timing data. Suppose every later permitted observation
depends only on that source and the recovery procedure's acquired
state. No deterministic procedure using that interface can recover
the enriched history on both realizations, even with arbitrarily many
later Reads.

Proof. Inductively the two recoveries start equally, select the same
next address, receive the same reply from the same source, and take
the same successor. They have identical later observations and
outputs. The two required enriched histories are different, so at
least one output is incorrect. $\square$

For example, an independently issued historical receipt identifier
with two possible values is such an omitted distinction if neither
the current source nor the entry retains it. A past timestamp is
another example when the enriched contract permits different schedules
with identical address/reply content. These examples specify enriched
domains; the deterministic content target (NPH.3) contains neither
field. Theorem 4.3 recovers that content, and does not assert its
cryptographic or physical authenticity. Supplying a source-bound
authenticated writer and callable persistent record is a new service
whose implementation and price require their own contract.

**Convention 5.3 (failures and unexecuted actions).** All finite
literal Reads here are legal and have one of the four replies.
In particular, $\mathsf{absent}$ has a completed event and a
successor. There are no executed hardware-failure, revocation or crash
labels in the stated interface. An unexecuted prohibited action has
no event or successor; it cannot be represented as
$\operatorname{some}(\mathsf{failure},s')$. An extension with
such executed failures must declare their full labels, joint
successors and recording behavior. The lower bound persists by
restriction if that extension preserves these original runs and adds
no accessible source/history information. The replay upper bound
does not reconstruct external failure or scheduling choices merely
from the tree.

**Consequence 5.4 (the changed interface choice).** If a proposed
Time view retains (NPH.3), an optimal finite acquired Memory name
cannot recover it within a uniformly bounded number of extra Reads.
An observer pursuing that recovery must retain a callable history
relation, enlarge its complete attained alphabet, or pay for source
reacquisition. With no fresh observation and no uncounted service,
the joint retained alphabet must have at least $3^{2^{D-2}}$ values.
The matching construction is proved only on the scaffold subfamily.

This is one obstructed recovery arrow. It does not instantiate four
natural views or equate any of their kernels to the original task
kernel. [PG, §34][PG] still requires a common actual image and
full/successor contracts. [PG, Proposition 43.1][PG] requires
nonredundancy as well as mutual recovery and task sufficiency;
[Atlas, Theorem 6.3][Atlas] requires each view kernel separately.
A semantic object listing every counterfactual source response is not
an already acquired finite name. An accessible complete history can
also retain distinctions irrelevant to the original prediction task.

**Open problem 5.5 (remaining mathematical bridges).** Determine the
full-family minimum preparation-transcript alphabet and sharp
history-reacquisition constants, jointly with complete naming,
preparation, execution and storage costs. Construct an actually
acquired same-source observer with concrete spatial support, ordered
events, continuation responses and callable memory, lawful selectors,
full failure successors and individual exact task kernels. The
general original $M_1(D)$, sharp $\lambda$, effective all-size
certificates and coherent global coverage/ThreadComplete and
whole-edge legality remain unresolved. The bounded history task
does not replace any of these objectives.

## 6. Supplier correspondence, resources and literature

**Convention 6.1 (separate resource accounts).** The alphabet
$|\mathcal H_A(D)|$ counts earlier actual sequences, not their
lengths. Equations (NPH.11)–(NPH.12) bound fresh calls; $K$ is a
conditional supplement, not total observer memory. Acquisition
buffers, reconstructed syntax, address construction, complete retained
state, installed public code, decoder workspace, transcript output,
local simulation work, archive persistence and access, and the
handoff/isolation/continuity/authentication services are separate
coordinates. No monetary, energy or physical execution optimum is
claimed. Theorem 4.3 can have large output even when its call count
is bounded by (NPH.13).

**Supplier correspondence 6.2 (repository contracts).**

| Supplier | Exact use and boundary |
| --- | --- |
| [PPF, §§1,3–7][PPF] | Original all-source/all-target/all-count contract, per-call prices, native comparison witnesses, actual `Acquire`, effective optimal naming and image disjointness. Its preparation projections are not the transcript-alphabet theorem. |
| [AAR, §§12–13,16][AAR]; [CBN, §§1–2][CBN] | Entire-trajectory factor and actual canonical trees/reply tables. These already own the finite spatial/prediction correspondence. |
| [FMR, §3][FMR]; [D3, §§2,4][D3] | Existence of the original rate, four-name depth-three value and strict rate upper bound used in Corollary 4.4. |
| [SCE, §§5–6][SCE] | Four-reply capacity method for a different task: common target-table pooling. The required image here is the actual earlier preparation sequence. |
| [NDR, §6][NDR]; [SLH, §43.5][SLH] | Existing deterministic replay boundary and terminal-record distinctions. Replay and generic coding are reused, not counted as the new native lower bound. |
| [ActualTreeReadoutAcquisition][ATR] and [its owning Scribe][ATB] | `readout` and stationary history-only `Policy`; `paid` counts distinct addresses for its membership task, whereas this volume charges each invocation. Its comparison operation `flip` is not a lawful source update. |
| [FixedTreeCommonExtension][FTE] and [its owning Scribe][FTB] | `Implementation` receives given leaf coordinates and full child-message tuples on a fixed `Full` tree. It supplies neither literal acquisition nor a past archive. |
| [NativeLiteralMoore][NLM] and [its owning Scribe][NLB] | `NativeLiteralFeasible` runs on `substitution u.val` and outputs predecessor `canonicalRow P u.val`. By PPF 7.1 this is not an identity-port handoff to the unchanged original family. |

**Literature correspondence 6.3 (primary models and transfer limits).**

| Primary source | Verified correspondence |
| --- | --- |
| Jain, Klauck and Santha, *Optimal Direct Sum Results for Deterministic and Randomized Decision Tree Complexity*, [arXiv:1004.0105v1](https://arxiv.org/pdf/1004.0105v1), Theorem 1 | `literature-attested`: deterministic query depth for independent Boolean-input relations has a direct-sum lower bound. Independent actual cones motivate comparison; four-valued probes, residual admissibility and terminal-leaf multiplication in Theorem 3.3 are proved here and are not an application of that depth theorem. |
| Greenwald, Moore, Pierce and Schmitt, *A Language for Bi-Directional Tree Transformations*, [author manuscript](https://www.cis.upenn.edu/~bcpierce/papers/lenses.pdf), Definitions 3.1.1–3.1.2 | `literature-attested`: partial get/put laws include GetPut and PutGet, and put receives the old concrete state, or the explicit missing-state argument. That complement is not an acquired inverse of a compressed native export or an event archive. |
| Matsuda, Nguyen and Wang, *Lenses for Partially-Specified States*, [extended version](https://arxiv.org/pdf/2601.04573), Definitions 2–3; [DOI](https://doi.org/10.1007/978-3-032-22723-2_2) | `literature-attested`: partial-state lenses use i-posets and a partial put; duplicability supplies a designated merge operation. Neither merge nor partial specification grants physical copying, historical acquisition or native prices. |
| Littman, Sutton and Singh, *Predictive Representations of State*, [primary paper](https://proceedings.neurips.cc/paper_files/paper/2001/file/1e4d36177d71bbb3558e43af9577d70e-Paper.pdf), Theorem 1 | `literature-attested`: finite-POMDP environments admit linear predictive representations with no more tests than minimal POMDP states, preserving history distributions. Prediction of future tests does not recover a realized deterministic past; POMDP structure and probabilistic coordinates do not supply native acquired names. |
| van den Bos and Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [arXiv:1907.11034v2](https://arxiv.org/pdf/1907.11034v2), introduction and adaptive-test construction | `literature-attested`: adaptive testing identifies states under a declared finite input/output transition-system model and compatibility conditions. Those input/output permissions are not original-root Reads, and state identification is not historical receipt recovery. |
| Prabhakaran and Prabhakaran, *Assisted Common Information with Applications to Secure Two-Party Computation*, [arXiv:1002.1916](https://arxiv.org/pdf/1002.1916), §II, Theorem 2.1 and Corollary 2.2 | `literature-attested`: correlated iid blocks, asymptotic agreement and a rate-limited omniscient helper define a common-information region; zero-rate common information follows support components. No helper, iid law, entropy-rate or allowed-error theorem is transferred to this single-source zero-error task. |

The native local calculation, its multiplicative propagation and the
history-recovery consequence are `repo-derived`. The paper models
above delimit useful comparisons; no exhaustive literature search or
global originality claim is made. Ordinary proofs establish the
quantified statements. Finite checks of small actual trees can falsify
them but do not certify their universal or kernel status.

[PPF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_PREPARATION_FRONTIERS.md
[AAR]: RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md
[CBN]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONSTRUCTOR_BOUNDARY_NETWORKS.md
[FMR]: RECURSIVE_RELATIONAL_OBSERVATION_LATE_TARGET_FRACTIONAL_MEMORY_RATE.md
[D3]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DEPTH_THREE_MEMORY_AND_FRACTIONAL_SEED.md
[SCE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SELECTOR_COMMON_EXTENSION.md
[NDR]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_DISCOVERY_AND_RETAINED_CONTEXT.md
[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[PG]: RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md
[Atlas]: RECURSIVE_RELATIONAL_OBSERVATION_ATLAS_STABLE_CORE_HOLONOMY.md
[ATR]: ../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[ATB]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.scribe.cs
[FTE]: ../../../D5/S3/Observer/Separation/FixedTreeCommonExtension.lean
[FTB]: ../../../Blueprint/D5/S3/Observer/Separation/FixedTreeCommonExtension.scribe.cs
[NLM]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeLiteralMoore.lean
[NLB]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeLiteralMoore.scribe.cs

## 追加锚（本行以下为增补区）
