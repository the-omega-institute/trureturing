# Recursive relational observation: native virtual substitution compiler

> **Reading contract.** This volume gives ordinary mathematical proofs,
> without Lean kernel certification. Numbered claims follow the
> `generic-v1` theory convention. Published bytes remain immutable;
> additions begin after the terminal append anchor and end with another
> append anchor. Repository suppliers designate their committed text at
> `5fe79351d430d929eb588422fdf31364c82d9363`.

## 1. Actual source, virtual responses and acquired entry

**Convention 1.1 (status and contribution).** The construction and
witnesses below are `repo-derived`. One Codex CLI author uses
`formal-thinking-and-answer` and `theory-volume-template` under a
theory-only contract, with inherited repository context. No independent
review, worldwide priority or kernel status is asserted. The result is
a priced response-port compiler on the unchanged source, with a
concrete separation between response correctness and recovery of actual
ordered events. It does not acquire a native four-view observer.

**Definition 1.2 (the two response functions).** Let $\mathcal T$ be
the free ordered tree algebra with distinct leaves $\alpha,\beta$.
Write $\langle u,v\rangle$ for pairing and put

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle u,v\rangle=\langle\rho u,\rho v\rangle.
\tag{NVC.1}
$$

The actual port is the stationary original-root literal Read:
$r_t(w)\in\mathcal A$, where

$$
\mathcal A=\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}.
$$

Every finite left/right word, including $\varepsilon$, is legal.
An absent reply means the path passed a leaf; it is a completed
observation with a successor. Define the *virtual one-substitution
response* by

$$
V_t(w)=r_{\rho t}(w).
\tag{NVC.2}
$$

Equation (NVC.2) is a mathematical target. The only actual source
register in this volume is $t$, and it never changes. No actual
$\operatorname{ApplyRho}$, copy, reset, subtree, cursor navigation,
equality or source-identity operation is installed by (NVC.1).

For comparison with the original task, retain

$$
\mathcal F_D=\{\langle\alpha,v\rangle:h(v)\le D\},\qquad
\mathcal P_D=\{Rq:|q|\le D-1\}.
\tag{NVC.3}
$$

Its preparation is source-blind and target-blind; after the complete
export, $p$ arrives, at most one original-root Read is selected before
its reply and every authentic $k$, and the final predictor answers
$r_{\rho^kt}(p)$ for every later $k\ge0$ without more Reads.
These are [PPF, Assumption 1.3][PPF]. A scalar request (NVC.2)
with fixed substitution count one is a different task.

**Definition 1.3 (explicit finite stationary controller).** Fix finite
disjoint running and halt carriers $Q,H$, an output set $Y$, and
public finite tables

$$
\operatorname{addr}:Q\to\{L,R\}^{<\omega},\qquad
\operatorname{next}:Q\times\mathcal A\to Q\sqcup H,\qquad
\operatorname{out}:H\to Y.
\tag{NVC.4}
$$

All accessible mutable controller state is the element of $Q\sqcup H$.
The output at a halt is its fixed complete value
$\operatorname{out}(h)$, with no source-dependent decoder argument.
Tables and addresses are source-independent installed data. Shared
states, repeated visits, cycles and arbitrary off-target words are
allowed. At a running state $q$, the virtual machine requests
$V_t(\operatorname{addr}(q))$ and follows $\operatorname{next}$.
At a halt it makes no further Read.

**Assumption 1.4 (genuinely acquired complete entry).** On a declared
source domain $X\subseteq\mathcal T$, an actual source-blind paid
preparation supplies entry $e(t)\in Q\sqcup H$. Every accessible
surviving source distinction at entry factors through $e(t)$ and
public inputs, including controls, buffers, selectors, lengths,
allocation and accessible timing. The original-root reference,
permission, continuity, authentication, lawful entry and isolation are
explicit paid services. Their handles supply no uncounted source
distinctions. Let

$$
r=|e[X]|,\qquad K=|Q|+|H|.
\tag{NVC.5}
$$

An existence statement for a finite-range function does not acquire it.
Theorems below require the actual preparation or an explicitly supplied
paid entry service. Installed code cannot depend on the unknown source.
A growing accessible event log is not included in the finite carrier
(NVC.4); if installed, it is additional complete operational state.

## 2. Literal lowering through one substitution

**Definition 2.1 (reply transforms).** Define a total map
$F:\mathcal A\to\mathcal A$ and the two branch-created replies by

$$
F(\alpha)=\beta,\quad F(\beta)=\mathsf{branch},\quad
F(\mathsf{branch})=\mathsf{branch},\quad
F(\mathsf{absent})=\mathsf{absent},\qquad
J_L=\beta,\quad J_R=\alpha.
\tag{NVC.6}
$$

The absent value of $F$ totalizes the finite tables; a truthful
empty-word Read or a child of a truthful branch cannot be absent.

**Theorem 2.2 (same-source one-substitution response algorithm).**
For every $t\in\mathcal T$ and every word $w$, the following
procedure computes $V_t(w)$ using only actual original-root Reads of
that same stationary $t$.

For $w=\varepsilon$, Read $\varepsilon$ and return $F$ of the
reply. For $w=ub$, $b\in\{L,R\}$, first Read $u$ and use

$$
V_t(ub)=
\begin{cases}
\mathsf{absent},&r_t(u)\in\{\alpha,\mathsf{absent}\},\\
J_b,&r_t(u)=\beta,\\
F(r_t(ub)),&r_t(u)=\mathsf{branch},
\end{cases}
\tag{NVC.7}
$$

where the last case makes the additional Read $ub$. A nonempty
request costs at most two calls, at most $2|w|-1$ submitted letters
and peak word length at most $|w|$. The empty request costs one
call and zero submitted letters. Both calls in the last case are
charged, even if their addresses have occurred before.

Proof. The root of a whole original tree is alpha, beta or branch;
its substituted root is given by $F$, proving the empty case.
Suppose $w=ub$. If the actual endpoint at $u$ is alpha,
substitution leaves a beta leaf there, so its child is absent. If it
is beta, substitution creates exactly the pair
$\langle\beta,\alpha\rangle$ there, giving $J_b$. If it is
branch, every ancestor on the path to $u$ and $u$ itself is an
original branch. Homomorphic substitution preserves each of these
occurrences, and $ub$ is present. Its new root constructor is $F$
of its acquired original reply. Finally, if $u$ is absent, an
original leaf occurs strictly above it. The word $ub$ is at least
two levels below that leaf, whereas one substitution extends a leaf
by at most one level. It remains absent. These exhaustive cases
prove (NVC.7) on variable shapes and arbitrary absent words.

The first submitted word has length $|w|-1$ and the optional
second length $|w|$. Their sum is at most $2|w|-1$. Selection of
the child is a lawful deterministic function of the already paid
parent reply; no prefix navigation or acquired subtree is used.
$\square$

This implements a nonidentity response bridge. [PPF, Proposition
7.1][PPF] proves $\mathcal F_D\cap\rho(\mathcal T)=\varnothing$.
That image obstruction prevents an identity handoff of the actual
register, but does not prevent the explicitly priced computation
(NVC.7).

## 3. Compiling a full finite response computation

**Theorem 3.1 (finite controller compilation with simultaneous costs).**
For every controller (NVC.4) and paid entry (Assumption 1.4), there
is an explicit public controller using only stationary Reads of $t$
whose attained complete-entry alphabet has exactly $r$ values and
whose installed carrier has

$$
|Q_0|+2|Q_+|+|H|\le2|Q|+|H|\le2K
\tag{NVC.8}
$$

states, where $Q_0=\{q:\operatorname{addr}(q)=\varepsilon\}$
and $Q_+=Q\setminus Q_0$.
For every $t\in X$, a finite virtual run from $e(t)$ reaches halt
$h$ if and only if its compiled run reaches that same halt. Its
whole output is the identical $\operatorname{out}(h)$.

On any such run let $n_0,n_+$ count the empty and nonempty virtual
requests, and let
$\ell=\sum |\operatorname{addr}(q)|$ count all virtual submitted
letters with multiplicity. Let $B$ be the multiset of nonempty
request visits for which the actual parent reply is branch. The
compiled actual call and letter counts satisfy the exact formulas

$$
\begin{aligned}
n'&=n_0+n_++|B|\le n_0+2n_+,\\
\ell'&=\ell-n_++\sum_{q\in B}|\operatorname{addr}(q)|
\le2\ell-n_+.
\end{aligned}
\tag{NVC.9}
$$

Its peak submitted length is no larger than the virtual peak.
All statements hold on the same source and run; bounds from
separately optimized histories are not combined.

Proof. Give each $q\in Q_0$ one running state, which Reads the
empty word and feeds $F$ of its reply to the original
$\operatorname{next}(q,-)$. Give each $q\in Q_+$ a first phase
and a child phase. The first phase Reads the parent of
$w=\operatorname{addr}(q)$. A branch reply enters its child phase.
Every other reply feeds the corresponding value in (NVC.7) directly
to $\operatorname{next}(q,-)$. The child phase Reads $w$ and
feeds $F$ of its reply to $\operatorname{next}(q,-)$. In each
case a resulting running state is replaced by its first phase, or
its unique empty-word phase; a halt is left unchanged. This defines
total tables even on the unreachable child-absent edge, using the
total map $F$. The same halts and their complete outputs are kept.
These phases give exactly the carrier count in (NVC.8).

Inject $Q\sqcup H$ into the compiled carrier by taking these first
phases and fixing the halts. The new entry is that injection of
$e(t)$, so its attained alphabet has exactly $r$ values. The map
is public and introduces no additional source selection. It is
computed from the paid entry; any redundant acquired preparation
material remains inaccessible under the same isolation contract.

By Theorem 2.2, each virtual request is implemented by one or two
actual Reads and reaches precisely the image of the virtual next
state. Induction on requests proves preservation of the full
controller path at these completion points and the identical final
halt and output. Conversely the compiled machine can leave a child
phase only by completing its current request. It cannot halt in an
intermediate phase. Thus any compiled termination projects to a
virtual termination. In particular virtual divergence cannot be
replaced by a compiled halt.

An empty visit uses one zero-length call. Each nonempty visit uses
its parent word, and exactly the visits in $B$ also use their
original word. Summing these actual costs proves both exact
formulas; the sum over $B$ is at most $\ell$. Every submitted
word is a virtual word or its parent, proving the peak claim.
$\square$

The finite state bound includes every installed phase and halt,
including unreachable ones. It counts the controller's accessible
mutable carrier, not a callable external log. The temporary reply
handling is the declared transition table, not an uncounted persistent
buffer. Installation, address-table storage, output payload, internal
transition computation and the paid preparation retain separate costs.

**Corollary 3.2 (uniform budget bridge for an explicit witness).** If
one explicit virtual witness has complete entry alphabet at most $r$,
total finite states at most $K$, at most $q$ calls and at most
$\ell$ submitted letters on every source of its declared domain,
then its compiled witness has simultaneous upper budgets

$$
(r,K,q,\ell)\longmapsto(r,2K,2q,2\ell).
\tag{NVC.10}
$$

The sharper same-run bounds are (NVC.8)–(NVC.9). A source-specific
choice of witness or controller is not included unless that selector
is genuinely acquired and counted.

Proof. Apply Theorem 3.1 to the given tables and acquired entry.
Every original call contributes one virtual visit and every original
letter is counted on that same run, so (NVC.9) implies the two
uniform inequalities. $\square$

## 4. Two necessary distinctions on original instances

**Theorem 4.1 (a sharp two-call scalar instance).** Fix $D\ge2$.
For a common source-independent initial state, exact computation of
$V_t(RR)$ on every $t\in\mathcal F_D$ requires at least two
original-root Reads in the worst case, even with arbitrary off-target
words. Theorem 2.2 attains two.

Proof. Consider $t=\langle\alpha,v\rangle$ for

$$
v=\alpha,\quad\beta,\quad
\langle\alpha,\alpha\rangle,\quad
\langle\alpha,\beta\rangle.
$$

Their required virtual replies at $RR$ are respectively
$\mathsf{absent},\alpha,\beta,\mathsf{branch}$.
The first two actual sources have identical replies at every word
except $R$. A correct procedure with at most one call must therefore
make that call at $R$: with constant entry its choice cannot depend
on the unknown source. But the last two sources both reply branch
at $R$ and require different outputs. This is a contradiction.
All four actual sources are in the promised family, and $RR$ is
an original allowed target at $D\ge2$. The upper bound follows
from (NVC.7). $\square$

This is a scalar fixed-count response lower bound with constant
advice. It is not a lower bound against the original paid
preparation/one-late-Read service with a nonconstant acquired export.

**Definition 4.2 (raw terminal transcript for a scalar task).** A
procedure here starts with the same source-independent state on
every $t\in\mathcal F_D$, performs deterministic actual literal
Reads, terminates on every source, and returns a function of its
acquired information and public inputs. Its complete raw transcript
is the ordered list of all actual word/reply pairs, including repeats
and constant calls. It contains no physical timing or external event
fields. No archive is supplied to the procedure merely by defining
this mathematical transcript.

For the scalar response task, two sources are equivalent exactly when
their requested virtual replies agree. For the raw-history task,
equivalence is equality of these complete ordered transcripts.

**Theorem 4.3 (three virtual outputs require five raw transcripts).**
For every $D\ge2$, the scalar task $V_t(RL)$ on the entire
$\mathcal F_D$ has exactly three attained output values. Among all
correct terminating procedures of Definition 4.2, the minimum attained
alphabet of complete raw terminal transcripts is exactly five.
Consequently, for every such procedure its raw transcript is not a
function of the single virtual reply alone.

Proof. Write $C=\langle\alpha,\alpha\rangle$ and consider
the following five actual right subtrees:

$$
\alpha,\quad\beta,\quad C,\quad
\langle\beta,\alpha\rangle,\quad
\langle C,\alpha\rangle.
\tag{NVC.11}
$$

Their virtual replies at $RL$ are, in order,
$\mathsf{absent},\beta,\beta,\mathsf{branch},\mathsf{branch}$.
Every right subtree has root alpha, beta or branch. Formula (NVC.7)
shows that these three are the only possible outputs on the entire
family, and (NVC.11) attains each.

Different output classes require different terminal transcripts,
because the procedure has common initialization and is deterministic.
The run on right subtree $\beta$ must query $R$: replacing it by
$\alpha$ changes the required output and changes no other original
literal reply. If $R$ were never queried, deterministic replay would
give identical termination and output on this competitor. Its
transcript therefore differs from that on right subtree $C$, whose
$R$ reply is branch. Thus the beta-output class requires at least
two transcripts.

The run on right subtree $\langle\beta,\alpha\rangle$ must query
$RL$: flipping only its left beta to alpha changes the virtual
output from branch to beta and changes no other original literal.
Its transcript therefore differs from that on right subtree
$\langle C,\alpha\rangle$, whose $RL$ reply is branch. Thus
the branch-output class also requires at least two transcripts. The
absent-output class is nonempty and requires at least one. These
disjoint classes give the lower bound five for arbitrary adaptive
finite procedures, without a call or word-length restriction.

For attainment use (NVC.7). Its only possible raw transcripts are

$$
\begin{gathered}
[(R,\alpha)],\qquad[(R,\beta)],\\
[(R,\mathsf{branch}),(RL,\alpha)],\qquad
[(R,\mathsf{branch}),(RL,\beta)],\qquad
[(R,\mathsf{branch}),(RL,\mathsf{branch})].
\end{gathered}
\tag{NVC.12}
$$

A branch at $R$ has a present left child, so no absent child case
occurs. All five transcripts are attained by (NVC.11). This proves
the exact minimum on the entire family. A three-valued output
cannot determine a transcript with at least five attained values,
which proves the final claim. $\square$

The theorem counts the actual raw sequence, not an optimal encoding
of its requested reply. The virtual response task intentionally merges
some actual traces; retaining those traces refines that task.
The five actual subtrees in (NVC.11) are the comparison witnesses of
[PPF, Theorem 3.2][PPF]. The distinction between an output code and
an acquired raw record, including a five-record single-child case,
is already present in [SLH, §43][SLH]. Those witnesses and that
distinction are credited; the use here fixes the scalar
one-substitution output and proves its exact full-family raw range
within the compiled-port analysis.

## 5. An acquired branch guard gives a different resource point

**Definition 5.1 (finite public guard menu).** For a fixed public
controller $M$, let $A=\operatorname{addr}[Q]$ be its finite set
of installed words, and put

$$
P=\{\operatorname{parent}(w):w\in A,\ w\ne\varepsilon\},
\qquad m=|P|,\qquad
g(t)_u=\mathbf1_{r_t(u)=\mathsf{branch}}\quad(u\in P).
\tag{NVC.13}
$$

The vector $g(t)$ is an additional source-bearing relation. Its
indexing order is public and fixed before acquisition. If several
late targets select different controllers, this definition applies to
a fixed public finite union of their installed menus; the later
target cannot be used during target-blind guard preparation.

**Theorem 5.2 (paid guard compilation).** Under Assumption 1.4,
source-blind preparation can acquire (NVC.13) with $m$ additional
actual Reads and exactly $\sum_{u\in P}|u|$ submitted letters.
It exports only the complete joint name $(e(t),g(t))$ through the
paid isolation/handoff service. Its exact attained alphabet is

$$
r_g=|\{(e(t),g(t)):t\in X\}|\le r2^m.
\tag{NVC.14}
$$

There is an explicit public controller with at most $2^mK$
installed states that reproduces the entire virtual output with
exactly one actual Read per virtual Read and no larger submitted
length on any visit. On a terminating run its call count is
$n_0+n_+$ and its letters are

$$
\ell_g=\ell-
\#\{\text{nonempty visits with }g(t)_{\operatorname{parent}(w)}=0\}
\le\ell.
\tag{NVC.15}
$$

The peak submitted length is at most the virtual peak. If a specified
public effective function of the old complete entry gives the guard
vector, no further source acquisition or retained-name distinction is
required.
No necessity of this particular vector, optimality of its price or
improvement of $M_1(D)$ is asserted.

Proof. Query each word in $P$ once, in public order, on the
unchanged actual source. Retain only its branch bit. This acquires
every source-bearing guard entry actually used and has exactly the
stated call and letter charges; peak guard-acquisition length is
$\max(\{0\}\cup\{|u|:u\in P\})$. All other accessible
dependence from this acquisition must be isolated or counted in the
complete joint name. Correlations between entry and guard are
retained in its actual image (NVC.14), not replaced by a free product.

Replicate the original $Q\sqcup H$ carrier for each possible bit
vector on $P$. Keep the vector fixed through a run. At an empty
word, Read that word and apply $F$. At a nonempty $w=ub$, if
$g_u=1$, select $w$ before its reply and return $F$ of that
reply: the acquired guard certifies its present parent branch. If
$g_u=0$, select $u$ and use the alpha, beta and absent cases of
(NVC.7). The branch reply on this latter edge is unreachable on a
truthful acquired vector; define its table arbitrarily to make the
controller total. Feed the computed virtual reply to the original
$\operatorname{next}$, retaining the vector. At $(g,h)$ output
the same complete $\operatorname{out}(h)$.

Theorem 2.2 proves correctness at every request, so induction gives
the same virtual path, termination and full output. The carrier is
the declared product of all $2^m$ bit vectors and all $K$ original
states, including unused states. Each visit now uses one actual
call; it submits either the virtual word or its parent. This proves
(NVC.15) and the peak bound. The entry is the injective image of
the pair $(e(t),g(t))$, so its exact complete range is (NVC.14).
If $g$ is a specified computable function of $e$, compute it
locally from that actually acquired entry. Its joint range then has
exactly $r$ values and no source call is needed to acquire it.
$\square$

The phrase “one Read” in this theorem includes the new acquired
guards in its premises. It cannot contradict Theorem 4.1, whose
entry is constant. The original target/count ordering and the
complete guard acquisition have to be verified separately for any
application to the all-count late-target task.

## 6. Source acquisition, existing witnesses and actual successors

**Proposition 6.1 (a sufficient paid finite-source entry producer).**
Fix public $D$ and public effective finite-output maps $e$ and $g$
of the complete syntax of $t\in\mathcal F_D$. An entry producer
can acquire both using the credited
$\operatorname{Acquire}(R,D)$ of [PPF, Lemma 4.1][PPF], with at
most $2^D$ actual calls, $(D+1)2^D$ letters and peak length
$D+1$. It can then export only the complete intended joint name
through the declared paid isolation service. If the full syntax has
already been acquired, computing these maps requires no additional
Read.

Proof. The acquired depth-$D$ table reconstructs the entire right
subtree under $h(v)\le D$, including its terminal leaf labels.
The wrapper is public. Evaluate the specified effective maps on
that reconstructed finite syntax and retain their joint value.
Other source-bearing work is removed from access by the supplied
isolation contract. The bounds and their actual original-root
implementation are the supplier's, not new optima. $\square$

For an arbitrary unbounded finite source, an actual reached-node
traversal similarly acquires its syntax before computing such maps;
it terminates pointwise but has no uniform source-size bound.
An arbitrary noncomputable finite-range entry map is not covered.
Neither reconstruction nor a proof of existence grants a free
source-specific installed program. If both Proposition 6.1 and the
guard construction are used, compute guards from the already acquired
syntax instead of charging a second compulsory acquisition that is
not needed.

**Application 6.2 (the exact supplied predecessor-controller
premises).** The committed definition
[`NativeLiteralMoore.NativeLiteralFeasible`][NLM] has witnesses
$Q,H,M$ and

$$
\operatorname{code}:\operatorname{ImageValues}(C)\to Q\sqcup H.
$$

For every eligible $v\in\operatorname{ImageValues}(C)$ and
$u\in\operatorname{OriginFiber}(P,C)$ it requires the actual
origin equation

$$
\rho u=\operatorname{evaluateRow}(\operatorname{extend}(C,\operatorname{values}(v)),C),
\tag{NVC.16}
$$

where $\operatorname{values}(v)$ forgets the membership wrappers
and is the underlying assignment written `v.val.val` in the supplied
definition, and a run of $M$ on $\rho u$, entered at
$\operatorname{code}(v)$, whose whole halt output is
$\operatorname{canonicalRow}(P,u)$. The definition also bounds
the entry range, total state count, calls and the sum of the actual
submitted lengths on that same run. Its owning [Blueprint
Scribe][NLB] makes the same runtime/predecessor distinction.

Given explicit finite public tables for that witness, an actual
eligible $u,v$ satisfying (NVC.16), and a genuinely acquired complete
entry $\operatorname{code}(v)$, Theorem 3.1 runs the response
computation on the stationary original $u$ instead. Its output is
the identical whole predecessor row. The simultaneous upper-budget
bridge is (NVC.10), or Theorem 5.2 after guard acquisition. This
is a conditional implementation of the supplied response witness.
It does not acquire $v$, its code, its origin equation or a
source-specific choice of $C$ merely from feasibility.

To cover sources needing different $C$ values one needs a public
catalogue and a genuinely acquired counted selector, with its code
and carrier costs. A nonconstructive existential witness is not an
installed public controller. Proposition 6.1 is a sufficient entry
producer only when the desired entry is specified effectively on the
acquired original syntax. Neither
`literal_moore_feasibility` nor `finite_literal_synthesis` supplies
the original late target, subsequent authentic-count ordering or
the original one-Read budget after unguarded compilation.

**Definition 6.3 (same-source actual run image).** A compiled run
prefix has one actual stationary source, the same supplied
source/epoch/type and original-root reference/permission contract,
its current phase state, and its actual ordered Read prefix. Each
reply, phase choice and successor comes from that one execution. The
actual image is the image of these prefixes, not independently
realizable source, work, reference, permission and history margins.

If a record-bearing realization is desired, explicitly supply an
authenticated same-source writer that appends $(w,r_t(w))$ on
each completed Read, plus lawful callable access and persistence.
With that service, at a running state $s$ let
$w=\operatorname{addr}_{\rm compiled}(s)$. The successor is

$$
(t,s,\tau)\longmapsto
\bigl(t,\operatorname{next}_{\rm compiled}(s,r_t(w)),
\tau\mathbin{+\!+}[(w,r_t(w))]\bigr),
\tag{NVC.17}
$$

with the reference/permission successor prescribed by that same
service contract. Induction constructs its entire reachable joint
image: initialize it from the actual paid entry and empty new
archive, then append each truthful event and its declared successor.
This is closure for this explicitly installed Read/writer system.
The archive length, content, accessible controls, allocation and timing
are additional complete state; the finite controller bounds do not
bound this augmented observer. Without that writer service the
mathematical prefix is not a callable archive or a verified PG34
memory realization.

**Proposition 6.4 (what descends at request completion).** On every
actual compiled run, forgetting the intermediate parent phase and
mapping completed requests to their virtual replies gives exactly the
virtual controller run and whole output. This projection does not
identify full actual raw labels, costs or archive successors with
those of the virtual run, and has no inverse from the requested
virtual reply to the raw transcript in the scalar instance of
Theorem 4.3.

Proof. The completion statement is the induction in Theorem 3.1.
The extra parent event and possible child event are the actual
labels counted in (NVC.9) and appended in (NVC.17). A virtual
one-request event need not have the same address or the same
number of events. Theorem 4.3 proves the absence of the claimed
inverse even on a fixed scalar task with three outputs. $\square$

Thus the simulation is a refinement after choosing a task that
forgets these intermediate events. A task observing every Read and
its original joint successor cannot declare them invisible merely
because the requested output agrees. This is exactly the scope
distinction needed before using [PG, §§34,39,43][PG]. Its
full-response task retains legality, success/failure labels, original
successors and archives, beyond a projected controller output.

**Convention 6.5 (full failure boundary).** All finite Read words
in this source interface are legal and return one of the four
labels. Every absent reply has an actual successor. There are no
executed hardware-failure, permission-revocation or crash outcomes in
these theorems. An unexecuted illegal action is different from
$\operatorname{some}(\mathsf{failure},s')$. To compile an
extension with such outcomes, one must specify and transport its
same-source full failure label, work/reference/permission successor
and archive effect. Formula (NVC.7) alone supplies none of these.
Using two actual Reads exceeds an original one-Read resource cap;
that mathematical resource violation does not create a recorded
runtime failure event. Halting itself makes no further Read.

## 7. Costs, attribution and the remaining observer

**Convention 7.1 (resource coordinates).** The unguarded compiler
preserves the attained complete-entry alphabet, increases installed
finite controller states as in (NVC.8), and charges actual calls and
whole submitted words as in (NVC.9). The guard compiler changes
the complete acquired alphabet to the joint image (NVC.14), charges
its preparation separately and uses one call per virtual visit.
Neither alphabet count is a total observer-memory measure. Installed
public address/transition/output tables, generation of those tables,
entry acquisition, transient workspace, complete output payload,
recording/access/persistence, authenticated root continuity, handoff
and isolation, internal execution work and physical scheduling retain
their own costs. Numeric tariffs for these services are unspecified;
no complete physical or monetary implementation cost is established.

**Supplier correspondence 7.2 (exact repository uses).**

| Supplier | Use and boundary |
| --- | --- |
| [ActualTreeReadoutAcquisition][ATR] and [owning Scribe][ATB] | `readout` is total on finite words; `Policy` is stationary; `paid` charges distinct addresses. This volume instead charges every invocation. Its `flip` is a comparison operation, not an installed update permission. |
| [NativeSixSourceMoore][NSM] | `Controller` and `Run` supply the complete finite-control/whole-output stationary semantics. A mathematical run trace is not accessible workspace. |
| [NativeLiteralMoore][NLM] and [owning Scribe][NLB] | Conditional predecessor feasibility on actual `substitution u.val`; whole output `canonicalRow P u.val`. The explicit acquired entry and origin equation remain necessary premises in Application 6.2. |
| [FixedTreeCommonExtension][FTE] and [owning Scribe][FTB] | Given leaf coordinates and full child-message tuples on a fixed `Full` tree; no native literal acquisition or original late-target port is inferred. |
| [PPF, §§4–7][PPF] | Credited actual acquisition, optimal preparation projections, exact-name acquisition and nonidentity source-domain obstruction. Proposition 6.1 reuses acquisition. |
| [AAR, §12][AAR]; [CBN, §2][CBN]; [SCE, §§5–6][SCE] | Credited prediction/finite spatial correspondences and common-table pooling costs. Per-request compilation does not acquire a pooled whole table. |
| [PG, §§34,38–39,43–44][PG]; [Atlas, §6.3][Atlas] | Common actual image and lawful successors, explicit actual-update services, corrected nonredundancy, and each-view kernel requirements. Response simulation does not discharge these conditions. |

**Literature correspondence 7.3 (primary executable-view and history
models).**

| Primary source | Verified scope and parameter correspondence |
| --- | --- |
| Greenwald, Moore, Pierce and Schmitt, *A Language for Bi-Directional Tree Transformations*, [author manuscript](https://www.cis.upenn.edu/~bcpierce/papers/lenses.pdf), Definitions 3.1.1–3.1.2 | `literature-attested`: partial get and put obey GetPut/PutGet; put receives the modified abstract view and the old concrete state or a missing-state argument. These operations and concrete access are premises, not native acquisition or update permissions. Theorem 2.2 is proved from original Read semantics instead. |
| Matsuda, Nguyen and Wang, *Lenses for Partially-Specified States*, [extended version](https://arxiv.org/pdf/2601.04573), Definitions 2–3; [DOI](https://doi.org/10.1007/978-3-032-22723-2_2) | `literature-attested`: i-posets describe partial specification; partial put and a designated merge operator govern lawful composition and duplicability. A merge operator is not actual copying, common-source history acquisition or a price theorem. |
| Lamport, *Refinement in State-Based Formalisms*, [primary technical note](https://lamport.azurewebsites.net/pubs/refinement.pdf), implementation discussion and auxiliary variables, PDF pp.6–7 | `literature-attested`: implementation by the stated refinement requires stuttering-invariant specifications; history and stuttering variables have distinct roles. Projected controller completion can ignore microsteps, whereas a full event/archive task observes their changes and requires a separate refinement proof. |
| Lamport, *Time, Clocks, and the Ordering of Events in a Distributed System*, [primary paper](https://lamport.azurewebsites.net/pubs/time-clocks.pdf), Clock Condition | `literature-attested`: happened-before implies increasing logical-clock values; the converse is not assumed. A count is neither an actual event nor a lossless encoding of our ordered Read history. |
| Lanese, Phillips and Ulidowski, *An Axiomatic Theory for Reversible Computation*, [arXiv:2307.13360v2](https://arxiv.org/html/2307.13360v2), Definition 3.2 and Proposition 3.8; [DOI](https://doi.org/10.1145/3648474) | `literature-attested`: causal equivalence allows swapping independent transitions and cancelling a transition with its reverse; causal consistency uses the stated well-foundedness/parabolic premises. Such a causal quotient can forget literal execution order, and reverse transitions are supplied operations. It cannot justify an inverse from current source or requested reply to our full actual trace. |
| van den Bos and Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [arXiv:1907.11034v2](https://arxiv.org/pdf/1907.11034v2), adaptive testing and compatibility | `literature-attested`: the finite state-identification model declares its input/output transitions, tests and compatibility relation. Here actual trees are candidate objects and literal words are tests; their particular response and acquisition prices are proved separately. |
| Prabhakaran and Prabhakaran, *Assisted Common Information with Applications to Secure Two-Party Computation*, [arXiv:1002.1916](https://arxiv.org/pdf/1002.1916), §II | `literature-attested`: iid correlated observations and an omniscient helper with rate-limited messages define an asymptotic agreement problem. Neither that helper nor common-information rates supply a zero-error single-source branch guard or a free shared transcript. |

The literature comparison includes partial-state lenses and axiomatic
reversibility as well as older state/refinement models. No exhaustive
search, global originality or formal-certification claim follows.
The quantified compiler and lower bounds rest on their ordinary
proofs; bounded exact checks of actual trees cannot replace them.

**Open problem 7.4 (original interface and four native views).**
The compiler supplies two concrete response interfaces: pay up to two
actual Reads per virtual request, or acquire a finite branch-guard
relation and pay one. A proposal preserving actual chronology must
also retain and price the raw event relation it claims to recover.
Theorem 4.3 shows that merely retaining the requested scalar reply
does not do this. A genuinely evolving register needs the separate
actual-update, permission and writer contracts of PG38/44; authentic
prediction $k$ is not an executed substitution count.

Neither interface proves four concrete natural views each having the
original task kernel. Mutual recovery and task sufficiency give only
the inclusion of PG43.1; nonredundancy is an additional obligation.
Full same-source history coverage, lawful whole successors including
executed failures, and coherent infinite-scale bonding/ThreadComplete
remain unproved. The original all-source/all-target/all-later-count
task, general $M_1(D)$, sharp $\lambda$ and effective all-size
certificates retain their original unresolved scope. No scalar,
finite-controller or guard-augmented result replaces them, and no
universal physics or ontological conclusion is asserted.

[PPF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PAID_PREPARATION_FRONTIERS.md
[AAR]: RECURSIVE_RELATIONAL_OBSERVATION_ADAPTIVE_ACQUIRED_REFERENCE_FRONTIER.md
[CBN]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_CONSTRUCTOR_BOUNDARY_NETWORKS.md
[SCE]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SELECTOR_COMMON_EXTENSION.md
[SLH]: RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md
[PG]: RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md
[Atlas]: RECURSIVE_RELATIONAL_OBSERVATION_ATLAS_STABLE_CORE_HOLONOMY.md
[ATR]: ../../../D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.lean
[ATB]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/ActualTreeReadoutAcquisition.scribe.cs
[NSM]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/NativeSixSourceMoore.lean
[NLM]: ../../../D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeLiteralMoore.lean
[NLB]: ../../../Blueprint/D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeLiteralMoore.scribe.cs
[FTE]: ../../../D5/S3/Observer/Separation/FixedTreeCommonExtension.lean
[FTB]: ../../../Blueprint/D5/S3/Observer/Separation/FixedTreeCommonExtension.scribe.cs

## 追加锚（本行以下为增补区）
