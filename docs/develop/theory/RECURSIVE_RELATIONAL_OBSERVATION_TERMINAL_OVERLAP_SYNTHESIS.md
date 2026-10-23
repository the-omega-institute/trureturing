# Automatic joint-prefix synthesis for terminal native overlaps

This volume gives a terminating ordinary mathematical algorithm for a
recognizable class of complete acquired signed inputs. It constructs its
source covers, classifies their forced finite residuals, and decides one
joint arithmetic cofinality condition. A positive answer produces actual
finite originals at every requested depth; a negative answer produces a
finite exclusion depth. No functional presentation or completed point is
supplied as an input.

The proofs are ordinary mathematics, not new Lean evidence. This is
reference input under `generic-v1`; definitions and numbered theorem/proof
blocks retain their full hypotheses. The volume is append-only after
integration, with additions below its final append anchor. General
residual-versus-constructor contact synthesis remains open.

## 1. The entire acquired source and the joint question

**Definition 1.1 (native carrier and original prefixes).** Let

$$
\mathcal T::=\alpha\mid\beta\mid\langle\mathcal T,\mathcal T\rangle,
\qquad
\rho\alpha=\beta,\quad
\rho\beta=\langle\beta,\alpha\rangle,\quad
\rho\langle u,v\rangle=\langle\rho u,\rho v\rangle,
\qquad T_n=\rho^n\alpha.
\tag{TOS.1}
$$

All sources are nonempty finite free ordered trees. The displayed $\rho$
is interpreted, not a free unary constructor. An address is a word in
$\{L,R\}^*$, with root $\varepsilon$. Its reply is
$r_u(p)\in\{\alpha,\beta,\mathsf{branch},\mathsf{absent}\}$.
Write $u\equiv_h v$ when these replies agree at every $|p|\le h$;
the inclusive prefix $p_h(u)$ includes absence below early leaves.

For a finite prefix-free cut $A$, the complete original row $R_A(u)$
consists of its ordered reached set, its concrete exterior with numbered
holes, and the equality partition of the entire reached subtrees. Every
repeated occurrence and every different-class inequality is retained.
An absent cut position contributes no hole. In particular the root cut
has a constant one-hole row, and the empty cut retains the whole source.

**Definition 1.2 (complete acquired input).** Fix
$I=(P,R,H_0,H_{\rm rel},Q,N)$. The old row $R$ is an attained whole
$P$-row. Literal records $(a,p,c)$ impose $r_{\rho^a u}(p)=c$.
A signed record $e=(a,p,b,q,\bowtie)$, with $\bowtie\in\{=,\ne\}$,
imposes

$$
\operatorname{Rel}_e(u)\iff
p\in\operatorname{Pos}(\rho^a u)\ \land\
q\in\operatorname{Pos}(\rho^b u)\ \land\
(\rho^a u)|_p\ \bowtie\ (\rho^b u)|_q.
\tag{TOS.2}
$$

Both signs require both endpoints. All lists retain repetitions and
constrain the same original. The entire source fiber and a full-row
stratum are

$$
\begin{aligned}
D&=\{u\in\mathcal T:R_P(u)=R,\ H_0(u),\
                 \bigwedge_{e\in H_{\rm rel}}\operatorname{Rel}_e(u)\},\\
D_r&=\{u\in D:R_Q(u)=r\}.
\end{aligned}
\tag{TOS.3}
$$

The old concrete exterior, old absent positions, all old class comparisons
and off-task constraints remain in $D$. A target label specifies the
whole exterior, reached set and partition, not selected equality bits.

**Assumption 1.3 (actual paid handoff).** For operational consequences
use exactly [ARH, Assumption 1.3][ARH]. Acquisition was paid on the same
source, original root and physical register. At entry that register has
authentically reached $\rho^N u$, with common $N$ at least all recorded
epochs. The entire accessible state is a common recoverable encoding of
$I$ and common parameters, with precisely fiber $D$. Every accessible
source-bearing cache, address, count, length, program position, timing
field, archive, output, permission and handle is included. This is an
access and source-continuity premise, not a physical-erasure measurement.

Services are deterministic, effective, terminating and correct on all
$D$. The source actions are paid four-valued original-root
$\mathsf{Read}(p)$, real same-register forward $\mathsf{ApplyRho}$, and
absorbing $\mathsf{Halt}$. Local computation and updates reveal no extra
source-dependent information. There is no chart, rank, equality, selected
source, old-version, reset, reroot, clone or clock port.

**Definition 1.4 (joint contact of alternative originals).** Supply a
finite set $B$ of distinct attained complete target rows, $|B|\ge2$.
Set

$$
J_B(h)\iff
\exists(u_r)_{r\in B}\in\prod_{r\in B}D_r\quad
\forall r,s\in B\quad u_r\equiv_h u_s.
\tag{TOS.4}
$$

Each $u_r$ is a different possible original satisfying one whole common
producer contract. Different target labels are not assigned to one
realization. One jointly shared prefix is required; unrelated pairwise
witnesses do not suffice. Fresh finite witnesses may be used at each
depth. This is [SJM, Definition 3.1][SJM]'s fixed-set question.

## 2. Automatic source covers and terminal recognition

**Definition 2.1 (exact mixed covers).** A chart has natural coordinates
$\mathbf n$, residual coordinates $\mathbf z$, one whole source map $U$,
and predicate

$$
\begin{aligned}
A&::=g\mid T_{n_i+c}\mid\rho^a z_j\mid\langle A,A\rangle,\\
C(\mathbf n,\mathbf z)&=P(\mathbf n)\land\Delta(\mathbf n,\mathbf z),
\qquad \Delta=\bigwedge_\ell A_\ell\ne A'_\ell,\\
D_r&=\bigcup_c\{U_{r,c}(\mathbf n,\mathbf z):C_{r,c}(\mathbf n,\mathbf z)\}.
\end{aligned}
\tag{TOS.5}
$$

Here $g$ is a fixed finite tree, $a,c\ge0$ are fixed, and $P$ is
Presburger. Before the complete negative conjunction the residual domain
is the entire Cartesian product $\mathcal T^m$. Repeated names inside
one chart share their values, including occurrences in negatives and
auxiliaries. Different alternative sources have separately renamed
coordinates. Zero-dimensional products contain their empty tuple.

Both inclusions in (TOS.5) concern the same original source: a chart point
has every guard, record, old-row constraint and exactly row $r$; every
$u\in D_r$ is reconstructed as that very $u$. A support section or a
witness subset is not a replacement for (TOS.5).

The covers are computed from $I,B$. The general route is [NIC, Theorems
3.2–3.3 and 4.3][NIC]. In its fixed-navigation step, enumerate original
prefix patterns strictly deeper than every fixed endpoint and cut word.
Their actual frontier subtrees reconstruct each source. Navigation at
the stipulated epochs decides every guard and literal, including born
and absent addresses. Masks with the reached sets impose each complete
exterior, and all reached-hole pairs impose each full partition. Keep
every frontier and auxiliary in the declared tuple.

NIC then flattens the positive equations, branches over atomic-code
collapses, solves the finite free *shape* equations, and connects the
offset blocks of each residual sort. A minimum-potential block gives one
native residual with nonnegative decorations. Its assembled codes may
be nonnormal, but expansion is sound for every residual in $\mathcal T$.
Conversely the actual normal blocks and ranks of an admitted source give
that same source in one branch. This is NIC's reason the pre-negative
domain is actually Cartesian. Pull back the original native negatives
after expansion; ambient code inequality is never a signed predicate.
These supplier steps give both whole-source directions of (TOS.5), not
merely exact scalar support. Fix any effective choices of branch order
and most general unifiers; recognition below need not be invariant under
all equivalent presentations.

There is also the finite structural source reduction in §5. It applies
when its displayed public acquired pattern matches, and constructs the
entire covers there directly. Use that route for this pattern and NIC
otherwise. Thus the input is always $I,B$, without a supplied cover,
functional system, finite barrier or completed point. In either route,
discard an empty chart only by the exact URR support test conjoined with
$P$; this preserves the whole union.

**Definition 2.2 (terminal-overlap recognition).** Choose one remaining
chart per $r\in B$. Compare their entire source expressions by equating
one reference expression to each of the others. Distribute fixed powers
through explicit pairs and evaluate fixed grounds. Cancel equal ordered
pair constructors on both sides, and decompose a fixed ground pair when
it faces an explicit pair. A fixed leaf facing an explicit pair, or two
unequal fixed grounds, is a clash. A clash makes that chart tuple's
completed common-output relation empty.

For a nonclash tuple, recognition succeeds precisely when every
remaining comparison is between terminals

$$
g,\qquad T_{n_i+c},\qquad \rho^a z_j.
\tag{TOS.6}
$$

An atomic or residual terminal facing an explicit pair is unresolved
by this recognizer. No occurs check treats $\rho$ as free. The
cancellations and ground decompositions are equivalences in both
directions on finite or completed native trees: native pair injectivity
gives the child equalities, and pairing reconstructs the parent. Hence
the collected terminal equations are equivalent to equality of all
whole outputs. Their original coordinate incidence is retained.

The input is recognized when every chart tuple either clashes or passes
this finite test. There are finitely many charts and comparisons, so
cover construction and recognition terminate. Failure of recognition
returns **unresolved**, never a finite exclusion or an undecidability
claim. The class is defined by this finite procedure, rather than by an
assumption that a functional presentation exists.

## 3. Effective finite-anchor classification

**Definition 3.1 (completion and scalar faces).** Let
$\widehat{\mathcal T}$ be the valid finite or infinite ordered tree reply
tables, with the finite-prefix topology. It is a closed subset of the
countable product of four-point discrete spaces: root presence, two
children of a branch, and absence below leaves or absent nodes are
closed finite-coordinate conditions. It is compact. Finite trees are
isolated by a prefix extending below their leaves. Let $\Omega$ have
branch at every address. Extend $\rho$ by its actual leaf replacements
and pair law. It fixes $\Omega$, preserves every infinite branch, and
is prefix-nonexpanding. The latter follows by navigation through the
shared original branches, or through identical early leaf replacements;
it includes absent replies. Pairing is a prefix guard; bare $\rho$
is not asserted to be a strict contraction.

By the supplied atomic recurrence, the minimum leaf depth of $T_n$ is
$\lfloor n/2\rfloor$. Induction on the recurrence proves this from
the two depth-zero leaves. Thus $T_n\to\Omega$ as $n\to\infty$.
Every mixed source map is continuous on
$(\mathbb N\cup\{\infty\})^k\times\widehat{\mathcal T}^m$, when an
infinite atomic coordinate means $\Omega$ and finite scalar points are
isolated.

For one recognized chart tuple choose a subset $K$ of its *original*
scalar names to diverge. All other scalar names have finite values
$\mathbf t$. Each occurrence of a divergent name becomes $\Omega$;
an occurrence of a finite name remains $T_{t_i+c}$. Sharing is not
changed by this choice.

**Theorem 3.2 (forced finite anchors and a canonical solution).** For
each such tuple and face $K$ one can compute a Presburger condition
$A_K(\mathbf t,\mathbf q)$ and residual values $f_K(\mathbf t,\mathbf q)$
on a fixed set $F_K$ of residual names. The additional natural tuple
$\mathbf q$ gives finite atomic indices, determined by $\mathbf t$
whenever $A_K$ holds. The terminal equations have a completed solution
at this scalar face if and only if
$\exists\mathbf q\ A_K(\mathbf t,\mathbf q)$.

When consistent, precisely the residual components incident to a finite
anchor are forced finite. Their values are exactly $f_K$ in every
solution. Every other component can simultaneously be assigned
$\Omega$, giving a computable canonical completed solution. The theorem
does not assert that all solutions have this canonical form.

**Proof.** Make a graph on all residual names, including unused ones.
For $\rho^a z_i=\rho^b z_j$, put an edge retaining both exponents.
Comparisons of a decorated residual with a ground or an atomic terminal
are anchors. Grounds and atomic terminals with finite scalar indices
are finite anchors; divergent atomic terminals are infinite anchors.
There may be loops, multiple edges and several anchors at a vertex.

Since $\rho^a$ preserves infinite branches, a finite value of either
edge side forces both residuals finite. Thus any component with a finite
anchor is finite throughout. A component with both a finite and an
infinite anchor is inconsistent.

For finite inversion reuse [ABC, Theorems 2.2–2.3][ABC] exactly. In the
normal code $B(g)$, $g$ lies in the image of $\rho^a$ precisely when
every primitive rank is at least $a$. Subtracting $a$ then gives the
unique finite preimage, still normal. This is inversion on that actual
image, never an inverse on arbitrary completions or a physical reset.

In a finite-anchored component choose a ground anchor if present.
The equation $\rho^a z_i=g$ gives either failure of this image test or
one fixed finite $z_i$. Along a spanning tree compute
$\rho^a z_i$ and its inverse under the other edge exponent. Each
step either fails or fixes the next finite residual uniquely. Test every
remaining edge and anchor; this includes cycles and parallel constraints.
A variable finite atomic anchor against a computed ground either fails
because the ground is non-atomic, or imposes the affine equality of its
index with the ground's primitive rank.

If there is no ground anchor, start from a finite atomic anchor
$\rho^a z_i=T_{t_j+c}$. Its preimage is $T_{q_i}$ with
$q_i+a=t_j+c$, $q_i\ge0$. Propagation along an edge gives
$q_i+a=q_j+b$, with every $q_j\ge0$. All additional edges and atomic
anchors give the same affine constraints. These natural auxiliaries
avoid informal subtraction at a negative index. A direct finite
atomic/atomic comparison gives equality of indices. Direct
atomic/ground comparison requires that ground to be atomic with the
same index. Ground/ground tests are finite exact tests. Two divergent
atomic terminals agree; a divergent and a finite terminal cannot agree.
These finite procedures construct $A_K$. They also compute every
forced value as a fixed ground or $T_{q_i}$.

In a component without a finite anchor assign every residual $\Omega$.
Every edge holds, regardless of its offset cycle, because every fixed
power fixes $\Omega$. Every infinite anchor holds too. Unused names
receive the same value. The direct terminal tests just imposed then
make all remaining equations true. This proves sufficiency.

Conversely any completed solution propagates finiteness from every
finite anchor. Unique finite inversion forces exactly the values just
computed, and every extra edge and anchor must pass the listed tests.
Its atomic indices provide $\mathbf q$ satisfying $A_K$. Components
without finite anchors admit the all-$\Omega$ solution, so none of
their vertices is forced finite. These arguments prove both directions
and the claimed classification. $\square$

## 4. Exact cofinal support and the terminating choice

**Definition 4.1 (one joint support sentence).** For a recognized
nonclash tuple and face $K$, substitute only its forced finite residuals
$f_K(\mathbf t,\mathbf q)$ into each chart's *whole* $\Delta$. Leave
all other residual names independent within that source. Grounds and
$T_{q_i}$ keep the syntax in the mixed grammar. [URR, Corollary 3.2][URR]
therefore computes its exact feasible support in all natural parameters;
conjoin every chart's $P$. Call the conjunction
$\Phi_K(\mathbf t,\mathbf q,\mathbf v)$, where $\mathbf v$ lists the
original scalar names in $K$. It means existence of finite residual
fillings satisfying all chart negatives at these same scalar values,
with forced finite values held exactly fixed. Independence between
alternative sources makes conjunction of these support tests exact.

Define the Presburger sentence

$$
\mathcal C_K:\quad
\exists\mathbf t\,\exists\mathbf q\quad
 A_K(\mathbf t,\mathbf q)\ \land\
 \forall b\in\mathbb N\ \exists\mathbf v\quad
 \left[\Phi_K(\mathbf t,\mathbf q,\mathbf v)
           \land\bigwedge_{i\in K}v_i\ge b\right].
\tag{TOS.7}
$$

Every finite scalar and forced finite atomic index is fixed **before**
all lower-bound requests. One joint tuple meets all coordinate bounds.
Equal individual supports or separately unbounded marginals cannot
replace this sentence. For example the Presburger support
$\{(v_1,v_2):v_1=0\text{ or }v_2=0\}$ has both marginals unbounded
and has no jointly cofinal tuple for $b>0$. If $K$ is empty, (TOS.7)
reduces to finite support nonemptiness.

URR supplies exact support, not a whole-image replacement by its
separator. The unforced residuals remain free for the later prefix
construction. Arithmetic quantifier elimination decides (TOS.7): the
integer formulation in [Haase et al., §2 and Corollary 3][PA] covers
Boolean affine constraints; natural quantifiers are integer quantifiers
guarded by nonnegativity. Eliminate blocks from inside out, rewriting
universals by negated existentials. Once truth is decided, enumeration
of finite $\mathbf t,\mathbf q$ with their remaining decidable sentence
extracts witnesses and terminates in the true case. Likewise a true
finite-bound support query extracts $\mathbf v$. No complexity or
uniform cost bound is inferred.

**Theorem 4.2 (existential completeness of the canonical choice).**
For a fixed recognized chart tuple, there are finite chart points with
one common whole-output prefix at every depth if and only if
$\mathcal C_K$ holds for at least one scalar face $K$. Consequently the
canonical all-$\Omega$ choice on unanchored components is complete
for this existential question, even when other completed solutions have
additional finite coordinates.

**Proof.** First assume arbitrarily deep joint finite witnesses in this
fixed tuple. Choose witnesses at increasing depths. The finite product
of the compact scalar spaces $\mathbb N\cup\{\infty\}$ and compact
tree completions has a convergent subsequence. This can also be obtained
by successive finite-coordinate subsequences and a diagonal sequence.
Continuity of all whole source maps and increasing prefix agreement
make their completed outputs equal. The equivalent terminal equations
therefore hold on that limit.

Let $K$ be its divergent original scalar names. The other scalars
eventually equal one fixed $\mathbf t$. Theorem 3.2 forces every
finite-anchored residual to the computed $f_K$, with one finite
$\mathbf q$. Since each such finite tree is isolated, the subsequence
eventually has those exact values, not merely close prefixes. For any
$b$, sufficiently late finite witnesses have all $v_i\ge b$ and still
satisfy every original chart negative and policy. Hence they witness
$\Phi_K$ at this same $\mathbf t,\mathbf q$, proving (TOS.7).

Some unanchored residuals in the extracted limit may also be finite.
Removing these additional finite restrictions enlarges the existential
support. The proof has imposed only the values that every terminal
solution at this scalar face must have. Assigning $\Omega$ to all
remaining components still satisfies every terminal equation by Theorem
3.2. Thus necessity does not assume the extracted limit was canonical;
it proves that an available contact always permits the canonical choice
with adequate signed finite support. No negative is extended to a limit.

Conversely suppose (TOS.7) holds, and fix its $\mathbf t,\mathbf q$.
Theorem 3.2 gives a canonical residual tuple with $f_K$ on $F_K$ and
$\Omega$ elsewhere. At the scalar face its whole source outputs are
one common completed tree $W$.

For a requested $h\ge0$ put $b=2h+2$ and choose one $\mathbf v$
witnessing (TOS.7). Every divergent atomic terminal at these finite
values has minimum leaf depth at least $h+1$ and agrees with $\Omega$
through $h$. Finite scalar terminals and forced residuals already have
their exact canonical values. At these very same ranks every chart's
full substituted negative conjunction is feasible, by $\Phi_K$.

Apply [SLP, Lemma 2.1][SLP] separately to each alternative source,
prescribing $p_h(\Omega)$ on its remaining residuals and keeping $f_K$
exactly fixed. Its premises hold: these residuals range over the full
Cartesian carrier before the negatives, there is a finite seed at the
chosen ranks, and the prescribed completion for each unfixed name is
infinite. The construction uses one prefix context per name and shares
that context and filling at every repeated occurrence. It returns one
finite tuple satisfying *all* negatives of that chart together.

Fixed powers are prefix-nonexpanding; pairing and ground evaluation
preserve the required output prefixes. Induction on each source template
shows its actual finite output agrees with $W$ through $h$. The chart's
forward source correspondence puts it in exactly $D_r$, with every
actual-epoch guard and signed constraint. All outputs therefore have one
common original prefix. Every step is effective and terminates for this
requested $h$. The completion $W$ has neither a retained negative nor a
finite-source partition assigned to it. This proves sufficiency and the
existential completeness claim. $\square$

**Theorem 4.3 (automatic exclusion or finite realization).** For every
input recognized by Definition 2.2, there is a terminating mathematical
algorithm deciding $\forall h\ J_B(h)$ and returning exactly one of:

1. A finite $H$ with $\neg J_B(H)$.
2. An effective construction that, for each requested $h$, returns one
   actual finite $u_r(h)\in D_r$ for every $r\in B$, all sharing $p_h$.

All whole-source, full-row, rank and residual sharing requirements of
§1 are retained. The construction takes $I,B$, not contact certificates.

**Proof.** Compute the complete covers and their finite recognition
tests. For each nonclash chart tuple and each of its finitely many scalar
faces compute (TOS.7). Decide their finite disjunction.

If one sentence is true, extract its fixed finite data and apply Theorem
4.2's finite construction for every requested depth. The chart forward
maps establish membership in the corresponding entire strata.

For the converse, the exact covers reconstruct every joint finite
source witness in some chart tuple. There are only finitely many tuples,
and each tuple's prefix feasibility is downward closed in depth. If
every tuple failed at some depth, the maximum of those failed depths
would exclude every tuple and hence $J_B$. Thus $\forall h\ J_B(h)$
forces one fixed tuple to have witnesses at every depth. It cannot be
a clash tuple, and Theorem 4.2 makes one of its sentences true. This
proves both directions of the disjunction test on the whole source fiber.

If the disjunction is false, the same argument proves that some finite
exclusion depth exists. Run the exact multi-source fixed-depth query
for $h=0,1,2,\ldots$ and stop at its first false answer. [SJM, Theorem
3.2, fixed-set proof][SJM], using [NSF, Lemma 5.1 and Theorem 5.2][NSF],
decides this query on $|B|$ independent whole-source copies with their
specified complete rows and identical four-valued prefix replies.
Each query terminates, and the already decided negative alternative
proves that this search terminates. Thus it is not a test sequence
being mistaken for a persistence certificate. The two branches are
sound, complete and terminating on the recognized class. $\square$

## 5. An entire acquired residual-visible family

**Definition 5.1 (a finite recognizable producer pattern).** Put

$$
V(t,x,w)=\langle t,\langle x,\langle w,
                       \langle\rho t,t\rangle\rangle\rangle\rangle,
\qquad Q=\{L,RL,RRL,RRRL,RRRR\}.
\tag{TOS.8}
$$

Take $P=\{\varepsilon\}$ with its attained one-hole row. The retained
epoch-zero literals are branch at $\varepsilon,R,RR,RRR$. Retain
the following whole-subtree records:

$$
\begin{gathered}
(0,RRRL,1,L,=),\quad(0,RRRR,0,L,=),\quad
(0,RRR,2,L,=),\\
(0,RRL,0,L,\ne),\quad(0,RRL,1,L,\ne).
\end{gathered}
\tag{TOS.9}
$$

Allow also any finite list $\mathcal H$ of negative records whose
endpoints are *structural*: each original word follows this four-node
outer skeleton and stops at one of its nodes or five holes, without
entering an unspecified hole. Their epochs are any fixed finite numbers.
Every such endpoint remains reached under its recorded iterate, and
its whole value is a fixed native expression in the five hole values.
Let $N$ authentically be at least two and every additional epoch.
The finite recognizer checks these coordinates, signs, cut and complete
root row; repetitions are permitted and retained. The case
$\mathcal H=\varnothing$ will give the explicit inhabited example.

**Proposition 5.2 (automatic entire-source reduction and full rows).**
For this pattern the exact whole fiber is

$$
D=\{V(T_n,x,w):n\ge0,\ x,w\in\mathcal T,\
 w\ne T_n,\ w\ne T_{n+1},\ H(n,x,w)\},
\tag{TOS.10}
$$

where $H$ is the entire pulled-back additional negative conjunction.
There are at most four full target rows. They have the same reached set
$Q$ and exterior

$$
\langle\square_1,\langle\square_2,\langle\square_3,
                            \langle\square_4,\square_5\rangle\rangle\rangle\rangle.
\tag{TOS.11}
$$

Their possible partitions and exact chart substitutions are

| Row | Complete partition | Substitution and remaining whole negatives |
| --- | --- | --- |
| $r_0$ | $\{\{1,2,5\},\{3\},\{4\}\}$ | $x=T_n$; $w\ne T_n,T_{n+1}$ and $H(n,T_n,w)$ |
| $r_1$ | $\{\{1,5\},\{2,4\},\{3\}\}$ | $x=T_{n+1}$; $w\ne T_n,T_{n+1}$ and $H(n,T_{n+1},w)$ |
| $r_w$ | $\{\{1,5\},\{2,3\},\{4\}\}$ | $x=w$; $w\ne T_n,T_{n+1}$ and $H(n,w,w)$ |
| $r_d$ | $\{\{1,5\},\{2\},\{3\},\{4\}\}$ | $x\ne T_n,T_{n+1},w$; $w\ne T_n,T_{n+1}$ and $H(n,x,w)$ |

These are whole-stratum correspondences in both directions. Exact URR
support removes precisely the empty rows and produces finite realizing
sources for the others. For every attained $B$ these computed charts
pass terminal recognition, so Theorem 4.3 applies automatically.

**Proof.** The four literals uniquely write any admitted original as
$\langle t,\langle x,\langle w,\langle a,b\rangle\rangle\rangle\rangle$.
Every listed endpoint follows this skeleton and is originally reached.
Original branches persist under $\rho$, so the first two positive
records give $a=\rho t$ and $b=t$. The third gives
$\rho^2t=\langle\rho t,t\rangle$. The exact finite stability
classification [ARH, (ARH.4.4)][ARH], supplied by
`SourceTransportCentralizer.source_transport_centralizer`, says precisely
$t=T_n$ for some $n\ge0$. This is an acquired constraint on an interior
subtree, not a whole-source atomic promise. The two negatives become
exactly the displayed inequalities for $w$. Each additional record is
evaluated at its own actual epoch on this same expression, yielding
$H$ with every repeated name retained.

Conversely every finite tuple in (TOS.10) has all four literals and the
entire root old row. Atomic recurrence gives
$\rho^2 T_n=\langle T_{n+1},T_n\rangle$, proving all three positive
records. Both endpoints of every base and additional record are reached
and persist, so their signs are precisely the stated whole negatives.
Thus (TOS.10) reconstructs the same original and proves the reverse
source inclusion, with no omitted guard.

The five reached hole values are $T_n,x,w,T_{n+1},T_n$.
The atomic indices are distinct, and $w$ differs from both atomic
values. Therefore $x$ equals exactly one of $T_n,T_{n+1},w$, or differs
from all three. These four alternatives exhaust all full partitions.
Substitution yields each table row; conversely its complete partition
forces that substitution and every remaining distinct-class comparison.
The other rows remain in $D$ when selecting $B$. All residuals before
the negatives range over their full independent carrier. Whole negative
expressions stay mixed after each substitution, so URR gives exact
support and finite attainment rather than a witness-only cover.

This is a finite procedure on the acquired pattern: skeleton
decomposition, positive variable substitution, the supplied stability
classification, full partition enumeration and exact support tests.
For any tuple of its row charts, whole output cancellation leaves only
comparisons among $T_n,T_{n+1}$ and its residual names. Every occurrence
uses its chart's same $n$ and repeated residuals. All comparisons are
terminal. Thus class membership and the entire covers are established
from $I$, without a supplied functional or completed presentation.
$\square$

[ARH, Proposition 2.1][ARH] supplies an actual public paid producer for
precisely these coordinates: obtain the whole old row, traverse the
endpoint subtrees at epochs zero, one and two and any additional epochs,
compare their paid descriptions, advance the same register to $N$, and
perform the stipulated complete cut. Every source in (TOS.10) produces
this retained successful input, and every source producing it belongs to
(TOS.10), conditional on Assumption 1.3. Invalid endpoints have a
different producer outcome. Traversal lengths and descriptions are
paid acquisition fields; none survives as an undeclared selector.

**Proposition 5.3 (visible residuals, indispensable ranks and no whole
atomic anchor).** With $\mathcal H=\varnothing$, all four rows in the
table are attained and the table is the entire finite row image.
Each selected stratum $D_{r_0},D_{r_1}$ contains all natural ranks,
has an unrestricted residual before its two negatives, consists of
non-atomic whole sources, and has unbounded constructor mass. Neither
stratum has a finite exact rank-free negative-chart cover of FJC
Definition 2.1. For $B=\{r_0,r_1\}$, every depth has joint finite
witnesses, while no bounded section of either original rank coordinate
can retain those witnesses at all depths.

**Proof.** For attainment take $n=0$, $w=\langle\alpha,\alpha\rangle$,
and choose respectively $x=\alpha,\beta,w$, or a tree distinct from
those three. These give exactly the four complete partitions. At every
$n$, positive constructor-mass residuals differ from $T_n,T_{n+1}$,
so both selected strata retain every rank.

Use the native canonical constructor mass $\gamma$ from [URR,
Definition 2.1][URR]: atoms have mass zero, fixed powers preserve mass,
and a pair with a positive-mass child has mass one plus its child masses.
The last pair of $V$ is $T_{n+2}$. If $w$ has positive mass $M$, the
whole source in either selected stratum has mass $M+3$. The finite
combs $C_0=\alpha$, $C_{j+1}=\langle C_j,\alpha\rangle$ have
$\gamma(C_j)=j$, so these whole-source masses are unbounded.

For any allowed $w$, the pair $\langle w,T_{n+2}\rangle$ is either
non-atomic, or, by the normal-code exceptional-pair rule, $w=T_{n+3}$
and its value is $T_{n+4}$. In the first case the two containing pairs
give positive whole mass. In the second the next pair has left child
$T_n$ or $T_{n+1}$ and right child $T_{n+4}$, so it cannot collapse;
the outer pair also has positive mass. Thus every source in either
stratum is non-atomic. Their positive records constrain an interior
rank; they do not put their entire outputs in an atomic orbit.

Suppose one feasible rank-free whole negative chart were contained in
one selected stratum. Apply NSF's finite fixed-navigation decomposition
to its source expression at $L$: decompose each original residual into
finitely many prefix contexts strictly beyond this word, retain the
same context and frontier at repeated uses, and distribute fixed powers.
Each case has the full Cartesian frontier carrier before its substituted
whole negatives. Its reached left subtree is a rank-free expression in
these frontiers. This is a finite exhaustive decomposition of the chart,
not a choice of convenient fillings.

On any inhabited case that left expression must always be atomic. If it
contains a residual frontier, URR's equality-reflecting separator can
choose any common mass $G$ above its finite syntax bound and still
satisfy the entire feasible negative conjunction, as in [FJC, Theorem
7.1][FJC]. Fixed powers and pairs never decrease this positive mass, so
the left expression then has mass at least $G>0$, a contradiction.
Thus every inhabited case fixes one finite left subtree, hence one
rank. Each rank-free chart fixes only finitely many ranks after this
finite decomposition. A finite union fixes finitely many, whereas both
entire strata attain every $n$. This proves the exact rank-free-cover
obstruction, not an obstruction to arbitrary representations.

For the terminal algorithm, compare the $r_0$ chart with rank $n$ and
residual $w$ to the $r_1$ chart with rank $m$ and residual $v$.
Cancellation gives, with their repetitions,
$T_n=T_m$, $T_n=T_{m+1}$, $w=v$, and
$T_{n+1}=T_{m+1}$. The face $K=\{n,m\}$ assigns all atomic
terminals and the residual component $\Omega$. There is no finite
anchor. Its joint support is all $\mathbb N^2$, since positive-mass
residuals satisfy both negatives at every rank. Hence (TOS.7) is true.

For explicit finite witnesses at depth $h$, choose $n=m=2h+2$ and
let $w=v$ be the perfect binary tree of height $h+1$ with $\alpha$
leaves. It has positive constructor mass and branch at every address
through $h$. The two originals are $V(T_n,T_n,w)$ and
$V(T_n,T_{n+1},w)$. They satisfy the entire input, exactly the two rows,
and share $p_h$. Their possibly unequal atomic values have no leaf
through that depth. This is one jointly faithful finite construction.

Finally suppose witnesses at unbounded depths could keep $n\le C$.
There is a subsequence with one fixed $n$. At $L$, sufficiently deep
agreement isolates that finite $T_n$, forcing the other rank $m=n$.
At $RL$, still deeper agreement would then equate $T_n$ with
$T_{n+1}$, which is impossible. The same argument starts from bounded
$m$. Thus each original rank must escape every fixed bound along
arbitrarily deep joint witnesses. Whole residual mass cannot erase this
constrained interior rank. $\square$

## 6. Whole-row recovery and paid resources

**Corollary 6.1 (the actual same-register consumer).** Under Assumption
1.3, a positive outcome for any attained $B$ of size at least two
excludes a uniform finite-new-read service recovering the whole $R_Q$
on $D$, even with lawful serial forward updates. A negative outcome
excludes only this selected joint set $B$ at the returned depth.

If the entire attained row image is finite, and every distinct pair in
that image is recognized, the pair decisions give a complete choice
between a persistent different-row pair and a determining original
depth. In the latter case there is a lawful static whole-row service
at authentic $N$, with the sufficient post-entry bounds

$$
q\le2(2^{H+1}-1),\qquad a=0,\qquad
\ell\le2(2^{H+1}-1)(H+\lceil N/2\rceil).
\tag{TOS.12}
$$

**Proof.** A joint positive outcome supplies a different-row pair at
every depth. Thus no depth determines the whole row. Apply [ARH,
(ARH.2.3)][ARH] on precisely its complete-state and action premises to
exclude every uniformly bounded serial or static new-read service.
This uses actual finite counterpairs, not a signed infinite source.

For positive recovery, first obtain the *entire* finite attained row
list and actual realizing originals from [NPL, Theorem 5.3][NPL].
Apply Theorem 4.3 to every distinct pair. A positive pair gives the
preceding exclusion. Otherwise take the maximum $H$ of every pair's
exclusion depth, zero if there are no pairs. Downward closure and the
full row list show that equal $p_H$ implies equal complete row on all
$D$. An exclusion for one larger selected $B$ alone would not prove
this implication.

At the actual register $\rho^N u$, use the supplied original decoder
to obtain every original reply $|p|\le H$, with at most two paid
current reads of length at most $H+\lceil N/2\rceil$ per original
word. Then finite whole-source feasibility, or source enumeration on
the entire conditioned $D$, returns a matching original whose whole
row is the constant correct output on that conditioned fiber. The
actual source proves that this local search terminates. [NSF, Theorem
6.1][NSF] gives (TOS.12). No mathematical chart parameter was read.
$\square$

If NPL returns an infinite whole-row image, the existing finite-reply
argument already excludes uniformly bounded whole-row reads. If a pair
is not recognized, this volume leaves its all-depth decision unresolved.
The merged [SJM, Theorem 3.2][SJM] may use fixed-set choices for all
required subsets to determine its conditional field cardinality; that
is its exact source boundary, not a new minimum-memory theorem here.

Paid full traversal of the actual finite current tree, followed by local
normal-code inversion at its authentic $N$, still gives sourcewise
finite recovery. This does not imply a uniform new-call, literal-word,
local-computation, preparation, memory or retention bound. Pre-cut
acquisition, uniform new reads, actual submitted words, forward updates,
local work, installation, working memory and retained descriptions are
separate charges. Neither finite inverse mathematics nor the offline
witness construction is a runtime old-version read or a free source
selector. No optimal budget or physical spacetime reconstruction follows.

## 7. Sources, evidence scope and the remaining problem

**文献与来源表态。** The new content is the automatic terminal-graph
finite-anchor classification, the existential completeness of its
canonical unanchored choice, and its quantified full-support synthesis
with the acquired family above. These are `repo-derived` ordinary
derivations. The ingredients below retain their own hypotheses and
credit; there is no literature-wide priority claim.

| Source | Exact contribution and transfer boundary |
| --- | --- |
| [ARH, §§1–2 and (ARH.4.4)][ARH] | Whole guarded acquired fiber, both paid-producer directions, same-register service/prefix equivalence, and finite interior stability classification. Complete accessible-state factoring and authentic epoch remain operational premises. |
| [ABC, Theorems 2.2–2.3][ABC] | Finite normal-code bijection and fixed-$\rho$ image inversion by primitive-rank subtraction. No inverse on arbitrary completions or physical backward action. |
| [NSF, Lemma 5.1 and Theorems 5.2, 6.1][NSF] | Exact fixed-coordinate whole-source navigation, signed finite feasibility and the supplied-depth actual consumer. Increasing finite tests alone do not settle persistence. |
| [NIC, Theorems 3.2–3.3, 4.3 and Proposition 3.5][NIC] | Complete mixed whole-source covers with the actual Cartesian pre-negative domain and native signed pullback. Support sections do not replace those images. |
| [URR, Theorem 3.1 and Corollary 3.2][URR] | Exact simultaneous negative support in fixed ground/atomic/mixed syntax. It supplies no unknown finite-barrier or whole-image replacement. |
| [SLP, Lemma 2.1, Theorem 3.1 and Corollary 3.2][SLP] | Finite signed prefix lifting at feasible fixed ranks and finite barriers. This volume proves the automatic barrier classification and existential contact completeness needed before invoking it. |
| [FJC, Definition 2.1 and Theorem 7.1][FJC] | Rank-free whole negative-chart format and the mass separation method used in the interior projection obstruction. Its supplied functional class is not assumed universal. |
| [NPL, Theorem 5.3][NPL] | Exact entire finite/infinite row-image decision and original realizing sources; required for whole-row recovery rather than selected-set exclusion. |
| [SJM, Definition 3.1 and Theorem 3.2][SJM] | Fixed-set multi-source query and the distinction between one set's exclusion, all-pair determination and all-set conditional alphabet optimization. No global optimizer is reproduced here. |
| [Haase–Krishna–Madnani–Mishra–Zetzsche, *An efficient quantifier elimination procedure for Presburger arithmetic*, arXiv:2405.01183v1, §2 and Corollary 3][PA] | `literature-attested`: elimination of existential integer Presburger formulas. Nonnegative guards and negation give the finite alternating sentence (TOS.7). This transfers only after the proved native reduction, with fixed integer coefficients; no product of unknown scalars, transducer equivalence or native synthesis theorem is imported. |

**核验边界。** Owning public and private D5 sources were searched and
their relevant types and proof boundaries inspected:
`SourceTransportCentralizer.source_transport_centralizer`;
`NativeDepthPatterns.original_present_transport`,
`original_prefix_locality`, `depthEquiv`, and private
`fill_decompose`/`decompose_fill`;
`NativeCutFibers.legal_values_row`, `rowFiberEquiv`, and private
`filled_exterior`, `recover_fill`, `fill_injective`,
`classValue_distinct`;
`NativeHistoryCells.cell_feasibility_exact`, `historyCellEquiv`, and
private `syntax_iff_ground`, `sourceCell_right`, `cellSource_injective`;
`NativeGroundSeparation.simultaneous_ground_separation` and its private
mass helpers; and `DelayedOriginalReadout.original_decoder_correct`,
`original_decoder_service` and their private presence/query bounds.
These are their actual finite-source, literal-history, separator and
decoder interfaces. They are not textual evidence of a newly compiled
arbitrary signed contact solver. No Lean compilation, numerical
experiment or software solver is part of this volume.

**开放问题 7.1 (general nonterminal contact synthesis).** For arbitrary
complete acquired $I$ and arbitrary finite attained full $B$, construct
a terminating, sound and complete exclusion-or-finite-realization
choice when exact mixed covers retain residual-versus-constructor or
atomic-versus-constructor overlaps. Multiple image restrictions,
nonfunctional feedback, unknown finite barriers and shared rank/residual
occurrences must be retained on the entire source strata. The terminal
recognizer supplies no reduction of these cases. Failure to recognize
an input is unresolved; neither novelty nor undecidability follows from
an unsuccessful search. This finite recognized-class result leaves the
broader space/time/boundary/memory research goal active.

[ARH]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_RELATION_HISTORY.md
[ABC]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_BLOCK_CONJUGACY.md
[NSF]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_SIGNED_FEASIBILITY.md
[NIC]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_IMAGE_COVER_AND_PREFIX_COST.md
[URR]: RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_RESIDUAL_REALIZATION.md
[SLP]: RECURSIVE_RELATIONAL_OBSERVATION_SIGNED_LOCAL_PREFIX_LIFTING.md
[FJC]: RECURSIVE_RELATIONAL_OBSERVATION_FUNCTIONAL_JOINT_CONTACT.md
[NPL]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_PROJECTION_LIMITEDNESS.md
[SJM]: RECURSIVE_RELATIONAL_OBSERVATION_SIGNED_JOINT_MEMORY.md
[PA]: https://arxiv.org/html/2405.01183v1

## 追加锚（本行以下为增补区）
