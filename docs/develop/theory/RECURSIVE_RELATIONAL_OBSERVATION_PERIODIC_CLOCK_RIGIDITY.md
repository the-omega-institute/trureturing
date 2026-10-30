# Recursive Relational Observation: Periodic Clock Rigidity and Acquired Spatial Recovery

## 1. The actual source and the local comparison domain

**Definition 1.1 (retained physical meanings).** The source is the actual
alpha-origin source of [GPO, Definition 27.1][GPO], in its original class
$\mathscr R_d$ of GPO Definition 29.1. Physical links persist and are ordered
$a<b$. An old alpha becomes beta; an old beta branches into one alpha and
one beta, with beta at $a$ precisely when the consumed bit is one. Only old
leaves are updated. Births in one update consume consecutive source bits
in the physical lexicographic order of their parent addresses. Write
$z_j=s_{j-1}$, with the original alignment to the first actual birth, and
$F_0=0,F_1=1,F_{k+2}=F_{k+1}+F_k$.

Use [ACR, Theorem 27.3][ACR]'s unique decomposition $s=y+t$: the transient
$t_i$ vanishes for $i\ge a$, and the aligned core $y$ has a least monic
annihilator $g(E)$ with $g(0)=1$ and $a+\deg g\le d$. At zero, take
$g=1$ and degree zero. The core is periodic: its companion transition is
invertible on a finite binary state space. Its least positive period is
always denoted by $p$, including $p=1$ for either constant. The zero stream
has degree zero; the all-one stream has degree one. A presented positive
period $u$ need not be least. Periodic sequences are extended to integer
indices by their unique periodic extension whenever an index is reduced
modulo a period.

**Definition 1.2 (a genuinely core-only normalized cone).** Fix one actual
physical prefix $v$. Its immutable descriptor and branch time are those
of ACR Definition 27.1. Put $e=\tau_v-1$. At actual cut $e$, the cone is a
single beta leaf. Local normalized cut $T$ means actual cut $n=e+T$,
where $T\ge0$; its rank is $T+1$, rather than $T$. Write $S_T(v)$ for its
support in relative physical words, keeping the order $a<b$ and forgetting
all labels. Its exterior preceding forest is ACR (ACR.112)'s forest.

The core-only condition means that **every** subsequent birth in this
cone consumes its bit from the aligned core at its original global index:
$z_j=y_{j-1}$ at all these events. A sufficient source condition is that
its first index exceed $a$, and a source-independent sufficient condition
under the public order promise is that it exceed $d$. Another sufficient
condition is the physical-depth frontier of ACR Theorem 27.3. Earlier
births used to create $v$ need not be core births. Eventual periodicity
without this cutoff is insufficient. This condition is an authentic
premise, or a conclusion of a separate proved supplier; a local support
or a proposed periodic word alone does not certify it.

**Definition 1.3 (two clocks and the actual batch words).** Let $I_k$ be
the first global birth index in the cone in normalized update $k\ge1$.
ACR Theorem 27.2 gives the exact integer equations

$$
 I_k=F_{e+k}+L_v(e+k-1),\qquad
 I_{k+2}=I_{k+1}+I_k,\qquad A_1=I_1,\quad A_2=I_2,
 \tag{PCR.1}
$$

where $L_v$ counts beta leaves in the preceding exterior forest. There
are $F_k$ births in this batch. Define its **ordered chronological word**

$$
 W_k=(z_{I_k},\ldots,z_{I_k+F_k-1})
     =(y_{I_k-1},\ldots,y_{I_k+F_k-2})
 \tag{PCR.2}
$$

on a core-only cone. The word lists actual simultaneous births from left
to right, not births along a semantic traversal. In particular the first
and second batch each have length one. Consecutive batches need not be
adjacent intervals of the global stream: exterior births occur between
them. No index or word in this definition is an extra Read reply.

For hypothetical local trials, any pair in $(\mathbb Z/u\mathbb Z)^2$
may be used as $A_1,A_2$. Extend it by the Fibonacci recurrence, form
(PCR.2) by periodic indexing, and feed the batch words to the same local
beta-origin replacement rule. These trials are finite local mathematical
models. Their definition asserts no realization by an exterior forest,
actual alpha-origin source, or chosen physical prefix.

## 2. Exact finite-cut correspondence

**Theorem 2.1 (support is exactly the visible chronological batches).**
At a common normalized cut $T\ge0$, for any two beta-origin local
histories with the stipulated chronological order, regardless of a law
promise,

$$
 S_T=S'_T\quad\Longleftrightarrow\quad
 W_k=W'_k\text{ for every }1\le k\le T-1.
 \tag{PCR.3}
$$

An empty range imposes no condition. There are finite maps between this
ordered support and $(T,W_1,\ldots,W_{T-1})$. They recover every visible
parent address, its normalized update and orientation. By contrast, the
full labelled state at $T$ is equivalent to $(T,W_1,\ldots,W_T)$.
The latest batch $W_T$ has $F_T$ orientation bits for $T\ge1$; these are
structurally invisible in presence-only support. There are
$2^{F_{T+1}-1}$ supports at fixed $T\ge1$ when all batch assignments are
allowed. At $T=0$ there is one support and one beta root.

Proof. A beta-origin orbit after $T$ updates has $F_{T+2}$ leaves,
regardless of orientations. These counts are strictly increasing for
$T\ge0$, so complete support also determines $T$. The full binary node
count is $2F_{T+2}-1$. A parent branching in update $k$ has final rank
$T+2-k$. Its child subtrees have ranks $T+1-k$ and $T-k$. For
$k\le T-1$ their leaf counts $F_{T+2-k},F_{T+1-k}$ are unequal, and their
physical order recovers the bit. For $k=T$ both children are terminal,
so their supports are the same in either order. Equivalently, their
maximum depths differ by one exactly when the parent rank is at least
three; this is [NRW, Lemma 1.4][NRW].

Each branch's descendant leaf count determines its rank, hence its
normalized branch update $k=T+2-\operatorname{rank}$. List recovered
parents first by this update and then by their actual physical address.
This recovers exactly $W_1,\ldots,W_{T-1}$ and their marked chronology.
One may instead start a beta roster at zero and apply NRW Lemmas
2.1--2.3's common-domain roster induction. It reads only these visible
orientations and outputs exactly the same chronological words.

Conversely, the words through $T-1$ construct the entire labelled local
state at $T-1$. Its beta leaves determine the positions of both children
created at $T$, independently of the last orientations; its other leaves
remain in place. Thus they determine $S_T$. Labels at cut $T$ also
determine the last bits by the position of beta at each newest cherry;
older bits have already been recovered from support. Forward replacement
proves the converse for the labelled state. For $T=0,1$, the same argument
has no old batch, with respectively a beta root or one unlabelled cherry.
Finally $\sum_{k=1}^{T-1}F_k=F_{T+1}-1$, and (PCR.3) is injective and
surjective on the unrestricted assignments of these bits. This proves
the count. Under a fixed law, some words are constrained; the count is
not a claim that all supports occur in that restricted family. $\square$

**Proposition 2.2 (the observation distinctions).** Equation (PCR.3)
concerns complete ordered support. A fixed finite menu of paid literal
presence tests need not determine its visible batches, even at a mature
cut. Forgetting physical child order loses every orientation. The family
$(S_T)_{T\ge0}$ determines every batch, whereas its timeless union is
$\{a,b\}^*$ for every local trial and therefore separates none of them.
Newest structural invisibility does not prevent inference of newest bits
from older bits together with an authentic sufficiently restrictive law.

Proof. For a nonempty relative word of length $h$, its creation time from
beta lies between $h$ and $2h-1$: its first edge is born in update one,
and each subsequent edge adds the initial label delay one or two. Hence
any fixed menu with maximum word length $h$ receives only ones at
$T\ge\max(0,2h-1)$, independently of its law and clocks. Such a cut can
also be chosen above any maturity threshold below. Distinct mature
supports therefore remain possible with the same menu replies. An
adaptive menu likewise earns only its actual transcript; (PCR.3) grants
no complete support from it.

After physical order is forgotten, each rank has the same unordered
Fibonacci tree, by induction on rank. For the cut-indexed family, apply
Theorem 2.1 at $T=k+1$ to recover $W_k$. Every finite word is eventually
created, by the delay bound, proving the timeless-union assertion. A
recurrence can determine later bits from recovered earlier ones, without
making a rank-two cherry's orientation a direct presence observation.
$\square$

## 3. Fixed-core rigidity of both clock residues

**Theorem 3.1 (exact local clock classification and finite witnesses).**
Fix one aligned periodic core $y$ with least positive period $p$ and any
presented period $u$. For two local trials with this same core, complete
local forward behaviour agrees if and only if

$$
 A_1\equiv A'_1\pmod p,\qquad A_2\equiv A'_2\pmod p.
 \tag{PCR.4}
$$

Here complete behaviour can be taken to mean all finite labelled local
states, all cut-indexed supports, or all future presence answers on
relative words at their indexed cuts. The same equivalence holds for
equality of the single support $S_T$ whenever

$$
 s\ge1,\quad F_s\ge r,\quad T\ge s+2,
 \qquad r=\deg g_y,
 \tag{PCR.5}
$$

where $g_y$ is the core's least monic annihilator and $r>0$. A sufficient
bound requiring only a presented period is $F_s\ge u,T\ge s+2$, because
$r\le p\le u$. These bounds are sufficient, without an optimality claim.
For zero and both constants, $p=1$ and there is one clock behaviour;
within a fixed constant core no maturity condition is necessary.

Proof. First record the recurrence facts used here. On periodic streams,
forward shift is invertible. A nonzero periodic stream's least monic
annihilator has constant term one: otherwise dividing its annihilator
by $E$ would give a smaller annihilator, since shift is injective on
periodic streams. Its recurrence determines all entries from any $r$
consecutive entries, both forwards and backwards. For the backwards
step, solve the recurrence for the earliest entry using its nonzero
constant term. Thus two shifts of $y$ agreeing on $r$ consecutive
entries agree as integer-indexed periodic sequences. An integer shift
preserves $y$ exactly when it is divisible by $p$: divide any positive
period by $p$ and use periodic extension to show that its remainder is
a period unless zero. Negative shifts reduce to positive ones. In
particular $p\mid u$. Finally $E^p-1$ annihilates $y$, proving $r\le p$.
These are classical recurrence and periodicity facts, used here inside
the source correspondence rather than claimed as new theorems.

If (PCR.4) holds, the Fibonacci recurrence preserves equality of every
$I_k$ modulo $p$. Equation (PCR.2) gives identical batch words, and
forward replacement gives identical labelled states and supports. This
is the sufficient direction of ACR Lemma 33.2, now reduced to least
period rather than a possibly redundant presented period.

For the converse at (PCR.5), Theorem 2.1 recovers equal batches $s$ and
$s+1$, since both are at most $T-1$. Each has at least $r$ entries.
Their equality and the recurrence fact just proved imply that each
start-index difference $I_s-I'_s$ and $I_{s+1}-I'_{s+1}$ is zero modulo
$p$. The clock transition

$$
 \begin{pmatrix}I_{k+1}\\I_{k+2}\end{pmatrix}
 =\begin{pmatrix}0&1\\1&1\end{pmatrix}
  \begin{pmatrix}I_k\\I_{k+1}\end{pmatrix},\qquad
 \begin{pmatrix}I_k\\I_{k+1}\end{pmatrix}
 =\begin{pmatrix}-1&1\\1&0\end{pmatrix}
  \begin{pmatrix}I_{k+1}\\I_{k+2}\end{pmatrix}
 \tag{PCR.6}
$$

is invertible modulo every positive $p$, including composite periods.
Iterate backwards to the seeds to obtain (PCR.4). Agreement of the
entire support family includes a cut satisfying (PCR.5), so it has the
same converse. All labelled histories determine all supports; equality
of all supports gives the seeds and therefore all labelled histories.
A difference of finite supports supplies a relative literal presence
separator at that cut. For $p=1$ every pair is congruent, and fixed
constant orientations directly prove the remaining assertion. $\square$

**Corollary 3.2 (the exact hypothetical and attainable counts).** For a
fixed aligned core of least period $p$, the hypothetical residue trials
have exactly $p^2$ complete local behaviours. A presentation of period
$u$ has $u^2$ seed trials but only $p^2$ behaviours, each represented by
$(u/p)^2$ pairs. If $\mathcal A$ is any specified set of actually attainable
integer seed pairs for the source/cone comparison under consideration,
its behaviour count is exactly

$$
 \bigl|\{(A_1\bmod p,A_2\bmod p):(A_1,A_2)\in\mathcal A\}\bigr|,
 \tag{PCR.7}
$$

and can be smaller. These assertions include zero with $p=1$.

Proof. Distinct pairs modulo $p$ are separated by Theorem 3.1 at the
same sufficient finite cut, and every residue trial is defined in
Definition 1.3. Reduction from $u$ to its divisor $p$ has $u/p$ lifts
per coordinate. Restricting this exact classification to $\mathcal A$
gives (PCR.7). Nothing proves that $\mathcal A$ is the full residue
square. Nor does cardinality require two physical registers: one encoded
finite register can represent a pair. Integer clocks differing by
multiples of $p$ are not distinguished, and no exterior forest is
reconstructed. $\square$

## 4. Unknown cores in the original recurrence-order comparison domain

**Theorem 4.1 (three mature batches identify the original alignment).**
Let $d\ge1$. Take two genuinely core-only normalized cones, possibly
from different members of the original $\mathscr R_d$, with aligned
cores $y,y'$ each of least recurrence order at most $d$. Compare their
complete local supports at the same $T$. Set

$$
 s=\min\{j\ge1:F_j\ge2d\}.
 \tag{PCR.8}
$$

If $T\ge s+3$ and $S_T=S'_T$, then $y=y'$ at their original aligned
indices. Their least positive periods coincide, say $p$, and both clock
seeds agree modulo $p$. Conversely those conclusions imply equality of
all local forward behaviour. More generally the forward implication
needs any three consecutive visible batches of at least $2d$ entries.
At $d=0$, both cores are zero, $p=1$, and the conclusion holds at every
common normalized cut, with the empty residue information.

Proof. By Theorem 2.1, the batch words at $s,s+1,s+2$ agree. Their
lengths are at least $2d$, and their last index $s+2$ is visible because
$s+2\le T-1$. Let the least monic annihilators of the two cores have
degrees $r,r'\le d$ and constant term one, taking the degree-zero
polynomial one for zero. For each of the three batches the difference
of the shifted streams

$$
 i\longmapsto y_{I_k-1+i}-y'_{I'_k-1+i}
 \tag{PCR.9}
$$

is annihilated by their product, a monic polynomial of degree
$r+r'\le2d$ with constant term one. This follows by commuting the two
shift polynomials; each kills its corresponding summand. Its first
$r+r'$ values vanish, so forward recurrence makes every subsequent
value vanish, and the nonzero constant term gives every preceding value
as well. Degree zero means the difference is already identically zero.
This is precisely the classical product-annihilator argument of GPO
Lemma 29.2, applied to periodic extensions and their shifts, with a
justified backwards step. It uses order, not a bound on period.

The first such identity shows that $y'$ is a shift of $y$, so their
least periods agree. Choose the common phase $c$ modulo $p$ such that
$y'_i=y_{i+c}$ for every integer $i$. Equation (PCR.9) then gives

$$
 I_k-I'_k\equiv c\pmod p\qquad(k=s,s+1,s+2),
 \tag{PCR.10}
$$

by least-period rigidity. Subtracting the two clock recurrences shows
that these differences themselves satisfy the Fibonacci recurrence.
Thus $c\equiv c+c\pmod p$, forcing $c\equiv0$. It follows that the
cores agree at **original** alignment, not merely as necklaces or up to
a cyclic shift. The two consecutive zero differences and (PCR.6) give
both seed congruences. For constants the same argument has $p=1$;
equality of a nonempty batch forces their values to be the same. The
converse is Theorem 3.1's sufficient direction. At $d=0$ the all-index
order-zero promise forces both original streams, and therefore both
cores, to be zero. $\square$

**Proposition 4.2 (what the order theorem reconstructs).** Theorem 4.1
identifies the aligned infinite core and its two local clock residues
from the stipulated equality comparison. It neither changes the original
source class to period at most $d$, nor recovers the original stream's
transient, integer clocks, global cut, private recurrence presentation,
exterior forest, or the original deficient-rank normal form $K_d$.
The horizon is a sufficient semantic identification threshold and does
not supply a polynomial acquisition or decoding procedure.

Proof. The proof uses only $r+r'\le2d$, hence preserves every periodic
core arising from the original all-index class. Invertible binary
order-$r$ dynamics can have least period $2^r-1$, as witnessed by a
nonzero primitive recurrence; NRW Theorem 2.4 states the same supplier.
In particular period can exceed $d$ even with zero transient and order
$d$. Phase equality in the proof concerns only $y$, and all clock
conclusions are modulo its least period. No step observes erased early
births or the exterior. If the core period is exponential in $d$, merely
writing its period word need not have polynomial size. Finally complete
support in the hypothesis remains a mathematical observation until it
is actually acquired; Theorem 2.1 did not give a small Read menu.
$\square$

## 5. A conditional constructive spatial inverse with an authentic period bound

**Definition 5.1 (earned input, supplied promise and completion charges).**
Supply an actual root binding, total paid presence-Read grant, persistent
physical order, finite local progress, growing owned readable backing,
and one exclusive stationary completed-cut interval covering all Reads,
calculations, allocations, temporary and retained writes, and completed
handoff. Give the full literal prefix $v$ of length $m$, whose presence
has been earned, and the authentic promise that this is a core-only
beta-normalized cone with a least core period at most a public $D\ge1$.
The current normalized age $T$ need not be supplied. Its promised maturity
is

$$
 s_D=\min\{j\ge1:F_j\ge2D\},\qquad T\ge s_D+3.
 \tag{PCR.11}
$$

These are actual service and class premises, not certificates manufactured
by an arithmetic decoder. If presence of $v$ has not already been earned,
first pay Read$(v)$ and continue only on a positive reply. No additional
source update, reset, recut, clone, relative Read port, labelled reply,
core word, phase, cut or clock is an input. The sparse class of ACR
Definition 33.1 has the authentic bound $D=d$ for $d\ge1$; this fact does
not give that bound to the unrestricted $\mathscr R_d$.

**Theorem 5.2 (constructive aligned core and clock recovery).** Under
Definition 5.1 there is a finite zero-source-update inverse returning
$T$, the least period $p$, the aligned word $(y_0,\ldots,y_{p-1})$ and
$(A_1\bmod p,A_2\bmod p)$, and installing those values with a local
physical literal evaluator. All source-dependent data it uses come from
earned complete support. Complete scanning is one sufficient supplier;
when support is already acquired the same inverse uses no further Read.

Proof. First acquire support if needed by the presence-only scan of
ACR Proposition 8.1. At each confirmed relative node $w$, submit the
**full-root** literal $vwa$. A negative reply marks $w$ terminal; a
positive reply schedules both children, since the actual tree is full
binary. This is a finite scan of the existing cone with one query per
node, including every terminal's absent-child query. It uses no age
bound, orientation guess or hidden semantic navigation. Count the
acquired leaves; their number $F_{T+2}$ uniquely gives $T$. If a supplied
maturity premise is absent, this test may instead certify that the
scanned cone is too young; the present theorem authorizes no update or
free recut to make it mature.

Decode the visible chronological batches by Theorem 2.1. Take the first
$2D$ entries of batch $s_D$ as a word $w$. Find the smallest
$q\in\{1,\ldots,D\}$ for which

$$
 w_i=w_{i\bmod q}\quad(0\le i<2D).
 \tag{PCR.12}
$$

The actual least period $p$ passes, so a candidate exists. Conversely
extend $w_0\cdots w_{q-1}$ periodically. This extension and the actual
shifted core have periods $q,p\le D$ and agree for $2D$ entries. They
are equal: their difference is annihilated by
$(E^p-1)(E^q-1)$, of degree $p+q\le2D$ with nonzero constant term,
and the zero-block recurrence argument of Theorem 4.1 applies. Therefore
$p\le q$, and the smallest passing value is exactly $p$.

This is also a direct application, with slack, of the classical
Fine--Wilf periodic extension boundary $p+q-\gcd(p,q)$; see [Rankin,
Introduction][RAN] and [Karhumaki, §1, Theorem 5, printed pp. 9--10][KAR].
The product proof above gives
all the weaker $2D$ bound needed here without requiring that sharp
boundary or a new periodicity theorem.

Put $x_i=w_{i\bmod p}$, so $x_i=y_{I_{s_D}-1+i}$. Match the first $p$
entries of each of the next two decoded batches against the $p$ cyclic
shifts of $x$. Their unique phases $b,c\in\mathbb Z/p\mathbb Z$ satisfy

$$
 b=I_{s_D+1}-I_{s_D},\qquad
 c=I_{s_D+2}-I_{s_D},\qquad
 I_{s_D}=c-b,\qquad I_{s_D+1}=c.
 \tag{PCR.13}
$$

Existence follows from the actual source correspondence; uniqueness
follows from the least period of $x$. The last two equalities follow
by the Fibonacci recurrence, not by an external clock observation.
Recover the aligned core by

$$
 y_i=x_{i-I_{s_D}+1}\qquad(i\in\mathbb Z/p\mathbb Z),
 \tag{PCR.14}
$$

and iterate (PCR.6) backwards to obtain both initial residues.
For $p=1$, the two phases and all residues are zero; (PCR.14) still
returns the actually observed constant, so zero is not confused with
one. The zero core may separately use an empty clock record, but its
least positive period remains one.

For the evaluator, start the normalized root descriptor at $(0,\beta)$.
At a relative node with descriptor $(b,\sigma)$, its branch time is
$\theta=b+2-\mathbf1_{\sigma=\beta}$. Compute the actual event index
modulo $p$ by ACR (ACR.115):

$$
 J(w)=I_{\theta_w}+
   \sum_{ub\preceq w}\lambda_{\sigma_{ua}}(\theta_w-1-\theta_u)
       \pmod p,\qquad
 \lambda_\alpha(h)=F_h,\quad\lambda_\beta(h)=F_{h+1}.
 \tag{PCR.15}
$$

Its orientation is $y_{J(w)-1}$. Create the corresponding two initial
child descriptors and continue only along the requested word, stopping
at a node not yet branched at $T$. Descriptor ages determine absence,
terminal alpha/beta, or branch exactly as in GPO (GPO.98), with the
normalized beta root exception. The ACR index proof and induction on
word length show that these are the actual local answers. In particular
the presence projection evaluates the acquired support and every future
normalized cut on the same core-only source. No exterior roster or
integer clock is used. The final installation writes the entire payload
and evaluator's actual callable control before exposing ready; binding,
grants and completion remain separate physical relations. $\square$

**Theorem 5.3 (explicit charged scope of this inverse).** Let
$N=2F_{T+2}-1$, $m=|v|$, and $K=N+m+T+D+2$. If the complete support is
supplied by the scan in Theorem 5.2, its exact and upper Read coordinates
are

$$
 Q=N,\qquad M=m+T+1,\qquad
 J=\sum_{w\in S_T}(m+|w|+1)\le N(m+T+1).
 \tag{PCR.16}
$$

Here $M$ is the longest complete root literal and $J$ is total literal
traffic. The optional initial Read$(v)$ adds one call and $m$ symbols.
There is an implementation with elementary sequential bit work and
cumulative bit writes at most $CK^{10}$ and peak owned working and
retained backing at most $CK^3$, for an absolute machine-model constant
$C$. Add any cost of supplying pre-earned support, binding, authentic
promises, code delivery, allocation, physical writes and retention,
service tariffs and durations, and completed handoff. If support is
already supplied, the post-acquisition inverse makes zero new Reads.
These are conditional finite bounds, not a polynomial-TOTAL acquisition
bound in $(d,\log T)$ or a physical latency bound.

Proof. The scan pays one full literal per present node. Maximum local
depth is $T$, attained by always following the initial-beta child, so
some terminal test has length $m+T+1$, and none exceeds it. This proves
(PCR.16), including the negative terminal replies. It is the existing
complete scan, not a selective acquisition improvement.

For explicit local accounting, store the expanded support with physical
relative addresses, child markers, heights, leaf counts and branch
updates; use at most $O(N(m+T+1))$ bits, since $\log(N+1)=O(T+1)$.
Counters, a depth-first stack, the acquired prefix, batches, current
phase candidates, aligned word and modular Fibonacci scratch fit
$O(K^3)$ bits. Full-root operands are copied into owned query buffers.
A scan node creates at most two address records, and their materializing,
copying and counter work are paid. Compute leaf counts and heights by
bottom-up finite scans, then extract batches by their recovered branch
updates in lexicographic order, or use the explicit beta-roster induction.
Neither requires an uncharged indexed structure. Keeping explicit full
addresses and comparing them lexicographically costs at most $O(K)$
bit operations per comparison.

Trial values $q\le D$ in (PCR.12) each compare at most $2D$ bits.
Matching each of the next two batches against $p$ shifts uses at most
$2p^2$ bit comparisons; copying the aligned word uses $p$ entries.
Recovering $T$ by Fibonacci iteration takes $O(T)$ additions on
$O(T+1)$ bits. Reversing the modular clock uses $O(s_D)$ operations
on $O(\log(D+1))$-bit residues. With generous slack, all traversal,
sorting, batching, copying and arithmetic require at most $CK^5$
indexed bit operations. An implementation that locates every indexed
cell by a full scan of the $O(K^3)$ layout, with $O(K)$ counter and
head-return work per scanned cell, uses at most $CK^9$ work and writes.
The stated $CK^{10}$ envelope includes initialization, discarded
candidates, buffer construction, retained output copies and ready-control
writes. This supplies a concrete finite sequential upper bound without
a unit-cost random-access assumption; it makes no optimized-exponent
claim. Allocation and physical write tariffs still attach to the actual
bits so written.

For a later literal of relative length $h$, (PCR.15) needs at most $h$
orientations and at most $h$ skipped-sibling terms at one edge. Branch
times on proper prefixes are at most $2h-1$. A modular Fibonacci table
and the two modular clocks through $2h+1$, stored period word, and
$O(h)$ descriptors consequently suffice; binary cut comparisons use
$O(\log(T+2))$ bits. Explicit finite scans give work, writes and backing
polynomial in $(D,h,\log(T+2),m)$ per requested answer. An actual Read
still submits and pays its complete root literal $vw$. Expanding the
entire boundary or support pays its full output, and later actual updates
and synchronized memory writes retain their own costs.

All computations are stationary and make no source update. A numerical
increment of $T$ is justified only after a completed actual update on the
same binding; retaining the acquired phase does not itself perform that
update. Every handoff requires the supplied stationary interval through
its real completion. An arbitrary old cone has exponentially many nodes
in $T$, and in the unrestricted order-$d$ domain a necessary period bound
can be exponential in $d$. Neither expense is suppressed by the finite
conditional bounds. $\square$

## 6. Actual-source clock separation and finite early equivalence

**Proposition 6.1 (a common first clock is insufficient on admitted sources).**
There are two actual alpha-origin sources in the original $\mathscr R_3$
with the same nonconstant aligned core, the same physical cone $v=bab$,
the same normalization cut $e=5$, and the same first clock $A_1=11$,
but second clocks $18$ and $19$. At the common admissible actual cut
$n=8$, hence normalized cut $T=3$, paid full-root Read$(babbaa)$ replies
one on the first source and zero on the second. At actual cut $n=7$
their local supports are equal, and this equality fails after the one
actual update to $n=8$.

Proof. Let $y_i=i\bmod2$, and define

$$
 s^{(0)}=010101\cdots=y,\qquad
 s^{(1)}=110101\cdots=y+\mathbf1_{i=0}.
 \tag{PCR.17}
$$

Both are in $\mathscr R_3$: $E^2+1$ annihilates $y$, $E$ annihilates
the impulse, and their product annihilates the sum. The impulse cannot
have a nonzero periodic component; the unique coprime decomposition of
ACR Theorem 27.3 therefore gives the same aligned core $y$ for both.
The first source has order two and the second has order three. The core
has least period two. Original birth bits are $z_j=s_{j-1}$.

Direct simultaneous old-leaf replacement gives the following complete
leaf rosters at actual cut five. The entries appear in physical order;
$A,B$ abbreviate alpha and beta only in this displayed roster.

$$
\begin{aligned}
 s^{(0)}:&\quad aa:B,\ aba:A,\ abb:B,\ baaa:B,\ baab:A,
                 \ bab:B,\ bba:A,\ bbb:B;\\
 s^{(1)}:&\quad aaa:B,\ aaba:A,\ aabb:B,\ aba:B,\ abb:A,
                 \ baa:A,\ bab:B,\ bb:B.
\end{aligned}
 \tag{PCR.18}
$$

To verify these rosters without an assumed clock, the beta parent lists
for updates two through five are respectively

$$
\begin{aligned}
 s^{(0)}:&\quad (\varepsilon),\ (b),\ (a,ba),\ (ab,baa,bb);\\
 s^{(1)}:&\quad (\varepsilon),\ (a),\ (aa,b),\ (aab,ab,ba).
\end{aligned}
 \tag{PCR.19}
$$

Assign $z_1$ at update two, $z_2$ at update three, $z_3,z_4$ at
update four, and $z_5,z_6,z_7$ at update five. These are exactly the
bits of (PCR.17); the other old leaves become beta. This proves
(PCR.18) by four finite substitutions. In the first source $bab$ was
born alpha at cut four, while in the second it was born beta at cut
five. Both are beta at five and branch at six. Thus they have exactly
the same normalization cut, including the mixed-descriptor issue of
NRW Lemma 2.1.

Before $bab$ at cut five, the exterior forest has leaf counts
$(A,B)=(2,3)$ and $(3,3)$ respectively, read directly from (PCR.18).
After one update these beta counts become $5$ and $6$. Formula (PCR.1),
with $F_6=8,F_7=13$, now gives

$$
 (I_1,I_2)=(8+3,13+5)=(11,18),\qquad
 (I'_1,I'_2)=(8+3,13+6)=(11,19).
 \tag{PCR.20}
$$

All these cone indices exceed one, so the impulse has disappeared from
all local births. In fact $I_1>d=3$. The cones are genuinely core-only;
their identical core is not being inferred from a zero-tail example.

Their first normalized bit is $z_{11}=0$, so at normalized cut one
both have alpha at relative $a$ and beta at relative $b$. In update two
only relative $b$ branches, using $z_{18}=1$ in the first cone and
$z_{19}=0$ in the second. Hence both supports at $T=2$ are
$\{\varepsilon,a,b,ba,bb\}$, but relative $ba$ is beta only in the
first. In update three it branches only there, so relative $baa$ is
present only there. The common full-root separator is exactly $vbaa$
$=babbaa$, of length six, with one paid presence reply per source.
Its operand must be materialized and submitted at the actual root;
no relative physical port has been introduced.

For the original entrance at $d=3$, the bound is
$n_0=N(6)=6$, since $F_5-1=4<6$ and $F_6-1=7\ge6$. Both actual
cuts seven and eight are therefore admissible mature **global** cuts.
Only the local comparison at $T=2$ is early: it has not reached the
fixed-core order-two bound $F_s\ge2,T\ge s+2$ (which gives $s=3,T\ge5$),
or the unknown-core bound. Thus its continuation failure contradicts
neither maturity theorem. It is not a comparison of equal full-entry
states: the supports outside this cone, and their erased original
prefixes, need not agree. $\square$

## 7. Correspondence, use and the remaining acquisition gap

**Proposition 7.1 (supplier domains and unclosed bridges).** The new
source-specific conclusions above are the exact finite-batch support
relation, the necessity of both least-period clock residues, the
three-batch recovery of original core alignment under the original order
bound, and the conditional spatial inverse. Their derivations use
ACR §§2, 8--9, 21, 27--29 and 33; NRW §§1--3; and GPO §§27--29 and 39
with the following correspondence and limits.

Proof. ACR Theorem 27.2 supplies the actual exterior clock (PCR.1) and
skipped-sibling index (PCR.15); Theorem 27.3 supplies the aligned
core-only frontier. NRW's rank $q$ is local age $T=q-1$, so a normalized
update $k$ has final rank $T+2-k$ and is visible exactly when $k\le T-1$.
This accounts for every maturity offset used here. The chronological
actuator proof is needed to turn each roster into consecutive global
outputs. GPO Theorem 28.2 is the alpha-root version of the same finite
support argument; its original class, including singular transients,
is kept rather than replaced by a short-period class.

Massey's *Shift-Register Synthesis and BCH Decoding*, §§II--IV [MAS],
supplies finite-prefix recurrence synthesis and its distinction between
register length, a zero final tap and transient rational numerators.
The product-annihilator proof of GPO Lemma 29.2 supplies the comparison
argument used here; the backwards step is licensed only on the periodic
cores with constant-term-one annihilators. A finite singular source is
not run backwards, and its transient is not normalized away in the
original all-index task. Rankin [RAN] explicitly states the infinite
periodic extension version of Fine--Wilf in its introduction; Karhumaki
[KAR] and Shallit [SHA] give accessible word-period formulations. The
$2D$ argument in Theorem 5.2 has a complete elementary proof above and
uses their periodicity result only as a classical supplier with slack.
The cited original Fine--Wilf paper is an attribution through these
accessible accounts, not a claim of access to its original AMS PDF.
None of these literature suppliers supplies the actual-port clock
correspondence or free acquisition.

The existing D5 and Blueprint declarations retain their exact domains.
`NativeRankedNavigationCompiler.rank_only_refinement_compilation`
quantifies over native residual-free ranked expressions, fixed epochs
and fixed semantic binary addresses, with four-valued literal replies
and positive whole-subtree equality links. Its native substitution fixes
beta on the semantic left. It is not a physical orientation sensor for
the arbitrary actual birth wiring here.
`NativeBirthVectorDecoder.decodeBirth_patternVector` decodes complete
recursive code vectors in the image of `patternVector`;
`birthVector_decompose` identifies that code with the decomposed native
pattern. Acceptance is not a general image test, and these types do not
identify the code with actual physical first-presence epochs on the full
source/address domain. `ActualFibonacciSupportChain.actual_fibonacci_support_chain`
provides strict native support inclusions together with bounded-address
presence agreement, not complete support equality or a paid inverse.
`NativeFullSourceProducer.native_source_producer` runs a source-blind
native stack with epoch-zero richer replies and exact finite native
output, preserving the register and listing its node reads. The
presence-only actual scan used here is the separate ACR §8 supplier;
the richer native reply must not be imported for free.
`FiniteFutureCongruence.finite_future_maximal_congruence` concerns an
arbitrary finite carrier, update and observation and its maximal invariant
future congruence. It gives neither (PCR.2)'s physical birth blocks nor
the source-specific two-clock converse. Those are the additional
mathematical bridges proved here. Source-level proofs make no new
Lean-verification claim.

ACR's existing guarded acquisition and sparse-list suppliers remain
available with their original bills. No new generic minimizer, candidate
controller, polynomial decoder under an order promise alone, or
improved physical acquisition bound follows. At an arbitrary hidden cut,
the remaining selective-acquisition obligation is to earn enough local
chronology, maturity and alignment through paid full-root literals and
bounded local work and backing, while retaining an authentic comparison
domain and the original output convention. Semantic uniqueness after a
complete-support comparison does not solve that acquisition problem.
The constructive period-bound inverse does not fill it by a free scan
or a free recut.

The unrestricted polynomial-TOTAL original acquisition problem, efficient
original deficient-rank $K_d$ normalization, and all unsupplied service,
installation and synchronization assumptions retain their unresolved
boundaries. Nor is this a recovery of full space, time, boundary and
memory: it recovers an ordered local cone, its future local birth
chronology and its aligned periodic descriptor under the stated inputs.
Integer age outside the normalized cone, exterior geometry, early
transient memory, capabilities and physical duration are separate.
These conclusions are `repo-derived` compositions with the cited
classical suppliers, without a worldwide-priority claim. $\square$

[ACR]: RECURSIVE_RELATIONAL_OBSERVATION_ACTUAL_CUT_REINSTATEMENT.md
[NRW]: RECURSIVE_RELATIONAL_OBSERVATION_NATIVE_RESIDUAL_WIDTH.md
[GPO]: RECURSIVE_RELATIONAL_OBSERVATION_ATOMIC_GLOBAL_PORT_ORIENTATION.md
[MAS]: https://www.isiweb.ee.ethz.ch/archive/massey_pub/pdf/BI411.pdf
[RAN]: https://arxiv.org/pdf/0906.1780v1
[KAR]: https://www.math.utu.fi/en/home/karhumak/pdf/combwo.pdf
[SHA]: https://cs.uwaterloo.ca/~shallit/Talks/vu3.pdf

## 追加锚（本行以下为增补区）
