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
has least period two: it is nonconstant and $E^2+1$ annihilates it,
whereas an order-one recurrence cannot generate this alternating word.
The impulse has least annihilator $E$. Applying the two coprime
projections to any annihilator of their sum forces divisibility by both
$E$ and $E^2+1$, proving the asserted least order three. Original birth
bits are $z_j=s_{j-1}$.

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

**Proposition 6.2 (a constant core does not erase an early singular birth).**
The fixed-core $p=1$ conclusion requires the core-only premise. At the
alpha root, the streams $000\cdots$ and $100\cdots$ have the same zero
core and the same exterior clocks $(I_1,I_2)=(1,2)$ after normalization
at $e=1$, yet their relative supports at $T=2$ differ. Similarly,
$111\cdots$ and $011\cdots$ have the same all-one core and these same
clocks, but different supports at $T=2$.

Proof. The impulse $100\cdots$ is annihilated by $E$, so the first pair
lies in $\mathscr R_1$ and has zero periodic component. The second pair
lies in $\mathscr R_2$, since $E(E+1)$ annihilates the all-one stream
plus that impulse. At the alpha root the preceding forest is empty and
$e=1$, so (PCR.1) gives the asserted common clocks. In either pair the
first birth has opposite orientation. After two normalized updates, the
beta child created in the first update has branched; relative $aa$ is
present exactly when that first bit was one. Thus a paid full-root
presence test at $aa$ separates each pair. Here the first index is inside
the transient, so these are deliberately outside Definition 1.2's
core-only domain. They do not assert an admissible erased full-entry
comparison at the original mature horizon: actual cut $n=3$ is less
than $N(2)=4$ for $d=1$, and less than $N(4)=5$ for $d=2$. $\square$

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

## 8. Acquired inputs for an operator boundary in the full order class

**Definition 8.1 (the local request and its authentic data).** Keep
Definitions 1.1--1.3 without a restriction on the period, a square-free
hypothesis or a supplied minimal presentation. The public order bound is
$d\ge0$ for the original all-index stream, including its transient. Fix
one retained actual root binding and a present full physical prefix $v$
of length $m$. Its normalized origin is the *same* cut $e=\tau_v-1$
throughout this construction; the current local age is $T=n-e\ge0$.
Assume genuinely core-only future evolution in the sense of Definition
1.2. Neither a recurring finite word nor a finite transcript proves that
premise. ACR Theorem 27.3's physical-depth cutoff is one sufficient
supplier. No local origin is physically reset and no relative port is
introduced.

The requested family is, for all finite physical suffixes $w$ and all
$u\ge0$,

$$
 \mathcal P_v(T;u,w)=\mathbf1_{vw\in S^{\rm actual}_{n+u}}.
 \tag{PCR.21}
$$

Every actual request submits the complete literal $vw$ at the original
root. A value for $u>0$ before those updates is a prediction; an actual
reply at that future cut requires the completed original-source updates.
This family includes every suffix, empty or absent, and every finite
serial adaptive continuation of local literals and original updates.
Words outside this cone are not part of (PCR.21). An arbitrary global
literal service still needs its own earned global descriptor, as in GPO
Theorem 39.4. In particular this local interface does not replace the
original acquisition of $(P,n)$.

For $d>0$ put $s=\min\{j\ge1:F_j\ge2d\}$. A sufficient *acquired
record* consists of $v,T$ and the first $2d$ entries of each of
$W_s,W_{s+1},W_{s+2}$, with authentic common-source chronological
provenance, $T\ge s+3$, and the preceding core-only premise. Provenance means that these are the actual physical
lexicographic actuator words at these indexed updates, not independently
sorted semantic words, conjectured shifts or oracle samples. An acquired
complete ordered support with its paid terminal absence tests supplies
this record by Theorem 2.1. A different supplier must prove these same
properties and charge its own acquisition and transfer. For $d=0$ the
core is zero, no batches are needed, and an authentic $T$ suffices.

The service premises are genuine retained binding, grants, finite local
progress and enough growing owned readable backing. The stationary
completed-cut interval covers all actual acquisition, conversion,
allocations, scratch and retained writes and the completed installation.
If already acquired data are transferred, their readable materialization,
root/origin association, finite transfer work and writes are part of the
supplier. Completion, exclusivity and survival of the binding are physical
premises, not consequences of the algebra.

**Theorem 8.2 (the missing supplier restriction can be removed at the
algebraic interface).** The three-prefix inverse of [PSA, Theorem
3.1][PCR-PSA] applies to every record in Definition 8.1, not only to the
terminal-spine cone chosen by PSA Theorem 2.1. It returns the original
aligned least monic core polynomial $g$ and seed $(y_0,\ldots,y_{r-1})$,
$r=\deg g\le d$, with $g(0)=1$ at $r>0$. At $r=0$ it returns zero.
The additional source-specific bridge needed for this use is exactly
the following hypothesis correspondence; it supplies neither unqueried
data nor a new acquisition theorem.

Proof. The original entrance, order promise, one-based index $z_j=y_{j-1}$
on core births, physical order and old-leaf rule are identical in PSA
Definition 1.1 and here. By genuine core-only evolution the three words
are shifts of a *single periodic aligned core* of order at most $d$.
The authentic provenance and Theorem 2.1 supply their exact ordered
entries. ACR Theorem 27.2, or (PCR.1), supplies, for
$A=I_s-1,B=I_{s+1}-1$, the identities

$$
 u=E^Ay,\qquad v'=E^By,\qquad w'=E^{A+B+1}y.
 \tag{PCR.22}
$$

Here $w'$ denotes a stream, not a physical suffix. Its first $2d$
entries are the third acquired prefix. Both actual starts are positive,
so $A,B\ge0$. The $+1$ is forced by one-based birth indexing. PSA
Theorem 2.2's conclusion therefore holds on this cone without requiring
its terminal-spine selection, a bounded cone size, $H$, $h$, shallow
clock bounds, a known exterior forest or a numerical value of $A,B$.
All three prefixes are visible because $s+2\le T-1$.

To check the dependency rather than assume a broader theorem, PSA
Theorem 3.1 computes $r$ as the rank of $H_d(w')$, obtains $g$ and a
polynomial $f$ by its two nonsingular leading-Hankel solves, and uses
$f(E)w'=Ev'$. Substitution of (PCR.22) gives
$E^{B+1}(f(E)u-y)=0$. The constant term of the *core* polynomial makes
shift injective on its solution space, so $f(E)u=y$. These are precisely
its proof's data and cancellation hypotheses. Its leading-Hankel
nonsingularity argument uses the least order and forward propagation,
not a short period or square-free factorization. Zero is handled before
inversion. No cancellation involves the singular factor of the original
stream. The acquired entries cover every index used in those solves.
Thus no step of that inverse uses the terminal-spine method of obtaining
the words. Reusing it after this hypothesis map is legitimate.

This establishes the algebraic bridge, rather than silently extending
PSA's complete physical entrance theorem. PSA Theorem 5.1's original
$(P,n)$ acquisition, PSA's early-parent heights and ACR's original
$K_d,\rho_d$ firstness remain distinct consumers and are not premises
silently supplied by this local record. The reused source is an ordinary
mathematical proof, not a compiled application. $\square$

## 9. Two clock operators recovered without numerical phases

**Definition 9.1 (the normalized operator descriptor).** At $r>0$ let

$$
 R_g=\mathbb F_2[X]/(g),\qquad x=X\bmod g,\qquad
 \lambda\left(\sum_{i<r}a_i x^i\right)=\sum_{i<r}a_i y_i.
 \tag{PCR.23}
$$

Use degree-less-than-$r$ coefficient strings for ring elements. The
proposed retained mathematical boundary is

$$
 \mathcal B_v(T)=(v,T;g,(y_i)_{i<r},Q_1,Q_2),\qquad
 Q_i=x^{I_i}.
 \tag{PCR.24}
$$

The last identities specify the mathematical meaning, not numerical
clock inputs. The acquisition algorithm below computes $Q_1,Q_2$
from the paid words. At $r=0$ use a zero tag and omit ring operations,
seed and clocks. Fixed public evaluation instructions and the actual
binding/permissions accompany this data with their separate supply and
retention bills.

**Theorem 9.2 (executable acquisition of the two operators).** The
record of Definition 8.1 determines (PCR.24) by finite binary linear
algebra, polynomial arithmetic and $s-1$ reverse operator transitions.
There is no period enumeration, factorization, multiplicative-order
calculation or discrete logarithm. Every inverted element is a proved
unit, including for a genuinely repeated-factor core.

Proof. First apply Theorem 8.2. For nonzero $y$, the classical
annihilator ideal says that the map

$$
 R_g\longrightarrow\operatorname{span}_{\mathbb F_2}\{E^i y:i\ge0\},
 \qquad a\longmapsto a(E)y
 \tag{PCR.25}
$$

is well defined and injective: its polynomial kernel is exactly $(g)$.
It is onto by the definition of that span. This is the polynomial-module
correspondence of [Shoup, Theorem 18.1 and Exercise 18.5][PCR-SHO], applied to the
*acquired* $g,y$, not to a different companion family. The first $r$
entries distinguish its elements. Indeed $a(E)y$ satisfies $g$; if its
first $r$ entries vanish, forward recurrence makes it identically zero,
and then injectivity gives $a=0$.

Consequently $H_r(y)=(y_{i+j})_{0\le i,j<r}$ is nonsingular. Generate
its needed entries from the acquired recurrence and seed. For $k=s,s+1$
solve

$$
 H_r(y)\,q^{(k)}=(W_k(1),\ldots,W_k(r))^{\mathsf T},\qquad
 \widehat Q_k=\sum_{j<r}q^{(k)}_j x^j,
 \tag{PCR.26}
$$

where $W_k(i)$ has zero-based word coordinate $i$. The right side is
acquired: $r+1\le2d$. The operator $x^{I_k}$ is one solution, since
its action on $y$ is $EW_k$. Uniqueness proves
$\widehat Q_k=x^{I_k}$. In particular these elements are units because
$g(0)=1$ makes $x$ a unit. They are not guessed logarithms. This is correctness on the authentic
acquired input, not an off-image test certifying that arbitrary supplied
words came from the actual source.

In the commutative unit group the actual clock recurrence becomes

$$
 Q_{k+2}=Q_{k+1}Q_k,\qquad
 (Q_k,Q_{k+1})\longmapsto(Q_{k+1},Q_kQ_{k+1}),\qquad
 (A,B)\longmapsto(BA^{-1},A)
 \tag{PCR.27}
$$

for the forward map and its inverse. Start at the acquired pair
$(\widehat Q_s,\widehat Q_{s+1})$ and apply the inverse $s-1$ times.
This produces exactly $(Q_1,Q_2)$. Extended Euclid in
$\mathbb F_2[X]$ computes each inverse modulo $g$; it inverts a unit,
not an arbitrary nonzero element of a presumed field. The inverses and
subsequent products remain in $\langle x\rangle$. Since $s=O(\log(d+2))$,
this takes polynomial work and writes.

For zero there is no ring inversion. For the all-one core $r=1$,
$g=X+1$, $x=Q_1=Q_2=1$ and $\lambda(1)=1$. A nonminimal original
presentation is harmless because the inverse has computed the least
$g$ first. PSA Proposition 3.2's padding counterexample shows why
replacing it by a redundant modulus is unjustified. The exact relation
between the ordinary-series connection polynomial and this forward
polynomial is $C(D)=D^r g(D^{-1})$, as in PSA Theorem 3.1 and [Massey,
Theorems 3--4][MAS]. None of these steps replaces the original $K_d$ by a
minimal core descriptor. $\square$

**Theorem 9.3 (exact data-to-boundary correspondence).** At a common
mature $T$ and for the same literal-prefix convention, (PCR.24) is a
canonical mathematical representative of complete local future presence
behaviour in this actual source comparison domain. Acquired complete
support determines it, and it determines that support. Two such supports
are equal if and only if their normalized descriptors agree. Equivalently,
for nonzero cores this is equality of original aligned $y$, its least
$g$, and both clock operators. Restricting to any specified attainable
source/cone family preserves the equivalence without enlarging that
family to hypothetical trials.

Proof. Theorem 2.1 extracts the acquired chronological record and $T$;
Theorems 8.2 and 9.2 give the stated deterministic map. The evaluator in
Theorem 10.2 below reconstructs all finite indexed supports from the
boundary. For the converse and uniqueness reuse Theorem 4.1: equal
mature supports give the same original aligned core and both clock
seeds modulo its least period $p$. On (PCR.25),

$$
 x^h=1\quad\Longleftrightarrow\quad E^h y=y
 \quad\Longleftrightarrow\quad p\mid h
 \qquad(h\in\mathbb Z).
 \tag{PCR.28}
$$

The first equivalence uses injectivity and invertibility, the second
is the least-period fact already used by Theorem 3.1. Thus equality of
operators is exactly the *existing* least-period clock classification.
No residues need be computed in order to compare their coefficient
strings. Equal descriptors give equal local forward behaviour by that
classification or by the evaluator. For zero all clock information is
omitted; the two constants are distinguished by their core descriptors.
One can reconstruct a finite support by the original finite replacement
rule through $T$ or by enumerating finite words with the evaluator;
that expanded output keeps its full cost. There is no efficient
whole-support-output claim. The classification is used, not reproved as
a new clock theorem. $\square$

## 10. The actual local literal evaluator

**Definition 10.1 (path descriptors and operator evaluation).** Give
the normalized root immutable descriptor $(b_\varepsilon,\sigma_\varepsilon)
=(0,\beta)$. For a relative node $q$ put
$\theta_q=b_q+2-\mathbf1_{\sigma_q=\beta}$. Define $Q_k$ by
(PCR.27), for $k\ge1$. For a proposed branch $q$ at $k=\theta_q$ form

$$
 D_q=\sum_{tb\preceq q}
       \lambda_{\sigma_{ta}}(k-1-\theta_t),\qquad
 \lambda_\alpha(h)=F_h,\quad\lambda_\beta(h)=F_{h+1},
 \tag{PCR.29}
$$

using precisely the skipped physical $a$ siblings at proper ancestors.
Their creation times are $\theta_t$, so all these ages are nonnegative.
For nonzero core set

$$
 \omega(q)=\lambda\bigl(x^{-1}Q_k x^{D_q}\bigr).
 \tag{PCR.30}
$$

Here the outer $\lambda$ is the linear functional (PCR.23), not a
sibling mass. For the zero core set $\omega(q)=0$. At this branch the
children have birth time $k$ and initial labels $(\beta,\alpha)$ at
$(a,b)$ if $\omega(q)=1$, and $(\alpha,\beta)$ otherwise.

For a full-root request $vw$, check the literal prefix and follow its
suffix from this root. At any descriptor $(b,\sigma)$, use the exact
label predicate (GPO.98), now at normalized age $T+u$: absent if
$T+u<b$, initial label if equal, beta one cut after an initial alpha,
and branch from $b+1$ for initial beta or $b+2$ for initial alpha.
Descend only through a branch. A nonempty remaining suffix below a
terminal or absent node returns absence. Return one exactly when the
final descriptor exists. The auxiliary label is an internal prediction;
it does not enlarge the physical presence-Read reply. The same predicate
also supplies a requested single-word terminal-boundary indicator.

**Theorem 10.2 (literal correctness, including chronology and absent
extensions).** For every descriptor acquired as above, every $u\ge0$
and every finite suffix $w$, Definition 10.1 returns (PCR.21). It uses
at most $|w|$ orientation evaluations and neither an expanded tree nor
a list of the core period. If a response discrepancy exists, a finite
full-root literal $vw$ at a finite indexed cut witnesses it.

Proof. ACR Theorem 27.2 supplies the *actual* index of branch $q$ as
$J_v(q)=I_k+D_q$. The initial normalized descriptor, immutable sibling
descriptors, chronological order and masses in (PCR.29) are exactly its
(ACR.115), not semantic addresses or counts with order forgotten.
By (PCR.23) and the recurrence, $\lambda(x^a)=y_a$ for $a\ge0$.
For negative $a$ the same identity follows from invertibility on the
periodic core. Hence (PCR.30) is

$$
 \lambda(x^{I_k+D_q-1})=y_{J_v(q)-1}=z_{J_v(q)}.
 \tag{PCR.31}
$$

The last equality is licensed by genuine core-only evolution. It is
not a backwards extension of the original singular stream. The $-1$
retains the original one-based birth convention; omitting it would
already give the wrong root orientation in general.

Induct on the length of the actual physical prefix. At a branch the
computed bit therefore creates exactly the actual two initial child
labels at the actual normalized time, preserving physical order. Alpha
promotion and later branching give exactly the label predicate in
Definition 10.1. Every failed descent is an actual absent extension;
every successful descent retains the correct immutable descriptor.
The root exists at every nonnegative normalized cut, including $T=0$.
This proves presence and the terminal predicate, including empty words,
newest cherries and later descendants. It is the local version of GPO
Theorem 39.4 with its previously unsupplied clock inputs now earned as
operators. A disagreement between finite supports has a word in their
symmetric difference, whose full literal is the promised witness.
$\square$

## 11. Completed original updates and the physical boundary

**Definition 11.1 (synchronized use of a retained boundary).** At a
completed source cut retain $\mathcal B_v(T)$, its actual root binding,
and the original origin association. A real original-source update is
serialized with Reads and local commits. After its completed
acknowledgement and before exposing the new boundary, replace the
represented age by $T+1$, committing the changed counter and any
required writer record. Keep $v,g,y,Q_1,Q_2$ unchanged. If the source
can complete several acknowledged updates atomically relative to this
consumer, replace $T$ by $T+u$ with their authentic count $u$.

An arithmetic addition by a hypothetical $u$ without those completed
source operations prepares a forecast. It does not advance the source,
prove a duration has elapsed, restore a revoked grant or install a
callable observer. The interface makes no assertion at an interrupted
or concurrently modified intermediate cut. Resuming there needs the
same original completion/reconciliation premises as GPO Theorem 34.3.

**Theorem 11.2 (response/update correspondence).** Let acquisition and
installation finish at one stationary completed cut satisfying
Definition 8.1. For every finite serial continuation of local literal
Reads and completed original-source updates, including adaptive choices
based on actually returned replies, the retained descriptor answers
exactly the actual presence family at every completed boundary. The
map from actual normalized source histories to (PCR.24) commutes with
completed updates. No new source-learning Read is needed after
installation while the authentic autonomous-source promise continues.

Proof. At installation, Theorem 10.2 establishes the invariant that the
retained age is the actual $n-e$, and every predicted immutable
descendant descriptor is the actual one. The clock seeds refer to this
fixed origin; the exterior forest continues its Fibonacci count rule,
so its $I_k$ and the operators continue to describe the same original
indices. One original update increments $n-e$ by one. It changes none
of the immutable descriptors, the original aligned core, the origin or
the seed operators. Definition 11.1 therefore restores the invariant at
the next completed cut. In particular it would be wrong to reinterpret
$(Q_2,Q_1Q_2)$ as a new beta root after an arbitrary physical update:
the root is already a branch, and there has been no physical recut.

At an actual Read the evaluator agrees by Theorem 10.2, while the real
call is still executed and charged. Induction on the finite serial call
word proves all replies, including adaptive continuations since equal
actual previous replies give the same next supplied choice. This is
GPO's completed-continuation semantics, with a compact local consumer;
it does not simulate completion of a source call by local prediction.
The invariant also proves that compressing the mature updated acquired
support returns this same immutable descriptor with its updated age,
by Theorem 9.3. The correspondence is at completed boundaries and
requires the stated binding, serialization, allocation, commit and
synchronization services. $\square$

## 12. Represented operands, sequential costs and explicit output

**Definition 12.1 (the charged coordinates).** Write
$b_t=\lceil\log_2(t+2)\rceil$. Let $\Gamma$ be the material size of
supplied code, binding/grant records and any required finite origin and
transfer metadata; count its actual representation, not a unit-cost
capability. Count $Q$ actual presence Reads, $U$ actual original-source
updates, $M$ maximum full-root literal length, $J$ their summed lengths,
$C$ sequential bit work including head motion, $W$ *all cumulative*
scratch and retained bit writes, and $V$ peak owned visited backing.
Overwrite, initialization, temporary powers, failed trials, copied
addresses and released records all count in $W$. Reusable backing may
reduce $V$ without reducing $W$. A transcript retained for audit counts
its entire payload separately. External service prices and durations are
not assigned unit tariffs by a binary-operation count.

**Theorem 12.2 (finite conversion and request bounds).** There is one
fixed finite sequential algorithm for Theorems 8.2--11.2. With
$A=d+m+b_T+\Gamma+2$, conversion from the acquired three-prefix record
at the first sufficient $s$ satisfies, for an absolute constant $c$,

$$
 C_{\rm cv},W_{\rm cv}\le c A^{12},\qquad
 V_{\rm cv}\le c A^4,\qquad Q_{\rm cv}=U_{\rm cv}=0.
 \tag{PCR.32}
$$

Reading/transferring the actual record and its metadata is included
when it has been materialized in the supplied sequential backing;
external transfer/acquisition services remain charged in addition. The
retained mathematical data have length

$$
 4r+m+b_T+O(\log(d+2)+1)
 \tag{PCR.33}
$$

at $r>0$, using four length-$r$ coefficient/seed/operator strings,
with the supplied metadata of size $\Gamma$ added separately. For
zero only $v,T$ and a zero tag are needed. A self-delimiting integer
encoding changes these lengths by at most a constant factor and
logarithmic delimiters. No bound here treats $T$ as a unit-cost integer.

For a request of suffix length $h$, an optional binary forecast offset
$u$, and explicitly requested output of length $L_{\rm out}$, put

$$
 A_q=d+m+h+b_T+b_u+\Gamma+L_{\rm out}+2.
$$

The local work and cumulative writes are at most $cA_q^{12}$ and peak
backing at most $cA_q^4$, including full literal construction and copying
the requested output. The one presence answer has length one. A real
presence request additionally has $Q=1$, $M=J=m+h$ and its physical
Read cost. Pure prediction has $Q=0$ and must be identified as such.
A counter commit after one completed update has local work and writes
$O(b_{T+1}+1)$ plus the actual writer-record and binding cost. Adding
an authentic binary count $u$ costs $O(b_T+b_u+1)$ locally, in addition
to those $u$ original updates. The field-algebra construction never
uses a numerical operand of length proportional to the core period.

Proof. The input prefixes have $6d$ bits. Minimal Hankel rank and solves
use $O((d+1)^2)$ bits of matrices and polynomially many binary row
operations. The two solves (PCR.26), monic polynomial multiplication,
reduction and extended Euclid use $O((d+1)^3)$ elementary bit operations
per operation under ordinary dense implementations. There are
$O(\log(d+2))$ reverse steps. Sequential scans can implement all of them
on polynomially bounded strings; even a scan for every indexed access
and a further quadratic sequential simulation are absorbed in (PCR.32).
The retained strings are $g$'s $r$ coefficients below its implicit monic
term, $r$ seed bits and two $r$-bit operators. Their degree and framing,
the literal $v$, age and metadata give (PCR.33).

For a request, an ancestor of relative depth $i$ has branch time at
most $2i+1$. Only proper prefixes of $w$ need bits, so $k\le2h-1$ at
$h>0$. Precompute $Q_1,\ldots,Q_{2h}$ by (PCR.27), or stream and
recompute as needed; this uses $O(h)$ ring products and $O(rh)$ bits
if the table is kept. Fibonacci numbers through $2h+2$ have $O(h+1)$
bits. Their table occupies $O((h+1)^2)$ bits and can be constructed by
ordinary binary addition. Each $D_q$ is a sum of at most $h$ sibling
masses; on the actual local tree it is less than $F_k$, since it counts
beta parents strictly preceding $q$ in that batch. Even using the loose
sum bound, it has $O(h+\log(h+2))$ bits. The algorithm never writes
$I_k$ or $J_v(q)$: it represents their powers by $r$ coefficients.
Binary powering of $x^{D_q}$ uses $O(h+\log(h+2))$ ring products, each
of degree-less-than-$r$ operands. There are at most $h$ such evaluations.
The remaining path times, sibling labels, additions and comparisons
with $T+u$ are polynomial in $h,b_T,b_u$. This is the classical
supplied-recurrence quotient evaluation of [Bostan--Mori, §1.3][PCR-BM], with the
actual index split proved in (PCR.31). No field or square-free quotient
is required.

All temporary tables, counters, prefix descriptors and literal buffers
fit a polynomial in $A_q$. Each arithmetic operation admits a sequential
scan implementation with polynomial head motion and writes. Allowing
$A_q^4$ backing and $A_q^{12}$ time/writes is a conservative common
envelope for these explicit loops, not a fast-arithmetic claim. It
also covers $h=0$, $d=0$, reading the metadata and output copies.
The binary addition/commit bounds include carry propagation. The
physical service must actually execute its call; $m+h$ literal letters
must be materialized even when arithmetic uses the suffix locally. No
construction here supplies a missing allocation, grant, binding or
synchronization service; their availability and actual physical duration
remain explicit premises rather than inferred machine-operation bounds.
$\square$

**Theorem 12.3 (finite continuation and output bills).** For any finite
actual continuation, sum the request/conversion work and write bounds,
all counter commits, acquisition and transfers, and every required
record and output copy. This gives a finite cumulative $C,W$ bound;
peak $V$ is the retained boundary, the maximum active scratch, actual
retained journal/output, and the separate original source backing.
There is no constant cumulative-write or constant retained-age bound
for an unbounded run. If the actual cut is $n$ and $u$ original updates
complete, the source consumes exactly

$$
 F_{n+u+1}-F_{n+1}
 \tag{PCR.34}
$$

new birth bits. Inside this cone the number of births is
$F_{T+u+2}-F_{T+2}$, and the number of new physical nodes is twice
that value. These physical operations, label promotions, allocations,
actual synchronization and installation are not eliminated by prediction.

Proof. Sequential composition adds work, writes and paid calls. Scratch
can be released between calls but previously written bits remain in
$W$; retained outputs and records remain in peak backing until actually
released. Original total births at cut $n$ are $F_{n+1}-1$; subtracting
the two completed totals proves (PCR.34). The local beta-origin total
births through $T$ are $\sum_{k=1}^T F_k=F_{T+2}-1$, giving the local
formulas. A representation of a request does not perform any of these
source operations. Global $n$ is not recoverable from this local $T$
alone, so (PCR.34) is an accounting fact about the actual execution,
not an additional numerical register furnished by the boundary.

For explicit full support at local age $t$ there are
$N_t=2F_{t+2}-1$ nodes. A list of full physical addresses has payload
$\sum_{w\in S_t(v)}(m+|w|)$ plus delimiters; it needs at least one
record per node even if $m=0$. The terminal-boundary list has
$F_{t+2}$ entries. An implementation can enumerate using the evaluator
or forward substitution and charge each output letter and scratch
operation; a compact description alone is not that explicit output.
Likewise a chronological batch output contains $F_k$ orientation bits.
Any proposed output bound must include these lengths. Costs for
retained journals include actual literal payloads, replies, completed
update acknowledgements and commit fields, as in GPO Proposition 35.1.
$\square$

## 13. Sufficient acquisition and the limit of a short record

**Theorem 13.1 (two sufficient suppliers with their different prices).**
There are the following source-faithful ways to reach Definition 8.1.
They do not imply that an arbitrary finite menu, an unearned bit string
or a young support already meets that definition.

First, at any actual cone satisfying the core-only premise, a complete
stationary paid root-literal scan supplies its whole ordered support,
its age and its visible batches. If $T\ge s+3$, this yields (PCR.24).
With $N=2F_{T+2}-1$, a scan which pays both child tests at every
present node has

$$
 Q\le2N+1,\qquad M\le m+T+1,\qquad J\le(m+T+1)(2N+1),\quad U=0.
 \tag{PCR.35}
$$

The initial confirmation is included; an already earned root can omit
it. If the acquired full-address support record has encoded length $L$,
conversion/extraction has conservative sequential work and cumulative
writes at most $c(L+d+\Gamma+2)^{12}$ and peak backing at most
$c(L+d+\Gamma+2)^4$. Expanded-record disposal does not refund its
writes. The retained boundary still has (PCR.33)'s size. In particular
(PCR.35) is generally exponential in $T$, not a polynomial paid
acquisition in $d,\log T$.

Second, in PSA Definition 1.1's *original entrance* with earned spine
$h$, $H=2h+1$, and $S=d+H+2$, the deep branch of PSA Theorem 2.1
actually supplies a cone with $s+3\le T\le2(s+3)$ and $N=O((d+1)^2)$.
Its complete scan and chronological decoding furnish the record here.
All complete root literals have length at most $H$; the spine and scan
use $O(\log(H+2)+(d+1)^2)$ Reads and at most $H$ times that total
literal traffic. The represented records, sequential calculations,
cumulative scratch/retained writes and peak backing admit, for example,
the conservative envelopes $c(S+\Gamma+2)^{60}$ and
$c(S+\Gamma+2)^8$ respectively. These
cover this supplier's prelude and conversion, without asserting any
improvement to PSA's full-domain acquisition bound. If its shallow
branch applies it instead acquires the original complete root and
$(P,n)$, with $O((d+1)^4)$ nodes; that root need not be core-only.
The second supplier is a genuine polynomial-size acquired local example
in the full source class. It neither selects the user's arbitrary $v$
nor makes a huge support at a prescribed $v$ cheap to scan.

Proof. Prefix closure and actual full binarity justify scheduling each
positive child once. Paying both child tests at each present node
closes all terminal absences and cannot stop at an unqueried fringe.
The normalized maximum depth is $T$ and a terminal test adds at most
one, giving (PCR.35). The acquired leaf count $F_{T+2}$ determines
$T$ uniquely, including $T=0,1$. Theorem 2.1 determines exactly the
visible batches, sorted by normalized update and *physical* address.
Counts, heights and addresses can be stored in delimited records and
propagated by finite repeated scans, with comparison sorting if desired.
Since $T\le N$, and an explicit record has at least $N$ entries,
all these computations and sequential address accesses fit the
stated polynomial in $L+d+\Gamma$. This does not shrink its input
bill to a polynomial in a succinct unknown age.

For the second supplier use its *proved* terminal-spine dichotomy,
not a generic cone assertion. Its earned all-$a$ endpoint, $s+3$
ancestors and rank decrements give exactly the stated local age
interval. Its selected depth is at least the ACR core cutoff, so every
subsequent birth is a core birth at its original index even when the
original stream has a singular transient. PSA Theorem 2.2 supplies
(PCR.22). These are precisely the physical selection hypotheses which
Theorem 8.2 did not give for an arbitrary cone. Its scan node/address
bounds and polynomial finite record processing give the stated price;
the larger conservative envelopes also accommodate the matrix/operator
conversion and all copies. This relies only on that prelude and the
checked algebraic inverse, not on assuming a successful original
normalization or installation. At $d=0$ the known zero law requires no
batches, but the age, binding and all actual service costs still need
their own supplier. $\square$

**Theorem 13.2 (necessary information, rather than a prescribed menu).**
On any fixed comparison family at a common age, equality of an acquired
data map $D$ implying equality of every response in (PCR.21) is necessary
for an exact deterministic predictive decoder. It is sufficient for a
set-theoretic factorization of those responses through $D$; neither
effectivity nor a polynomial decoding algorithm follows from that alone.
On the full mature core-only family it is equivalently that each data
fibre lies inside one of Theorem 9.3's descriptor fibres. Complete
support or the authentic three-prefix record above is sufficient with
the explicit decoder and costs; no necessity of exactly three batches
or the displayed slack horizon is claimed.

Proof. Equal data give the same deterministic retained computation;
a response which differs on that fibre is impossible to predict
correctly for both sources. Conversely, if every response is constant
on each fibre, it defines a mathematical response function on fibres.
This assertion alone supplies neither an effective encoding, termination
nor a polynomial algorithm. Theorems 8.2--12.2 provide those additional
properties for their stated inputs. The descriptor-fibre formulation
uses the already proved complete classification in Theorem 9.3.

For concrete failures reuse Proposition 2.2's shallow-menu saturation:
any fixed finite menu, at all sufficiently old actual cuts, consists
entirely of present words, whereas actual different constant sources
have different ordered supports and futures. The same fixed full
prefix $v$ can be chosen past the core cutoff for both constants;
its branch origins have bounded finite difference, and one can compare
at the same arbitrarily large normalized $T$. All queried suffixes
still saturate, but the constant-zero and constant-one cone supports
at $T\ge2$ differ. Adaptive acquisition earns only its actual transcript;
it must prove its fibres sufficient rather than invoke this fixed-menu
example as a universal adaptive lower bound.

Nor is youth sufficient even with the entire support: in actual
constant sources $0^\infty$ and $1^\infty$ the alpha root is beta at
$e=1$, and the two core-only cones have identical support at $T=1$.
At $T=2$, $aa$ is present exactly for the all-one source. They belong
to $\mathscr R_1$ and show a common young support with different local
future, with full-root paid separator $aa$. With a *fixed* nonconstant
core the more restrictive actual pair in Proposition 6.1 has the same
lesson before its maturity bound. An authentic stronger law may make
younger data sufficient; none of these examples forbids that.
$\square$

## 14. Degenerate, padded and transient cases in the original class

**Theorem 14.1 (the domain has not been narrowed).** The construction
covers zero, both constants, nonminimal original presentations and
periodic cores whose *least* polynomial has repeated factors. It does
not extend the core-only conclusion to a cone with a singular birth
inside it. There is no inverse here for the original transient, actual
integer clocks, original global age, exterior geometry or private law
presentation from a local boundary alone.

Proof. Zero and the all-one core were handled explicitly in Theorems
8.2 and 9.2, including $d=0$. For a concrete genuine repeated-factor
case take the purely periodic stream $00110011\cdots$. It has
$(E+1)^3=E^3+E^2+E+1$ as its least polynomial: the four-term recurrence
holds, and its leading $3$ by $3$ Hankel matrix is

$$
 \begin{pmatrix}0&0&1\\0&1&1\\1&1&0\end{pmatrix},
$$

whose determinant is one in $\mathbb F_2$. Thus its least degree is
three. In $R_g$ the class $x$ is a unit even though $x+1$ is a
nonzero nilpotent. Only powers of $x$ are inverted in the clock
construction; no step discards the repeated factor. Purely periodic
$0101\cdots$ similarly has least $g=(X+1)^2$. Hence reduced or
semisimple dynamics are not assumed. A redundant original modulus is
allowed by $\mathscr R_d$ and disappears only because the actual rank
calculation computes the least core polynomial. Inverting a numerator
under an arbitrary padded modulus would fail in PSA Proposition 3.2's
all-one example; that is not the algorithm here.

For a singular original stream, ACR Theorem 27.3 supplies
$s=y+t$, $E^at=0$, with $a+\deg g\le d$. All source-specific uses of
$y$ above are at actual original indices in a genuinely core-only cone.
The transient can be arbitrary within that promise, including early
bits used to create $v$ and its exterior. Their consequences for the
later local indexing are retained in $Q_1,Q_2$; their full values are
not recovered. If a birth inside the cone is transient, (PCR.31)'s
last equality is not licensed. Proposition 6.2 gives actual constant-core
pairs with identical normalized exterior clocks and different early
local supports; it refutes precisely that extension. No inference of
core-only evolution from empirical periodicity repairs it.

The local-output separation in PSA Proposition 4.3 gives original
sources with the same actually selected acquired cone and core but
different original $(P,n)$. It is a direct counterexample to treating
this compression as whole-source recovery. More generally the discarded
integer multiples of $p$ in the clocks, erasure of exterior geometry
and transient distinctions are already recorded by Propositions 4.2
and 7.1. The original source class has not been replaced by a short
period or a reversible all-index class. $\square$

## 15. Linear dimension, attainable capacity and unbounded age

**Theorem 15.1 (three distinct minimality questions).** For a fixed
nonzero core of least degree $r$, the unary scalar sequence
$i\mapsto y_i$ has least linear realization dimension $r$ over
$\mathbb F_2$. This does not prove that the nonlinear physical literal
response system, a controller's total bits, or its number of discrete
states is $r$. At fixed aligned core and fixed mature age, hypothetical
clock trials have $p^2$ distinct initial local behaviours; a specified
actually attainable clock family $\mathcal A$ has exactly the cardinality
in (PCR.7). A deterministic boundary at that age therefore needs at
least this many possible configurations, and at least its base-two
logarithm in fixed-length binary capacity. This counts initial behaviours
at one cut, not a finite carrier closed under unbounded updates. There is no assertion that all $p^2$
trials occur as actual histories.

Proof. The Hankel matrix $H_r(y)$ is nonsingular by (PCR.25)--(PCR.26).
Any $q$-dimensional linear realization factors its Hankel matrix into
a matrix of reachable rows times observable columns, of inner dimension
$q$, so $q\ge r$. The companion realization achieves $r$. This is the
classical unary instance of [Kiefer, Proposition 3.3 and the
Hankel/minimal-realization correspondence in §§3--4][PCR-KIE], with
$K=\mathbb F_2$, alphabet a singleton, and series $a^i\mapsto y_i$.
Kiefer's bit-complexity convention is rational coefficients; no rational
complexity bound is transferred here. The elementary binary-operation
bounds were supplied separately in Theorem 12.2. Zero has linear
dimension zero. This argument concerns a supplied scalar series, not
acquisition or the address-driven response transformation.

The state count is exactly Corollary 3.2, now represented by the
operator pair through (PCR.28). Count the whole predictive configuration,
including any source-dependent code or immutable advice; moving a clock
into such advice cannot evade this distinction bound. Distinct behaviours force distinct
retained deterministic predictive states at the common age; a carrier
of size $K$ needs $K$ values, or at least $\lceil\log_2K\rceil$ bits
with a fixed-length code. Variable-length codes retain their actual
lengths and corresponding counting bound. An encoding can combine the
two clocks into one register; two named registers are not a lower
bound. Restriction to $\mathcal A$ gives its image size and no
surjectivity claim. The stored pair uses $2r$ coefficient bits, and the
whole descriptor has (PCR.33)'s upper bound; it is not claimed to be a
bit-optimal representation. The period may be as large as $2^r-1$ in
a primitive core, so a small description is compatible with exponentially
many discrete states. $\square$

**Theorem 15.2 (finite descriptions do not make an age-free finite
carrier).** Even for a fixed zero core and a fixed actual $v$, the
family of all normalized cuts cannot be represented by one fixed finite
state carrier which answers every local literal correctly, unless the
unbounded age or equivalent state is supplied externally and charged.
A finite description at each cut, such as (PCR.24), is consistent with
this obstruction.

Proof. The supports at ages $T=0,1,2,\ldots$ have strictly increasing
leaf counts $F_{T+2}$. They are therefore pairwise different. For any
two ages a word in the symmetric difference is a finite physical literal
at the same retained prefix. A deterministic representation which
answers all current literals must distinguish these ages, even before
any further update. A finite carrier cannot do so for infinitely many
ages. Allowing an external age argument, unbounded backing, a changing
address journal or the actual source as additional readable state moves
the information and its cost rather than refuting the argument. The
binary age counter in (PCR.33) grows without bound; it is finite for
each finite cut. This proof is independent of numerical phase extraction
and already holds at $r=0$. $\square$

## 16. Supplier correspondence and the retained original goal

**Definition 16.1 (the scope of the derived addition).** The new
source-specific results are the general-cone bridge in Theorem 8.2,
acquired clock-operator extraction in Theorem 9.2, the mature
data/representation equivalence of Theorem 9.3, the actual full-literal
and completed-update correspondences of Theorems 10.2 and 11.2, and
their charged finite representations and supplier boundaries. Their
classical algebra occurs only as intermediate supplied-input tools.
The faithful correspondence is as follows.

| Supplier | Parameters and conclusion consumed | Obligation not supplied |
| --- | --- | --- |
| PCR Theorems 2.1, 3.1, 4.1 and Corollary 3.2 | Actual ordered batches, mature equality and least-period two-clock classification | A small arbitrary Read menu, attainable surjectivity or installed consumer |
| PSA Theorem 3.1 and Proposition 3.2 | Three acquired $2d$ prefixes satisfying (PCR.22), least core and original aligned seed, proved-unit/padding boundary | Its terminal-spine physical selection outside the separately mapped prelude, original firstness or source execution |
| ACR Theorems 27.2--27.3 | Same $v,e,k$, actual one-based $I_k$, skipped physical siblings and a sufficient depth cutoff | An earned arbitrary cone, cheap deep-clock phase or free normalization |
| GPO Definitions 27.1, 29.1 and Theorems 34.3, 39.4 | Original alpha source, all-index law including singular transients, full-root requests and serialized completed use | A relative-root port, free synchronization, source-free execution or a core-only certificate from finite apparent periodicity |
| Massey §§II--IV; Shoup §§16.4, 18.1--18.2 | Connection/forward polynomial conventions, least Hankel synthesis, module action, Euclidean unit inverse | Physical samples, ordered birth provenance, original cut or $\rho_d$ firstness |
| Bostan--Mori v1 §1.3 | A represented recurrence/seed and monic-quotient term evaluation | Acquisition, field reduction, a free random-access physical source |
| Kiefer v1 §§1, 3--4 | Unary supplied scalar series, Hankel-rank bound and linear-realization dimension | Minimal physical controller capacity or paid presence acquisition |

**Theorem 16.2 (existing native suppliers do not substitute for this
binary acquired input).** The inspected native companion and post-clock
inverse results have different exact input types. They do not eliminate
any actual-input, cost or completion hypothesis above. The local result
does not settle the full original normalization and installation target.

Proof. `D5.S1.Recurrence.FiniteCompanionCyclicModule.evaluate_ker` and
`cyclic_presentation` quantify over a commutative ring $A$, $u\in A$,
and $q>0$, using the specific polynomial
$P(u,q)=X^q-u\sum_{j<q}X^j$, the first-vertex vector and its particular
forward-time map. Its Blueprint gives the explicit coordinate inverse,
including the zero ring. An arbitrary acquired binary core polynomial
$g$ is not that polynomial family. Mapping (PCR.25) therefore requires
the annihilator/Hankel argument actually supplied here; specializing
$A=\mathbb F_2$ alone does not identify the time map or provide the
presence observations. The inspected project imports
`FiniteCompanionSquareDefect` and `FiniteCompanionDefect` retain these
native operators rather than introducing an arbitrary-core physical
input theorem.

`D5.S3.Arith.FibonacciAtomic.Observer.OriginalVector.NativePostClockInverse.postclock_inverse`
assumes positive rational $a,c$, determinant nonvanishing on every
reached legal native term, and a current endpoint consisting of the
full native term plus its exact rational field on the explicitly listed
finite material support. Its decoder unticks by rational adjugate and
determinant arithmetic, recognizes the fresh zero pattern, collapses
the last edit and recurses with current material-size fuel. The reached
image and positivity proof are its real hypotheses. Its Blueprint and
project import closure through `NativeFreshSensorGrowth`,
`NativeGuardedLeafRepair` and `NativeMaterialRootRecognition` preserve
that field/material interface. Binary presence replies here are not a
rational field, and the simultaneous original actuator is not that
addressed guarded edit history. No bridge recovering its richer input
is supplied or assumed. Reading those Lean/Blueprint sources establishes
their stated domains, not a new compiled application or verification
of this appendix.

The primary mathematical passages used here are Massey's finite
synthesis uniqueness and rational-series distinction (Theorems 3--4 and
corollary), Shoup's annihilator ideal, Hankel and module exercises,
reversed-Laurent theorem and unit criterion (Theorems 18.1--18.2,
16.18; Exercises 18.2--18.6), Bostan--Mori's monic-quotient evaluation,
and Kiefer's field-valued Hankel factorization/minimality. These concern
supplied inputs. The additional derivations concern this original
physical birth order and its actually acquired local data. This bounded
supplier comparison supports no worldwide originality or nonexistence
claim.

Finally the original requested $(P,n)$ includes transient information
which a local core record omits. After that acquisition, the original
normalization still requires
$K_d(P)=(\rho_d(i_P),P[0:d])$ with
$i_P=\min\{i:H(P)\rho_d(i)=y(P)\}$ in the *same original* enumeration;
ACR Theorems 26.1 and 29.2 charge its row evaluations, firstness search,
full $B_n=F_{n+1}-1$ output and installation. At positive $d$, the
zero original stream still requires $(\rho_d(0),0^d)$, not a freely
chosen zero row. An explicit original tuple has $4d$ prefix/row/seed
bits plus the represented $n$ and $B_n$ and framing; the bit length of
$B_n$ is $\Theta(n)$ for $n\ge2$. These original output writes are
additional to the compact local descriptor. Here $y(P)$ in that
Hankel system is ACR's original right-hand-side notation, not the
periodic core denoted by $y$ above. A computed least $g$, a convenient
core seed, a quotient representative or an auxiliary row cannot replace
that output. In particular deficient-rank firstness for the original
$\rho_d$ has no new polynomial bound here. Actual original acquisition,
canonical installation, physical lifetime and the broader recovery of
space, time, boundary and memory remain their original typed tasks.
The local predictive-consumer theorem makes no assertion that those
physical services have already been carried out. $\square$

[PCR-PSA]: RECURSIVE_RELATIONAL_OBSERVATION_POLYNOMIAL_SOURCE_ACQUISITION.md
[PCR-SHO]: https://shoup.net/ntb/ntb-v2.pdf
[PCR-BM]: https://arxiv.org/html/2008.08822v1
[PCR-KIE]: https://arxiv.org/pdf/2009.01217v1

## 追加锚（本行以下为增补区）

## 17. Transport to genuine physical children

**Definition 17.1 (integer boundary coordinates and child delays).**
Fix one source $s\in\mathscr R_d$ with its original alpha initialization,
physical order and aligned decomposition $s=y+t$ from Definition 1.1.
Consider its entire original forward orbit. For every finite physical
address $v$, put

$$
 A_v=I_v(1),\quad B_v=I_v(2),\quad e_v=\tau_v-1,
 \qquad c_v=s_{A_v-1}.
 \tag{PCR.36}
$$

These are mathematical attributes of the actual source, not entrance
registers. Every finite address is eventually created: the root branches
at cut two, and a newly created beta or alpha branches respectively one
or two cuts after creation. At the normalized origin of $v$, its first
branch is in local update one and consumes bit $c_v$. For a physical
child $vx$, let $\delta_x(c_v)$ be one for an initially beta child and
two for an initially alpha child. Thus

$$
 (\delta_a(1),\delta_b(1))=(1,2),\qquad
 (\delta_a(0),\delta_b(0))=(2,1).
 \tag{PCR.37}
$$

**Theorem 17.2 (authentic integer child transport).** For every $v$,
including cones containing singular births, the root boundary and child
boundaries satisfy

$$
 (e_\varepsilon,A_\varepsilon,B_\varepsilon)=(1,1,2),
 \qquad e_{vx}=e_v+\delta_x(c_v),
 \tag{PCR.38}
$$

and the following exact integer table:

$$
\begin{array}{c|c|c}
 c_v &(A_{va},B_{va})&(A_{vb},B_{vb})\\ \hline
 1 &(B_v,A_v+B_v)&(A_v+B_v+1,A_v+2B_v+2)\\
 0 &(A_v+B_v,A_v+2B_v)&(B_v,A_v+B_v+1).
\end{array}
 \tag{PCR.39}
$$

The children are created at actual cut $e_v+1$. Their normalization
origins are $e_v+1$ for beta and $e_v+2$ for alpha; neither is the
parent's normalization origin. In particular $1\le A_v<B_v$ and
$A_{vx}>A_v$. If $v$ is genuinely core-only, then so are both children,
$c_v=y_{A_v-1}$, and reduction of this table modulo the least period
$p$ is a well-defined transport depending only on $(A_v,B_v)\bmod p$.

Proof. The alpha root becomes beta at cut one, and its first two birth
batches begin at indices one and two. A child born at parent-local cut
one branches at cut two if initially beta, and at cut three if initially
alpha. Its beta normalization is therefore at parent-local cut one or
two, proving (PCR.38). By (PCR.1), the parent's first four batch starts
are $A,B,A+B,A+2B$.

The $a$ child has no preceding sibling inside $v$. Its first two starts
are therefore $B,A+B$ in the beta case and $A+B,A+2B$ in the alpha
case. For the $b$ child, the $a$ sibling contributes its beta-leaf
mass just before each relevant update. If $c_v=0$, that sibling is born
alpha and has beta masses zero and one at parent-local cuts one and
two. The right beta child's starts are $B,A+B+1$. If $c_v=1$, the
sibling is born beta and has beta masses one and two at cuts two and
three. The right alpha child's starts are $A+B+1,A+2B+2$. These masses
are independent of the sibling's later orientation bits. The preceding
exterior of $v$ is already included in the parent's batch starts, by
[ACR, Theorem 27.2][ACR]; adding precisely these internal masses gives
(PCR.39), with the original one-based indices and physical order.

The inequalities hold at the root and are preserved by each integer
row; they also give strict increase of $A$ at every descent. A child's
birth events are a subset of its parent's future birth events, so
core-only evolution is hereditary. On that domain its first bit is the
aligned core bit; periodicity makes it a function of $A\bmod p$.
Induction on the address proves that these equations recover the actual
boundary of every physical node, rather than a separately chosen local
trial. $\square$

## 18. Exact transient seeding, including shallow core-only cones

**Definition 18.1 (finite early clock tree and defect ancestors).**
Let $a$ be the transient exponent of Definition 1.1, and set

$$
 D_s=\{j:1\le j\le a,\ t_{j-1}=1\},\qquad
 \ell_a=\min\{m\ge0:F_{m+2}>a\}.
 \tag{PCR.40}
$$

Construct a finite rooted address tree $H_s$ as follows. Start with
$(\varepsilon,e,A,B)=(\varepsilon,1,1,2)$. At a node with $A\le a$,
use its actual bit $s_{A-1}$ and (PCR.38)--(PCR.39) to include both
children with their integer coordinates. Stop a branch as soon as
$A>a$. Let

$$
 Z_s=\{v\in H_s:A_v\in D_s\},\qquad
 U_s=\{u\in H_s:\text{some }v\in Z_s\text{ has }u\preceq v\}.
 \tag{PCR.41}
$$

Here $\preceq$ includes equality. Define the seed addresses $C_s$ to be
$\{\varepsilon\}$ if $U_s$ is empty, and otherwise

$$
 C_s=\{vx:v\in U_s,\ x\in\{a,b\},\ vx\notin U_s\}.
 \tag{PCR.42}
$$

The $a$ in the address alphabet remains distinct from the transient
exponent. The integer recursion uses only actual source entries with
indices at most that exponent; it does not enumerate finite source
cuts or invent exterior forests.

**Theorem 18.2 (complete seed characterization).** The construction is
finite, contains every defect birth parent, and has depth at most
$\ell_a$. Its marked nodes are exactly the actual parents whose
orientation bits differ from the aligned core. For every physical
address $v$,

$$
 v\text{ is genuinely core-only}
 \quad\Longleftrightarrow\quad
 \text{no }w\in Z_s\text{ extends }v
 \quad\Longleftrightarrow\quad
 v\in\bigcup_{c\in C_s}c\{a,b\}^*.
 \tag{PCR.43}
$$

The finite, nonempty set $C_s$ is prefix-incomparable. Its members are
exactly the core-only nodes whose proper ancestors are not core-only.
In particular a safe node with $A_v\le a$ is retained whenever it has
no defect descendant; the condition $A_v>a$ is not used as a necessary
condition. All original singular transients are included.

For $L=\lceil\log_2(a+1)\rceil$ one has $\ell_a\le2L$,
$|H_s|\le2^{\ell_a+1}-1\le8(a+1)^2$. The integer coordinates have
$O(\log(a+2))$ bits. These are bounds on this supplied-source
mathematical construction, not paid acquisition bounds.

Proof. At physical depth $m$, the first branch is no earlier than cut
$m+2$, and its birth index is at least $F_{m+2}$, by ACR Theorems
27.2--27.3. Consequently every branch of the construction stops by
$\ell_a$. Its edges agree with the true orbit by Theorem 17.2. Every
actual birth $j$ has one parent, whose first branch index is $A_v=j$.
If $j\le a$, every proper ancestor has smaller first index, so the
construction reaches that parent before stopping. Conversely each
marked node consumes a defect bit at precisely its actual index.
Thus $Z_s$ accounts for every and only actual defect parent, including
ones generated by the transient's own altered physical wiring.

A cone's subsequent births are precisely the first branches of all
nodes extending its root. Each such node eventually branches. Its
birth agrees with the aligned core if and only if its index is not
in $D_s$, since $t$ vanishes outside the prescribed range. This proves
the first equivalence in (PCR.43). The unsafe set is exactly the finite
ancestor closure of $Z_s$; it is prefix-closed. If nonempty it contains
the root, and each of its children is present in $H_s$, since an unsafe
node has $A_v\le a$. Any infinite address path leaves this finite
unsafe tree through exactly one edge; any finite safe address has a
unique earliest safe prefix. Those prefixes are precisely (PCR.42).
If there is no unsafe node, the root itself is that prefix. This proves
both directions, nonemptiness and prefix-incomparability, without
replacing a shallow safe cone by a deeper frontier.

Finally $F_{2k+2}\ge2^k$ gives the stated depth and size bounds (at
$a=0$ the construction is just the root). The seed bounds in ACR
(ACR.114), applied at depth at most $\ell_a$, give
$A,B<F_{2\ell_a+4}<2^{2\ell_a+4}$; (PCR.38) gives
$e\le2\ell_a+1$. Their binary lengths have the claimed order. No
period or transient parameter has thereby become an observer input.
$\square$

## 19. An explicit finite image of the original source

**Definition 19.1 (source-calibrated residue relation).** On
$Q_p=(\mathbb Z/p\mathbb Z)^2$, define $c_y(A)=y_{A-1}$ by original
periodic indexing. Define maps $f_a,f_b:Q_p\to Q_p$ by the two columns
of (PCR.39), using $c_y(A)$ and reducing the result modulo $p$. Retain
on each edge $q\xrightarrow{x}f_x(q)$ the positive integer weight
$\delta_x(c_y(A))$ from (PCR.37). The seed set and its initial times are

$$
 E_s=\{(A_c,B_c)\bmod p:c\in C_s\},\qquad
 \{(c,e_c,(A_c,B_c)\bmod p):c\in C_s\}.
 \tag{PCR.44}
$$

The second object retains multiplicities of residue seeds at distinct
addresses or times. Let $N_y$ be the $p^2$ by $p^2$ nonnegative integer
matrix with row $r$, column $q$ equal to
$\mathbf1_{r=f_a(q)}+\mathbf1_{r=f_b(q)}$. Write $\mathbf1_{E_s}$ for
the indicator column. Put

$$
 R_s=\left\{q\in Q_p:
 \left[\left(\sum_{j=0}^{p^2-|E_s|}N_y^j\right)
                  \mathbf1_{E_s}\right]_q>0\right\}.
 \tag{PCR.45}
$$

At $p=1$ this uses the single residue $(0,0)$ and the zeroth matrix
power. Formula (PCR.45), the explicit edge table and the finite defect
construction specify $R_s$ without an oracle for reachable histories.

**Theorem 19.2 (both realization directions and timed transport).**
For this one fixed original source,

$$
 R_s=\{(I_v(1),I_v(2))\bmod p:
                  v\text{ is genuinely core-only}\}.
 \tag{PCR.46}
$$

Every matrix path starting at a seed lifts to its literal physical
address in the same original source. If its edge word is $w=x_1\cdots
x_h$, then

$$
 q_{cw}=f_{x_h}\circ\cdots\circ f_{x_1}(q_c),\qquad
 e_{cw}=e_c+\sum_{i=1}^h
       \delta_{x_i}(c_y(A_{cx_1\cdots x_{i-1}})).
 \tag{PCR.47}
$$

All quantities $A$ in the last formula may be reduced modulo $p$ for
the bit evaluation. Conversely every core-only address has a unique
seed prefix and supplies such a path. Every state in $R_s$ has a
realization with at most $p^2-|E_s|$ edges after some seed, although
this shortened witness need not retain an original witness's address
or normalization time. A cone on a particular path has normalized age
$T\ge0$ at actual cut $n$ exactly when $n=e_{cw}+T$. In particular the
full square is attained if and only if every coordinate of the explicit
column in (PCR.45) is positive; a zero coordinate is a strict-image
certificate for that supplied source.

Proof. By Theorem 18.2 every seed is an actual core-only cone. Suppose
a path prefix has been lifted. Both actual children eventually exist;
they remain core-only, and Theorem 17.2 gives exactly the two outgoing
residue states and the stated time increments. Induction proves the
lift for every finite word, including its normalization time. This is
the realization direction for the finite presentation; no hypothetical
state is installed as an actual cone. Conversely (PCR.43) writes every
core-only address uniquely as $cw$, and the same induction computes
its actual residues. This gives equality with the states reached by
arbitrary finite graph paths.

For completeness, a shortest path from the seed set to any reached
state repeats no vertex, and has no seed vertex after its initial one:
a repeated segment can be deleted, and a later seed allows a shorter
start. All vertices after its first therefore lie in the complement
of $E_s$, so its length is at most $p^2-|E_s|$. Matrix powers count
these paths, proving (PCR.45)--(PCR.46), including both inclusions.
Deleting a repeated segment changes the sum of positive time weights;
there is no same-time shortening assertion. The time statement is
precisely the original normalization equation of Definition 1.2.

The elementary finite-path argument applies only after the physical
transport and transient initialization have been established. In the
terminology of [Rigo--Stipulanti, *Automatic sequences: from rational
bases to trees*, arXiv:2102.10828v5, Definition 25 and Theorem 28](https://arxiv.org/html/2102.10828v5),
the residue-decorated full address tree below a seed has finitely many
suffixes; Theorem 28 concerns an abstract numeration system built on a
prefix-closed regular language. Its address-enumeration correspondence
is not this source's chronological birth enumeration. Neither that
result nor finite graph closure supplies (PCR.39), (PCR.43), the actual
normalization times or a physical Read service. $\square$

**Proposition 19.3 (a strict-image obstruction).** Suppose $p>1$ and
the aligned core satisfies $y_{-1}=0$ and $y_{-2}=1$. If neither
$(0,0)$ nor $(-1,-1)$ belongs to $E_s$, then

$$
 R_s\subseteq Q_p\setminus\{(0,0),(-1,-1)\},
 \qquad |R_s|\le p^2-2.
 \tag{PCR.48}
$$

In particular every purely periodic source with these aligned terminal
bits satisfies this obstruction. The presence of a transient can change
the seed set, so this statement is not extended by forgetting $E_s$.

Proof. Each of the four affine branches in (PCR.39) has an invertible
linear part modulo every $p$. An edge into $(0,0)$ can have predecessor
$(0,0)$ in the $a$ column, $(-1,0)$ in the $b,c=0$ case, or
$(0,-1)$ in the $b,c=1$ case. The latter two require respectively
$c_y(-1)=0$ and $c_y(0)=1$, both contrary to the assumed bits. Thus
its only permitted incoming edges are from itself. An edge into
$(-1,-1)$ in the $a,c=1$, $a,c=0$, or $b,c=0$ cases requires
predecessor $(0,-1)$, $(-1,0)$, or $(-1,-1)$, respectively. These
require $c_y(0)=1$ or $c_y(-1)=0$, again impossible. The remaining
$b,c=1$ predecessor is $(-1,-1)$ itself and is permitted. Neither
vertex can first be entered from its complement. The seed assumption
therefore excludes them from (PCR.45). They are distinct for $p>1$.
For a purely periodic source the sole seed is the root $(1,2)\bmod p$,
which equals neither excluded pair: the second equality would require
$p$ to divide both two and three. $\square$

## 20. Actual strict and full images, and a shallow safe seed

**Proposition 20.1 (the same aligned core with two different images).**
Let $y=(10)^\infty$ with its displayed index-zero alignment. The purely
periodic original source $s=y$ belongs to $\mathscr R_2$ and has

$$
 p=2,\qquad R_y=\{(1,0),(0,1)\},\qquad |R_y|=2<4.
 \tag{PCR.49}
$$

For the original source $s'=y+(1,0,0,\ldots)=(001010\ldots)$,
the same aligned core has $a=1$, $s'\in\mathscr R_3$, and

$$
 C_{s'}=\{a,b\},\quad q_a=(1,1),\quad q_b=(0,0),
 \qquad R_{s'}=(\mathbb Z/2\mathbb Z)^2.
 \tag{PCR.50}
$$

The full square is therefore neither universally attained nor universally
excluded, even with the aligned core fixed and with authentic singular
sources retained.

Proof. The least core annihilator is $g(E)=E^2+1$ over $\mathbb F_2$:
$y$ has period two and is nonconstant, so neither order zero nor the
constant-term-one degree-one polynomial annihilates it. The first
source is purely periodic, and its root state is $(1,0)$. For this
aligned core, the entire residue table is

$$
\begin{array}{c|c|c|c}
 q&c_y(A)&f_a(q)&f_b(q)\\ \hline
 (0,0)&0&(0,0)&(0,1)\\
 (0,1)&0&(1,0)&(1,0)\\
 (1,0)&1&(0,1)&(0,1)\\
 (1,1)&1&(1,0)&(1,1).
\end{array}
 \tag{PCR.51}
$$

The two off-diagonal states form a closed set, both occur from the root,
and the other two cannot be reached, proving (PCR.49) by Theorem 19.2.
This is also the sharp $p=2$ instance of Proposition 19.3.

The transient of $s'$ is killed by $E$; $E(E^2+1)$ annihilates $s'$
at every nonnegative index, so the source is in the original class with
$d=3$. Coprime decomposition gives exactly the displayed aligned core
and transient. Its only defect is birth one at the root. That actual
birth uses zero, so the integer child boundaries are $(3,5)$ at $a$
and $(2,4)$ at $b$, with origins $e_a=3,e_b=2$. Both children are
core-only and are the minimal safe seeds. Their residues are the two
diagonal states. By (PCR.51), $a$ followed by $a$ reaches $(1,0)$,
and $b$ followed by $b$ reaches $(0,1)$; thus all four states have
actual address witnesses. This uses the original transient to initialize
the image, not hypothetical seed states. $\square$

**Proposition 20.2 (a core-only seed inside the transient bound).**
Let $y=(01)^\infty$ and $s=y+(0,0,1,0,\ldots)$. This original
source lies in $\mathscr R_5$, has transient exponent $a=3$, and has

$$
 Z_s=\{a\},\qquad U_s=\{\varepsilon,a\},\qquad
 C_s=\{b,aa,ab\}.
 \tag{PCR.52}
$$

In particular $b$ is genuinely core-only although its first birth index
is $A_b=2\le a$. Its normalization origin is two, whereas those of
$aa,ab$ are four and five. A depth or first-index cutoff alone would
not list all minimal safe cones.

Proof. Here $E^3(E^2+1)$ annihilates $s$, and the displayed finite
transient has least nilpotent exponent three. The root consumes zero,
so $a$ has boundary $(3,5)$ and origin three, while $b$ has boundary
$(2,4)$ and origin two. The only defect is at index three, hence its
actual parent is $a$. That parent consumes $s_2=1$, producing
$aa$ with boundary $(5,8)$ and origin four, and $ab$ with boundary
$(9,15)$ and origin five. The first indices of both exceed three.
For $b$, every proper descendant has first index at least $B_b=4$
by (PCR.39), while its own index two is not a defect. This proves
core-only evolution directly, including the shallow birth inside the
transient bound. There are no other defect parents, so (PCR.41)--(PCR.43)
give exactly the displayed sets. $\square$

## 21. Predictive capacity and the unchanged original recovery problem

**Theorem 21.1 (capacity on the authentic image).** Fix the entire
aligned source $s$ above as a comparison parameter, and put $K_s=|R_s|$.
There are exactly $K_s$ distinct complete normalized local forward
behaviours among its genuinely core-only physical cones. For every
common normalized age $T\ge0$, the future families $(S_{T+u})_{u\ge0}$
still have exactly $K_s$ behaviours. At any common normalized age
satisfying (PCR.5), the same $K_s$ behaviours are already
distinguished by complete current support. The statement includes the
constants with $p=1,K_s=1$, without a maturity requirement for clocks.
It compares cones at their respective actual cuts $e_v+T$; it does not
assert that they all have the same age at one common global cut.

A deterministic predictor for these behaviours, with aligned source
and common age fixed, must distinguish $K_s$ configurations and needs
at least $\lceil\log_2K_s\rceil$ bits in a fixed-length code. For the
clock distinction alone this many bits suffice as a mathematical index
into a supplied list of the $K_s$ states. The list, core, age, binding,
physical address, evaluator and any source-dependent advice contribute
their own stored data and costs. The two named coordinates are not two
compulsory physical registers or a claim about total minimal memory.

Proof. Theorem 19.2 identifies exactly the authentic residue image, with
a real cone for each member. Theorem 3.1 separates any two members by a
finite presence witness and identifies equal residues with equal full
local histories; its mature-cut conclusion gives the current-support
assertion. For a future family beginning at any earlier common age $T$,
choose a mature age at least $T$; that future cut separates every distinct
pair as well. Equal residues agree at every future cut. Thus the
restriction of that earlier exact classification
has cardinality $K_s$, now with a specified finite source presentation
and both realization directions instead of an abstract image. The
configuration lower bound and indexed coding argument are finite
counting, as in Theorem 15.1. For $s=y$ and $s'$ of Proposition 20.1,
these are respectively two and four behaviours and one and two bits of
fixed-core clock capacity, with all other data still charged. $\square$

**Proposition 21.2 (scope of representation, time and physical recovery).**
Formula (PCR.45) characterizes all-address future attainment from a
supplied mathematical description of the fixed original source.
It does not by itself provide the image from erased unknown inputs,
identify the actual cone's residue, certify that a path is present at
an unknown current cut, or perform acquisition or installation.
Unweighted state reachability cannot replace the timed equality
(PCR.47). A complete finite-cut support, complete cut-indexed local
future, timeless address union, and a paid finite Read transcript
retain the distinctions of Theorem 2.1, Proposition 2.2 and §13.

The supplied graph has $p^2$ vertices and two named outgoing edges
per vertex before restriction; no polynomial bound in the core degree
$r$ follows for its expansion, period extraction or numerical phase
extraction. The earlier operator representation and evaluator do not
need this graph to be expanded. Unbounded normalized age retains the
obstruction of Theorem 15.2.

The original task still requires the transient-inclusive output $(P,n)$,
unknown law and cut, all-index $\mathscr R_d$, original $K_d/\rho_d$
firstness and normalization, and actual completed installation with all
root-literal, stationarity, backing and physical service premises of
[PSA, Definitions 1.1--1.3 and §8](RECURSIVE_RELATIONAL_OBSERVATION_POLYNOMIAL_SOURCE_ACQUISITION.md).
A local core image is not a replacement for any of those objects or
obligations.

Proof. The seed construction uses the source's actual transient and
aligned core, and the residue table uses its least period; Definition
1.1 supplies these as mathematical properties, not observation inputs.
Theorem 19.2's path lifting proves eventual existence with an exact
normalization time, rather than existence at every earlier cut. Its
shortest-path reduction changes that time. Theorem 2.1 requires the
whole ordered support for its equivalence; Proposition 2.2 proves that a
finite menu can miss distinctions and that the timeless local union is
the same full address tree. These facts prevent substituting any of
those observations for another.

A binary degree-$r$ invertible recurrence can have exponentially long
period, as already accounted for in Theorem 15.1; constructing its
$p^2$-vertex table charges that expansion. None of (PCR.36)--(PCR.52)
solves an inverse exponent problem from the compact operators. Even a
single clock behaviour with $p=1$ has infinitely many distinct age-indexed
supports, by Theorem 15.2. Finally Proposition 20.1 gives the same
aligned core with different authentic images after changing a permitted
transient. The source entrance and output of PSA retain that transient;
discarding it can therefore lose even the initialization of this local
image, besides failing to return the original prefix. The missing
acquisition, original normalization and physical completion implications
cannot be inferred from a theorem whose inputs are supplied descriptions
and whose conclusions are about the original mathematical orbit.
$\square$

## 追加锚（本行以下为增补区）
