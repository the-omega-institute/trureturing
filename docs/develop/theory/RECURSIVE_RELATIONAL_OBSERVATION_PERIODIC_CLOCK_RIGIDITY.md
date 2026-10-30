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

## 22. Effective authentic operator-image coding from the original source

**Definition 22.1 (complete source input and charged synthesis).** The input
is an authentic $(d,P)$ from the original entrance: $d\ge0$ and
$P=z_1\cdots z_{2d}$ is PSA Definition 1.2's paid full-root prefix. The
source belongs to the original all-index $\mathscr R_d$ of GPO Definition
29.1. At $d=0$, $P$ is empty and the law is zero. An equivalent complete
aligned-source descriptor must determine the same original stream,
alignment and singular transient. Neither a local predictive boundary nor
a periodic tail alone is this input. The original cut $n$, root binding and
$K_d/\rho_d$ firstness retain their acquisition and verification costs.

Here is one deliberately elementary synthesis algorithm. Enumerate monic
binary forward polynomials in increasing degree $k=0,\ldots,d$, and then
in fixed coefficient order. Give each candidate the first $k$ displayed
bits, extend through $2d$, and compare with $P$. Degree zero denotes zero.
Reject a negative bound, wrong length, nonbinary entry, or absence of a
passing candidate. On the authentic promise at least one passes, and GPO
Lemma 29.2 makes every passing extension the same full source. The first
passing polynomial $h$ is its least annihilator: a smaller annihilator
would have passed earlier. Two different least monic polynomials cannot
occur, since their difference would be a smaller annihilator. This computes
a behavioral law, not the hidden private recurrence presentation or the
original first-passing object.

Write $h=X^a g$, $g(0)=1$, and use ACR Theorem 27.3's coprime projections
to compute $s=y+t$. Explicitly, extended polynomial Euclid supplies
$UX^a+Vg=1$; then $y=U(E)E^as$ and $t=V(E)g(E)s$. Reduce $U$ modulo $g$
when $g\ne1$. The needed aligned core seed and the first $a$ transient
bits are obtained by forward recurrence. Minimality of $h$ gives the least
core polynomial $g$ and $a+\deg g\le d$. At $g=1$ use the zero core.
All projections use forward shifts of the original one-sided stream;
there is no backwards extension of its transient. This representation
check does not certify physical provenance or stationarity: those remain
the authentic paid-input premises.

**Definition 22.2 (streaming seeded residue image).** For $r=\deg g>0$,
compute the least period $p$ by iterating multiplication by $x=X\bmod g$
from $1$ until its first positive return. By (PCR.28) this is the actual
core period, with $p\le2^r-1$. This works in a quotient ring, including
repeated factors, rather than in a presumed field. At $r=0$ set $p=1$.
Construct the actual $H_s,U_s,C_s$ and integer seed triples of
(PCR.40)--(PCR.42). In particular retain shallow safe seeds, not just the
frontier $A>a$. All these values are computed; none is supplied advice.

Put $Q_p=\{0,\ldots,p-1\}^2$, $N=p^2$. The successor oracle on $q=(A,B)$
evaluates $c_y(A)=y_{A-1}$ by periodic indexing and applies (PCR.39) modulo
$p$, retaining physical names $a<b$. Evaluate the following recurrence
depth first, without caching its subproblems:

$$
\begin{aligned}
\mathsf{Reach}(u,v,0)&\Longleftrightarrow
 (u=v)\lor(u\xrightarrow a v)\lor(u\xrightarrow b v),\\
\mathsf{Reach}(u,v,j+1)&\Longleftrightarrow
 \exists w\in Q_p\;
 [\mathsf{Reach}(u,w,j)\land\mathsf{Reach}(w,v,j)].
\end{aligned}
\tag{PCR.53}
$$

This is reachability in at most $2^j$ edges, since shorter paths can be
padded by zero-length portions. Set $\ell=\lceil\log_2(N+1)\rceil$ and

$$
\begin{aligned}
\mathsf{InImage}_s(q)&\Longleftrightarrow
 q\in Q_p\ \land\ \exists c\in C_s\;
 \mathsf{Reach}((A_c,B_c)\bmod p,q,\ell),\\
K_s&=\sum_{q\in Q_p}\mathbf1_{\mathsf{InImage}_s(q)}.
\end{aligned}
\tag{PCR.54}
$$

A numerical residue query uses canonical nonnegative coordinates and
rejects out-of-range values before any reduction. Scan $Q_p$ in
lexicographic order to count, rank and unrank its accepted values. Let
$b_s=\lceil\log_2K_s\rceil$ and use exactly $b_s$ binary bits for a rank
$0\le j<K_s$. At $K_s=1$ only the empty code is valid. Wrong lengths,
nonbinary codes and indices $j\ge K_s$ are rejected. No image table is
part of the input.

**Definition 22.3 (the operator query and inverse code interface).** At
$r>0$, an operator query consists of two canonical $r$-bit coefficient
strings $(Q_1,Q_2)$ in $R_g$. First enumerate
$1,x,\ldots,x^{p-1}$, comparing the supplied strings at each step. Reject
unless each has a match; otherwise take the unique matching exponents
$(u,v)\in Q_p$. Then accept exactly when
$\mathsf{InImage}_s(u,v)$ holds, and return its residue rank as the code.
This explicitly computes the numerical phase conversion. Being a unit,
or merely being a pair of well-formed ring elements, is insufficient.
Even pairs in $\langle x\rangle^2$ are rejected when their residues are
outside the seeded image. Noncanonical coefficient lengths or symbols
are invalid. No discrete logarithm, period or phase is supplied for free.

Conversely, given $(d,P)$ and a valid $b_s$-bit code $j$, recompute the
image count and unrank $j$ to $(u,v)$, then return $(x^u,x^v)$ in canonical
coefficient form. This returns the source-relative operator class. It does
not return a particular literal address, age or integer clock lift. At
$r=0$ the operator interface has just the zero-core tag with both operator
fields omitted; any extra pair is rejected. Its sole code is empty.
The two constant sources remain distinguished by their core descriptors.

**Theorem 22.4 (authentic operator-image correspondence and reversibility).**
On every authentic input in $\mathscr R_d$, the accepted operator domain is
exactly

$$
\mathcal O_s=
 \{(x^{A_v},x^{B_v}):v\text{ is genuinely core-only in the original source}\}
\tag{PCR.55}
$$

when $r>0$, with the stated zero-tag interpretation at $r=0$.
The operator-to-code and code-to-operator maps are inverse between
$\mathcal O_s$ and the valid codes. Its cardinality is exactly $K_s$.
These assertions include zero, constants, all allowed singular transients,
nonminimal private presentations and arbitrary repeated core factors.

Proof. Synthesis identifies the entire original stream by GPO Lemma 29.2;
the coprime decomposition and Theorem 18.2 therefore compute its actual
seeds. Theorem 17.2 lifts every edge out of a seed to the corresponding
literal physical child in that same source. Conversely every genuinely
core-only address has a unique seed prefix by (PCR.43), so it supplies a
seed-reachable graph path. Thus (PCR.54) is exactly $R_s$, in both
directions. A shortest witness needs at most $N-|E_s|$ edges, hence is
within the chosen reachability horizon. Shortening preserves only its
endpoint: it can change both its address and its positive normalization
time. A requested original witness's time must instead be evaluated along
that witness by (PCR.47).

By (PCR.28), $u\mapsto x^u$ is a bijection from $\mathbb Z/p\mathbb Z$
onto $\langle x\rangle$. The explicit scan in Definition 22.3 terminates
and computes its inverse for arbitrary supplied coefficients, rejecting
elements outside this subgroup. Composing this bijection in both
coordinates with the two realization directions for $R_s$ proves
(PCR.55). In particular an accepted pair has an actual source cone and
every actual safe cone's pair is accepted. Ordered enumeration gives
inverse residue rank/unrank, and quotient powering gives inverse operator
coding/decoding. At $p=1$, $R_s=\{(0,0)\}$; both constants have $K_s=1$,
with the zero tag only for the zero core. $\square$

**Proposition 22.5 (bit costs, polynomial peak space and exponential work).**
Use explicit binary integers, binary coefficient arrays, delimited literal
words, and a fixed multitape bit-operation model. Each elementary step
reads or writes a bounded number of bits; cumulative writes count every
scratch overwrite as well as retained output. Let $D=d+1$, and let $I$
include the entire represented input length, including malformed query
fields. On valid image queries $I=O(D)$. The following bounds concern the
declared elementary algorithms; no exact numerical envelope is asserted.

The raw synthesis and projections take
$T_{\rm src}=O(I+2^dD^2+D^4)$ work and $O(I+D^2)$ peak bits. There are
fewer than $2^{d+1}$ recurrence candidates, each tested in $O(D^2)$ bit
operations. Schoolbook polynomial division and extended Euclid, and
forward generation of the $O(D)$ seed entries needed by the projection,
fit the additional $O(D^4)$ allowance. One coefficient-product-and-reduce
operation modulo $g$ costs $O(D^2)$ bit operations and $O(D)$ temporary
bits: form at most $r^2$ binary coefficient products and eliminate at most
$r$ leading coefficients with at most $r+1$ XORs each. Each shifted-XOR
pass is a sequential $O(D)$-bit scan; $O(D)$ passes suffice, including
tape-head movement and loop control. Consequently
binary powering at an exponent of $L$ bits, including the exponent scan,
costs $O(D^2(L+1))$, with $O(D+L)$ temporary bits. The dot product with
the core seed then evaluates $y_i$ at the same bound. This argument
requires only a monic modulus, not square-freeness.

Period computation costs $O(pD)$ work and $O(D)$ additional space, since
multiplication by $x$ is one shift/reduction. A residue successor, including
its core bit at an $O(D)$-bit index and modular integer additions, costs
$O(D^3)$ work; it is not assigned a quadratic cost merely from a
ring-operation bound. Enumerating the powers to convert an arbitrary
operator pair costs a further $O(pD)$, and powering the decoded two
operators costs $O(D^3)$, plus the $2r$ output bits.

Seeds can be streamed in polynomial space and work. Traverse $H_s$ depth
first; to decide $v\in U_s$, rescan $H_s$ for a marked descendant. Stream
exactly the root if $U_s$ is empty, or the children of unsafe parents
which are not unsafe. Theorem 18.2 bounds each traversal by $O(D^2)$
nodes of depth $O(\log(D+1))$ with $O(\log(D+1))$-bit integer fields.
Repeated descendant scans and original-source bit evaluation fit, for
example, $O(D^8)$ work and $O(D^2)$ space. This generous polynomial
bound includes all literal comparisons and copies; it is independent of
$p$. There are $O(D^2)$ seeds and no stored seed/image table is needed.

Put $R=(2N+2)^{\ell+1}$. A reachability call has at most $R$ recursive
calls: if $R_0=1$, then $R_{j+1}\le1+2NR_j$. Every frame retains only its
two endpoints, current midpoint, depth and flags, all $O(D)$ bits. Depth
is $O(\log N)=O(D)$, so its peak stack is $O(D^2)$. Evaluating leaves
and loop arithmetic costs $O(D^3R)$ work. Implement the calls with
contiguous $O(D)$-bit frames on a stack tape whose head stays at the top
frame between calls. Pushing, popping and restoring a frame take $O(D)$
head moves and bit operations per call, within this allowance. Midpoints,
image candidates and ranks use $O(D)$-bit binary counters, updated and
compared by sequential scans. For count, either rank direction,
and either operator direction, a common upper bound is

$$
 T_{\rm img}=O\!\left(T_{\rm src}+D^8+pD+
               N(D^8+D^5R)+I+L_{\rm out}\right)
           =2^{O(D^2)}+O(I+L_{\rm out}).
\tag{PCR.56}
$$

Peak storage is $O(I+D^2+L_{\rm out})$ and cumulative bit writes are
$O(T_{\rm img})$. A count or one code/operator class has $L_{\rm out}=O(D)$.
The constants in the $O$ notation are uniform over all such sources.
These bounds follow from the displayed loops and arithmetic, not from a
measured running-time constant. A separately requested full image list
pays its entire delimited output, at most $O(K_sD)$ bits in these formats;
retaining that list also adds its actual size to peak storage.

The streaming algorithm trades recomputation for peak space; it
asserts neither polynomial time in $d$ nor sub-period or sub-period-square
work. Its bound is exponential computation with polynomial peak workspace
for one class/count output.

Raw zero and constant inputs still pay input inspection and synthesis.
Only an independently verified constant tag permits constant additional
image postprocessing; the tag's verification, represented source input,
acquisition, code schema and output remain charged. In particular $d=0$
has the known zero law and empty $P$, but not a known physical cut or free
installation. For a PSA supplier the composition is additive:

$$
 C_{\rm total}=C_{\rm PSA}(P,n)+T_{\rm img},\qquad
 W_{\rm total}=W_{\rm PSA}(P,n)+W_{\rm img}.
\tag{PCR.57}
$$

Here $W_{\rm img}$ includes its returned output. Source storage, backing,
full-root Read traffic, synchronization and binding have their original
bills; discarded expanded records are not refunded.

**Proposition 22.6 (raw zero-prefix inspection obstruction).** For every
$d\ge2$, an exact deterministic bit algorithm returning $K_s$ from raw
$(d,P)$ must inspect at least $d$ of the $2d$ prefix positions on the
zero input. Thus constant postprocessing on a verified tag cannot be a
constant-work raw-input algorithm.

Proof. For $j=0,\ldots,d-1$, compare zero with
$s^{(j)}_i=\mathbf1_{i\equiv j\pmod d}$. These are authentic members of
$\mathscr R_d$, with disjoint differing prefix-position pairs
$\{j,j+d\}$ in zero-based indexing. Each has least period $d$, no
transient, and the root is safe. The root residue's first coordinate is
$1$; its initially beta child's first coordinate is $2$, by (PCR.39),
so the image has at least two distinct residues modulo $d$. Zero has
$K_s=1$. On the zero execution, leaving any pair wholly uninspected
makes that valid alternative indistinguishable. The $d$ pairs are
disjoint, proving the inspection bound. This is an input lower bound,
not a hardness or physical-Read lower bound. $\square$

## 23. The exact local-data boundary for global authentic images

**Proposition 23.1 (same literal $aa$ cone, different global image).** Let
$y_i=1$ for even $i$ and $y_i=0$ for odd $i$. Use the two permitted
sources

$$
 s=y,\qquad s'_0=0,\quad s'_i=y_i\ (i\ge1).
\tag{PCR.58}
$$

Both lie in the common public class $\mathscr R_3$. The first is purely
periodic; the second has the one-bit singular transient of Proposition
20.1. In both actual sources the literal physical cone with address $aa$
has exactly

$$
 e_{aa}=4,\qquad (A_{aa},B_{aa})=(5,8),\qquad
s_{A_{aa}-1}=s'_{A_{aa}-1}=1.
\tag{PCR.59}
$$

Consequently every complete normalized future of this $aa$ cone is equal
in the two sources. At any common mature age $T\ge8$ its complete support,
its exact local integer clocks and origin, and the predictive boundary
$(aa,T;g,(y_i)_{i<2},Q_1,Q_2)$ of (PCR.24) agree. The public binding token,
permissions and evaluation instructions can be held fixed in this
comparison; they are capabilities, not a hidden source prefix.

Nevertheless, their global authentic images satisfy

$$
 |R_s|=2,\qquad |R_{s'}|=4.
\tag{PCR.60}
$$

Proof. For $s$, the root consumes one, so (PCR.39) gives
$(A_a,B_a,e_a)=(2,3,2)$; its first bit is $s_1=0$, and the same table gives
$(A_{aa},B_{aa},e_{aa})=(5,8,4)$. For $s'$, the root consumes zero, giving
$(A_a,B_a,e_a)=(3,5,3)$; the next bit is $s'_2=1$, and the one-bit branch
of (PCR.39) again gives $(5,8,4)$. The two literal words are therefore
the same actual physical address, with the same integer boundaries and
normalization origin, rather than merely isomorphic abstract trees.

The transient of $s'$ ends at index one. Every birth in $aa$ starts at
$A_{aa}=5$, hence consumes source entries with indices at least four; the
two streams in (PCR.58) coincide there. Theorem 17.2 and induction
therefore identify every later child, bit and positive delay. The least
core polynomial is $X^2+1$ and has the repeated factor $(X+1)^2$ over
$\mathbb F_2$, so $F_5=5\ge4$ and the maturity condition (PCR.5) holds
for $T\ge5+3=8$. Theorem 3.1 then turns the identical future stream and
clock pair into identical complete supports and identical operator
boundaries. The full-root acquisition of the literal $aa$ pays the same
presence query in both comparison worlds; it does not reveal the source
bits before that cone.

The global image counts are the explicit calculations (PCR.49)--(PCR.51):
the pure source has only the two off-diagonal residues, while the transient
source has diagonal seed residues and reaches the whole four-state square.
The missing datum is the global seed/defect ancestry $C_s$ and its integer
seed triples, equivalently the transient-bearing prefix outside the local
cone. The local descriptor contains no field from which that seed set can
be reconstructed. The complete original $(d,P)$ does contain it: its
canonical generator supplies the finite defect scan (PCR.40)--(PCR.42),
after which (PCR.54) computes the image. This is an information boundary
for a local predictive record, not a failure of PSA's original full-root
acquisition protocol. $\square$

## 24. Exact normalization-time address history and its code

**Definition 24.1 (one authentic seed and the exact target).** Fix one
actual seed $c\in C_s$ with its literal word and exact triple
$(e_c,A_c,B_c)$ from Theorem 18.2. For every integer $t\ge0$ put

$$
 H_c(t)=\{w\in\{a,b\}^*:e_{cw}-e_c=t\},\qquad
 \pi_{c,t}(w)=(A_{cw},B_{cw})\bmod p.
\tag{PCR.61}
$$

Only this seed is used, not a union over seeds, an invented initial cone,
or native elapsed time. The positive edge delays are exactly (PCR.37).
Every $cw$ is an actual core-only cone and $\pi_{c,t}$ takes values in
$R_s$. Let $J_{c,t}=\pi_{c,t}(H_c(t))$ and
$M_{c,t}=\max_{q\in J_{c,t}}|\pi_{c,t}^{-1}(q)|$.
The projection erases the relative address; a complete descriptor that
retains the literal $v=cw$ has not erased it. The endpoint here omits
integer lifts, the literal and its ancestry. All lower bounds below
refer to this precise projection and this declared time.

**Theorem 24.2 (exact count and endpoint-conditioned extra information).**
For all such sources, seeds and $t\ge0$,

$$
 |H_c(t)|=F_{t+1},\qquad
 M_{c,t}\ge\left\lceil\frac{F_{t+1}}{|J_{c,t}|}\right\rceil
          \ge\left\lceil\frac{F_{t+1}}{K_s}\right\rceil.
\tag{PCR.62}
$$

If $w\mapsto(\pi_{c,t}(w),\lambda(w))$ is injective, then
$|\operatorname{range}(\lambda)|\ge M_{c,t}$. In particular a uniform
fixed-length binary supplement needs at least
$b^{\rm cond}_{c,t}=\lceil\log_2 M_{c,t}\rceil$ bits. This bound is
attainable set theoretically by numbering each endpoint fiber; it does
not assert a cheap fiber computation or an online update interface.

Proof. At every node exactly one named child has delay one and the other
has delay two, regardless of the consumed bit. For any actual core-only
node let $h(t)$ count its descendants at exact relative normalization
time $t$, and set $h(u)=0$ for $u<0$. At zero only the empty suffix is
possible. Induction on $t$ gives the same count at every node, since
partition by the first edge gives $h(t)=h(t-1)+h(t-2)$ for $t\ge1$,
with $h(0)=1$. Hence $h(t)=F_{t+1}$, including $h(1)=1$.
Positive delays also make each layer prefix-incomparable. It is nonempty
at every nonnegative integer time. Its endpoint fibers partition it;
the largest has at least the ceiling of the average size. Injectivity
requires different supplements within each fiber. Fiber ranks reuse the
same alphabet of size $M_{c,t}$, proving attainability of that alphabet
size. Constants have one endpoint, but have $F_{t+1}$ addresses, rather
than one address at every time. At $t=0,1$ this count is one. $\square$

**Proposition 24.3 (the distinct physical-cut leaf domain).** If $L_t(c)$
denotes the leaves at physical cut $e_c+t$, then $L_0(c)=H_c(0)$ and,
for $t\ge1$,

$$
 L_t(c)=H_c(t)\;\dot\cup\;
 \{wx:\ w\in H_c(t-1),\ \delta_x(c_{cw})=2\},\qquad
 |L_t(c)|=F_{t+2}.
\tag{PCR.63}
$$

The first part consists of beta leaves at their normalization origins;
the second consists of initially alpha children just created at that cut,
which normalize one cut later. Every leaf is one of these: a beta
branches at the next cut, and an alpha promotes at the next cut. This
proves the disjoint union and its count. It also identifies $H_c(t)$
exactly as the beta leaves at that cut. It does not identify endpoint
fibers across a shift of the cut. For the zero source at the root,
$H_c(1)=\{b\}$ but $L_1(c)=\{a,b\}$. For $s=(10)^\infty$ at the root,
$L_1$ has two endpoints both $(0,1)$ modulo two, whereas
$H_c(2)=\{ab,b\}$ has endpoints $(1,0)$ and $(0,1)$. Thus even the
equality $|L_{t-1}|=|H_c(t)|$ for $t\ge1$ transfers neither this target's
addresses nor its conditioned fibers. The coding below uses (PCR.61)
directly.

**Definition 24.4 (period-free rank/unrank on the exact layer).** Order
$H_c(t)$ lexicographically in the physical order $a<b$, and encode its
rank in exactly

$$
 B_t=\lceil\log_2 F_{t+1}\rceil\text{ bits},\qquad
 \operatorname{Hcode}_{c,t}(w)=
 \operatorname{bin}_{B_t}(\operatorname{hrank}_{c,t}(w)).
\tag{PCR.64}
$$

At a current exact integer descriptor $(e,A,B)$ and remaining time $u$,
evaluate $y_{A-1}$ from the supplied core recurrence and seed, compute
$\delta_a,\delta_b$ by (PCR.37), and set

$$
 n_x(u)=\begin{cases}F_{u-\delta_x+1},&u\ge\delta_x,\\
                      0,&u<\delta_x.
        \end{cases}
\tag{PCR.65}
$$

If $u>0$, these are exactly the two first-letter block sizes. To rank a
word, take its actual next letter $x$, add $n_a(u)$ to the rank if $x=b$,
reject if $n_x(u)=0$, and update only that child's exact descriptor using
(PCR.38)--(PCR.39), with $u\leftarrow u-\delta_x$. Accept only if the
word ends exactly at $u=0$. An early ending, trailing letter after zero,
nonphysical symbol, or overshooting delay is invalid. To unrank, choose
$a$ when the remaining rank is below $n_a(u)$, otherwise subtract that
block size and choose $b$. Continue until $u=0$; return the suffix, or
the full literal $cw$ when that output is requested.

The source and seed must be authentic as above. On a raw $(d,P,c)$
interface, recompute $C_s$ by Definition 22.2 and verify this exact literal
and its triple; reject a different seed, an inconsistent supplied triple,
or a malformed source representation. No malformed representation proves
a physical authenticity premise. Reject $t<0$, nonintegral time, codes of
wrong length, nonbinary codes or ranks outside $[0,F_{t+1})$. At $t=0,1$
the sole valid rank is zero and its fixed-length code is empty; the
decoded suffix is respectively empty or the actual delay-one child.
No period, phase, endpoint, $K_s$, or image table is required by this
address codec. In particular it does not run the period computation of
the image interface.

**Theorem 24.5 (reversibility and a gap for this exact target).** The two
maps in Definition 24.4 are mutually inverse on $H_c(t)$ and all valid
codes. Relative to the optimal endpoint-conditioned fixed-length
supplement their length obeys

$$
 0\le B_t-b^{\rm cond}_{c,t}
 \le\lceil\log_2|J_{c,t}|\rceil
 \le\lceil\log_2K_s\rceil\le2r.
\tag{PCR.66}
$$

Thus $b^{\rm cond}_{c,t}\ge\max(0,B_t-2r)$. For either constant,
$K_s=1$ and the gap is zero for every $t$. The gap statement compares a
period-free full-address code with a supplement after this particular
endpoint is known, not a substitute recovery output.

Proof. Theorem 24.2 applied at each actual child gives precisely
(PCR.65). All words in the $a$ block precede every word in the $b$ block;
positive delays guarantee termination in at most $t$ edges. The exact
integer transport proves that every selected child is in the original
source, with the updated normalization time. Induction on the remaining
time therefore proves both rank/unrank identities and the stated invalid
domains, including empty codes. For the gap, $M_{c,t}\le F_{t+1}$ and
$F_{t+1}\le |J_{c,t}|M_{c,t}$. Taking ceilings of logarithms gives
$B_t\le\lceil\log_2|J_{c,t}|\rceil+b^{\rm cond}_{c,t}$. Finally
$|J_{c,t}|\le K_s\le p^2\le2^{2r}$, also at $r=0$. $\square$

**Proposition 24.6 (represented widths and charged address computation).**
Use the bit model of Proposition 22.5. Let $I$ be the actual input length,
including the raw source, seed literal/triple, binary time and supplied
word/code. Let $\beta$ be one plus the sum of the bit lengths of
$A_c,B_c,e_c$, and put

$$
 W=\beta+t+\lceil\log_2(t+2)\rceil+1.
\tag{PCR.67}
$$

The canonical seed has the bounds of Theorem 18.2, but no exact integer
at later time is treated as an $O(d)$-bit quantity. After at most $t$
child steps all coordinates have $O(W)$ bits: (PCR.39) gives
$B_{vx}+1\le3(B_v+1)$ and (PCR.38) gives $e_{vx}\le e_v+2$.
All Fibonacci counts and ranks have $O(t+1)$ bits, by $F_j\le2^j$.
The time field and source/seed literals remain represented input even
when a code has zero bits.

A declared implementation needs no retained ancestor stack. First compute
$(F_t,F_{t+1})$ by $t$ successive additions, using $O((t+1)^2)$ work and
writes and $O(t+1)$ peak bits. During descent retain only the current
integer descriptor, remaining time, rank and two Fibonacci values. From
$(F_u,F_{u+1})$, subtraction gives $F_{u-1}=F_{u+1}-F_u$ when needed;
a delay-one step keeps $(F_{u-1},F_u)$, and a delay-two step also computes
$F_{u-2}=F_u-F_{u-1}$. Treat the $u=1$ zero slow block directly and stop
at zero. Thus block counts and the next pair cost $O(t+1)$ bits of
arithmetic per step without a Fibonacci table. Each chosen-child
coordinate update costs $O(W)$; evaluating its parent bit by schoolbook
quotient powering costs $O(D^2(W+1))$, using $O(D+W)$ temporary bits.

Including raw synthesis and the polynomial seed verification scan, for
either valid direction, or rejection of an invalid supplied word/code,
a uniform upper bound is

$$
\begin{aligned}
 T_{\rm addr}&=O\!\left(T_{\rm src}+D^8+I+
                     (t+1)D^2W+(t+1)^2+L_{\rm out}\right),\\
 S_{\rm addr}&=O(I+D^2+W+L_{\rm out}),\qquad
 W_{\rm addr}=O(T_{\rm addr}).
\end{aligned}
\tag{PCR.68}
$$

Scanning malformed extra input costs its actual length $I$. The suffix
output has at most $t$ letters and a code has $B_t=O(t+1)$ bits; returning
$cw$ additionally pays the seed literal length. Peak space here includes
retained input and output. At $t=0$ the empty suffix still pays raw-source
and seed validation; at $d=0$ only core evaluation simplifies. Arithmetic
and writes have not been measured in fixed machine words.

If an implementation instead retains a descriptor at every descent depth,
its stack upper bound is $O((t+1)W+D^2)$ bits, in addition to input/output;
it can require quadratic space. For the authentic $d=1$ all-one source
and its root seed, the members $a^t\in H_c(t)$ satisfy
$(A_{a^j},B_{a^j},e_{a^j})=(F_{j+2},F_{j+3},1+j)$. The members
$b^h\in H_c(2h)$ satisfy
$(A_{b^j},B_{b^j},e_{b^j})=(F_{2j+3}-1,F_{2j+4}-1,1+2j)$.
Both formulas follow by induction in (PCR.39). Since the logarithm of
these Fibonacci integers grows linearly in $j$ (use
$F_{2k+2}\ge2^k$ and $F_k\le2^k$), separately retained
frames require $\Theta(t^2)$ coordinate bits and at least that many
writes on these families. Even the iterative exact-coordinate algorithm
writes $\Theta(t^2)$ boundary bits along these paths; it saves peak space,
not these writes. Its upper bound at fixed $d,\beta$ is quadratic work
and linear peak space, consistent with this obstruction.

The codec's work is polynomial in the numeric $t$ and represented seed
sizes after source synthesis; it is not polynomial in $\log(t+2)$.
Indeed $B_t=\Theta(t)$ for growing $t$, so even one general code output
can be that large. Enumerating all exact-layer addresses has its full
exponential enumeration and literal-output cost. This is mathematical
address recovery with supplied source data, not a physical clock or an
execution journal. No native acquisition, source advancement, recentering
or installation operation is introduced.

## 25. Comparison with the typed residual-cocycle route

TRC11, specifically Definition 11.1 and Theorem 11.2 of
[TRC](RECURSIVE_RELATIONAL_OBSERVATION_TYPED_RESIDUAL_COCYCLE_RECONSTRUCTION.md),
requires a fixed finite actual root-reachable complete residual graph,
named legal edges, exact endpoint acquisition, fixed positive native
vectors descending to that residual, and the complete joint box of
endpoint-plus-native observations. Its online update receives only the
executed name; all persistent control is charged. TRC12--15 keep the
successive-loop source and its joint-support/native-acquisition contract.

Here the literal address tree is infinite and acyclic. Its residue image
is finite, and the mathematical normalization delays do descend to its
named edges, since $y_{A-1}$ is determined by the residue. Their sums are
exactly (PCR.47). This fact does not make the residue image the complete
physical response quotient or give a native instrument. The predictive
boundary retains age and literal information, and its Read responses are
presence-only. Neither exact residual endpoint acquisition nor a native
positive-vector readout with the stipulated uncertainty support has been
supplied. Even zero mathematical observation error would not instantiate
TRC11's prescribed positive-error full-box theorem.

A physical transfer would need a proved rooted named-operation map
preserving every legal operation, complete response, endpoint, positive
native vector, same-source legality, physical order and binding, together
with the required joint acquisition. None is constructed here. Declaring
normalization increments to be a native elapsed-time response would add
an unavailable clock service. Therefore no TRC11 route-rank criterion or
TRC12--15 support classification is transferred to this source. The
endpoint-conditioned result (PCR.62) is instead proved directly for the
actual exact-normalization-time domain; no leaf-layer shift or noisy
native-duration premise enters its proof.

The loss measured here is the erasure of a rooted suffix by $\pi_{c,t}$.
A retained literal $v=cw$ already specifies that address. This does not
refute the full predictive descriptor (PCR.24), the original
transient-inclusive $(P,n)$ recovery, or PSA's paid full-root acquisition.
The chronological physical execution target and an online history
supplement require their own input and update contracts.

## 26. Suppliers, scope and the remaining original obligations

The source-specific additions are the complete-source seeded operator
query/code interface, the actual local/global information separation of
Proposition 23.1, and exact-normalization-layer coding and its
endpoint-conditioned gap. The finite reachability recurrence, fiber
pigeonhole bound and ordered-block coding are elementary reused methods;
the actual child transport, transient seed selection and operator/residue
classification are supplied by §§9 and 17--21. They are not recast as
new general quotient or automata theorems. The supplied-input projections
and bounded-prefix uniqueness are ACR27.3 and GPO29.2, with the singular
convention also described by [Massey §§II--IV][MAS].

The quotient-power evaluation is the monic-recurrence identity in
[Bostan--Mori v1 §1.3][PCR-BM], with binary coefficient arrays and an
explicit schoolbook multiplication/reduction bound here. It supplies
neither free source entries nor a constant-width integer clock.
Rigo--Stipulanti's abstract-numeration correspondence cited in §19
concerns decorated regular address trees, not this source's chronological
birth indexing or a native elapsed-time interface. The synthesis and
coding here are repository-derived applications and deductions on the
stated original source; no literature-priority claim or new Lean/kernel
verification is made. Finite executable checks can test the formulas
on specimens; they do not replace the quantified arguments above.

All assertions retain the unknown law and actual cut, the original
all-index $\mathscr R_d$, singular transients, nonminimal presentations,
arbitrary repeated core factors and physical order $a<b$. The original
output remains the transient-inclusive $(P,n)$ with original $K_d/\rho_d$
firstness and separately charged normalization. A complete aligned
source is sufficient for the computations; a complete local mature cone
can still miss the global transient-bearing seed information, as §23
shows. Computing a period, numerical residues or phases is explicit paid
computation, not new acquired advice. None of these computations acquires
the physical source or recovers a missing actual cut from local data.

Paid full-root presence Reads, stationarity over the service interval,
source storage, grants, backing, root binding, synchronization and
completed installation keep their original premises and costs. Computing
$R_s,K_s$, an operator-class code or an exact-layer suffix does not
advance the source, create a new physical operation, prove atomic
universality, or finish the recursive relational-recovery programme.
General acquisition, original firstness, normalization, installation and
whole-goal completion remain separate obligations.

## 追加锚（本行以下为增补区）

## 27. Original chronological queries with linear backing and represented-bit work

**Definition 27.1 (full-source data and the two query domains).** Fix the
original alpha-origin source $s\in\mathscr R_d$, physical order $a<b$,
old-leaf replacement and one-based birth order of Definition 1.1. The
supplied source field is exactly the authentic $(d,P)$ of Definition
22.1: $P=s_0\cdots s_{2d-1}$, including every singular transient. Use
[ACR, Theorems 21.2 and 21.4, (ACR.85)][ACR] to synthesize its least
all-index monic annihilator $m$ and its original initial seed. This is
the polynomial behavioral synthesis supplier, rather than Definition
22.1's enumerative implementation. It computes neither the original
$\rho_d$ first passing row nor a physical source certificate. At $d=0$
the source is zero, $P$ is empty and $m=1$. No factorization, period,
residue image or normalized local seed is an input to this query.

There are two supplied-data tasks. In the **whole-origin-orbit** task,
the query is a positive binary birth ordinal $j$, or a finite physical
word $v\in\{a,b\}^*$, including the empty root. In the **already-occurred**
task, the same input also contains the authentically acquired actual
cut $n\ge0$, and the requested event must have occurred by $n$. The
latter task is about the branching event of the queried parent, not just
its creation or current presence. Neither task supplies an ordinal Read
service or recovers $n$ from $(d,P)$.

For every physical word retain the exact coordinates $(e_v,A_v,B_v)$
of (PCR.36)--(PCR.39), using the actual bit $s_{A_v-1}$ also outside the
core. Retain its immutable creation descriptor $(b_v,\sigma_v)$, and put
$\tau_v=e_v+1$. Thus

$$
 (b_\varepsilon,\sigma_\varepsilon)=(0,\alpha),\qquad
 (e_\varepsilon,A_\varepsilon,B_\varepsilon)=(1,1,2),\qquad
 b_v=e_v-\mathbf1_{\sigma_v=\alpha}.
\tag{PCR.69}
$$

An event query returns the literal parent and the fields
$(j;b_v,\sigma_v,\tau_v,e_v,A_v,B_v,s_{j-1})$. A word query returns the
same tuple with its own event ordinal. The original recovery output
remains the transient-inclusive $(P,n)$: this tuple is an additional
mathematical query result, not a replacement for either field. Returning $(P,n)$ additionally requires that acquired $n$ in either
domain; a query never infers it. Copying the pair is charged to its
actual length.

**Theorem 27.2 (all-root beta layers and the exact chronological offset).**
For every source of Definition 27.1 define

$$
 \mathcal H_s(t)=\{v:e_v=1+t\}\quad(t\in\mathbb N_0),\qquad
 h_{s,t}(v)=\operatorname{rank}_{a<b}(v;\mathcal H_s(t)),
\tag{PCR.70}
$$

where ranks start at zero. Then $\mathcal H_s(t)$ is exactly the set of
beta leaves at actual cut $t+1$, has size $F_{t+1}$, and is exactly the
parent batch branching at actual cut $t+2$. For every $v$ in that set,

$$
 \begin{aligned}
 j_v=A_v&=F_{t+2}+h_{s,t}(v),\\
 e_v&=t+1,\qquad \tau_v=t+2.
 \end{aligned}
\tag{PCR.71}
$$

Consequently, for every $j\ge1$ there is a unique $\tau(j)\ge2$ with
$F_{\tau(j)}\le j<F_{\tau(j)+1}$. Its actual parent is the member of
$\mathcal H_s(\tau(j)-2)$ of zero-based rank
$j-F_{\tau(j)}$. In particular $A_{p_j}=j$ and
$e_{p_j}=\tau(j)-1$. These statements include the actual alpha root,
all finite singular transients and all repeated factors.

For an arbitrary actual prefix $c$, define the all-source local layer
$\mathcal H_{s,c}(t)=\{w:e_{cw}-e_c=t\}$, ordered in physical order,
and its zero-based rank $h_{s,c,t}$. At cut $e_c+t$ it is exactly the
beta-leaf list inside $c$, and the global event of $cw$ is

$$
 \begin{aligned}
 j_{cw}&=I_c(t+1)+h_{s,c,t}(w),\\
 I_c(t+1)&=F_{e_c+t+1}+L_c(e_c+t),\\
 h_{s,e_c+t-1}(cw)&=L_c(e_c+t)+h_{s,c,t}(w).
 \end{aligned}
\tag{PCR.72}
$$

Here $L_c$ is precisely [ACR, (ACR.112)--(ACR.116)][ACR]'s actual
preceding exterior forest, with its authentic integer data;
$I_c(1)=A_c$, $I_c(2)=B_c$ and $I_c(k+2)=I_c(k+1)+I_c(k)$.
For a safe seed of Definition 24.1, $\mathcal H_{s,c}(t)=H_c(t)$.
Equation (PCR.72), including its exterior offset, is the resulting
conversion from that exact local history layer to global chronology.

Proof. A node with immutable descriptor $(b,\sigma)$ is a beta leaf
at exactly the single cut $b+1$ for initial alpha and $b$ for initial
beta; in either case that cut is $e$. At the next update it branches
once and remains a branch. The root follows these same rules from
$(0,\alpha)$, so its beta cut is one, not zero. This proves the
beta-layer identities. If $U_n,V_n$ are the alpha and beta leaf counts,
old-leaf replacement gives $(U_{n+1},V_{n+1})=(V_n,U_n+V_n)$, with
$(U_0,V_0)=(1,0)$. Hence $V_n=F_n$, including $V_0=0$.
Before update $\tau\ge2$ there have been
$\sum_{q=1}^{\tau-1}F_{q-1}=F_\tau-1$ births. Physical lexicographic
order therefore assigns indices $F_\tau,\ldots,F_{\tau+1}-1$ to
that old beta list. This is exactly [GPO, Proposition 39.2][GPO]'s
one-based rank formula after subtracting one from the rank.

The first normalized batch of any cone $v$ consists of its own unique
branch, so its first index $A_v$ is $j_v$. Every physical word is
eventually created and branches: the root branches at two and each
edge adds one or two to branch time. Thus the batches partition all
finite physical words and all positive ordinals, proving uniqueness.
Inside $c$, its beta-normalized origin is $e_c$ and the same count
recurrence gives $F_{t+1}$ beta leaves at $e_c+t$. They form a contiguous
interval of the global beta list. The preceding exterior contributes
exactly $L_c(e_c+t)$ members. Applying ACR Theorem 27.2 to this interval
gives (PCR.72), with no core-only assumption. For a safe seed the
normalization-time definition is exactly (PCR.61). This neither
identifies an exact normalization layer with all terminal leaves nor
identifies a local rank with a global ordinal. $\square$

**Definition 27.3 (two iterative supplied-data queries).** For a physical
word, start at (PCR.69). At each proper prefix $u$, evaluate
$c_u=s_{A_u-1}$ from the full-source recurrence and seed, and follow only
the supplied next physical letter by (PCR.37)--(PCR.39). The child's
initial label is beta for delay one and alpha for delay two; its
creation time is $e_u+1$. Keep only the current coordinates and immutable
label, not an ancestor stack. At the final word, return $j=A_v$ and
the tuple of Definition 27.1, evaluating its event bit if not yet done.
Denote the ordinal component by $Q_s(v)$.

For an ordinal $j\ge1$, successive Fibonacci additions locate the
unique bracket in Theorem 27.2. Put

$$
 t=\tau(j)-2,\qquad u=t,\qquad q=j-F_{\tau(j)}.
\tag{PCR.73}
$$

Begin at the same actual root with $(F_u,F_{u+1})$ and residual rank
$q$. When $u>0$, evaluate its actual bit $c$ and delays. The two
first-letter block sizes are

$$
 N_x(u)=
 \begin{cases}
 F_{u-\delta_x(c)+1},&u\ge\delta_x(c),\\
 0,&u<\delta_x(c).
 \end{cases}
\tag{PCR.74}
$$

Select $a$ if $q<N_a(u)$; otherwise select $b$ and subtract $N_a(u)$.
Append that one letter, update only that child's actual coordinates and
initial label, and replace $u$ by $u-\delta_x(c)$. Update the Fibonacci
pair by subtraction, retaining no table: a delay-one step takes
$(F_u,F_{u+1})$ to $(F_{u+1}-F_u,F_u)$; a delay-two step with $u\ge2$
takes it to $(2F_u-F_{u+1},F_{u+1}-F_u)$. At $u=1$ only the delay-one
block is nonempty. Stop at $u=0$, where the residual rank must be zero,
and return the literal and its tuple. Denote the literal by $U_s(j)$.

Integers use canonical binary nonnegative representations (zero has
one digit); an ordinal must be positive. Reject wrong signs, malformed
integer fields, a nonbinary $P$, a prefix length different from $2d$,
a nonphysical letter, or a source prefix with no order-at-most-$d$
passing recurrence. The last check can use the synthesized register
length and regenerate the prefix for comparison within (ACR.85)'s
bound; a failed synthesis is not replaced by a guessed periodic tail.
An authentic source always passes. A passing finite representation
alone does not certify acquisition or physical provenance. If labels
or coordinates are supplied as extra claimed fields, compare them with
the recomputed tuple and reject disagreement. In the already-occurred
task require a valid acquired $n$ and return the event tuple only if
$\tau(j)\le n$, equivalently $e_v+1\le n$; otherwise return
$\mathsf{not\ yet\ occurred}$. Missing $n$ is invalid for that task.
The whole-origin-orbit task imposes no such guard and certifies no
current occurrence.

**Theorem 27.4 (both inverse laws and the current-cut restriction).**
For every authentic $(d,P)$ and every $j\in\mathbb N_{>0}$ and
$v\in\{a,b\}^*$, Definition 27.3 terminates and gives

$$
 Q_s(U_s(j))=j,\qquad U_s(Q_s(v))=v.
\tag{PCR.75}
$$

Its returned descriptors, bit, branch time and normalization origin
are those of the actual source. In particular $U_s(1)=\varepsilon$,
with creation $(0,\alpha)$, beta origin one, branch time two and
$(A,B)=(1,2)$. The already-occurred versions restrict these inverse
maps exactly to

$$
 \{j:1\le j\le F_{n+1}-1\}
 \quad\longleftrightarrow\quad
 \{v:e_v+1\le n\}.
\tag{PCR.76}
$$

Both sets are empty at $n=0,1$. A word can be present and have no
occurred branching event: creation, beta normalization and branching
are separate cuts in (PCR.69). In particular root presence at cut zero
does not make birth ordinal one an already-occurred event.

Proof. Full-source synthesis supplies the same all-index stream by
ACR Theorems 21.2 and 21.4, including its seed and singular part.
Theorem 17.2 then proves word descent correct at every step. It uses
only earlier actual event bits; the strict increase $A_{ux}>A_u$
also rules out a recursive request for its own unknown orientation.
The returned initial label and creation time follow the actual child
rule, not the child's possibly later beta label.

For ordinal descent, the subtree rooted at a word has exactly one
child of normalization delay one and one of delay two, even in a
transient. Its exact remaining-time count $f(u)$ therefore satisfies
$f(0)=f(1)=1$, $f(u)=f(u-1)+f(u-2)$ for $u\ge2$, and zero count
at negative remaining times. Thus $f(u)=F_{u+1}$, and (PCR.74) gives
its actual ordered first-letter block sizes. The words in an exact
layer are prefix-incomparable, because every edge has positive delay.
Hence the whole $a$ block precedes the whole $b$ block in physical
order. At every selection, $0\le q<F_{u+1}$ and the selected block
is nonempty; the new rank is in its exact range. Remaining time
strictly decreases, so descent terminates after at most $t$ letters.
At zero the only suffix is empty, of rank zero. Induction on remaining
time proves that the output is precisely the required beta-layer
member. Theorem 27.2 then proves both identities in (PCR.75), the
root tuple and every output field. This is the all-root specialization
of the beta-list inverse already used in [ACR, Proposition 10.2][ACR];
no new inverse-existence claim is needed.

An event in batch $\tau$ occurs precisely at update $\tau$. Summing
batch sizes through $n$ gives $F_{n+1}-1$ for $n\ge1$, also zero at
$n=0$. This proves (PCR.76) and the guard, including a batch at $n$
itself. A hypothetical future event computed from supplied source data
provides no evidence that the actual source has reached it. $\square$

**Proposition 27.5 (local records and a periodic core do not determine
these queries).** Even the complete mature local record at the same
literal safe cone, with the same exact normalization origin and both
integer clocks, need not determine $U_s$ or $Q_s$ on the original root.
A periodic-core record alone is insufficient even when the core is
zero.

Proof. Reuse Proposition 23.1's sources in the common class
$\mathscr R_3$: $s=(10)^\infty$ and $s'=001010\cdots$. Their same
literal $aa$ has $(e,A,B)=(4,5,8)$ and identical complete normalized
future. All the mature local records stipulated there agree. Yet the
root consumes one in the first source and zero in the second. The
unique parent in batch three is respectively $a$ and $b$, so

$$
 U_s(2)=a,\quad U_{s'}(2)=b,\qquad
 Q_s(a)=2,\quad Q_{s'}(a)=3.
\tag{PCR.77}
$$

The core has least polynomial $(X+1)^2$, so this example also retains
the permitted repeated factor and the one-bit singular transient.
For the second assertion compare the zero source and the impulse
$1000\cdots$ in $\mathscr R_1$. Both have zero periodic core; their
least all-index annihilators are respectively $1$ and $X$. The same
root-bit calculation gives $U_0(2)=b$ and $U_{\rm impulse}(2)=a$.
Thus replacing the actual root by a beta-normalized periodic core
erases information necessary for the query. Complete $(d,P)$
distinguishes both pairs, as required by the sufficient interface.
At $d=0$ the sole admitted source is zero, not the impulse. $\square$

**Theorem 27.6 (uniform represented-bit work, cumulative writes and
linear peak backing).** Use the fixed finite sequential multitape
model of ACR §21.4: every symbol operation and one-cell head move is
charged, every written bit is counted cumulatively, and peak backing
includes every visited cell. Let $I$ be the actual encoded input length,
including all source fields, query, optional actual cut and any extra
claimed output fields; let $L_{\rm out}$ be the actual encoded output
length, including any requested copy of $(P,n)$. Put

$$
 D=d+1,\qquad
 \ell_d=\lceil\log_2(64(d+2)^4)\rceil,\qquad
 R=\begin{cases}
 |\operatorname{bin}(j)|,&\text{ordinal input},\\
 |v|+1,&\text{physical-word input}.
 \end{cases}
\tag{PCR.78}
$$

There is one uniform implementation of both queries with

$$
 \begin{aligned}
 C,W&=O\!\left(I+D^3\ell_d^2+D^2(R+1)^2+L_{\rm out}\right),\\
 V_{\rm peak}&=O(I+D+R+L_{\rm out}).
 \end{aligned}
\tag{PCR.79}
$$

The constants are independent of source, period, transient, query and
cut. Work $C$ and writes $W$ include preparation from raw authentic
$(d,P)$, not just access to a prepared term evaluator. If $d$ itself is
malformed, reject before synthesis in $O(I+L_{\rm out})$ work, writes
and backing. Otherwise $D$ uses that parsed bound; on an invalid query
field take $R$ to be its actual digit or symbol length plus one. The
same bound covers all other invalid fields at their actual lengths.
At an already-occurred query, the length of $n$ is charged in $I$;
its numeric value adds no forward simulation. No all-previous-node,
period or image table is expanded.

Proof. First validate syntax and source length by scans of the actual
input. A length scan may use a moving unary tally and one sequential
conversion to binary: increment a binary accumulator at its low end
with ripple carry, returning only across the changed carry prefix.
Over all increments its bit visits and writes are linear, since bit
$k$ changes $O(1+M/2^k)$ times during $M$ increments. Final reversal
and comparison cost the represented lengths. Equivalently the unary
tally can be counted by repeated adjacent pairing, whose sweep lengths
form a geometric sum. This includes zero, delimiters and return scans,
without scanning a huge declared length when the actual field is
short. Syntax failures return immediately; recurrence failures use the
same bounded source pass. ACR (ACR.85) supplies preparation in
$O(D^3\ell_d^2)$ work and writes and $O(D+\ell_d)$ backing, including
its polynomial output, coefficient convention and authentic seed.
Regenerating and comparing the $2d$ bits has the same bound. Since
$\ell_d=O(D)$, this is $O(D)$ peak backing beyond the retained input.
This preparation preserves the full annihilator $m$, not only its
unit-constant core factor.

Here is a sequential implementation of each subsequent term evaluation.
If $r=\deg m>0$, for the requested exponent $k\ge0$ compute
$X^k\bmod m$ by left-to-right binary square-and-multiply, starting with
one. Dot its coefficients with the original first $r$ source bits.
The monic-quotient identity gives

$$
 s_k=\left\langle X^k\bmod m,(s_0,\ldots,s_{r-1})\right\rangle.
\tag{PCR.80}
$$

This is Fiduccia's recurrence identity as stated by
[Bostan--Mori, v1 §1.3, equation (3)][PCR-BM]. It requires a monic
polynomial, not an invertible companion or a field quotient; hence it
applies to $X^a g$, repeated factors, constants and an impulse. For
$r=0$ return zero, after reading the requested exponent field.

No indexed coefficient access is hidden in its arithmetic bound.
Use contiguous coefficient strings of length $O(r+1)$ on a fixed
number of tapes. To multiply two polynomials, sweep one factor and
add a shifted copy of the other into a length-$2r+1$ accumulator.
Each of the $O(r+1)$ shifts costs $O(r+1)$ head moves, copies and
XOR writes, including the return scan; moving the alignment by one
cell is charged. Mark the current alignment on a separate track.
For reduction, sweep high coefficients downwards and, for every
nonzero one, XOR the aligned monic divisor across at most $r+1$
cells, then return to the next marked high position. At most $O(r+1)$
positions are reduced, at cost $O((r+1)^2)$ including positioning.
A marked unary sweep, delimited by the actual coefficient strings,
controls these loops; it uses $O(r+1)$ cells and does not require a
binary array-index operation at each coefficient. Buffer clearing,
copying, end markers, multiplication by $X$, and the final dot product
fit the same bound. Each exponent bit is read once while the other
tape heads perform these scans, with $O((r+1)^2)$ work and writes per
bit and $O(r+1)$ reused arithmetic backing. Thus a $K$-bit exponent
costs $O(D^2(K+1))$ work and writes, using $O(D+K)$ bits if its
explicit exponent copy is included. This is a bit and head-motion
bound over $\mathbb F_2$, not merely a ring-operation count.

Next bound every query operand. After $h$ selected edges, (PCR.39)
gives $B_v+1\le3^{h+1}$, $1\le A_v<B_v$, and $1\le e_v\le1+2h$.
For a word query $h\le|v|$, so all exact coordinates and evaluated
exponents $A_v-1$ have $O(R+1)$ bits. There are at most $|v|+1$
term evaluations, including the returned event bit. Coordinate
addition, doubling, comparison, subtraction, label changes, end
markers and buffer resizing take $O(R+1)$ sequential work and writes
per step, using a constant number of reused strings. The input-word
head only advances; there is no rescan of all earlier letters and no
stored sibling list.

For an ordinal query, $F_{2k+2}\ge2^k$ by induction, so locating
$F_\tau\le j<F_{\tau+1}$ takes $O(R+1)$ successive additions.
The final pair and every intermediate Fibonacci integer have
$O(R+1)$ bits: the first one exceeding $j$ is at most $2j+1$.
The bracket search, comparisons, its represented loop counter and
initial two subtractions to obtain $(F_t,F_{t+1})$ therefore cost
$O((R+1)^2)$ work and writes and $O(R+1)$ backing, with the small
$\tau=2,3$ cases treated directly. Descent takes at most
$t=\tau-2=O(R+1)$ edges, so the same coordinate-width bound applies.
Its block counts, residual rank, remaining time and pair of Fibonacci
values all have $O(R+1)$ bits. Every rank comparison/subtraction and
pair rollback, including the zero slow block at $u=1$, takes
$O(R+1)$ work and writes. A selected letter is appended with the
output head kept at its end. No ancestor is retained when $u$
decreases. There are $O(R+1)$ term evaluations, each at an exponent
of $O(R+1)$ bits, so their total is $O(D^2(R+1)^2)$.

The cut guard is one final sequential comparison of the computed
$\tau=e+1$ with the supplied $n$, costing $O(I+R+1)$. It is not
repeated along descent. Extra claimed fields are compared once with
the resulting tuple in $O(I+R+L_{\rm out})$ work. Copying requested
input fields and writing or retaining the explicit output cost their
actual lengths. All controller state is either finite control, a
represented counter bounded above, or one of the named strings.
No loop traverses blank gaps beyond these contiguous buffers. At all
times their total visited backing is
$O(I+D+R+L_{\rm out})$, and all arithmetic, allocation, clearing,
relocation, counter and output writes have already been included.
This proves (PCR.79) for successes and each rejection path. $\square$

**Proposition 27.7 (the resource scope and the unacquired interfaces).**
The word and ordinal lengths in (PCR.78) are comparable on valid inverse
pairs, up to absolute constants and an additive one. Linear peak
backing is attained on a fixed admitted source. Nevertheless (PCR.79)
is a supplied-data query bound and supplies no source acquisition,
original-enumeration firstness, physical installation or finite-state
online history machine.

Proof. For $|v|=h$ the branch time lies in $[h+2,2h+2]$.
By (PCR.71), $F_{\tau_v}\le Q_s(v)<F_{\tau_v+1}$.
The inequalities $F_k\le2^k$ and $F_{2k+2}\ge2^k$ give
$|\operatorname{bin}(Q_s(v))|=\Theta(h+1)$. For the all-one source,
$v=a^h$ has $(e,A,B)=(h+1,F_{h+2},F_{h+3})$ by (PCR.39).
Its inverse literal output has $h$ symbols and thus requires
$\Omega(R)$ output bits. Separately materializing the current exact
boundary at every step writes $\Theta(h^2)$ bits along this family;
Retaining all those boundaries would require quadratic peak space. The iterative query uses only the current boundary, so
this is consistent with its quadratic work and linear peak space.
It is not a universal quadratic-work lower bound on all possible
query algorithms.

The preparation in (PCR.79) reuses the original authentic prefix and
seed. It does not establish that the prefix has been earned: paid
full-root presence-only Reads, source storage, root binding,
stationarity throughout the service interval, grants, backing and
synchronization retain exactly their original premises and tariffs.
The acquired actual $n$ and the original transient-inclusive $(P,n)$
output are preserved; law-ready hypothetical evaluation cannot replace
them. Minimal-source synthesis also does not select $K_d(P)$ or the
original $\rho_d$ first passing row on a deficient-rank fibre. Those
normalization and completed physical-installation obligations remain
the separate tasks in ACR §§21 and 26 and GPO §§34 and 39.

The ordinary inverse here reuses ACR Proposition 10.2; its global birth
calibration is GPO Proposition 39.2 and ACR Theorem 27.2, while the
source-specific linear-backing query bound uses the exact integer
transport of §17 and the exact-layer block counts of §24. Equation
(PCR.79), with authentic raw preparation and growing operand widths,
is the resource assertion in addition to those existing inverses.
Massey's finite synthesis [MAS] and the monic-quotient identity
(PCR.80) are reused suppliers, not new recurrence theorems or a
literature-priority claim for this application.

The distinct typed interfaces also prevent a change of source model.
`ActualTreeReadoutAcquisition.readout` in D5 takes an explicit finite
native labelled tree and returns alpha, beta, branch or absent;
`ArchiveClockRecovery.archive_clock_recovery_and_finite_ambiguity`
takes a finite partial-action system and complete visible archives.
Neither supplies this entrance's paid presence-only full prefix,
actual cut, or an ordinal service. The conditional exact quotient
endpoint and native-clock acquisition of TRC23, Definition 23.1,
also differs from these inputs, even with constant current readout.
No such native readout or clock is an argument to (PCR.69)--(PCR.80).
These are ordinary mathematical deductions on the original supplied
source, without a fresh compiled Lean assertion. $\square$

## 追加锚（本行以下为增补区）

## 28. Paid sparse authentication along actual physical ancestry

**Definition 28.1 (source, menu and certificate domain).** Retain the
original alpha-origin source of Definition 1.1, the authentic public
promise $s\in\mathscr R_d$, and the entire paid entrance of
[ACR, Definition 9.1][ACR]. In particular the unknown completed cut $n$
is mature, the root is genuinely bound, and the only replies are
stationary, total, paid full-root presence bits. Law, seed, labels,
ordinal ports and the cut are not supplied. Reads do not advance the
source. The original requested output remains $(P,n)$ with
$P=s_0\cdots s_{2d-1}$; the following scoped output is an additional
boundary, not an alternative definition of that task.

Let $T\subseteq\{a,b\}^*$ be a finite public prefix-closed set of $K$
words. Empty $T$ is allowed; otherwise it contains the empty root.
Put $h=\max_{v\in T}|v|$, with $h=0$ for empty $T$. The immutable
creation descriptors, actual indices and event bits are those of
Definitions 17.1 and 27.1. Write

$$
 \gamma_s(T)=(c_v:v\in T),\qquad c_v=s_{A_v-1},\qquad
 \mathcal D_{d,n}(T)=\{s\in\mathscr R_d:
                   \tau_v=e_v+1\le n-1\text{ for all }v\in T\}.
\tag{PCR.81}
$$

The menu has a fixed length-then-physical-lexicographic order. This is
an actual-image domain: every record must be produced by the same
original source, with its own recursively determined indices. Arbitrary
bit records, independently chosen local cones and unbound numerical
clocks are not declared attained data. The guard in (PCR.81) means that
at least one update has followed the queried branching event. It is
stronger than PCR27's already-occurred guard $\tau_v\le n$.

A proposed certificate consists of a binary integer $\nu\ge2$, the
root words $x,y$ below, and, for each $v\in T$, a bit $\widehat c_v$
and a physical suffix $w_v$. Derive all proposed coordinates from
$(e,A,B)=(1,1,2)$ and the actual integer table (PCR.37)--(PCR.39), using
only the bits at proper physical ancestors. Derive the root creation
pair $(0,\alpha)$, and a child's creation cut $e_{\rm parent}+1$ and
initial label from the chosen delay. No earlier chronological prefix
is an argument to this derivation. Require

$$
 \widehat\tau_v=\widehat e_v+1\le\nu-1,
 \qquad |w_v|=t_v:=\nu-\widehat\tau_v\ge1.
\tag{PCR.82}
$$

The root tests, including their indispensable length conditions, are
exactly [ACRC, Definition 33.1][PCR-ACRC]: $|x|=\nu-1$, with
$\operatorname{Read}(x)=1$, and

$$
\begin{array}{c|c|c}
\nu&|y|&\text{required replies}\\ \hline
2k+1&k&\operatorname{Read}(ya)=0\\
2k&k-1&\operatorname{Read}(yaa)=\operatorname{Read}(yba)=0.
\end{array}
\tag{PCR.83}
$$

After these tests pass, check the menu in its fixed ancestor-first
order. For $\widehat c_v=1$ put $p_v=a$, and for $\widehat c_v=0$
put $p_v=b$. Require the single paid reply

$$
                \operatorname{Read}(v p_v w_v)=1.
\tag{PCR.84}
$$

Every displayed argument is materialized at the original root, including
$v$. There is no relative-root operation. An acceptance returns the
acquired cut and every PCR27 full tuple

$$
 \Theta_s(v)=
 (v; j_v,b_v,\sigma_v,\tau_v,e_v,A_v,B_v,c_v),\qquad j_v=A_v,
\tag{PCR.85}
$$

including the event bit at the final queried node.

Reject noncanonical or signed integer encodings, a nonphysical letter,
a nonbit, duplicated or missing menu entries, a menu that is not
prefix-closed, a wrong suffix or root length, or a failed guard before
source tests. Integers use canonical binary notation, with one digit
for zero. If extra indices, creation fields or labels are proposed,
compare them with the derived values and reject disagreement. Reject
on any failed required reply. A failed suffix is a failed certificate,
not by itself a certificate that its proposed bit is false. The
public source-class promise and the physical binding remain premises;
no syntactic check certifies either.

**Theorem 28.2 (universal soundness and existential completeness).**
On every original input, every accepted certificate of Definition 28.1
has $\nu=n$, $s\in\mathcal D_{d,n}(T)$, and exactly the actual
orientation record and tuples (PCR.85). Conversely, for this fixed
source there exists an accepted certificate for a proposed cut and
record exactly when

$$
 \nu=n,\qquad s\in\mathcal D_{d,n}(T),\qquad
           \widehat c_v=c_v\quad(v\in T).
\tag{PCR.86}
$$

Verification uses at most $K+3$ paid Reads. A well-formed but incorrect
proposal cannot acquire an actual-image boundary by passing these tests.

Proof. ACR Theorem 22.2 and ACRC Theorem 33.2 give universal root
soundness and existential root completeness with precisely (PCR.83).
For clarity, a rank-$q\ge1$ cone has maximal suffix depth $q-1$;
ranks zero and one are terminal. Presence of $x$ forces $n\ge\nu$.
If $\nu=2k+1$ and $n\ge\nu+1$, every word of length $k+1$ is
present, contradicting $ya$ absent. If $\nu=2k$ and $n\ge\nu+1$,
every $y$ of length $k-1$ reaches residual rank at least three, so
one of $yaa,yba$ is present. Thus an acceptance forces $n=\nu$.
At the true cut choose a longest $x$ and a path repeatedly taking the
rank-two decrement for $y$. It ends at rank one in the odd case and
rank two in the even case, giving the required absences. For $\nu=2$
this is empty $y$ and the absent literals $aa,ba$. No independent
presence query for $y$ is needed. Cuts zero and one cannot pass this
root certificate and are outside the original mature entrance.

Now induct on the menu order. The root's proposed descriptor is actual.
At any later $v$, prefix closure supplies all its proper ancestors.
Their already authenticated bits and Theorem 17.2 give the actual
$(e_v,A_v,B_v)$, creation label and creation time, using only this
ancestry. In particular this is the genuine physical parent of birth
$A_v$, regardless of any bits at earlier chronological events outside
its ancestry. The exterior contribution in (PCR.39) is already exact;
it does not require authenticating the exterior's orientations. This
discharges the genuine-parent premise of ACRC Theorem 33.3 without
its earlier-prefix reconstruction.

At cut $n$, set $t=n-\tau_v\ge1$. The originally beta child has rank
$t+1$ and maximal suffix depth $t$; the originally alpha child has
rank $t$ and maximal suffix depth $t-1$. These are the same actual
children created at $\tau_v$, with no normalization of the source.
Consequently a supplied positive length-$t$ suffix exists exactly
under the true beta child. Every positive such suffix certifies
$\widehat c_v=c_v$; a wrong orientation admits none. This proves
the induction and every returned field, including the final event bit.
For the reverse direction choose one longest suffix under every true
beta child and the true root witnesses. The ancestor induction makes
all lengths and guards correct. There are at most three root Reads
and exactly one required Read per menu node, proving the bound.
A particular correct record with badly chosen witnesses can still fail;
only existence of accepting witnesses is asserted. $\square$

**Corollary 28.3 (one word and one ordinal).** For one physical word
$v$ of depth $h$, use its $h+1$ prefixes, including itself. If its
actual branch time satisfies $\tau_v\le n-1$, a certificate for its
full tuple uses at most $h+4$ paid Reads. For one positive ordinal
$j$ in birth batch $\tau=\tau(j)$, a certificate for its actual word
and full tuple uses at most $\tau+2$ Reads when $\tau\le n-1$.
Neither certificate assumes the full acquired law.

Proof. The word's proper ancestors branch strictly earlier, so its guard
implies all ancestral guards. Theorem 28.2 gives the first bound.
For the ordinal, compute its unique Fibonacci bracket
$F_\tau\le j<F_{\tau+1}$, without source bits. A certificate proposes
one physical word $v$, with its full prefix menu, and additionally
requires $|v|\le\tau-2$, $\widehat\tau_v=\tau$ and
$\widehat A_v=j$. Reject ordinal zero or any failed comparison.
PCR27.2 makes these equalities sufficient to identify the unique actual
parent of birth $j$ after the ancestry has been authenticated.
Conversely that actual parent has depth at most $\tau-2$, so its
certificate has $K\le\tau-1$. Theorem 28.2 proves soundness,
completeness and $K+3\le\tau+2$. The tuple includes $s_{j-1}$,
not merely an address. The empty word is included: $j=1$, $\tau=2$,
and the sparse orientation certificate needs $n\ge3$. At $n=2$ that
event has occurred but this certificate guard fails; at $d=0$ its bit
can instead be inferred from the public zero-source promise. No
necessity of this guard for all possible methods is claimed. $\square$

**Theorem 28.4 (literal traffic and represented certificate charges).**
Let $I$ be the complete actual encoded input length, including $d$, the
menu or query, every certificate field and every extra proposed field.
Let $L$ be the complete actual output length. On a well-formed proposal,
let $L_{\rm root}$ be the sum of all root literal lengths in (PCR.83).
Verification has

$$
 Q\le K+3,\qquad
 J\le L_{\rm root}+\sum_{v\in T}(|v|+1+t_v)
       \le3\nu+K(\nu-1),\qquad M\le\nu.
\tag{PCR.87}
$$

Here $J$ counts full literal traffic and $M$ is the maximum literal
length. On success $\nu=n$. In the sequential symbol-and-head-motion
model of Theorem 27.6 there is a uniform verifier with conservative
bounds

$$
 C,W=O((I+L+1)^4),\qquad V_{\rm peak}=O((I+L+1)^2).
\tag{PCR.88}
$$

These include rejected proposals, actual input access, local arithmetic,
all copied literals, cumulative writes, retained cut, tuples and any
requested certificate copy. They exclude no address prefix. Physical
Read charges and durations retain the original tariff in addition to
these local charges.

Proof. Every derived edge increases $e$ by one or two. Hence
$\widehat\tau_v\ge|v|+2$, even before authenticity is established.
Thus $|v|+1+t_v\le\nu-1$. Directly from the two parity cases,
$L_{\rm root}\le3\nu$ and each root literal has length at most
$\nu$, including $\nu=2$. Early rejection only shortens this list
of tests. No source Read is needed on a malformed structural proposal.
The caller pays for receiving and retaining proposed witnesses; the
Read count does not pay for their discovery.

Here is a finite sequential realization of the local bound. Scan actual
input fields and count their lengths before expanding any declared
quantity. Compare the binary $\nu-1$ with the actual length of $x$;
a huge but short malformed integer proposal causes no numeric-$\nu$
loop. Validate letters and all other lengths similarly. On a structurally
valid proposal $\nu\le I+1$ and every explicit menu depth is at most
$I$. Repeated scans of the finite menu can check duplicates, order and
prefix closure and locate each parent without indexed unit-cost access.
After depth $r$, the integer transport has $B+1\le3^{r+1}$, so its
coordinate operands have $O(r+1)$ bits. Addition, doubling, comparison,
label propagation and subtraction use sequential scans of those strings.
Root and suffix literals are copied in full. Even charging a complete
input scan for each lookup, comparison and buffer relocation fits the
fourth-power work and write bound. Storing the finite records, visited
buffers, input and explicit output fits the stated quadratic backing.
The ordinal variant computes its Fibonacci bracket by $O(|\operatorname{bin}
(j)|+1)$ additions on operands of that represented width, as in PCR27.6.
No table indexed by the numeric ordinal is built. All syntax failures,
false fields, failed guard tests and failed presence tests fit (PCR.88)
at their actual input lengths. An accepted explicit certificate has
size $O((K+1)(n+1)+I_{\rm request})$; its words and output copies are
paid data, even if the retained orientation payload is only $K$ bits.
$\square$

## 29. Finite discovery and exact source-coordinate retention

**Theorem 29.1 (unknown-cut and unknown-law discovery).** On the original
paid entrance, there is a finite uniform discovery of the boundary and,
if requested, a positive certificate of Definition 28.1, for every
$s\in\mathcal D_{d,n}(T)$. It assumes neither actual $n$ nor a source
law. With $t_v=n-\tau_v$, put

$$
 S(n)=\sum_{\nu=2}^n
          (2^{\nu-1}+2^{\lfloor\nu/2\rfloor}),\qquad
 R=S(n)+2\sum_{v\in T}2^{t_v}.
\tag{PCR.89}
$$

One such discovery has $Q_{\rm disc}\le R$, maximum literal length
at most $n$ and literal traffic $J_{\rm disc}\le nR$. In particular
$R\le(n+K)2^n$ for $n\ge2$. These are conservative exponential
bounds, not a cheap discovery optimum. If $I_0$ is the actual request
length and $L_0$ the actual discovery output length, a sequential
realization has, with $E=I_0+L_0+K+n+2$,

$$
 C_{\rm disc},W_{\rm disc}=O(E^4(R+1)),\qquad
 V_{\rm disc}=O(E^2),\qquad U_{\rm source}=0.
\tag{PCR.90}
$$

The same discovery applies to a word query and, with an adaptively
generated ancestor chain, to an ordinal query under Corollary 28.3's
guard. If the actual menu fails its visibility guard, the procedure
instead returns that scoped failure after finite root recovery and
ancestral work; it does not report the original $(P,n)$ task impossible.

Proof. Reuse exactly ACRC Proposition 33.4's root discovery. Try
$\nu=2,3,\ldots$. Enumerate length-$(\nu-1)$ words until a positive
$x$ appears; if none appears skip the $y$ search. Otherwise enumerate
all correctly sized $y$ until (PCR.83)'s required absences hold. Odd
proposals use at most $2^{\lfloor\nu/2\rfloor}$ negative tests;
even proposals use at most twice $2^{\nu/2-1}$ tests. Universal
soundness excludes acceptance at a false cut, and existential
completeness forces acceptance at $n$. This gives $S(n)$, including
all unsuccessful proposals and negative replies. It does not repeat
ACR's spine doubling/bisection as a new acquisition result.

Proceed in menu order. With ancestors earned, compute the genuine
parent coordinates by Theorem 28.2's induction. A failed actual guard
ends this scoped attempt. Otherwise try orientation zero and enumerate
all $2^{t_v}$ suffixes under its selected child. A positive reply
authenticates zero and supplies its witness. If every reply is zero,
ACRC (ACRC.1) authenticates one, because the genuine parent's true beta
child must have a length-$t_v$ suffix. For a positive certificate,
search that other child until one such suffix appears. This costs at
most another $2^{t_v}$ Reads. Retain the successful suffix; exhausted
negative replies need not be stored to output a positive certificate.
The extra factor two in (PCR.89) pays for obtaining that witness.
If only the orientation boundary is requested, the complete-negative
argument alone avoids this second search, with bound
$S(n)+\sum_{v\in T}2^{t_v}$. No single absent suffix is used to infer
a bit. Parent correctness at every step uses only earned ancestry.

For an ordinal query, root discovery first earns $n$; its public
Fibonacci bracket supplies $\tau(j)$. Reject this scoped request when
$\tau(j)>n-1$. Otherwise use PCR27.3's exact layer block counts and
residual rank. Earn the current node's orientation by the same suffix
search, select the next physical child using those counts, and continue
until the remaining layer time is zero. At that final node also earn
its own event bit. The block counts depend only on Fibonacci numbers
and the earned current orientation. PCR27.4's descent proof therefore
applies without supplying a term evaluator or the full law. Its chain
has $K\le\tau(j)-1$ nodes, all within the visibility guard. Equations
(PCR.89)--(PCR.90) apply with that actual finite chain; $I_0$ includes
the represented ordinal and $L_0$ its full literal and tuple output.

Root literals have length at most $n$ and subsequent literals at most
$n-1$. Each summand defining $S(n)$ is at most $2^\nu$, so
$S(n)<2^{n+1}\le n2^n$ for $n\ge2$. Also $t_v\le n-2$, so
$2\sum_v2^{t_v}\le K2^{n-1}$. These imply the displayed conservative
bound $R\le(n+K)2^n$. Contiguous binary-word enumeration, actual
root words, one current suffix and the finite retained records suffice.
All counters have at most $O(n+1)$ bits. Scans, copies, arithmetic,
clearing and output can each be charged within $O(E^4)$ per trial;
only a polynomial amount of scratch and the actual output is retained.
This gives (PCR.90) without treating exponentially many trials as
free. Fresh re-verification after discovery has the separate bill
(PCR.87); the successful discovery replies themselves already justify
the boundary.

This finite entrance is different in cost and output from
[PSA, Theorem 8.4][PCR-PSA], which acquires the entire original $(P,n)$
with its stated logarithmic-Read and polynomial represented-work bounds.
That supplier, followed by PCR27, remains available for queries outside
(PCR.81), including occurred events at the final cut and whole-orbit
future queries. Neither bound creates an ordinal Read service. $\square$

**Definition 29.2 (the actual source-label image).** For fixed $d,T$ put

$$
 \Gamma_d(T)=\{\gamma_s(T):s\in\mathscr R_d\},\qquad
 \mathcal Q_s(T)=(\Theta_s(v):v\in T).
\tag{PCR.91}
$$

Fix a common public cut $n\ge\max(n_0(d),2h+3)$, where $n_0(d)$ is
the original maturity bound of ACR (ACR.23). Then every such source is
in (PCR.81). All capacity statements below fix this cut, the public
menu and the public order bound, and count only a source-dependent
fixed-width binary label for mathematical query output. They do not
count the public codebook, binding, grants, cut storage or physical
installation as zero-cost acquired resources. Empty $T$ requires no
additional cut bound beyond original maturity.

**Theorem 29.3 (mutual recovery on the actual image and exact label capacity).**
On the domain of Definition 29.2, $\gamma_s(T)$ and the entire full-tuple
menu $\mathcal Q_s(T)$ determine one another. Their zero-error source-label
capacity is exactly

$$
 b_d(T)=\left\lceil\log_2|\Gamma_d(T)|\right\rceil,
 \qquad 0\le b_d(T)\le\min(K,2d).
\tag{PCR.92}
$$

If $T$ is nonempty with maximal depth $h$, then

$$
 d\ge F_{2h+3}-1\quad\Longrightarrow\quad
                \Gamma_d(T)=\{0,1\}^T,
 \qquad b_d(T)=K.
\tag{PCR.93}
$$

Every assignment in (PCR.93) is realized by an original all-index source
fixed before its first birth, at the same legitimate cut. These are
not independent hypothetical local-cone assignments. At any smaller
mature cut the same mutual recovery holds on $\mathcal D_{d,n}(T)$;
when this domain is nonempty its exact label capacity is the ceiling
logarithm of its restricted orientation image.

Proof. Given an attained orientation record, run the physical ancestor
transport, including the creation descriptors, and output each node's
own record bit as its event bit. Theorem 17.2 and PCR27.2 give exactly
(PCR.85). Conversely extract the event bit in each full tuple. The
compositions are identities on the actual images in (PCR.91), not on
arbitrary malformed tuple arrays. The same tuple and the public cut
also decide that node's already-occurred guard. A full-tuple distinction
therefore is exactly a distinction of attained orientation records.

The finite-label pigeonhole bound gives the lower bound in (PCR.92).
An enumeration of the finite set $\Gamma_d(T)$ attains it as an
abstract code. A $K$-bit uncompressed record also suffices. GPO Lemma
29.2 makes $P=s_0\cdots s_{2d-1}$ injective on $\mathscr R_d$, so
there are at most $2^{2d}$ sources and at most that many records.
This proves the upper bounds, and restricting the same bijection and
counting argument proves the assertion at smaller cuts. It supplies no free
codebook acquisition or efficient optimal encoder. At $d=0$ the sole
source is zero and the label has zero bits. For empty $T$ there is one
empty record and one empty tuple menu, so again $b_d(T)=0$; cut recovery
has its independent bill.

For (PCR.93), set $M=F_{2h+3}-1$ and prescribe arbitrary bits
$\eta_v$ at every $v\in T$. Construct one finite chronological word
by running the actual alpha-origin rule through cut $2h+2$: when the
next old beta parent is $v\in T$, append $\eta_v$, and at every other
parent append zero. Process each batch in physical order. Counts do
not depend on orientations, so exactly $M$ bits are appended.
Every node of physical depth at most $h$ branches by cut $2h+2$,
because each edge adds at most two to branch time. Each such parent
is consequently encountered once, with its prescribed bit if in $T$.

Now define a single stream $s$ to be this finite word followed by
zeros. This definition specifies the source before any observation or
first physical birth. The finite construction is a mathematical way
to compute its seed, not feedback supplied to the running generator.
Forward induction on chronological events shows that its original
orbit reproduces that construction. Also $E^Ms=0$ at every
nonnegative index, so $s\in\mathscr R_M\subseteq\mathscr R_d$,
including its entire finite singular transient. Its record is precisely
$\eta$. Fix $n\ge\max(n_0(d),2h+3)$ for all these sources. Every
selected event is then visible by (PCR.81), and Theorem 28.2 gives
actual accepting certificates at that common cut. Thus all $2^K$
assignments are attained. The sufficient bound is not asserted sharp;
no generic independence of coordinates at a smaller $d$ is presumed.
$\square$

**Theorem 29.4 (exact limits of retained-menu extension).** Let
$T\subseteq T'$ be fixed finite prefix-closed full-tuple menus, and
fix a common legitimate cut large enough for the visibility guard of
both. The retained boundary for $T$ determines all of $T'$ exactly
when the actual restriction

$$
          \Gamma_d(T')\longrightarrow\Gamma_d(T)
\tag{PCR.94}
$$

has singleton fibres. If $T'=T$ this holds. If $T'\setminus T$ is
nonempty and $d\ge F_{2h'+3}-1$, where $h'$ is its maximal depth,
it fails. For an arbitrary finite word menu $V$ that is not necessarily
prefix-closed, orientations on its ancestor closure, including the
queried nodes, are sufficient for its full tuples; no necessity or
minimality of that sufficient record is asserted.

Proof. Theorem 29.3 identifies each complete tuple menu with its actual
orientation record. Thus unique extension of the record is sufficient
and necessary for extension of the prefix-closed full-tuple menu.
This uses the actual simultaneous source image, not a Cartesian
product of independently realizable cone records. In the large-order
case Theorem 29.3 realizes two assignments equal on $T$ and different
at a selected node of $T'\setminus T$. Their target event-bit fields
differ, refuting extension. For a non-prefix-closed menu, applying
ancestor transport to its prefix closure proves only the stated
sufficient direction. Correlations at small order can reduce necessary
information, as the zero source already demonstrates. An arbitrary
new query need not factor through (PCR.94), so there is no automatic
boundary-update rule for undeclared extensions. $\square$

**Proposition 29.5 (a mature actual pair and the two visibility limits).**
A retained root full tuple need not determine a later word or ordinal
query, or its already-occurred domain. This failure occurs on two
sources in the same original class at a common mature cut. Further,
omitting the positive residual-time guard in (PCR.82) makes its
one-literal orientation check unsound even on a mature source.

Proof. Take $s=000\cdots$ and $s'=01000\cdots$ in $\mathscr R_2$.
The latter is annihilated by $E^2$; the sources are fixed before birth.
Both root bits are zero, and hence both root tuples are
$(\varepsilon;1,0,\alpha,2,1,1,2,0)$. Both have child $b$ with
$(e,A,B)=(2,2,4)$, but its event bit is respectively zero and one.
Transport gives

$$
 U_s(4)=bb,\quad U_{s'}(4)=ba,\qquad
 Q_s(bb)=4,\quad Q_{s'}(bb)=7.
\tag{PCR.95}
$$

At common cut six the root and the $bb$ queries satisfy the sparse
visibility guards for both sources; the full tuple of $b$ also differs.
Their original prefixes are respectively $0000$ and $0100$, so this
common current query record has not determined the full original law.
The two individual queries in (PCR.95) are available without retaining
all earlier chronological bits, but acquiring their missing ancestry
still has Theorem 29.1's bill.

The original maturity bound at $d=2$ is five. At common cut five,
the word $bbb$ branches at cut five for $s$ and six for $s'$:
its normalization origins are four and five. Thus even the legality
of an already-occurred event query at that word is not determined by
the common retained root tuple and cut. This is a query-domain
distinction, not an authorization to perform a physical update.

For the last assertion take the zero source with $d=1$ at its mature
cut four. The node $a$ branches at that very cut. Both $aa$ and $ab$
are present. If $t=0$ were admitted, the empty suffix under either
claimed beta child would pass, although its actual event bit is zero.
The event has occurred; its children's just-created supports do not
yet distinguish their initial labels. PCR27 with a separately acquired
law can still answer it. With $t\ge1$, a negative suffix also cannot
alone refute a bit: at cut four the true root beta child is $b$, but
$baa$ is absent while $bba$ is present. These are genuine original-source
words, not abstract rank trials. $\square$

**Proposition 29.6 (supplier scope and preservation of the original task).**
The preceding authentication, discovery and retention conclusions use
the original full class without invertibility, squarefreeness, a period
bound or a supplied law. They add a sparse genuine-parent entrance to
PCR27's supplied-data queries, while retaining the independent original
acquisition, normalization, source-binding and installation obligations.

Proof. The only source-specific inputs to the new ancestor induction
are PCR17.2's exact integer table and PCR27.2's global calibration.
ACR22.2 and ACRC33.2 supply precisely the parity- and length-guarded
root test. ACRC33.3--33.4 supply the actual-parent maximal-suffix
criterion and finite paid enumerations. The additional induction in
Theorem 28.2 proves their genuine-parent premise from physical ancestry;
it does not invoke their chronological-prefix reconstruction. ACR10.2
already supplies the beta-list inverse mechanism; ACR21 gives behavioral
synthesis and firstness boundaries; ACR27 gives authentic integer
exterior clocks. ACR28--33 and PSA8.4 concern acquisition or
normalization with their own hypotheses and bills. None is replaced
by a new general inverse-existence or generic quotient theorem.

The source-label count and finite transient realization in Theorem 29.3
are repository-derived ordinary deductions on this same source. The
finite-label counting step is elementary; it is not a literature-priority
claim. Massey [MAS], §§II--III, defines length-$L$ synthesis without
requiring the final tap nonzero, and distinguishes register length from
connection-polynomial degree. With forward coefficients as here the
polynomial is $X^L C(1/X)$, retaining possible factors of $X$. This is
the existing ACR21/GPO29 convention, not a physical acquisition theorem.
Bostan--Mori [PCR-BM], v1 §1.3, equation (3), takes the coefficient
vector of $X^N\bmod\Gamma$ against the original initial terms for
$\Gamma=X^r-\sum_{i<r}c_iX^i$. Its monic quotient identity is PCR27's
computational supplier, including singular factors; it is not needed
to manufacture any Read in (PCR.83)--(PCR.84).

The D5 suppliers discussed in PCR27.7 keep their exact types:
`ActualTreeReadoutAcquisition.readout` takes an explicit native tree and
returns a four-valued reply, while
`ArchiveClockRecovery.archive_clock_recovery_and_finite_ambiguity`
takes a finite action system and full visible archives. Neither is an
unknown-law presence entrance. Likewise TRC24's finite partial-token
source, source-refining online state and final-only acquired endpoint
and clock belong to a different interface. No endpoint, archive or
source-refining online state is an input here. The new statements are
ordinary mathematical proofs, without a fresh Lean/kernel claim.

Authentic root binding, grants, reliable completed Reads, sufficient
owned readable backing, source storage and a stationary completed-cut
interval covering all realized discovery, verification, local work and
writes remain independent premises. If the cut changes, the root
certificate must be reacquired or a separately justified synchronized
update must provide the new cut. A record for a fixed menu gives no
arbitrary-source online update, additional permission or physical
installation. The same applies to retaining a compressed label: its
encoding, decoding, copying, codebook and output must be paid.

The original transient-inclusive $P$ is not generally recovered by the
sparse menu, as Proposition 29.5 proves. If the original $(P,n)$ output
is requested, use a supplier that actually earns it, such as PSA8.4,
and charge its work and the full output copy. The original $K_d(P)$,
$\rho_d$ first passing row, normalization and completed same-source
installation remain the independently charged tasks of ACR26/29 and
GPO34/39. Finite transients, repeated core factors, nonminimal
presentations and unbounded periods retain their original domains;
none of the present arguments substitutes a core for the source.
$\square$

[PCR-ACRC]: RECURSIVE_RELATIONAL_OBSERVATION_ACTUAL_CUT_REINSTATEMENT_CONTINUATION.md
[PCR-PSA]: RECURSIVE_RELATIONAL_OBSERVATION_POLYNOMIAL_SOURCE_ACQUISITION.md

## 追加锚（本行以下为增补区）
