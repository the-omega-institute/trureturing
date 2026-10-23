# FIB-ATOM boundary geometry: finite joint cycle and radial prediction

## 1. The fixed source and the bounded-jump experiments

**Definition 1.1 (source, clock and exact observation).** Fix an integer
$m\ge3$. Throughout this companion, the source is literally the infinite
ordered address tree $\mathcal P=\{L,R\}^{*}$ with root $o=\varepsilon$,
unit symmetric parent--child seam rates and counting measure. The root
has degree two and every nonroot has degree three. Retain the functions
$q:\mathcal P\to C_m$ and $\delta:\mathcal P\to\{-1,0,+1\}$ of
[V Definition 120.3, (120.12)](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_V.md).
In particular, their ordered child recursion, rather than an arbitrary
cycle colouring, is part of the assumptions.

Let $X$ have the conservative continuous-time law $\mathbf P_p$ from the
deterministic start $p$, with backward generator $\mathscr G=-L_\infty$,
in the unit counting clock of V Definition 121.1. Write

$$
n=d(p)=|p|,\qquad \phi(p)=2^{-|p|},\qquad
O(p)=(q(p),d(p))\in E=C_m\times\mathbb N_0.
\tag{1.1}
$$

The field and source are those of
[Continuation Definitions 55.1--55.2 and Theorem 55.3](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md).
The present probability law is the kinetic law alone, with neither a
potential multiplier nor an amplitude evolution. The observation is the
exact continuous path of $O$, including time zero and every jump time.
Replacing depth by $\phi$ gives the same experiment only for exact
noiseless field values. Every actual seam changes depth by one, including
a seam that preserves $q$.

Use the path spaces and coordinate sigma algebras of V Definition 121.1.
Their full observed laws are denoted by $\mathsf L_p^T$ on $[0,T]$ and
$\mathsf L_p^\infty$ on $[0,\infty)$. For probabilities on the same
measurable space the convention is

$$
\|\mu-\nu\|_{\mathrm{TV}}=\sup_A|\mu(A)-\nu(A)|\in[0,1].
\tag{1.2}
$$

All statements below quantify over deterministic starts in this fixed
infinite law. Restricting allowed starts does not restrict the subsequent
chain to a finite domain. No initial mixtures, changed seam rates,
changed clock, masses, weights, potential, killing, noisy observations or
discrete sampling are implicit.

**Definition 1.2 (actual jumps and the frozen observed display).** Put
$\tau_0=0$, and let $\tau_j$ be the time of the $j$th actual source jump.
Let $Y_j=X_{\tau_j}$, with $Y_0=p$. The embedded true-jump kernel is

$$
J(x,z)=
\begin{cases}
1/\deg(x),&z\sim x,\\
0,&\text{otherwise}.
\end{cases}
\tag{1.3}
$$

Conditional on the embedded route, the successive waiting times are
independent exponentials of parameters $\deg(Y_j)$. In particular the
root waiting time has parameter two, not three.

For an integer $h\ge0$, define the stopped and then frozen observation

$$
Z_t^{[h]}=O(X_{t\wedge\tau_h}),\qquad
\mathsf F_{h,p}^T=\operatorname{Law}_{\mathbf P_p}
       ((Z_t^{[h]})_{0\le t\le T}),\qquad
\mathsf F_{h,p}^\infty=\operatorname{Law}_{\mathbf P_p}
       ((Z_t^{[h]})_{t\ge0}).
\tag{1.4}
$$

The source process $X$ continues after $\tau_h$; (1.4) only freezes its
display. This is not a new closed or killed source, nor a native Stop
instruction. At $h=0$ the display is constant from time zero. For finite
$h$ the complete display records its first $h$ actual jumps and their
waiting times and then remains at the $h$th observed state.

The rate-three uniformization is exactly
$R_\infty=I-L_\infty/3$ of V Proposition 120.4: each nonroot row chooses
parent, left child or right child with probability $1/3$, whereas the root
row chooses its two children and one virtual hold with probabilities
$1/3$ each. A virtual hold is neither an actual source jump nor a jump of
the observed depth. A common independent rate-three Poisson clock
therefore gives finitely many actual jumps on every bounded interval.
Each next actual waiting time has parameter two or three and is finite
almost surely. Consequently every finite $\tau_h$ is finite almost
surely, and nonexplosion makes $\tau_h\to\infty$ almost surely.

For this discrete countable observation space, jump times, numbers of
jumps, and specified first finite sequences of observations are measurable
on these laws' locally finite-jump paths. For example, the number of jumps
up to a fixed time is the supremum of the numbers of changes along finite
rational partitions, with the right endpoint included. Right continuity
and finitely many jumps make this supremum the actual number. Successive
jump times and their observed values are obtained from the same rational
approximations. Equality of two paths is determined by rational-time
evaluations, with the finite right endpoint included.

**Definition 1.3 (the signature and the endpoint response family).** For
$0\le j\le n$, set $a_j(p)=\operatorname{par}^j(p)$ and
$c_j(p)=q(a_j(p))$. No ancestor beyond the root is introduced. Put

$$
S_h(p)=\bigl(n,c_0(p),c_1(p),\ldots,c_{\min(h,n)}(p)\bigr).
\tag{1.5}
$$

For each $0\le j\le h$ and every bounded function $f:E\to\mathbb R$, let

$$
B_{j,f}(p)=\mathbf E_p[f(O(Y_j))].
\tag{1.6}
$$

The complete bounded-endpoint response family through $h$ is the entire
collection $(B_{j,f}(p))_{0\le j\le h,\ f\ \mathrm{bounded}}$. It includes
$j=0$ and all cell indicators. It is a family of separate endpoint
expectations of the true-jump chain, not the law of a single endpoint,
not a continuous-time terminal law and not a supplied random trace.
No ability to execute the family by repeated resets is part of (1.6).

## 2. Exact finite-jump classification

**Theorem 2.1 (signature classification of the stopped observed law).**
For every $h\ge0$ and all $p,p'\in\mathcal P$, the following are equivalent:

$$
\begin{aligned}
&S_h(p)=S_h(p'),\\
&\mathsf F_{h,p}^\infty=\mathsf F_{h,p'}^\infty,\\
&\mathsf F_{h,p}^T=\mathsf F_{h,p'}^T
       \quad\text{for a specified fixed }T>0.
\end{aligned}
\tag{2.1}
$$

In particular the equivalence holds separately for every fixed $T>0$.
At $T=0$, equality of the restricted laws means exactly $O(p)=O(p')$,
regardless of $h$.

**Proof.** First record the concrete one-step correspondence. Suppose
$h\ge1$, $S_h(p)=S_h(p')$ and their common depth $n$ is positive.
The difference $c_0-c_1$ determines $\delta(p)=\delta(p')$: the three
integer possibilities $-1,0,+1$ have distinct residues in every
$C_m$ under consideration, including $m=3$. Match the parent move
with the parent move and each literal child move with the same child
move. Under this matching,

$$
\begin{aligned}
S_{h-1}(\operatorname{par}p)&=
 S_{h-1}(\operatorname{par}p'),\\
S_{h-1}(pL)&=S_{h-1}(p'L),\\
S_{h-1}(pR)&=S_{h-1}(p'R).
\end{aligned}
\tag{2.2}
$$

For the parent, the list is the common list $c_1,c_2,\ldots$, truncated
at the lesser of the remaining budget and the remaining depth.
For a child, its first colour is determined by $(c_0,\delta(p))$ and
its literal letter through (120.12); the subsequent colours are the
needed prefix of $c_0,c_1,\ldots$. When $h=1$, only that first child
colour and its depth are required. This proves all three equalities
without requesting a nonexistent ancestor.

Both nonroot states have the same escape rate three and assign
probability $1/3$ to each matched move. If the common depth is zero,
both states are the single root. Match its two child moves, each of
probability $1/2$ in $J$, and use the common parameter-two waiting
time; (2.2) for its children is immediate. Thus equal signatures at
budget $h$ allow a coupling of the next true jump with equal waiting
times and equal budget-$(h-1)$ signatures afterwards.

Iterate this construction for $h$ actual jumps. Before each jump the
two depths agree, so the exponential parameters agree even if a route
visits the root and later leaves it. The observations agree initially
and after every coupled jump. Freeze both displays at their $h$th
jumps. Their entire paths, including all waiting times, are identical
under this coupling. This proves that the first line of (2.1) implies
the other two. At $h=0$, the signature is just the initial observation
and the assertion follows directly from (1.4). The root's virtual
Poisson holds are not involved in this true-jump construction.

For the converse, different initial $O$ values are separated at time
zero. Suppose the initial observations agree, with common depth $n$,
but the signatures differ. There is a first unequal colour at some

$$
1\le k\le\min(h,n-1).
\tag{2.3}
$$

Indeed $c_0$ agrees and, if included, $c_n$ is the root colour zero
for both starts. Consider the event that the frozen display has at
least $k$ jumps before $T$, that its first $k$ depths decrease by one,
and that its successive colours are
$c_1(p),\ldots,c_k(p)$. This event prescribes the unique all-parent
route of $k$ seams. All visited depths through its $k$th jump are
positive by (2.3). From $p$, its probability is

$$
\int_0^T e^{-3s}\frac{s^{k-1}}{(k-1)!}\,ds
 =3^{-k}\mathbf P\{\operatorname{Pois}(3T)\ge k\}>0.
\tag{2.4}
$$

To see the density, each specified seam has rate one; the survival
factor up to the last prescribed time $s$ is $e^{-3s}$; the preceding
$k-1$ ordered times have simplex volume $s^{k-1}/(k-1)!$.
After jump $k$ the event imposes no conditions. Thus this same formula
applies whether $k<h$ or $k=h$, when the display freezes immediately.
From $p'$ the event has probability zero, because the forced parent
route has a different $k$th colour. Hence equality on any fixed
positive window forces signature equality. Equality of the complete
frozen laws also forces equality on that window.

At time zero the display is the deterministic value $O(p)$, proving
the final assertion. The convention $\min(h,n)$ includes $n=0$ and
short addresses. For $h\ge n$, V Theorem 121.3's complete-ancestor
decoding also says that each signature cell on level $n$ is a
singleton; no new complete-address decoding theorem is needed here.
$\square$

**Theorem 2.2 (classification by all bounded true-jump endpoints).**
For the same fixed source and each $h\ge0$,

$$
S_h(p)=S_h(p')
\quad\Longleftrightarrow\quad
B_{j,f}(p)=B_{j,f}(p')
\ \text{for every }0\le j\le h
\ \text{and every bounded }f:E\to\mathbb R.
\tag{2.5}
$$

Consequently this complete family and the complete frozen path
experiment have the same deterministic-start equality classes.
This assertion concerns the inclusive family of endpoints, rather
than equality of only its last member.

**Proof.** The true-jump coupling (2.2) gives equal observations at each
$j\le h$, hence equal expectations of every bounded test. Conversely,
$j=0$ supplies the initial $O$. If signatures still differ, choose
$k$ as in (2.3) and let

$$
f(c,r)=\mathbf1_{\{(c,r)=(c_k(p),n-k)\}}.
\tag{2.6}
$$

In exactly $k$ actual jumps, depth $n-k$ can be reached only by
decreasing depth at every jump. The unique all-parent route has
probability $3^{-k}$ from $p$, since every starting vertex along
that route is a nonroot. Its terminal colour is $c_k(p)$. From $p'$
the route terminates at its different $k$th ancestor colour; no
other $k$-jump route can reach that depth. Thus the two expectations
of (2.6) are $3^{-k}$ and zero. This contradicts equality of the
complete response family. Root and zero-budget cases follow from
the included initial endpoint. $\square$

**Convention 2.3 (relation to existing completion results).** Equations
(2.1) and (2.5) identify a particular stochastic source's finite
experiments. They do not replace
[Main §§17 and 30](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md):
§17 uses finite-dimensional real linear controlled updates and §30
uses totalized deterministic operation words, including failure and
termination. In the same way,
[FiniteFutureCongruence](../../../D5/S3/Observer/Separation/FiniteFutureCongruence.lean)
and
[FiniteHorizonKernelRecurrence](../../../D5/S3/ObserverMemory/RefinementClosure/FiniteHorizonKernelRecurrence.lean)
use one deterministic map $\tau$ and its iterates; their finite
stabilization clauses require a finite state type.
[PredictiveCompletionMaximalInvariantQuotient](../../../D5/S3/ObserverMemory/RefinementClosure/PredictiveCompletionMaximalInvariantQuotient.lean)
constructs the complete-itinerary quotient for that deterministic map.
Here the source is countably infinite and the transition is a
stochastic row, so neither finite-state stabilization nor a
deterministic update is imported. The additional correspondence
proved in (2.2)--(2.6) is precisely the one needed for this source.

## 3. Finite auxiliary labels with the current observation supplied

**Definition 3.1 (static exact auxiliary code).** Supply the complete
current $O(p)=(c_0,n)$ to a decoder as side information, including its
unbounded depth coordinate. An auxiliary code for budget $h$ is a
map $\alpha_h:\mathcal P\to A_h$ into a finite fixed alphabet together
with a decoder of $(O(p),\alpha_h(p))$ into the signature, or,
equivalently by Theorems 2.1--2.2, its exact frozen law or complete
endpoint response family. The alphabet can be reused at different
current observations. This is a static deterministic representation
of probability laws; a code symbol is not obtained from a random
path by this definition.

**Theorem 3.2 (an explicit uniform auxiliary alphabet and an exact lower
bound).** In Definition 3.1 one can use alphabets of cardinalities

$$
N_0=1,\qquad N_h=3\cdot2^{h-1}\quad(h\ge1).
\tag{3.1}
$$

Thus zero extra bits suffice at $h=0$, and at most $h+1$ additional
fixed binary bits suffice for every $h\ge1$, uniformly in initial
depth. Conversely every alphabet that exactly decodes either of
these experiments for all starts at level $h$, with $O$ supplied,
satisfies

$$
|A|\ge\max_{c\in C_m}|\{p:d(p)=h,\ q(p)=c\}|
 \ge\left\lceil\frac{2^h}{m}\right\rceil.
\tag{3.2}
$$

The alphabet in (3.1) is a sufficient construction; its optimality is
not asserted. The lower bound (3.2) is for exact decoding and is not
a positive-error coding lower bound.

**Proof.** At $h=0$, $S_0$ is already supplied by $O$.
Let $h\ge1$ and $\ell=\min(h,n)$. If $\ell=0$, use any one fixed
symbol. Otherwise encode the $\ell$ incoming increments

$$
d_j=\delta(a_j(p))\quad(0\le j<\ell).
\tag{3.3}
$$

Each such ancestor is a nonroot. The first increment has three
possible values. Inspection of the fixed ordered table (120.12)
gives the following possible parent increments for a specified
child increment:

$$
\begin{array}{c|c}
\text{child increment}&\text{possible parent increments}\\ \hline
0&-1,\ +1\\
+1&0,\ +1\\
-1&-1,\ 0
\end{array}
\tag{3.4}
$$

Each subsequent $d_j$ in (3.3) therefore has at most two possible
values once $d_{j-1}$ is known. Order the two values in each row
of (3.4) numerically, and encode the choice by one bit. Pad the
remaining $h-\ell$ bit positions with zeros. The fixed alphabet
$\{-1,0,+1\}\times\{0,1\}^{h-1}$ has exactly the cardinality in
(3.1), independent of $n$. On an actual code, the supplied depth
tells the decoder how many positions to use, and

$$
c_{j+1}=c_j-d_j\pmod m\qquad(0\le j<\ell)
\tag{3.5}
$$

recovers the signature. Infeasible codes need no source
interpretation. At short addresses the root increment is never
requested in (3.3); any necessary root boundary restriction simply
removes possible codes. Since
$3\cdot2^{h-1}\le2^{h+1}$, the symbols fit in $h+1$ fixed bits.

For the lower bound, at level $h$ the signature contains the whole
ancestor-colour list. V Theorem 121.3 implies that its $2^h$
addresses have different signatures. Theorems 2.1 and 2.2 make their
target laws different as well. Inside any one current-colour fibre,
equal auxiliary symbols would give equal decoder inputs, so they
must represent the same target. They therefore cannot encode two
different addresses in that fibre. There are $m$ colour fibres and
$2^h$ addresses, giving (3.2) by pigeonhole, including $h=0$.

This counting uses the existing finite-label principle of
[Main Definition 35.1](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY.md),
[MinimalAppealLabelCount.minimal_appeal_label_count](../../../D5/S3/ConceptDynamics/Appeal/MinimalAppealLabelCount.lean)
and
[BinaryRepairCost.binary_repair_cost_is_log_of_minimal_labels](../../../D5/S3/ConceptDynamics/Coding/BinaryRepairCost.lean).
For their finite source take the single level $h$, for the record
take its colour, and for the target take its signature. The source
and record types are then finite; the target type need not be.
[MinimumRollbackAlphabet.minimum_rollback_alphabet](../../../D5/S0/History/Coding/MinimumRollbackAlphabet.lean)
gives the same fibre-injectivity bound with process map
$p\mapsto q(p)$ on this finite level, but grants no rollback
operation here. These suppliers do not themselves assert a
fixed alphabet over all depths. That assertion is supplied by
the concrete backwards choices (3.3)--(3.5). None of these
cardinalities counts acquisition, computation, precision, sample
size, a finite online workspace, or storage protection. $\square$

## 4. Finite-window total variation bounds

**Theorem 4.1 (freezing error and a direct same-signature comparison).**
For every finite $T\ge0$, every $h\ge0$ and every deterministic start,
put

$$
b_h(T)=\mathbf P\{\operatorname{Pois}(3T)>h\}
      =e^{-3T}\sum_{k=h+1}^\infty\frac{(3T)^k}{k!}.
\tag{4.1}
$$

Then

$$
\|\mathsf L_p^T-\mathsf F_{h,p}^T\|_{\mathrm{TV}}\le b_h(T).
\tag{4.2}
$$

For any two starts with $S_h(p)=S_h(p')$ there is also the direct bound

$$
\|\mathsf L_p^T-\mathsf L_{p'}^T\|_{\mathrm{TV}}\le b_h(T).
\tag{4.3}
$$

In particular (4.3) has no factor two.

**Proof.** Couple $X$ with its own frozen display (1.4). If there
have been at most $h$ actual jumps by $T$, the two observed paths
agree throughout $[0,T]$. Under the rate-three construction their
actual jump count is no larger than the Poisson event count, so
the probability of disagreement is at most (4.1). For any event
$A$ in path space, a coupling $(U,V)$ gives

$$
|\mathbf P\{U\in A\}-\mathbf P\{V\in A\}|
 \le\mathbf P\{U\ne V\}.
\tag{4.4}
$$

Taking the supremum proves (4.2). The strict tail is essential:
the display includes the $h$th actual jump; possible disagreement
requires an $(h+1)$st actual jump. Root virtual holds count only
towards the dominating Poisson count.

For (4.3), use one rate-three clock for both full source processes.
At a nonroot whose signatures agree with positive remaining
budget, choose the same parent/left/right option in the two rows.
Equation (2.2) makes the next signatures agree with one less
budget. If both are at the root, choose the same child or virtual
hold in the two rows. A child move has the same property, and on
a hold the states remain the root, so their signatures agree at
every budget. Reduce the comparison budget by one for each
Poisson event, including a virtual hold; this can only discard
information.

Starting at budget $h$, induction gives identical observations
at and between the first $h$ Poisson events. At zero remaining
budget the observations still agree; any subsequent evolution
can be coupled using the correct source rows. Thus if the common
clock has at most $h$ events by $T$, the complete observations
agree up to $T$. Apply (4.4). This proves the single-tail bound
directly, without adding two errors from (4.2). At $h=0$ only
the no-Poisson-event event is used; at $T=0$ both bounds vanish.
The construction always retains the actual root row. $\square$

The Poisson construction in this proof is the specialization already
supplied by V Proposition 120.4. In
[Rao--Teh, Fast MCMC Sampling for Markov Jump Processes and Extensions,
JMLR 14 (2013), §3.1, Proposition 1](https://jmlr.org/papers/volume14/rao13a/rao13a.pdf),
their dominating rate $\Omega$ is three and their
$B=I+A/\Omega$ corresponds to $R_\infty$ after transposing their
column convention to the present backward row convention. Their
finite-state presentation is not used to infer an unproved
countable-source extension: the bounded-rate construction above
and in V 120.4 gives that extension explicitly. Their virtual jumps
correspond here only to the root's hold in the source row, not to
an actual same-colour seam. The source-specific increment table
and (2.2) supply the comparison, rather than a new uniformization
result.

## 5. Whole-future approximation by full-law representatives

**Theorem 5.1 (whole-future diameter of every signature cell).**
For all $h\ge0$ and all deterministic starts with $S_h(p)=S_h(p')$,

$$
\|\mathsf L_p^\infty-\mathsf L_{p'}^\infty\|_{\mathrm{TV}}
 \le2^{-h}.
\tag{5.1}
$$

For finite windows this gives, together with Theorem 4.1,

$$
\|\mathsf L_p^T-\mathsf L_{p'}^T\|_{\mathrm{TV}}
 \le\min\{b_h(T),2^{-h}\}.
\tag{5.2}
$$

**Proof.** For $h=0$ this is the general bound one in the convention
(1.2). Let $h\ge1$ and let $n$ be the common depth. If $n\le h$,
the signatures contain the complete ancestor lists. V Theorem
121.3 gives $p=p'$, so both distances are zero. Hence suppose
$n>h$.

Set $u=a_{h-1}(p)$ and $v=a_{h-1}(p')$. They are nonroots and have
the same depth, colour and incoming increment:

$$
d(u)=d(v)=n-h+1,\qquad q(u)=q(v)=c_{h-1},\qquad
\delta(u)=\delta(v)=c_{h-1}-c_h.
\tag{5.3}
$$

In the last equality the residue determines its unique allowed
integer increment. Moreover there is one common literal suffix
$w$ of length $h-1$ with $p=uw$ and $p'=vw$. Indeed for the edge
from $a_{j+1}$ to $a_j$, $0\le j<h-1$, the signatures give both
incoming increments
$c_{j+1}-c_{j+2}$ and $c_j-c_{j+1}$. In each row of (120.12) the
two children have different increments. The two known increments
therefore determine the same literal child letter for both
addresses, proving the suffix assertion edge by edge.

Identify the two entire descendant cones by $uz\leftrightarrow vz$
for every finite suffix $z$. Equation (5.3) and the unchanged child
recursion show by induction on $|z|$ that this identification
preserves $q,\delta,d$ and every internal parent--child seam.
If $u=v$, then the common suffix already gives $p=p'$.
Otherwise these distinct roots have the same depth and their
cones are disjoint.

Use one rate-three Poisson clock and identical parent/left/right
choices until the coupled pair first exits its matched cones.
Every state before exit is a nonroot; every such Poisson event
is an actual jump. The source states remain matched and their
observations agree until exit. Extend each marginal after exit
by its correct source law using fresh randomness. Let $\sigma$
be the exit time. On $\{\sigma=\infty\}$ the complete observed
paths agree, so (4.4) on the whole-future path space yields

$$
\|\mathsf L_p^\infty-\mathsf L_{p'}^\infty\|_{\mathrm{TV}}
 \le\mathbf P\{\sigma<\infty\}.
\tag{5.4}
$$

Before exit, height above the respective cone parent starts at
$h$: the initial suffix has length $h-1$. At every jump it
decreases by one with probability $1/3$ and increases by one
with probability $2/3$. Exit is hitting height zero. For a
barrier $M>h$, the probability of hitting zero before $M$ is

$$
H_j^{(M)}=\frac{2^{-j}-2^{-M}}{1-2^{-M}}\quad(0\le j\le M).
\tag{5.5}
$$

This is the standard biased gambler's-ruin formula, here with
outward probability $2/3$. To check its use, its boundary values
are one and zero and
$3H_j^{(M)}=H_{j-1}^{(M)}+2H_{j+1}^{(M)}$ in the interior.
The stopped finite walk reaches a barrier almost surely:
from every interior site, $M$ consecutive downward choices
would hit zero, with probability at least $3^{-M}$, so the
chance of avoiding both barriers for $kM$ steps is at most
$(1-3^{-M})^k$. The recurrence with those boundary values is
unique, since a nonzero difference cannot attain its positive
maximum or negative minimum only in the interior. Thus it
indeed equals the hitting probability.

As $M\to\infty$, hitting zero before $M$ increases to ever
hitting zero. Each finite hitting route has finite maximum.
The construction is nonexplosive, so finite jump-index hitting
is the same as finite-time hitting. Substitution of $j=h$ in
(5.5) gives

$$
\mathbf P\{\sigma<\infty\}=\lim_{M\to\infty}H_h^{(M)}
 =2^{-h}.
\tag{5.6}
$$

Equations (5.4)--(5.6) prove (5.1). Restriction of paths to
$[0,T]$ cannot increase TV, proving the $2^{-h}$ part of
(5.2); (4.3) supplies the other part. In fact the observations
at exit also agree, since both cone parents have colour $c_h$.
The proof only needs agreement before exit and does not infer
agreement of the subsequent rows there. $\square$

The hitting calculation is a source-specific application of
[Lyons--Peres, Probability on Trees and Networks, Chapter 2,
Example 2.4](https://rdlyons.pages.iu.edu/prbtree/book.pdf):
their fortune is the height just used, their winning probability
is $2/3$, and their ruin event is cone exit. The elementary coupling
comparison (4.4) is the same inequality as
[Levin--Peres with Wilmer, Markov Chains and Mixing Times, second
edition, §4.2, Proposition 4.7](https://pages.uoregon.edu/dlevin/MARKOV/mcmt2e.pdf).
For the path-space version used here, (4.4) proves the needed
inequality directly; equality of paths is measurable by Definition
1.2. V Theorem 121.6 supplies particular close-anchor examples.
The new assertion (5.1) concerns every pair in every $S_h$ cell;
it neither replaces nor rederives those anchor examples.

**Definition 5.2 (static full-law representative decoder).** For every
realized signature $s$, choose $r_h(s)$ to be the first address
in lexicographic order $L<R$ among its realizations. This exists
because the signature specifies a finite depth and hence has a
nonempty finite realizing level. Define

$$
D_h^\infty(s)=\mathsf L_{r_h(s)}^\infty,\qquad
D_h^T(s)=\mathsf L_{r_h(s)}^T.
\tag{5.7}
$$

The side information and auxiliary alphabet of Theorem 3.2 first
decode $s=S_h(p)$ and then apply (5.7). Unrealized inputs may be
assigned any fixed probability law. This decoder returns a full
infinite-source law, rather than a frozen law; its finite-window
answers are restrictions of the same chosen full law. Its
definition places no finite resource bound on representative
selection, law storage, computation or law evaluation.

**Corollary 5.3 (uniform positive-TV static representation).** The
decoder (5.7) satisfies, simultaneously for every start and every
finite $T\ge0$,

$$
\begin{aligned}
\|\mathsf L_p^T-D_h^T(S_h(p))\|_{\mathrm{TV}}
 &\le\min\{b_h(T),2^{-h}\},\\
\|\mathsf L_p^\infty-D_h^\infty(S_h(p))\|_{\mathrm{TV}}
 &\le2^{-h}.
\end{aligned}
\tag{5.8}
$$

For $0<\epsilon<1$, choosing
$h=\lceil\log_2(1/\epsilon)\rceil$ gives whole-future error at
most $\epsilon$ using the finite auxiliary alphabet (3.1)
and the supplied current $O$. It does not make the total
decoder input finite, since its depth coordinate is unbounded.

**Proof.** The representative and the true start lie in the same
signature cell. Apply Theorem 5.1 and the direct bound (4.3).
The chosen integer $h$ has $2^{-h}\le\epsilon$. Theorem 3.2
encodes its signature. No inference about the exact lower
bound (3.2) at positive tolerance is used. $\square$

**Proposition 5.4 (a frozen infinite future has maximal error).**
For every finite $h$ and every start,

$$
\|\mathsf L_p^\infty-\mathsf F_{h,p}^\infty\|_{\mathrm{TV}}=1.
\tag{5.9}
$$

Thus (5.8)'s whole-future approximation uses the representative's
full law and cannot be obtained by freezing for all subsequent
time.

**Proof.** Let $A_h$ be the measurable event that a whole-future
observed path has at most $h$ jumps. The frozen law assigns it
probability one. Under the full law, each finite next waiting
time is almost surely finite, and nonexplosion places the
infinitely many actual jumps at times tending to infinity,
as in Definition 1.2. Every actual jump changes observed
depth. Hence the full observed path has infinitely many
jumps almost surely and assigns $A_h$ probability zero.
Use (1.2). This includes $h=0$. $\square$

## 6. Exact transition closure, total alphabets and acquisition

**Proposition 6.1 (declining budget and failure of fixed-budget
transition closure).** For each $h\ge1$, the pushed-forward
one-step true-jump row

$$
(S_{h-1})_*J(p,\cdot)
\tag{6.1}
$$

depends only on $S_h(p)$. The waiting-time parameter likewise
depends only on the depth within this signature. Nevertheless,
for every finite $h\ge0$, the map $S_h$ is not transition-stable:
there are $p,p'$ with equal $S_h$ but unequal pushed-forward
rows $(S_h)_*R_\infty(p,\cdot)$ and
$(S_h)_*R_\infty(p',\cdot)$. The same failure holds for the
true-jump rows and for aggregate continuous-time transition
rates.

**Proof.** Equation (2.2), with its degree-two root case, matches
all destinations in (6.1) with their correct probabilities.
Depth determines the escape rate. Iterating gives an exact
remaining-budget description $S_{h-j}(Y_j)$ through $j=h$,
with the exact waiting times. This description spends one
unit of its initial budget per actual jump.

For $h=0$, use V Proposition 121.2's addresses $LLR,RRL$.
Their $S_0=O$ values agree, but only the first has a parent
with observation $(1,2)$; the corresponding row probabilities
are $1/3$ and zero, and the corresponding seam rates are one
and zero.

For $h\ge1$, take exactly the supplied V Theorem 121.6 pair
$p_{h-1},p'_{h-1}$. Its first unequal ancestor colour is at
$h+1$, and its common depth is $2m+h-1>h$. Therefore its
$S_h$ values agree while

$$
S_h(\operatorname{par}p_{h-1})
 \ne S_h(\operatorname{par}p'_{h-1}).
\tag{6.2}
$$

Let $s$ be the first signature in (6.2). Its depth is one
less than the initial common depth. The first start moves
to that signature only by its unique parent seam. The
second start cannot reach it in one move: its only
lower-depth neighbour has the other signature, and both
children have larger depth. Thus the two rows give mass
$1/3$ and zero to $\{s\}$ under either $J$ or $R_\infty$.
Both starts are nonroots. Their aggregate generator rates
to this different-depth cell are one and zero. This
establishes every asserted failure without a new anchor
construction.

This is the source-specific row test of
[StrongLumpabilityDescent.strong_lumpability_descent_tfae](../../../D5/S3/Observer/ProbabilisticClosure/StrongLumpabilityDescent.lean),
which allows arbitrary types and probability mass functions:
take the readout to be $S_h$ and the source row to be
$R_\infty$. Its fibre-constant pushed-forward-law condition
fails at the exhibited pair. The algebraic factorization
[StochasticDescentLumpability.strongly_lumpable_iff_exact_quotient_kernel](../../../D5/S3/Estimation/DecisionRisk/StochasticDescentLumpability.lean)
also has no finite-type hypothesis; its finite supremum
and uniform-defect theorems do have such hypotheses and
are not applied to $\mathcal P$. The familiar finite-state
matrix criterion is
[Wolfer--Watanabe, Geometric Aspects of Data-Processing of Markov
Chains, arXiv:2203.04575v3, §3.4, Theorem 3.1](https://arxiv.org/pdf/2203.04575v3).
Its $\kappa$ is here $S_h$, and its aggregated row
$P(y,S_{x'})$ is the pushforward just tested. No stationary
measure or finite-state conclusion from that paper is
needed for this explicit countable-source counterexample.

A budget that decreases is therefore compatible with exact
finite prediction, but does not keep a fresh horizon $h$
after each jump. Freezing at exhausted budget, returning a
static approximate full law, and maintaining an indefinitely
updateable exact quotient are different constructions.
The injectivity statement for the last of these, when it
recovers $O$, is already V Theorem 121.3. $\square$

**Proposition 6.2 (no finite total alphabet at error below one).**
Fix any finite $T\ge0$ or the whole-future experiment. Suppose
a deterministic code $\alpha:\mathcal P\to A$ and probability-law
decoder $\Psi$ receive only $\alpha(p)$, with no supplied
current observation or other source-dependent input. If

$$
\|\Psi(\alpha(p))-\mathsf L_p^T\|_{\mathrm{TV}}\le\epsilon
\quad\text{for every }p,\qquad 0\le\epsilon<1,
\tag{6.3}
$$

then $A$ cannot be finite. The same assertion holds with
$\mathsf F_{h,p}^T$ for any fixed $h$, and with either whole-future
law in place of its finite restriction.

**Proof.** In the relevant path space let $C_n$ be the event
that the initial observed depth is $n$. The $C_n$ are
pairwise disjoint, and every law in the assertion starting
at depth $n$ assigns probability one to $C_n$.
Choose one address at each depth, for instance $L^n$.
If $A$ were finite, one code value $a$ would be used at
infinitely many different depths. The single probability
law $\nu=\Psi(a)$ would then have

$$
\nu(C_n)\ge1-\epsilon>0
\tag{6.4}
$$

at infinitely many $n$, by (6.3). For $K$ such depths,
disjointness gives $1\ge K(1-\epsilon)$, contradicted by
sufficiently large finite $K$. The proof uses initial
observations only, so it applies at $T=0$, to frozen
displays, and to whole futures. It does not assume
$\epsilon<1/2$: a two-law triangle inequality would not
give the asserted full range $\epsilon<1$.

In Corollary 5.3, the decoder has the additional input
$O(p)$ and therefore a specified unbounded depth. Its
finite auxiliary alphabet is consistent with this
proposition. Neither statement gives a finite total
alphabet for those unbounded inputs. $\square$

**Proposition 6.3 (one trace does not guarantee recovery).** Equality
classes of the law experiments in Theorems 2.1--2.2 and the
existence of static codes in Theorem 3.2 do not imply
recovery from one random trace. More precisely, there is
no measurable decoder that, given only one observed trace
and the current $O$, returns the starting address almost
surely for every deterministic start. This holds on every
fixed finite window $T>0$ and on the complete infinite
future; no auxiliary code is supplied to this decoder.

**Proof.** For a finite window, use the distinct same-$O$
nonroot starts $a=LLR,b=RRL$ of V Proposition 121.2.
Their common constant observation path on $[0,T]$ has
probability $e^{-3T}>0$ from each, because every actual
jump changes depth and each initial escape rate is three.
A decoder must give the same output on that identical
input trace; it cannot be almost surely correct for
both starts. Extra randomness cannot help: on that
common atom its conditional output distribution would
have to assign probability one to each of two different
addresses.

For an infinite future, the no-jump event has probability
zero and is not evidence for the assertion. Instead use
V Theorem 121.6 at $r=0$. Its distinct same-$O$ starts
$p_0,p'_0$ satisfy

$$
\|\mathsf L_{p_0}^\infty-
       \mathsf L_{p'_0}^\infty\|_{\mathrm{TV}}\le\tfrac12<1.
\tag{6.5}
$$

If a measurable decoder were almost surely correct at both
starts, its event of returning $p_0$ would have probability
one under the first law and zero under the second. Their
TV would be one, contradicting (6.5). For a randomized
decoder, adjoining independent randomness cannot increase
TV: for each event its conditional indicator is a
measurable function taking values in $[0,1]$, and the
layer-cake identity bounds its expectation difference
by the original sup-event TV. The same contradiction
therefore applies.

This argument gives the finite and infinite law evidence
separately. It claims neither that every starting pair
is impossible to distinguish from one trace nor a
uniform positive error floor, acquisition tariff or
sample-complexity bound. In particular, exact law
identifiability from V 121.3 and all-variable-time
terminal identifiability from V 121.4 are different
inputs from one random observed path. The specific
prescribed-time terminal question left open there is
not settled by Theorem 2.2. $\square$

## 7. Supplier correspondence and mathematical scope

**Convention 7.1 (attributed source-specific synthesis).** The
classification in Theorems 2.1--2.2, the concrete alphabet
construction (3.3)--(3.5), the direct same-signature bound
(4.3), the all-cell bound (5.1) and their stated consequences
are repo-derived deductions for the single source in
Definition 1.1. Uniformization, coupling, gambler's ruin,
fibrewise exact-label counting and the row criterion for
lumpability are the attributed intermediate suppliers,
rather than new generic theorems. No worldwide priority
claim is made.

V §§120--121 retain their own statements: the colouring
and rate-three construction, exact singleton classes,
transition-stable quotient injectivity, variable-time
terminal distinction, exact full-law state counts and
the special close anchors are used by reference.
Definitions 55.1--55.2 and Theorem 55.3 retain source,
field and clock custody. Nothing in the present finite
experiments changes those predecessor assumptions.

The following additional correspondences fix the scope
of related suppliers:

- [MarkedPredictiveQuotient.actual_endpoint_mass](../../../D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/MarkedPredictiveQuotient.lean)
  takes a finite hidden producer, stationary binary
  edge-emission matrices with zero original $11$-word mass,
  row-unifilarity and the original integer-time cylinder law.
  Its joint marked-word/final-class
  endpoint mass is not (1.6), whose source is an
  infinite deterministic-start true-jump chain. No
  stationary synchronization or finite predictive-class
  count is transferred.
- [Shalizi--Crutchfield, Computational Mechanics: Pattern
  and Prediction, Structure and Simplicity,
  cond-mat/9907176v2, Theorems 2--3](https://arxiv.org/pdf/cond-mat/9907176v2)
  concerns causal-state entropy minimality and almost-sure
  uniqueness for stationary discrete-time histories.
  Equality of future laws motivates a related equivalence,
  but the present pointwise deterministic-start
  classification is (2.1)--(2.6), not an application
  of their almost-sure stationary conclusion.
- [FinitePredictionTruncation.finite_prediction_truncation_formula_and_error](../../../D5/S3/Observer/MetricGeometry/FinitePredictionTruncation.lean)
  uses a deterministic update, a bounded readout
  discrepancy and a discount $0<\gamma\le1$ to bound a
  discounted supremum along iterates. Neither a
  discounted discrepancy nor a deterministic update
  occurs in (5.1); the number $2^{-h}$ here is an
  actual outward-biased cone-exit probability, not a
  substituted discount factor.
- [III §91](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md)
  fixes an inclusive native four-reply prefix table,
  a finite closed tree Laplacian and a screened
  root resolvent. Its geometric remainder is for
  that scalar same-operator response and its
  acquired prefix contract. Here $S_h$ is an
  ancestor-colour list on an infinite chain and
  (4.2), (5.8) concern complete observed laws.
  No native prefix acquisition conclusion follows
  from their superficially similar truncation form.

**Definition 7.2 (operational and spatial boundaries).** The
original ordered source, immutable INITIAL, actual
versions, four-valued Reads, acquired records, common
guard, accepted and refused Apply calls and absorbing
native Stop remain exactly the contract recalled in
V Definitions 120.1 and 121.1. The functions, probability
laws and static decoders in this companion are added
mathematical objects on that same carrier, without
native path acquisition, field preparation, reset,
clone, heat actuator, seam operation or equality
maintenance. In particular (1.4) is a stopped
mathematical display, not an authorized native action.

Unit heat time, accepted source epoch, acquisition
chronology and physical time are distinct. A supplied
unbounded depth and an unrestricted full-law decoder
do not assert finite online workspace, finite
coordinate precision or a sampling or resource
tariff. Counting measure on vertices is not the
separate ray probability of V Definition 120.8.
The bounded-observable laws do not remove V
Proposition 120.7's counting-$\ell^2$ pullback and
field/potential non-descent boundaries. No new
metric placement, physical three-dimensional
realization or high-dimensional impossibility
conclusion is attached to the cycle choice, the
three increment values or any finite auxiliary
alphabet.

## 追加锚（本行以下为增补区）
