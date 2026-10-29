# Recursive relational observation: stopped mean cost and spatial risk on one source

This companion fixes one PG27 source and relates two quantities measured on the
same realization: fresh-edge queries actually paid before a marker or a
voluntary stop, and prior-average root error on the connected interval that was
actually exposed. The hidden parameter is integrated before decoding. The
observer keeps the original independent seed and never receives a parameter
port, a reset, a copied arm, or a survival-conditioned seed law.

## 1. Source, replay horizons, and the two objectives

**Definition 1.1 (fixed shared source).** Let $a,b>0$ with $a+b=1$, let
$Q\sim\mu$ on $(0,1)$, and let $X_0\sim\operatorname{Bernoulli}(b)$ be
independent of $Q$. Conditional on $(Q,X_0)$, the left and right arms are
independent copies of the Markov chain
$$
P_Q=\begin{pmatrix}1-Q&Q\\1&0\end{pmatrix}.
$$
A fresh boundary query costs one unit and returns $1$ exactly on a newly
exposed $00$ edge. The first such marker stops source access. An observer has
an independent seed $U\sim\nu$ and may choose sides causally from $U$ and the
ordered action/reply journal. Every fixed finite-history seed section of the
action, stop, and decoder rules is measurable. The seed is visible to decoding.
The controller must decide almost surely, with a forced root label; coherent
interval labels are obtained by propagating that root guess through the journal.
Their event $0$-$1$ loss equals root loss: correct root plus the acquired
relations gives every exposed label, and a correct whole labeling includes the
root. An incoherent labeling cannot improve the minimum, since it matches
neither of the two possible coherent labelings. On a marker the root and every label in the
exposed connected interval are recovered by propagation. On a marker-free
journal the observer may stop voluntarily.

Put
$$
M_j=\int q^j\,\mu(dq),\qquad A_j=M_j-M_{j+1},\qquad
v_j=bA_{j-1}-aA_j\quad(j\ge1),
$$
and $J_N=\sum_{j=0}^{N-1}M_j$ for $N\ge1$. Thus $A_j>0$ and
$M_j\downarrow0$. A zero-reply replay has arm lengths $(\ell,r)$, with
$$
k=\lfloor\ell/2\rfloor+\lfloor r/2\rfloor,\qquad
s=(\ell\bmod2)+(r\bmod2).
$$
Its two integrated root masses are $aM_{k+s}$ and $bM_k$, so write
$$
e(\ell,r)=\min\{aM_{k+s},bM_k\}.
$$
Write $C=\mathbb E T$ for the extended mean actual paid count and $E$ for
the prior-average error of the chosen decoder. Prior-integrated MAP minimizes
this error separately on every finite terminal journal, including ties.

For a fixed horizon $n$, a policy is required to continue on the zero-reply
replay until exactly $n$ queries and then stop if no marker has appeared. Its
actual paid count is the marker time truncated at $n$, not the declared
horizon.

## 2. A common linear description of zero-replay shapes

**Lemma 2.1 (shape sequence and actual prefix cost).** At every odd depth
$2m+1$, the zero-reply replay has one even and one odd arm. At every even
depth $2m$, it has either two even arms or two odd arms. Let
$\lambda_m\in[0,1]$ be the original-seed probability of the latter shape at
depth $2m$; for a deterministic seed it is $0$ or $1$. Every prescribed
finite sequence of even-depth shapes is realized by a lawful side schedule, and
the schedule can be chosen independently of $(Q,X_0)$.

Let $\tau$ be the marker time of any continued version of the replay route.
For depths before the voluntary horizon, its integrated survival tails are
$$
\Pr(\tau>2m+1)=bM_m+aM_{m+1},
$$
and, for $m\ge1$,
$$
\Pr(\tau>2m)=M_m+\lambda_m v_m.
$$
Consequently $C_0=0$, $C_1=1$, and, for $N\ge1$,
$$
\begin{aligned}
C_{2N}(\lambda)
 &=2J_N-a+aM_N+\sum_{m=1}^{N-1}\lambda_m v_m,\\
C_{2N+1}(\lambda)
 &=2J_N-a+(1+a)M_N+\sum_{m=1}^{N}\lambda_m v_m.
\end{aligned}
$$

**Proof.** A zero reply flips the selected arm’s parity. The conditional
survival mass at an odd depth is $q^m(b+aq)$; at an even depth it is $q^m$
for the even/even shape and $q^{m-1}(b+aq^2)$ for the odd/odd shape. Their
difference is $(1-q)(b-aq)q^{m-1}$, whose $\mu$-integral is $v_m$. The
original seed is independent of the source, so averaging the replay partition
gives the displayed tails. Summing $\Pr(\tau>t)$ for $0\le t<n$ by Tonelli
gives the two formulas. To realize a requested next even shape from an even
depth, first query the
left arm. On a zero reply the parities are mixed. Then query the arm whose
current parity is $1$ when the target is even/even, and the arm whose parity
is $0$ when the target is odd/odd. A marker interrupts either step.
This is the lawful shape construction in PG27.17, with no extra clock or
random source. $\square$

**Lemma 2.2 (terminal risk at a fixed cap).** For $N\ge1$, the even-cap
zero-replay risks of the two terminal shapes are
$$
E_N^{\mathrm{ee}}=\min(a,b)M_N,\qquad
E_N^{\mathrm{oo}}=\min(aM_{N+1},bM_{N-1}).
$$
At an odd cap $2N+1$ with $N\ge0$, both possible zero-replay shapes have risk
$\min(aM_{N+1},bM_N)$. Therefore the cap frontier supplied by finite-query spatial recovery is
$$
R_0^*=\min(a,b),\qquad R_1^*=\min(aM_1,b),\qquad
R_{2N}^*=\min(aM_{N+1},bM_N),\qquad
R_{2N+1}^*=\min(aM_{N+1},bM_N).
$$

**Proof.** A marker identifies a $00$ edge and hence the root and the whole
connected exposed interval. On the only non-marker leaf, the two root masses
are $aM_{k+s}$ and $bM_k$, so its Bayes error is their minimum. The displayed values and the fact that the even-cap minimum of the two lawful
shapes equals the cap frontier are exactly the finite-query spatial
recovery result. $\square$

## 3. Joint attainment at every finite replay horizon

**Definition 3.1 (joint finite-horizon cost).** Let $\mathcal D_N$ be the
subset of $\{0,1\}$ consisting of the even/even indicator $d=0$ and the
odd/odd indicator $d=1$ that attain $R_{2N}^*$; it contains one or both
indicators according as the two values in Lemma 2.2 are unequal or equal.
For $n\ge0$, let $K_n$ be the least expected actual paid count among lawful
fixed-horizon policies whose terminal risk is $R_n^*$.

**Theorem 3.2 (same-source joint attainment).** The quantities $K_n$ are
attained on the original source and original seed law. They are
$$
K_0=0,\qquad K_1=1,
$$
and, for $N\ge1$,
$$
\boxed{
K_{2N}=2J_N-a+aM_N+\sum_{m=1}^{N-1}\min(0,v_m),
}
$$
and
$$
\boxed{
K_{2N+1}=2J_N-a+(1+a)M_N+\sum_{m=1}^{N}\min(0,v_m).
}
$$
At an even horizon, choose any terminal shape $d\in\mathcal D_N$; at all
earlier even depths choose odd/odd exactly when $v_m<0$ (ties are arbitrary).
At an odd horizon use the same sign choice through $m=N$.

In fact every fixed-horizon policy, regardless of its terminal error, has
mean cost at least $K_n$. Thus $K_n$ is also the unrestricted least paid-prefix
mean at that horizon.

**Proof.** By Lemma 2.1, the cost is affine in the shape indicators. Each
coefficient before the terminal even depth is $v_m$, so its least value is
obtained by choosing $\lambda_m=1$ when $v_m<0$ and $0$ when $v_m>0$.
For $n=0,1$ the statements follow directly. At an odd cap the terminal shape
does not change risk, so the same choice is
made at $m=N$. At an even cap the terminal shape is restricted only by
$d\in\mathcal D_N$ and does not occur in $C_{2N}$; it can therefore be
chosen independently of the preceding cost-minimizing shapes. Lemma 2.1
realizes all these choices with a single causal side schedule on the same
source and the same original seed. The linear lower bound holds for every
seed-randomized schedule because $0\le\lambda_m\le1$ and
$\lambda_mv_m\ge\min(0,v_m)$. $\square$

The theorem is a joint statement: the cap-risk attainer and the least actual
paid-prefix mean are realized by one lawful route. Separate minimization of
the two coordinates would not establish this. The horizon is a replay index;
the cost is the expectation of the queries actually paid before a marker or
the cap.

## 4. Infinite endpoint and arbitrary original-seed selectors

Assume for this section
$$
I_\mu=\int\frac{\mu(dq)}{1-q}=\sum_{m\ge0}M_m\in(0,\infty].
$$
Let $N_*\in\mathbb N_{\ge1}\cup\{\infty\}$ be the first index with
$v_{N_*}<0$, with $N_*=\infty$ if there is no such index, and put
$w_j=bM_{j-1}-aM_j$ and $w_\infty=0$.

**Theorem 4.1 (infinite joint endpoint).** Query left except for the single
right query numbered $2N_*$ when $N_*<\infty$, and stop at the first marker.
This controller has zero terminal risk and
actual mean cost
$$
K_\infty=
\begin{cases}
2I_\mu-a+w_{N_*},&I_\mu<\infty,\\
+\infty,&I_\mu=\infty.
\end{cases}
$$
The zero-risk claim is almost sure under the fixed source. The finite value is
attained by this controller; when $I_\mu=\infty$, zero risk remains attained
but is outside every finite mean-cost budget.

**Proof.** PG27.15--27.18 give the exact tail identity, the sign-minimizing
shape sequence, and the telescoping correction
$\sum_m\min(0,v_m)=w_{N_*}$. The marker occurs almost surely for every
$q<1$, while Tonelli gives the stated finite-mean criterion. The present
controller uses the same $Q$, both arms, and the original seed, so no new
endpoint realization is introduced. The finite-prefix formulas also give
$$
K_n\uparrow K_\infty,\qquad R_n^*\longrightarrow0.
$$
Indeed $\sum_m|v_m|<1$ by PG27.17 and $M_N\to0$. If $I_\mu=\infty$,
the baseline partial sums diverge while their signed correction stays bounded;
no subtraction of two infinite quantities is used. Strict increase follows from
$$
\begin{aligned}
K_1-K_0&=1,\\
K_{2N+1}-K_{2N}&=\min\{M_N,bM_{N-1}+aM_{N+1}\}>0 &&(N\ge1),\\
K_{2N+2}-K_{2N+1}&=bM_N+aM_{N+1}>0 &&(N\ge0).
\end{aligned}
$$
All terms are source survival probabilities. $\square$

**Theorem 4.2 (all-policy domination on the original seed).** Let any lawful
almost-sure-decision controller and decoder have paid mean $C$ and error $E$.
Its hypothetical all-zero replay determines a measurable horizon
$H:U\to S:=\mathbb N_0\cup\{\infty\}$. There is a lawful replacement on
the same source, using exactly the same seed $U$ and the same map $H$, with
$$
\boxed{
\widetilde C=\int K_{H(u)}\,\nu(du)\le C,\qquad
\widetilde E=\int R_{H(u)}^*\,\nu(du)\le E,
}
$$
where $R_\infty^*=0$. Products $0\cdot\infty$ in the corresponding
countable sums are interpreted as zero. Every measurable horizon selector has
such an attainer; an infinite replay is allowed because the marker still
arrives almost surely.

**Proof.** Before a marker the only possible reply string is all zeros. At
every finite depth its past actions and stop decision are measurable functions
of $u$: induction uses a finite partition by action words and the measurable
seed sections. The first replay stop therefore defines the measurable sets
$\{H=h\}$, and $\{H=\infty\}$ is their complement. Extend each finite
replay route arbitrarily after its voluntary stop. The actual paid count agrees
with $\min(H,\tau)$ under that route, including a marker at query $H$.
There is no other source-dependent non-marker branch on which to choose a
horizon.

For a fixed finite fiber $\{H=h\}$, each replay action word has mean at least
$K_h$ by Theorem 3.2, and its Bayes leaf error is at least $R_h^*$ by the
published cap supplier. The actual decoder can only have larger error. These
statements are integrated on the finite measurable action-word partitions, not
by conditioning on a seed singleton of possibly zero probability. On the
infinite fiber the marker arrives almost surely for each seed route: the
conditional cylinder tails are bounded by the larger of the two even tails,
which tends to zero for every $q<1$. Dominated convergence and Tonelli give
almost-sure decision after integration. The waiting mean is at least
$K_\infty$ by PG27.17, with all waiting means infinite if $I_\mu=\infty$.

Use the deterministic joint route of Theorem 3.2 on each finite horizon fiber,
and the route of Theorem 4.1 on the infinite fiber. At a marker decode exactly;
on a finite zero leaf compare the two already integrated root masses and use
MAP, with either fixed choice on a tie. A countable measurable partition of the
seed gives measurable finite-history sections for this one controller. Tonelli
and source-seed independence give the two identities and inequalities. The
same underlying $Q,X_0$, and two actual arms may be used for both executions;
expected domination is claimed, not a pathwise paid-count ordering. No source
copy or new seed draw is used. $\square$

**Corollary 4.3 (exact selector integrability test).** For a joint replacement,
finite paid mean is equivalent to
$$
\sum_{h<\infty}\nu(H=h)K_h<\infty,\qquad
\nu(H=\infty)=0\ \text{or}\ I_\mu<\infty.
$$
For a general original policy put $\beta_m=\nu(H>2m)$,
$\gamma_m=\nu(H>2m+1)$, and let $d_m(u)$ indicate odd/odd replay at $2m$
on $\{H>2m\}$. Its exact cost is
$$
\begin{aligned}
C={}&\nu(H>0)+\sum_{m\ge0}\gamma_m(bM_m+aM_{m+1})\\
&+\sum_{m\ge1}\left[\beta_mM_m+
 v_m\int_{\{H>2m\}}d_m(u)\,\nu(du)\right].
\end{aligned}
$$
Each bracket is nonnegative; the signed corrections are absolutely summable.
Hence it is finite exactly when the nonnegative baseline series obtained by
omitting the $v_m$ terms is finite. In particular, $I_\mu=\infty$ and
$\nu(H=\infty)=0$ alone do not ensure finite mean.

**Proof.** The first claim is integration of $K_H$. For the second, sum the
actual survival events $\{H>t,\tau>t\}$ before query $t+1$, using the original
seed event and the PG27 cylinder mass at each depth. Absolute summability follows
from $\sum_m|v_m|<1$, so no divergent baseline can be cancelled. $\square$

## 5. Exact average-budget consequences with the seed retained

**Definition 5.1 (original-seed feasible weights).** Give $S$ the sigma algebra
of all subsets and let
$$
\mathsf P_\nu=\{(\nu(H=h))_{h\in S}:H:U\to S\text{ measurable}\}.
$$
For $p\in\mathsf P_\nu$ write
$$
C(p)=\sum_{h<\infty}p_hK_h+p_\infty K_\infty,\qquad
E(p)=\sum_{h<\infty}p_hR_h^*.
$$
For $B\in[0,\infty)$ let $F_\nu(B)$ be the infimum of actual error over all
lawful almost-sure-decision controllers with actual mean at most $B$.

**Theorem 5.2 (exact reduction, positivity, and zero error).** For every original
seed law and every finite budget,
$$
\boxed{F_\nu(B)=\inf\{E(p):p\in\mathsf P_\nu,\ C(p)\le B\}.}
$$
An attained minimizing selector yields an optimal original-source controller.
Conversely an optimal original-source controller yields a minimizing selector
by Theorem 4.2. This equivalence distinguishes an infimum from an attained
minimum without changing the seed domain.

For every finite integer $L$ with $K_{L+1}>B$,
$$
F_\nu(B)\ge R_L^*\left(1-\frac{B}{K_{L+1}}\right)>0.
$$
Consequently finite-budget zero error, and also zero infimum error, occur
exactly when $I_\mu<\infty$ and $B\ge K_\infty$. In that case the constant
selector $H=\infty$ attains zero for every original seed law. When
$I_\mu=\infty$, every finite budget has strictly positive infimum risk;
arbitrarily small error remains attainable with sufficiently large finite
budgets by constant finite horizons.

**Proof.** Every $p$ in the displayed set has an original-seed realization by
definition and Theorem 4.2, giving one inequality; every admissible policy has
a dominating such selector, giving the other. The same argument proves the
attainment equivalence. Because $K_h$ increases, $C(p)\le B$ implies
$p(H\ge L+1)\le B/K_{L+1}$. The cap risks are nonincreasing and positive
at every finite depth, so the remaining mass contributes at least $R_L^*$
per unit, proving the bound. If $B<K_\infty$, the limit in Theorem 4.1 gives
such an $L$. Zero error also forces $H=\infty$ almost surely since
$R_h^*>0$ for each finite $h$, and its least mean is $K_\infty$. The infinite
route and the finite-horizon limit prove the remaining assertions. $\square$

**Proposition 5.3 (realizable randomization and two horizons).** If the original
seed probability space is nonatomic, then $\mathsf P_\nu$ is the full set of
probability vectors on $S$. For every finite $B$ its infimum in Theorem 5.2 is
attained, and some optimum uses at most two horizons. The two horizons need not
be neighbors. More generally any proposed two-horizon weight $\theta$ is
lawful precisely when the original seed has a measurable event of mass
$\theta$ (unless the two horizons coincide). For a purely atomic seed with
atom masses $(c_i)$, its exact class is
$$
p_h=\sum_{i:f(i)=h}c_i
$$
for assignments $f$ of its atoms to horizons. A seed with atoms and a nonatomic
remainder of mass $c$ realizes exactly such atomic assignments plus an arbitrary
nonnegative vector of total mass $c$.

**Proof.** We first justify the measure-splitting fact used here. In a finite
nonatomic measure space every positive set has a positive subset of measure
at most any prescribed $\epsilon>0$: repeatedly split it into two positive
parts and follow the smaller part until its mass is small enough. To carve a
subset of prescribed mass $t$, successively choose a subset of the remaining
set with mass at most the current deficit and greater than half the supremum
of the available masses with that bound; stop if the deficit is zero. The
increasing union has mass at most $t$. If a positive deficit remained, the
small-subset property applied to the residual of this union would give a fixed
positive admissible mass at every earlier step, contradicting the increments
tending to zero. Thus the union has mass $t$. Repeated carving gives every
countable mass partition; the leftover is null. On an atom a countable-valued
measurable map is almost surely constant, since its countable fibers partition
the atom. These facts prove all the seed-feasibility statements, including
the mixed case. They supply mathematical existence, not effective exact-real
synthesis.

For completeness, attainment follows directly by compactifying the horizon
indices. Take a minimizing sequence of probability vectors with cost at most
$B$. A diagonal subsequence has limits $p_h$ for every finite $h$; put
$p_\infty=1-\sum_{h<\infty}p_h\ge0$. For each fixed $L$, the bounded
truncated cost $\min(K_h,K_L)$ is constant for $h\ge L$, including infinity,
so its expectation depends continuously on finitely many coordinates. Its
limiting expectation is at most $B$. Monotone convergence as $L\to\infty$
gives $C(p)\le B$, including the case $K_\infty=\infty$. Risk expectations
converge too: retain finitely many coordinates and bound the remaining
contribution by $R_L^*\to0$. Thus $p$ attains the infimum. The original
nonatomic seed realizes this entire vector by the partition construction.
This argument retains escaped mass at infinity and charges its actual cost.

At budget zero only horizon zero is feasible. If $B\ge K_\infty<\infty$,
the infinite horizon is optimal. In the remaining case $0<B<K_\infty$, write
$F(B)$ for this unrestricted attained value. Mixtures make $F$ convex and it
is nonincreasing. It is strictly decreasing below $K_\infty$: an optimizer
has positive error by Theorem 5.2, and mixing in a sufficiently small mass at
a finite horizon with smaller risk strictly improves it at any larger budget.
In particular an optimizer at $B$ uses mean exactly $B$. A supporting slope
$s<0$ exists at this interior budget: convexity orders all left secant slopes
below all right secant slopes, and any slope between their one-sided limits
supports the graph; local boundedness makes those limits finite. A zero slope
would force a constant later segment,
contradicting strict decrease. Put $\lambda=-s>0$. For every horizon of finite
cost, the supporting inequality implies
$$
R_h^*+\lambda K_h\ge F(B)+\lambda B.
$$
The same holds at infinity when it has finite cost. Averaging over an optimal
measure gives equality, so every horizon in its positive support lies on this
line. If the support contains a horizon of cost $B$, that single horizon is
optimal. Otherwise its mean $B$ supplies one supported cost below $B$ and one
above $B$. Their unique Bernoulli mixture of mean $B$ lies on the same line
and has risk $F(B)$. Its weight is realizable by the original nonatomic seed.
For example, take $a=b=1/2$, $\mu=\delta_{1/2}$, and $B=2$. Then
$$
(K_2,K_3,K_4)=(7/4,9/4,21/8),\qquad
(R_2^*,R_3^*,R_4^*)=(1/8,1/8,1/16).
$$
The original nonatomic seed can put weight $2/7$ at horizon $4$ and $5/7$ at
horizon $2$, giving cost $2$ and risk $3/28<1/8$. Interpolation of the two
adjacent horizons $2,3$ whose costs bracket $2$ has risk $1/8$ and is therefore
suboptimal. For a
restricted atomic seed these convex combinations cannot replace its own
feasibility class, and only the infimum/attainment equivalence of Theorem 5.2
is being asserted. $\square$

## 6. Sources and limits

The shared-$Q$ posterior, parity replay, and all-marker stopping identities
are the PG27.1--27.3 and PG27.14--27.19 results in [Process Geometry](RECURSIVE_RELATIONAL_OBSERVATION_PROCESS_GEOMETRY.md).
The terminal risks and their lawful cap attainers are supplied by [Finite-query
spatial recovery](RECURSIVE_RELATIONAL_OBSERVATION_FINITE_QUERY_SPATIAL_RECOVERY.md),
at immutable supplier revision `5234b4de599f6ed513dab4bbe2f65b5c743f0115`, especially §§2--4.\nThe stopping-tail interface is also exposed by
`D5/S3/Observer/ProbabilisticClosure/AdaptiveMarkerStoppingTails.lean` and
its Blueprint source. The mixed-mean suppliers in that directory are
BeneficialMarkerDeflection.lean and SingleDeflectionOptimalController.lean.
The cylinder and parity helpers, including private statements, in
FiniteAtomLinearRealization.lean and RawFiniteAtomLinearRealization.lean
supply the same fixed-source interfaces. These are repo-derived suppliers;\nthis companion adds
the common finite-horizon cost/risk attainment and the original-seed
replacement statement.

Visible-seed averaging itself is supplied by [Wave-particle events, Theorem
393.3](RECURSIVE_RELATIONAL_OBSERVATION_WAVE_PARTICLE_EVENTS.md); it is used
only for prior-average cost and risk, with the seed visible and independent.
Measure splitting, diagonal compactness of probability vectors with a retained
infinite endpoint, and supporting lines of convex functions are used only as
intermediate classical facts, with the needed arguments given in Proposition
5.3. They do not supply the source-specific common realization in Theorems
3.2 and 4.2. The new bridge and its mean-budget consequences are repo-derived
ordinary conditional mathematics.

Paid fresh-edge count excludes computation, seed bits, record/output/storage,
effective prior precision, and physical time. Fixed-prior measurable control
does not provide effective synthesis from arbitrary approximate descriptions
of $\mu$, its moments, or exact Bernoulli weights. The labels recovered are
only those of the actual exposed interval; neither the unacquired law table
nor $Q$ is recovered. The frontier describes the best feasible tradeoff;
an arbitrary controller can use a worse decoder at the same cost. These
results assert no physical realization, whole-literature novelty, total-memory
optimum, or complete four-expression recovery.

## 追加锚（本行以下为增补区）
