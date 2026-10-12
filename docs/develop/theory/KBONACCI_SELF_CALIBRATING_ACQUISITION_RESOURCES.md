# Self-calibrating acquisition resources

## 71. Actual sources and the simultaneous optimum of the maximum address

**Definition 71.1 (Source, carrier and exact acquisition).** Retain the labeled
source and static prime answers of
[Source-Correlated Laws, Definition 45.1](KBONACCI_SELF_CALIBRATING_SOURCE_CORRELATED_LAWS.md#45-lawful-acquisition-through-one-inherited-seed):

$$
\begin{aligned}
&F_0=0,\quad F_1=1,\quad F_{r+2}=F_{r+1}+F_r,\\
&X=\{(r,g):r\text{ prime},\ g\in\mathbb Z,
          \ \lceil F_r/10\rceil\le g\le\lfloor F_r/5\rfloor\},\\
&N(r,g)=1+F_rg,\qquad
p_1<p_2<\cdots,\qquad q_i(x)=\mathbf1_{p_i\mid N(x)},\\
&C_m(x)=\{y\in X:q_i(y)=q_i(x)\text{ for }1\le i\le m\},
\qquad C_0(x)=X.
\end{aligned}
\tag{71.1}
$$

The set $X$ is countable and retains all its labels. Its members have positive
integer $N(x)$ and hence finite prime support. Every prescribed finite prime
answer pattern is realized by an actual member of $X$, by
[Boundaries, Theorem 35.2](KBONACCI_SELF_CALIBRATING_BOUNDARIES.md#35-exact-finite-divisibility-fibres-in-canonical-fibonacci-windows).
Only these actual sources enter any cylinder or comparison below.

Fix a nonempty measurable original tape carrier $(\Theta,\mathcal F)$ and its
consumer. An acquisition uses one source-independent probability space
$(S,\mathcal A,\mathsf P_A)$ as its seed and one common deterministic rule after
the seed is fixed. Its only source observations are the static answers $q_i$;
the supplied advice is zero. Addresses may be chosen arbitrarily and
adaptively, and requests may be repeated. Finite records and tape-output
events are measurable. At each actual source, handoff occurs after finitely
many transitions almost surely, and the original consumer then runs on the
same source with the handed original tape. The rule receives no source label,
integer value, first-absence index, source distribution or extra probe, and
uses no restart or conditioning away of failures.

For a selected family of probability measures $\lambda=(\lambda_x)_{x\in X}$
on this carrier, let $\mathcal A(\lambda)$ be the class of all such acquisitions
whose handed-tape law is exactly $\lambda_x$ at every actual $x$. Different
members of $\mathcal A(\lambda)$ may use different seed probability spaces.
All probabilities and expectations indexed by $A$ use its own seed law.
Fixed shared tables and countable product seed spaces are permitted, as in
[Source-Correlated Laws, Theorem 46.4](KBONACCI_SELF_CALIBRATING_SOURCE_CORRELATED_LAWS.md#46-operational-envelopes-and-a-fixed-family-criterion).
This is a measurable common-rule class with no computability or processing-time
bound imposed.

**Definition 71.2 (Intrinsic deficit and address resources).** Enumerate the
actual labels without repetitions as $x_1,x_2,\ldots$. For a nonempty occupied
prefix cylinder $C$, use the selected family's own tape mixture and define

$$
\begin{aligned}
\tau_\lambda&=\sum_{j\ge1}2^{-j}\lambda_{x_j},
&f_x&=\frac{d\lambda_x}{d\tau_\lambda},\\
\ell_C&=\left(\inf_{x\in C}f_x\right)\tau_\lambda,
&a_C&=\ell_C(\Theta),\\
r_x(m)&=1-a_{C_m(x)},
&\Omega_\lambda(m)&=\sup_{x\in X}r_x(m).
\end{aligned}
\tag{71.2}
$$

Nonnegative measurable density versions are understood. The Radon--Nikodym
and countable-infimum argument in Theorem 46.4 makes $\ell_C$ the greatest
measure dominated by every $\lambda_y$, $y\in C$. It is independent of the
enumeration and versions. The mixture is on tapes, not on sources. In
particular it is not the original targets' mixture, and no absolute continuity
with respect to that other mixture is assumed.

At finite handoff, let $K_{A,x}$ count all prime requests, including
repetitions, and let $I_{A,x,j}$ be the index of the $j$th requested prime. Put

$$
M_{A,x}=\max\{I_{A,x,j}:1\le j\le K_{A,x}\},
\qquad \max\varnothing=0.
\tag{71.3}
$$

On every branch with no finite handoff put $K_{A,x}=M_{A,x}=\infty$, including
a branch that eventually ceases making requests. Thus $M$ is the maximum
requested prime **index**, and $K$ is the number of requests. These are
distinct random variables. Their finite sublevel events are measurable unions
of finite-handoff record events.

**Theorem 71.3 (Simultaneous minimum maximum-index tails).** Suppose

$$
a_{C_m(x)}\uparrow1\qquad\text{for every }x\in X.
\tag{71.4}
$$

For every $A\in\mathcal A(\lambda)$, every actual $x$ and every
$m\in\mathbb N_0$,

$$
\mathsf P_A\{M_{A,x}>m\}\ge r_x(m).
\tag{71.5}
$$

There is one $A^+\in\mathcal A(\lambda)$ attaining equality simultaneously
for all $x,m$. Consequently the following are attained minima, with the same
minimizer at every source and depth:

$$
\begin{aligned}
\min_{A\in\mathcal A(\lambda)}\mathsf P_A\{M_{A,x}>m\}&=r_x(m),\\
\min_{A\in\mathcal A(\lambda)}\sup_x
             \mathsf P_A\{M_{A,x}>m\}&=\Omega_\lambda(m).
\end{aligned}
\tag{71.6}
$$

Conversely, $\mathcal A(\lambda)\ne\varnothing$ implies (71.4).

**Proof.** Fix $A,x,m$ and the whole measurable seed event

$$
E_{x,m}=\{\text{finite handoff at }x\text{ with every requested index }\le m\}.
$$

For each $y\in C_m(x)$ and every seed in this event, induction over the finite
execution gives the same requests, answers, internal transitions and handed
tape at $y$ as at $x$. Indeed the next action is determined by the common
seed and preceding answers, and every answer used in this execution agrees
at $x,y$. Thus, for every measurable tape event $B$,

$$
\rho_{x,m}(B)=\mathsf P_A(E_{x,m}\cap\{\phi_x\in B\})
\le\lambda_y(B)\qquad(y\in C_m(x)).
\tag{71.7}
$$

Here $\phi_x$ is the finite-handoff output map; the restriction only uses its
termination domain. Greatestness of $\ell_{C_m(x)}$ gives
$\mathsf P_A(E_{x,m})\le a_{C_m(x)}$. By the nonhandoff convention,
$E_{x,m}=\{M_{A,x}\le m\}$, proving (71.5). The argument transports a whole
seed event to each fixed comparison source and requires no measurable tape
equality diagonal.

For attainment use the positive-increment prefix acquisition of Theorem 46.4,
with the tail identity (70.6) in
[Source-Correlated Laws, Section 70](KBONACCI_SELF_CALIBRATING_SOURCE_CORRELATED_LAWS.md#70-intrinsic-uniform-calibration-and-the-exact-cap-versus-query-tail-frontier).
It queries $p_1,p_2,\ldots$ in order until handoff. Its accumulated output
submeasure through depth $m$ at $x$ is $\ell_{C_m(x)}$, and its handoff depth
$L_x$ satisfies

$$
K_{A^+,x}=M_{A^+,x}=L_x,\qquad
\mathsf P_{A^+}\{L_x>m\}=r_x(m).
\tag{71.8}
$$

Condition (71.4) gives sourcewise almost-sure finite handoff. These are the
already supplied construction and its exact law, so they yield simultaneous
attainment in (71.5)--(71.6). If any exact acquisition exists, its $M_{A,x}$
is finite almost surely at every $x$. Taking $m\to\infty$ in (71.5) gives
$r_x(m)\to0$, proving necessity. Without (71.4) there is no nonempty
acquisition class to which an attained minimum could refer. $\square$

The lower-envelope/range-partition precedent used by the cited construction
is Gallo, Lerasle and Takahashi,
[*Markov approximation of chains of infinite order in the $\bar d$-metric*,
Section 3, Lemma 3.1](https://arxiv.org/html/1107.4353v2). That lemma concerns
countable-alphabet chain kernels; its stationary-chain and coalescence
conclusions are not assumptions or conclusions of Theorem 71.3. A related
simultaneous agreement optimum for two laws on Polish path spaces is
Völlering, [*On maximal agreement couplings*, Lemma 1.1 and Theorem
1.2](https://arxiv.org/html/1608.01511). Theorem 71.3 uses finite-execution
transport and the existing source-prefix construction, rather than an
identification with those two-process couplings.

## 72. Maximum charges, cumulative charges and a sharp address budget

**Definition 72.1 (Two address charges).** Let $c:\mathbb N_0\to[0,\infty)$
have finite values, be nondecreasing and unbounded, and satisfy $c(0)=0$.
Write $\Delta c(i)=c(i)-c(i-1)$ and $c(\infty)=\infty$. On finite handoff
define the maximum charge and cumulative charge respectively by

$$
Z_{c,A,x}=c(M_{A,x}),\qquad
S_{c,A,x}=\sum_{j=1}^{K_{A,x}}c(I_{A,x,j}).
\tag{72.1}
$$

Set both charges to $\infty$ on every nonhandoff branch. Repetitions each
contribute a term to $S_c$. The function $c$ is a prescribed numerical charge
on prime indices; it is not a duration assigned to execution transitions.

**Theorem 72.2 (Exact intrinsic maximum-charge moments).** Under (71.4), for
every $x$ and every charge of Definition 72.1,

$$
\begin{aligned}
\min_{A\in\mathcal A(\lambda)}\mathsf E_A Z_{c,A,x}
 &=\sum_{i\ge1}\Delta c(i)r_x(i-1),\\
\min_{A\in\mathcal A(\lambda)}\sup_x\mathsf E_A Z_{c,A,x}
 &=\sup_x\sum_{i\ge1}\Delta c(i)r_x(i-1).
\end{aligned}
\tag{72.2}
$$

All sums and expectations are nonnegative extended real numbers. The one
acquisition $A^+$ of Theorem 71.3 attains these minima for all $x,c$
simultaneously. For cumulative charges one always has $S_{c,A,x}\ge Z_{c,A,x}$,
and the same prefix acquisition satisfies the distinct formula

$$
\mathsf E_{A^+}S_{c,A^+,x}=\sum_{i\ge1}c(i)r_x(i-1).
\tag{72.3}
$$

In particular a uniformly finite expected maximum charge exists exactly when
the second right-hand side of (72.2) is finite. The supremum in that formula
remains outside the sum; $\sum_i\Delta c(i)\Omega_\lambda(i-1)$ is an upper
bound, not an asserted equality for a general selected family.

**Proof.** For any $M\in\mathbb N_0\cup\{\infty\}$, telescoping gives

$$
c(M)=\sum_{i\ge1}\Delta c(i)\mathbf1_{M\ge i}.
\tag{72.4}
$$

At $M=\infty$ the identity uses the unboundedness of $c$. Tonelli's theorem
and (71.5) now give

$$
\mathsf E_A Z_{c,A,x}
=\sum_{i\ge1}\Delta c(i)\mathsf P_A\{M_{A,x}>i-1\}
\ge\sum_{i\ge1}\Delta c(i)r_x(i-1).
$$

Equation (71.8) gives equality for the same $A^+$ at every source and charge.
Taking a source supremum after this sourcewise equality proves the second
line of (72.2), without interchanging a supremum and a sum. At finite handoff
the largest requested charge is at most the sum of all requested charges;
the convention makes the inequality true also on nonhandoff. Finally, the
prefix acquisition requests index $i$ exactly on $\{L_x\ge i\}$, and requests
it once. A second application of Tonelli and (71.8) proves (72.3). $\square$

**Theorem 72.3 (Sharp fixed-depth budget and strict cumulative separation).**
If a lawful exact acquisition satisfies either
$\sup_x\mathsf E_A Z_{c,A,x}\le B<\infty$ or
$\sup_x\mathsf E_A S_{c,A,x}\le B<\infty$, then, whenever $c(m+1)>0$,

$$
\Omega_\lambda(m)\le\min\{1,B/c(m+1)\}.
\tag{72.5}
$$

For every fixed depth $m$, every such charge with $c(m+1)>0$, and every
$B\ge0$, this bound is attained by a selected family on the unchanged tapes
and actual sources of Theorem 67.5. Even maximum-tail optimality of the
prefix acquisition does not imply cumulative-charge optimality.

**Proof.** On $\{M_{A,x}>m\}$,
$Z_{c,A,x}\ge c(m+1)$. Thus (71.5) gives
$c(m+1)r_x(m)\le\mathsf E_A Z_{c,A,x}$. Use $S_c\ge Z_c$ when the cumulative
budget is given, and take the supremum in $x$. Deficits are at most one,
proving (72.5).

For the witness fix $d=m+1$ and $t\in[0,1]$. On the carrier of Theorem 67.5
choose two distinct points $\theta_0,\theta_1$ in $B_1$ and put

$$
\lambda_x=(1-t)\delta_{\theta_0}+t\delta_{\theta_{q_d(x)}}.
\tag{72.6}
$$

At every occupied depth $j<d$, finite-pattern realization supplies both
answers at $p_d$, consistent with that prefix. The two laws there are
$\delta_{\theta_0}$ and $(1-t)\delta_{\theta_0}+t\delta_{\theta_1}$, whose
greatest common submeasure is $(1-t)\delta_{\theta_0}$. At depth $j\ge d$ the
law is fixed. Therefore, at every actual source,

$$
r_x(j)=\Omega_\lambda(j)=
\begin{cases}t,&j<d,\\0,&j\ge d.\end{cases}
\tag{72.7}
$$

With a common Bernoulli seed of success probability $t$, emit $\theta_0$
immediately on failure; on success query only $p_d$ and emit
$\theta_{q_d(x)}$. This exact acquisition has finite handoff for every seed
and source, measurable finite records, and

$$
\mathsf E Z_{c,A,x}=\mathsf E S_{c,A,x}=t c(d)\qquad(x\in X).
\tag{72.8}
$$

The first formula of (72.2) and (72.7) give the sourcewise lower bound
$t c(d)$ for every exact acquisition's maximum charge, and hence also for
its cumulative charge. Thus (72.8) attains both optima for this family.
Taking $t=\min\{1,B/c(d)\}$ proves sharpness of (72.5), including $B=0$.

For the prefix acquisition, (72.3) instead gives
$\mathsf E S_{c,A^+,x}=t\sum_{i=1}^dc(i)$. With $t>0$, $d\ge2$ and
$c(i)=i$, this is $td(d+1)/2>td$, although its maximum-index tails are
optimal. For example $d=100,t=1$ gives cumulative charges $5050$ and $100$
respectively. The exact general-family formula (72.2) is consequently a
maximum-charge result; (72.3) supplies a prefix cumulative cost, not an
arbitrary-family cumulative optimum. $\square$

## 73. Monotone marked first-absence laws and their finite certificates

**Definition 73.1 (Marked first-absence family).** From here on retain exactly
the carrier, consumer and original targets of
[Source-Correlated Laws, Theorem 67.5](KBONACCI_SELF_CALIBRATING_SOURCE_CORRELATED_LAWS.md#67-original-target-proportional-containment-and-unavoidable-nonatomic-ranges).
In particular

$$
\Theta=\bigsqcup_{j\ge1}B_j\ \sqcup\ \bigsqcup_{j\ge1}P_j,
\qquad B_j\cong(0,1),\quad P_j\cong(0,1),
\tag{73.1}
$$

with its disjoint-union Borel sigma algebra. The unchanged consumer returns
unknown immediately on every $B_j$ and proposes $j$ immediately on $P_j$.
Fix distinct original points
$\theta_j=(B_1,1/(j+2))$ for $j\in\mathbb N_0$; their singletons are
measurable. Define

$$
n(x)=\min\{i\ge1:q_i(x)=0\},\qquad D_n=\{x:n(x)=n\}.
\tag{73.2}
$$

Every $n(x)$ is finite because $N(x)$ has finite prime support. Every $D_n$
is occupied by Theorem 35.2. For a sequence

$$
1\ge a_1\ge a_2\ge\cdots>0,\qquad \lim_{i\to\infty}a_i=0,
\tag{73.3}
$$

prescribe the selected laws

$$
\lambda^a_x=(1-a_{n(x)})\delta_{\theta_0}
                  +a_{n(x)}\delta_{\theta_{n(x)}}.
\tag{73.4}
$$

This specifies a selected family on the original tapes, not a change to the
original target family or an observation of $n(x)$ supplied to an acquisition.

**Theorem 73.2 (Exact marked modulus and sourcewise prefix resources).** For
every $x\in D_n$,

$$
r_x(m)=
\begin{cases}a_{m+1},&m<n,\\0,&m\ge n,\end{cases}
\qquad \Omega_{\lambda^a}(m)=a_{m+1}.
\tag{73.5}
$$

The positive-increment prefix acquisition has a realization, denoted $A^a$,
which hands off by the $n$th request at every $x\in D_n$ for every seed.
It satisfies, for $1\le i\le n$,

$$
\begin{aligned}
\mathsf P_{A^a}\{\text{request }p_i\text{ at }x\}&=a_i,\\
\mathsf E_{A^a}K_{A^a,x}&=\sum_{i=1}^na_i,\\
\mathsf E_{A^a}S_{c,A^a,x}&=\sum_{i=1}^nc(i)a_i,\\
\mathsf E_{A^a}Z_{c,A^a,x}&=\sum_{i=1}^n\Delta c(i)a_i.
\end{aligned}
\tag{73.6}
$$

It never requests indices greater than $n$. Its uniform request-count tail
is exactly $a_{m+1}$, and hence tends to zero.

**Proof.** If a depth-$m$ prefix has a negative answer, it fixes its first
absence $n\le m$. All selected laws in that cylinder are then the same,
so their common mass is one. Otherwise the prefix is all positive. Let
$H_m=\{x:q_1(x)=\cdots=q_m(x)=1\}$, with $H_0=X$. It contains every
occupied $D_j$, $j>m$, and contains only sources with $n(x)>m$.

A common submeasure in $H_m$ is supported on the union of the displayed
atoms, since it is dominated by any one of the laws (73.4). At every marked
atom $\theta_j$, $j\ge1$, another member of $H_m$ has zero mass there:
choose any occupied $D_k$ with $k>m$ and $k\ne j$. Hence the common measure
has no marked-atom mass. Its mass at $\theta_0$ is at most

$$
\inf_{j>m}(1-a_j)=1-a_{m+1},
$$

and $(1-a_{m+1})\delta_{\theta_0}$ is dominated by all these laws. This proves
the asserted greatest common submeasure and (73.5). Occupation of every
$D_n$ ensures that the supremum deficit is exactly $a_{m+1}$.

The existing positive-increment rule has a particularly simple realization
here. Use one uniform seed $U\in(0,1)$. At an all-positive prefix of depth
$m$, emit $\theta_0$ if $U<1-a_{m+1}$; otherwise query $p_{m+1}$. If its
answer is negative emit $\theta_{m+1}$, and if positive continue at depth
$m+1$. The thresholds increase because $(a_i)$ decreases. At $x\in D_n$
the rule therefore reaches request $i\le n$ exactly when $U\ge1-a_i$, and
hands off by request $n$. The output $\theta_n$ has probability $a_n$, and
the only other output is $\theta_0$, proving exactness of (73.4).

Finite records are measurable threshold events in $U$, and output events
are unions of the corresponding threshold intervals; handoff is finite at
every seed and actual source. The rule uses only the current prefix and its
fixed thresholds. The increments at all-positive nodes are multiples of
$\delta_{\theta_0}$, and at the first negative node the increment is
$a_n\delta_{\theta_n}$, so this is a realization of the cited prefix
construction. Counting each reached index once proves the first three
lines of (73.6). The last line follows by (72.4), or by the tail (73.5).
Since every $D_n$ is occupied, the supremum of
$\mathsf P\{K_{A^a,x}>m\}$ over $x$ is $a_{m+1}$. $\square$

**Theorem 73.3 (Every marked output certifies all initial indices).** For
every $A\in\mathcal A(\lambda^a)$, every $n\ge1$ and every $x\in D_n$,
almost every seed on which the finite handoff tape is $\theta_n$ has
requested each of $p_1,\ldots,p_n$. In particular

$$
\begin{aligned}
\mathsf P_A\{K_{A,x}\ge n\}&\ge a_n,\\
\mathsf E_A K_{A,x}&\ge n a_n,\\
\mathsf E_A S_{c,A,x}&\ge a_n\sum_{i=1}^nc(i).
\end{aligned}
\tag{73.7}
$$

The last inequality is valid for any nonnegative finite charges on indices,
even without monotonicity.

**Proof.** Fix $A,n,x$ and an index $i\le n$. Partition the measurable event
of finite handoff with tape $\theta_n$ without any request to $p_i$ by its
finite set $F$ of queried indices. There are countably many finite subsets
of $\mathbb N_{>0}$. Each corresponding event $E_F$ is measurable: it is a
countable union over finite handoff times and finite request/answer words
with index set $F$, intersected with the measurable tape-output event.
Every such $F$ omits $i$.

For each $F$ choose one actual comparison source $y_F$, independently of
the seeds within $E_F$. If $i<n$, prescribe the answers of $x$ on $F$,
positive answers at $1,\ldots,i-1$, and a negative answer at $i$. These
constraints are consistent: $x$ has positive answers at all indices below
$n$, and the one changed coordinate $i$ is not in $F$. Theorem 35.2
realizes this finite pattern at an actual $y_F$ with $n(y_F)=i\ne n$.
If $i=n$, prescribe the answers of $x$ on $F$ and positive answers at every
index $1,\ldots,n$. Again the constraints are consistent, since $n\notin F$.
An actual realization has $n(y_F)>n$, using its finite prime support.

On the whole event $E_F$, the common seeded rule at $y_F$ follows exactly
the finite execution at $x$: every requested index is in $F$ and its answer
agrees. Thus it hands over the same tape $\theta_n$ on all of $E_F$.
But $n(y_F)\ne n$, and exactness gives

$$
\mathsf P_A(E_F)\le\lambda^a_{y_F}(\{\theta_n\})=0.
\tag{73.8}
$$

The countable union in $F$ is null. Taking the finite union over $i\le n$
proves that almost every $\theta_n$ output contains every initial request.
The output event has probability $a_n$. On its nonexceptional part,
$K_{A,x}\ge n$ and $S_{c,A,x}\ge\sum_{i=1}^nc(i)$, proving (73.7).
Countability of $X$ also allows a common null union over actual labels for
each fixed acquisition, if desired. The comparison sources were chosen for
entire measurable events, never separately for an individual seed.
$\square$

## 74. Exact minimax count, cumulative charge and maximum charge

**Theorem 74.1 (Marked-family resource identities against all adaptive rules).**
For every sequence (73.3), all infima below range over the full class
$\mathcal A(\lambda^a)$ of arbitrary adaptive exact acquisitions on all
actual sources. One acquisition $A^a$ attains all three identities:

$$
\begin{aligned}
\min_{A\in\mathcal A(\lambda^a)}\sup_x\mathsf E_A K_{A,x}
 &=\sum_{i\ge1}a_i,\\
\min_{A\in\mathcal A(\lambda^a)}\sup_x\mathsf E_A S_{c,A,x}
 &=\sum_{i\ge1}c(i)a_i,\\
\min_{A\in\mathcal A(\lambda^a)}\sup_x\mathsf E_A Z_{c,A,x}
 &=\sum_{i\ge1}\Delta c(i)a_i.
\end{aligned}
\tag{74.1}
$$

For the charged identities assume Definition 72.1 and $c(1)>0$.
Values of $\infty$ are allowed, and attainment at $\infty$ means that every
competitor has infinite supremal mean for that resource. These are uniform
minimax identities; no sourcewise minimum-count or minimum-cumulative-charge
claim is made by (74.1).

**Proof.** The sourcewise formulas (73.6), together with occupation of every
$D_n$, show that $A^a$ has uniform means equal to the three series: each
supremum is the increasing limit of its nonnegative finite partial sums.
These give the upper bounds, including extended-real values. The third
identity also follows directly from (72.2) and (73.5), since

$$
\sup_{x\in X}\sum_{i\ge1}\Delta c(i)r_x(i-1)
=\sup_{n\ge1}\sum_{i=1}^n\Delta c(i)a_i
=\sum_{i\ge1}\Delta c(i)a_i.
\tag{74.2}
$$

It remains to establish the universal lower bounds for count and cumulative
charge. We prove them together. Let either $b_i=1$ for every $i$, or
$b_i=c(i)$. On finite handoff write
$W_{A,x}=\sum_{j=1}^{K_{A,x}}b_{I_{A,x,j}}$, and put $W_{A,x}=\infty$ on
nonhandoff. In either case $b_i\ge b_1>0$ and $W_{A,x}\ge b_1K_{A,x}$.
Fix any $A\in\mathcal A(\lambda^a)$ and set
$B_A=\sup_x\mathsf E_A W_{A,x}$. If $B_A=\infty$, the desired lower bound
$B_A\ge\sum_i b_i a_i$ is immediate in the extended order. Suppose instead
that $B_A<\infty$.

Fix a finite $r\ge1$ and $\varepsilon>0$. Choose a finite $k$ such that

$$
\sup_x\mathsf P_A\{K_{A,x}>k\}
\le\frac{B_A}{b_1(k+1)}<\varepsilon.
\tag{74.3}
$$

Use the common finite-query-forest event of (70.3)--(70.4). Explicitly, let
$I_{A,x,j}=0$ when the $j$th request is never made, and put

$$
J_{A,k,m}=\bigcup_{x\in X}\ \bigcup_{1\le j\le k}
                    \{s:I_{A,x,j}(s)>m\}.
\tag{74.4}
$$

For completeness, its applicable finite-forest property is as follows. Each
request index is measurable by a countable union over finite transition
times and finite request/answer words; countability of $X$ makes $J$ measurable.
At a fixed seed the common rule has at most two answer continuations at each
request. Its first $k$ requests across all actual sources therefore occupy
at most $2^k-1$ nodes, with a finite largest requested index. A terminated
branch, or one with infinite processing before another request, adds no
node. Consequently $J_{A,k,m}\downarrow\varnothing$ as $m\to\infty$, and
continuity from above gives $\mathsf P_A(J_{A,k,m})\to0$.
This is precisely the finite-branching supplier in Section 70, with the
decision-tree background of Buhrman and de Wolf,
[*Complexity Measures and Decision Tree Complexity: A Survey*, Sections
3.1--3.2](https://homepages.cwi.nl/~rdewolf/publ/qc/dectree.pdf).
No finite Boolean input-size bound is being transferred to $X$.

Choose $m\ge r$ with $\mathsf P_A(J_{A,k,m})<\varepsilon$. Theorem 35.2
supplies one actual $z$ whose first $m$ answers are all positive, and, for
each $1\le i\le r$, an actual $y_i$ whose first $m$ answers are all positive
except at $i$. In particular $n(y_i)=i$. These finitely many comparison
sources are fixed for this $r,\varepsilon,k,m$.

At $y_i$ the finite output event $\{\phi_{y_i}=\theta_i\}$ has probability
$a_i$. Intersect it with $\{K_{A,y_i}\le k\}\setminus J_{A,k,m}$, and remove
the null subset on which the certificate of Theorem 73.3 fails. Denote the
result by $E_i$. All these are events in the same seed probability space,
and the two probability losses and the null removal give

$$
\mathsf P_A(E_i)\ge a_i-2\varepsilon.
\tag{74.5}
$$

For every seed in $E_i$, execution at $y_i$ requests $p_i$ at least once.
All its requests lie within indices $1,\ldots,m$, because it uses at most
$k$ requests and the seed is outside $J_{A,k,m}$. Before its first request
to $p_i$, each requested answer agrees with that at $z$: the first $m$
answer words of $y_i,z$ differ only at $i$. Induction over this finite
execution prefix therefore makes $z$ issue the same first request to $p_i$
on the entire event $E_i$. It does not matter how the two executions differ
after that request.

Let $Q_i(z)$ be the measurable event that $z$ requests $p_i$ at least once.
We have $E_i\subseteq Q_i(z)$. Counting a charge once for each distinct
index among $1,\ldots,r$ gives, pointwise, including nonhandoff,

$$
W_{A,z}\ge\sum_{i=1}^r b_i\mathbf1_{Q_i(z)}.
$$

The events $E_i$ need not be disjoint; no disjointness is used in the
following finite linearity of expectation:

$$
B_A\ge\mathsf E_A W_{A,z}
\ge\sum_{i=1}^r b_i\mathsf P_A(Q_i(z))
\ge\sum_{i=1}^r b_i(a_i-2\varepsilon).
\tag{74.6}
$$

For fixed $r$ this inequality holds for every $\varepsilon>0$, although the
chosen actual source $z$ may change with $\varepsilon$. The left side is the
same source supremum. Letting $\varepsilon\downarrow0$ gives
$B_A\ge\sum_{i=1}^r b_i a_i$, and then taking $r\to\infty$ gives
$B_A\ge\sum_{i\ge1}b_i a_i$. If that series diverges, this contradicts the
assumed $B_A<\infty$ and proves that no competitor has a finite uniform
mean. Otherwise it is the required finite lower bound. The choices $b_i=1$
and $b_i=c(i)$ establish the first two lines of (74.1).

At each finite stage $z$ has only a prescribed finite all-positive prefix;
it remains an actual source with finite prime support. No all-positive
infinite word is introduced as a source, and no individual-seed choice of a
comparison source enters the proof. $\square$

## 75. The same calibration modulus with incompatible mean-count optima

**Theorem 75.1 (Harmonic marked versus one-request laws).** There are two
selected families on exactly the original sources, tapes and consumer of
Theorem 67.5 with the identical intrinsic modulus

$$
\Omega(m)=\frac1{m+1}\qquad(m\in\mathbb N_0),
\tag{75.1}
$$

such that one admits an exact acquisition using exactly one request at every
source and seed, whereas every exact acquisition of the other has infinite
supremal mean request count. Both admit uniformly tight request counts.
Thus the intrinsic modulus does not determine the existence of a uniformly
finite mean request count.

**Proof.** Take $a_i=1/i$ in (73.4). Theorem 73.2 gives (75.1), and the first
line of (74.1) gives

$$
\min_{A\in\mathcal A(\lambda^a)}\sup_x\mathsf E_A K_{A,x}
=\sum_{i\ge1}\frac1i=\infty.
\tag{75.2}
$$

The divergence follows, for example, by grouping indices
$2^j,\ldots,2^{j+1}-1$, each group contributing at least $1/2$.
Nevertheless the prefix acquisition has sourcewise finite mean
$\sum_{i=1}^{n(x)}1/i$ and uniform count tail $1/(m+1)$.

For the comparison reuse exactly the selected two-tape family (70.9) in
Source-Correlated Laws, with weights $w_i=1/(i(i+1))$. Its one shared integer
seed selects index $i$ with probability $w_i$, requests $p_i$ once, and emits
the original tape $\theta_{q_i(x)}$. Equations (70.9)--(70.10) give its exact
intrinsic modulus (75.1) and $K=1$. Its zero-depth common submeasure has
mass zero by (70.10), so (71.5) at $m=0$ forces every exact acquisition to
make at least one request almost surely. Its minimum uniform mean count
is therefore exactly one. This reuses that existing family and its modulus,
rather than replacing its source model. Both families have uniformly tight
count tails, respectively by $K=1$ and Theorem 73.2. $\square$

**Theorem 75.2 (Power thresholds and the square-root separation).** In the
marked family let $a_i=i^{-s}$ with $s>0$, and let $c(i)=i^t$ for $i\ge1$,
$c(0)=0$, with $t>0$. The exact uniform optima are finite under precisely
the following conditions:

$$
\begin{aligned}
\min_A\sup_x\mathsf E_A K_{A,x}<\infty
   &\quad\Longleftrightarrow\quad s>1,\\
\min_A\sup_x\mathsf E_A S_{c,A,x}<\infty
   &\quad\Longleftrightarrow\quad s>t+1,\\
\min_A\sup_x\mathsf E_A M_{A,x}^{t}<\infty
   &\quad\Longleftrightarrow\quad s>t.
\end{aligned}
\tag{75.3}
$$

In particular, for $s=1/2$ the modulus is $(m+1)^{-1/2}$, and every exact
acquisition satisfies $\mathsf E_A K_{A,x}\ge\sqrt n$ at every $x\in D_n$.
Every such acquisition has infinite supremal mean count and cumulative
charge for every charge in Theorem 74.1. Nevertheless the optimal uniform
mean $M^{1/4}$ is finite. The prefix acquisition has finite mean count at
every individual source and uniformly tight counts.

**Proof.** Substitute into (74.1). The three exact optima are respectively

$$
\sum_{i\ge1}i^{-s},\qquad
\sum_{i\ge1}i^{t-s},\qquad
\sum_{i\ge1}\bigl(i^t-(i-1)^t\bigr)i^{-s}.
\tag{75.4}
$$

For $i\ge2$, the mean-value theorem writes the increment as
$t\xi_i^{t-1}$ with $i-1<\xi_i<i$. Since $1/2\le\xi_i/i\le1$, this increment
is bounded above and below by positive constants depending only on $t$
times $i^{t-1}$. The last series thus has the convergence behavior of
$\sum_i i^{t-1-s}$. Integral comparison, using the elementary evaluation of
$\int_1^R u^{-v}\,du$, gives convergence of $\sum_i i^{-v}$ exactly when
$v>1$; at $v=1$ the integral is $\log R$. Applying this criterion to the
three series proves (75.3), including divergence at each equality boundary.

For $s=1/2$, the sourcewise certificate (73.7) gives $n a_n=\sqrt n$.
Since every $D_n$ is occupied, its supremum is infinite for every acquisition.
For any charge with $c(1)>0$, $S_c\ge c(1)K$, so its supremal cumulative
mean is infinite as well. Taking $t=1/4<s$ in the last line of (75.3) gives
the finite uniform maximum-charge optimum

$$
\sum_{i\ge1}\bigl(i^{1/4}-(i-1)^{1/4}\bigr)i^{-1/2}<\infty.
\tag{75.5}
$$

Finally, (73.6) gives the prefix mean
$\sum_{i=1}^n i^{-1/2}\le1+\int_1^n u^{-1/2}\,du=2\sqrt n-1$ and its
uniform count tail $(m+1)^{-1/2}$. This proves the stated sourcewise finite
and uniform tightness properties alongside the unavoidable infinite
supremal mean. $\square$

## 76. Original-target and resource applicability boundaries

**Theorem 76.1 (Atomic resource witnesses have original-target TV one).**
For the selected families (72.6), (73.4) and the reused family (70.9), with
their tape points in $B_1$ as above, every actual source satisfies

$$
\operatorname{TV}(\lambda_x,\mu_x)=1,
\tag{76.1}
$$

where $\mu_x$ is the unchanged nonatomic original target of Theorem 67.5.
Consequently none of these resource witnesses is a cap-$\eta$ preparation
for those original targets at any $\eta<1$.

**Proof.** Let $H\subset B_1$ be the union of the countably many marked points
and the two-point supports used in (72.6) and (70.9). This is a countable
Borel set. Each selected law in question is a finite point mixture supported
on $H$, so $\lambda_x(H)=1$. Every original target $\mu_x$ of (67.18) is
nonatomic, hence assigns mass zero to each singleton and therefore to $H$.
The event $H$ gives TV at least one, and TV between probabilities is at most
one on the event-supremum normalization. This proves equality. The original
consumer still returns unknown on all these selected tapes, whereas the
original target problem retains its specified positive-proposal row.
$\square$

**Convention 76.2 (Scope of the resource comparisons).** The quantities
optimized here are requests, their largest prime index, and the numerical
charges of those indices. The maximum-tail and maximum-moment results
quantify over every selected family satisfying pointwise exhaustion (71.4).
The cumulative and count identities (74.1) quantify over every adaptive
exact acquisition of the particular marked family (73.4); they are not a
classification of cumulative optima for arbitrary selected families.
Sourcewise finite handoff is retained throughout, and no bound on transition
counts, arithmetic running time, effective evaluation of cylinder tables,
finite descriptions or effective sampling of arbitrary probability laws is
an additional conclusion. The actual-source finite-pattern theorem,
whole-event execution transport, greatest common submeasures and
positive-increment acquisition are the cited suppliers; the resource
comparisons above are deductions under their stated measurable hypotheses.

## 追加锚（本行以下为增补区）
