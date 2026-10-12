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

## 77. Positive-error marked acquisition and the unique full-carrier centers

**Definition 77.1 (Selected-law approximation).** Retain the actual labeled
sources, static answers, zero advice and common-rule acquisition contract of
Definition 71.1, and exactly the original carrier and consumer of Definition
73.1. Fix a sequence satisfying (73.3). For brevity write

$$
\lambda_n=(1-a_n)\delta_{\theta_0}+a_n\delta_{\theta_n},
\qquad \lambda^a_x=\lambda_{n(x)},
\qquad H_m=\{x:n(x)>m\}\quad(m\in\mathbb N_0).
\tag{77.1}
$$

Thus $H_0=X$, and $H_m$ is precisely the actual all-positive depth-$m$
cylinder. Every $D_n$, and every finite comparison pattern used below, is
occupied by Boundaries, Theorem 35.2. There is no additional source with an
infinite all-positive signature.

For $0\le\varepsilon\le1$, let $\mathcal A_\varepsilon(a)$ consist of all
lawful acquisitions whose original-tape output probabilities satisfy

$$
\sup_{x\in X}\operatorname{TV}(\widehat\lambda_{A,x},\lambda^a_x)
\le\varepsilon,
\qquad
\operatorname{TV}(\nu,\lambda)=\sup_{E\in\mathcal F}|\nu(E)-\lambda(E)|.
\tag{77.2}
$$

The seed probability space may vary with $A$, but within each acquisition
its law is source-independent and its seeded deterministic rule is common
to every actual source. Arbitrary adaptive addresses, repeated requests,
measurable finite records and outputs, and sourcewise almost-sure finite
handoff are retained. The laws $\widehat\lambda_{A,x}$ may have mass on any
original tapes, including outside the marked points. No extra support or
proposal-row condition is imposed in (77.2). The error in (77.2) is relative
to the selected laws (73.4); the nonatomic original targets $\mu_x$ of
Theorem 67.5 are unchanged. The resources $K,M,S_c$ and their nonhandoff
values retain Definitions 71.2 and 72.1.

For $t\ge0$ put

$$
S_m(t)=\sum_{n>m}(a_n-t)_+,
\qquad v_+=\max\{v,0\}.
\tag{77.3}
$$

At $t=0$ the sum is an extended nonnegative real number. At every $t>0$
it has finite support, since $a_n\to0$.

**Theorem 77.2 (Full-carrier center feasibility and its unique minimum).**
For every $m\ge0$, $0\le\varepsilon\le1$ and probability $\nu$ on the
entire original carrier,

$$
\sup_{x\in H_m}\operatorname{TV}(\nu,\lambda^a_x)\le\varepsilon
\quad\Longleftrightarrow\quad
\begin{cases}
\nu(\{\theta_0\})\ge1-\varepsilon,\\
\nu(\{\theta_n\})\ge(a_n-\varepsilon)_+&\text{for every }n>m.
\end{cases}
\tag{77.4}
$$

Such a probability exists exactly when $S_m(\varepsilon)\le\varepsilon$.
The attained minimum radius is

$$
R_m=\max_{k\ge1}\frac{\sum_{j=1}^k a_{m+j}}{k+1}.
\tag{77.5}
$$

It is the unique positive solution of $S_m(R_m)=R_m$. Its unique minimizing
probability, even among all full-carrier probabilities, is

$$
\nu_m^*=(1-R_m)\delta_{\theta_0}
       +\sum_{n>m}(a_n-R_m)_+\delta_{\theta_n}.
\tag{77.6}
$$

This law has finite support. Moreover
$a_{m+1}/2\le R_m<a_{m+1}$, and $R_m$ is nonincreasing with limit zero.

**Proof.** Put $T=1-\nu(\{\theta_0\})$ and
$b_n=\nu(\{\theta_n\})$. The two target singletons and their complement
give

$$
\begin{aligned}
\operatorname{TV}(\nu,\lambda_n)
 &=1-\min\{1-T,1-a_n\}-\min\{b_n,a_n\}\\
 &=\max\{T,a_n\}-\min\{b_n,a_n\}.
\end{aligned}
\tag{77.7}
$$

Indeed all negative mass of $\nu-\lambda_n$ lies on these two singletons;
the sum of their negative deficits equals its positive mass, since both
measures have total mass one. This also proves (77.7) when $\nu$ has
diffuse mass or other atoms. The elementary TV overlap identity and its
event-supremum normalization are the ingredients in Levin and Peres, with
Wilmer, [*Markov Chains and Mixing Times*, second edition, Chapter 4,
Proposition 4.2, Remark 4.3 and equation
(4.13)](https://pages.uoregon.edu/dlevin/MARKOV/mcmt2e.pdf).
The finite partition argument here accounts for the whole original carrier.

Every $n>m$ is realized at an actual source in $H_m$. As $n\to\infty$,
the right side of (77.7) tends to $T$: both $a_n$ and
$\min\{b_n,a_n\}$ tend to zero. A uniform cap therefore forces
$T\le\varepsilon$. If $a_n>\varepsilon$, then
$b_n\le T\le\varepsilon<a_n$, and (77.7) reduces to $a_n-b_n$.
The cap then forces $b_n\ge a_n-\varepsilon$. If
$a_n\le\varepsilon$, (77.7) is at most
$\max\{T,a_n\}\le\varepsilon$ without an additional condition.
These statements prove necessity and sufficiency in (77.4). The limiting
inequality is taken along occupied actual $D_n$; it introduces no limiting
source.

Disjointness of the marked singletons gives
$S_m(\varepsilon)\le T\le\varepsilon$. Conversely, if this sum is at
most $\varepsilon$, assign mass $(a_n-\varepsilon)_+$ to each $n>m$
and the remaining mass to $\theta_0$. This is a probability satisfying
(77.4). At $\varepsilon=0$ feasibility is impossible, because
$S_m(0)\ge a_{m+1}>0$.

For $t>0$, monotonicity of $(a_n)$ gives the finite-positive-part identity

$$
S_m(t)=\sup_{k\ge0}
       \left(\sum_{j=1}^k a_{m+j}-kt\right),
\tag{77.8}
$$

where the term $k=0$ is zero. The positive summands form an initial
segment, and adjoining a nonpositive summand cannot increase a partial
sum. Hence $S_m(t)\le t$ is equivalent to
$\sum_{j=1}^k a_{m+j}\le(k+1)t$ for every $k\ge1$.
The averages in (77.5) tend to zero, by $a_n\to0$, and the first one is
positive. Their positive supremum is consequently a maximum at a finite
$k$. Let that maximum be $R$. The preceding equivalence gives
$S_m(R)\le R$. A maximizing $k$ in (77.5), substituted in (77.8), gives
$S_m(R)\ge R$. Thus $S_m(R)=R$ and $R$ is the minimum feasible radius.

On every closed interval of positive $t$, only finitely many summands can
be nonzero; therefore $S_m$ is continuous there. Since $S_m$ is
nonincreasing, $S_m(t)-t$ is strictly decreasing. Its positive root is
unique. At that root (77.4) forces

$$
R_m=S_m(R_m)\le\sum_{n>m}b_n\le T\le R_m.
$$

All inequalities are equalities. Each required marked mass is fixed, and
there is no remaining mass for another tape. This proves (77.6) and
uniqueness on the entire carrier. Finite support follows from $R_m>0$.
The first average in (77.5) gives $R_m\ge a_{m+1}/2$. Each average is
strictly less than $a_{m+1}$, and the maximum is attained, so
$R_m<a_{m+1}$. Finally $S_{m+1}(t)\le S_m(t)$ implies
$R_{m+1}\le R_m$, and the upper bound implies $R_m\to0$.
$\square$

## 78. The sharp deterministic maximum-index boundary

**Theorem 78.1 (Error under a hard address ceiling).** Among all lawful
adaptive acquisitions satisfying $M_{A,x}\le m$ almost surely at every
actual source, the attained minimum of
$\sup_x\operatorname{TV}(\widehat\lambda_{A,x},\lambda^a_x)$ is $R_m$.
For every $0<\varepsilon\le1$, the least possible deterministic
maximum-index ceiling in $\mathcal A_\varepsilon(a)$ is the finite integer

$$
h_\varepsilon=\min\{m\ge0:S_m(\varepsilon)\le\varepsilon\}
             =\min\{m\ge0:R_m\le\varepsilon\}.
\tag{78.1}
$$

It has an attainer with $K_{A,x}\le h_\varepsilon$ and
$M_{A,x}\le h_\varepsilon$ at every source and seed. The minimum remaining
error after an actually observed all-positive prefix of length $m$, with
no further source observations and a common continuation seed law, is
$R_m$. A prefix containing a negative answer instead fixes $n(x)$ and has
remaining error zero.

**Proof.** Fix an acquisition under the ceiling and one actual $x\in H_m$.
Let $E_{x,m}$ be its measurable event of finite handoff with all requested
indices at most $m$. It has probability one. On this whole event every
$y\in H_m$ follows the same finite execution and hands the same tape:
the initial inputs are common, and every requested answer agrees. This
is the finite-record transport in Lemma 45.3 and the proof of Theorem
71.3, applied to the complete event rather than to a selected seed.
The output submeasure on $E_{x,m}$ is dominated by every
$\widehat\lambda_{A,y}$. Its mass is one, so it equals each of these
probabilities. There is therefore one common probability on $H_m$,
whose uniform error is at least $R_m$ by Theorem 77.2. Adaptivity and
repeated requests do not alter this argument.

For attainment query $p_1,\ldots,p_m$ in order, stopping at the first
negative answer. If that answer has index $n\le m$, sample $\lambda_n$.
If all $m$ answers are positive, sample $\nu_m^*$. The finite-support
sampling tables use a uniform coordinate of one source-independent seed,
and the same rule applies at every actual source. The queried prefix
chooses the appropriate table. Handoff is finite for every seed, and its
finite records and output events are measurable intervals. The error is
zero on $D_n$ with $n\le m$ and at most $R_m$ on $H_m$, with equality
in the supremum by Theorem 77.2. Both $K$ and $M$ are at most $m$.

The center criterion proves both equalities in (78.1). An $m$ with
$a_{m+1}\le\varepsilon$ has $S_m(\varepsilon)=0$, proving finiteness.
For the continuation assertion the possible selected laws are precisely
$\lambda_n$, $n>m$, so a zero-request continuation produces a common
center and Theorem 77.2 applies. An observed negative fixes the first
absence and permits its exact two-point sampler. This assertion uses a
common continuation seed law; it does not condition a source-dependent
failure event away. $\square$

## 79. One shared error allowance and all adaptive mean-resource optima

**Definition 79.1 (Residual mass and cumulative weights).** Fix
$0<\varepsilon\le1$ and put

$$
\begin{aligned}
u_i&=(a_i-\varepsilon)_+,&
S&=\sum_{i\ge1}u_i,& D&=(S-\varepsilon)_+,\\
d_i&=\min\left\{u_i,\left(D-\sum_{j<i}u_j\right)_+\right\},&
b_i&=u_i-d_i,& B&=\sum_{i\ge1}b_i.
\end{aligned}
\tag{79.1}
$$

All sums in (79.1) have finite support. Let $w_1,w_2,\ldots$ be any
nondecreasing sequence of finite real weights with $w_1>0$. At finite
handoff define

$$
W_{w,A,x}=\sum_{j=1}^{K_{A,x}}w_{I_{A,x,j}},
\tag{79.2}
$$

and put $W_{w,A,x}=\infty$ on nonhandoff. Taking $w_i=1$ gives $K$;
taking $w_i=c(i)$ for a charge of Definition 72.1 with $c(1)>0$ gives
$S_c$. Repetitions contribute repeatedly in (79.2).

**Theorem 79.2 (Sharp positive-error means over all adaptive acquisitions).**
For every sequence (73.3) and every $0<\varepsilon\le1$,

$$
\begin{aligned}
\min_{A\in\mathcal A_\varepsilon(a)}\sup_x\mathsf E_A K_{A,x}
 &=\left(\sum_{i\ge1}(a_i-\varepsilon)_+-\varepsilon\right)_+=D,\\
\min_{A\in\mathcal A_\varepsilon(a)}\sup_x\mathsf E_A W_{w,A,x}
 &=\sum_{i\ge1}w_i d_i.
\end{aligned}
\tag{79.3}
$$

One acquisition attains these minima simultaneously for every allowed
weight sequence. It also satisfies $K_{A,x},M_{A,x}\le h_\varepsilon$ at
every source and seed, where $h_\varepsilon$ is the sharp maximum-index
ceiling of (78.1). In particular the attained optimum for every
nondecreasing cumulative charge is $\sum_i c(i)d_i$.

**Proof.** If $D=0$, all $d_i$ are zero. If $D>0$, let $h$ be the first
index with $\sum_{i\le h}u_i\ge D$. Then

$$
d_i=u_i\ (i<h),\qquad
0<d_h=D-\sum_{i<h}u_i\le u_h,\qquad
d_i=0\ (i>h).
\tag{79.4}
$$

In either case $(d_i)$ is nonincreasing, $\sum_i d_i=D$, and
$B=S-D=\min\{S,\varepsilon\}$. When $D=0$ set $h=0$.
For $D>0$ the condition defining $h$ is
$S_h(\varepsilon)=S-\sum_{i\le h}u_i\le\varepsilon$ and fails at
every smaller index. When $D=0$ it already holds at zero. Thus
$h=h_\varepsilon$ in all cases.

We first prove the universal lower bound for a fixed $w$. Put
$C_A=\sup_x\mathsf E_A W_{w,A,x}$. If $C_A=\infty$ the finite right
side of (79.3) is a lower bound. If $D=0$ the desired lower bound is zero.
Suppose $C_A<\infty$ and $D>0$. Let
$L=\max\{i:u_i>0\}$, which is finite. For any $\delta>0$, the pointwise
bound $W_{w,A,x}\ge w_1K_{A,x}$ and Markov's inequality permit a finite
$k\ge1$ with

$$
\sup_x\mathsf P_A\{K_{A,x}>k\}
\le\frac{C_A}{w_1(k+1)}<\delta.
\tag{79.5}
$$

Use the common event $J_{A,k,m}$ of (70.3), also written (74.4).
Its finite-forest property (70.4) uses only the common seeded rule and
finite binary branching, so applies here without exact output laws.
Specifically, at a fixed seed the first $k$ requests across all actual
sources use at most $2^k-1$ query nodes, with a finite maximum address.
Processing without a further request adds no node. Request-index events
are measurable unions over finite records, and countability of $X$ makes
$J_{A,k,m}$ measurable. Hence $J_{A,k,m}\downarrow\varnothing$ and its
probability tends to zero. Choose $m\ge L$ with
$\mathsf P_A(J_{A,k,m})<\delta$.

Before using any individual seed, fix one actual $z$ positive through
index $m$, and, for each $1\le i\le L$, one actual $y_i$ positive through
$m$ except at $i$. Boundaries, Theorem 35.2 supplies these finite patterns.
Then $n(y_i)=i$ and $n(z)>m$. At $y_i$ the cap on the singleton
$\{\theta_i\}$ gives an output probability at least
$a_i-\varepsilon=u_i$. Restrict this finite-handoff output event to
$\{K_{A,y_i}\le k\}\setminus J_{A,k,m}$ and call the resulting measurable
event $E_i$. The two probability losses give

$$
\mathsf P_A(E_i)\ge u_i-2\delta.
\tag{79.6}
$$

Every execution in $E_i$ uses indices at most $m$. Partition this whole
event by its finite request/answer record and handoff time. If the record
requests $p_i$, its execution up to the first such request replays at $z$,
since all preceding requested answers agree. If it never requests $p_i$,
its complete execution replays at $z$, including output $\theta_i$.
For the measurable events $Q_i(z)$ of requesting $p_i$ at least once and
$O_i(z)$ of finite output $\theta_i$, this proves

$$
E_i\subseteq Q_i(z)\cup O_i(z),\qquad
\mathsf P_A(Q_i(z))\ge(u_i-v_i)_+-2\delta,\quad v_i=\mathsf P_A(O_i(z)).
\tag{79.7}
$$

The finite marked union $F=\{\theta_1,\ldots,\theta_L\}$ has target mass
zero at $z$, since $n(z)>m\ge L$. Its cap therefore gives the single
collective constraint

$$
\sum_{i=1}^L v_i=\widehat\lambda_{A,z}(F)\le\varepsilon.
\tag{79.8}
$$

The comparison source $z$ is one fixed actual source for all these events.
Counting each distinct requested index once in the resource yields

$$
C_A\ge\mathsf E_A W_{w,A,z}
\ge\sum_{i=1}^L w_i(u_i-v_i)_+-2\delta\sum_{i=1}^L w_i.
\tag{79.9}
$$

For any nonnegative $v_i$ satisfying (79.8), put $t_i=(u_i-v_i)_+$.
Then $0\le t_i\le u_i$ and
$\sum_i t_i\ge S-\sum_i v_i\ge D$. The earliest filled vector (79.4)
minimizes every nondecreasing weighted cost under these conditions.
To see this without assuming strict weights, subtract its cost and use

$$
\begin{aligned}
\sum_{i=1}^L w_i(t_i-d_i)
={}&w_h\left(\sum_{i=1}^L t_i-D\right)\\
 &+\sum_{i<h}(w_i-w_h)(t_i-u_i)
  +\sum_{i>h}(w_i-w_h)t_i\ \ge0.
\end{aligned}
\tag{79.10}
$$

Each term is nonnegative, by monotonicity of $w$ and the stated bounds
on $t$. Equations (79.9)--(79.10), followed by $\delta\downarrow0$,
prove $C_A\ge\sum_i w_i d_i$. The finite actual comparison sources may
change with $\delta$, while the same source supremum $C_A$ remains on
the left. No infinite source or seed-dependent comparison is used.
Taking $w_i=1$ gives the count lower bound. Wrong marked outputs are
accounted for by (79.8), rather than assigned the null probability in
the exact certificate of Theorem 73.3.

For attainment take a common uniform seed $U\in[0,1)$. Reserve consecutive
half-open intervals of lengths $b_i$ in $[0,B)$, and immediately emit
$\theta_i$ on its interval. On $[B,1)$ put $V=U-B$. At an all-positive
prefix of depth $j$, emit $\theta_0$ if $V\ge d_{j+1}$; otherwise request
$p_{j+1}$. On a negative answer emit $\theta_{j+1}$, and on a positive
answer continue. This is the threshold rule of Theorem 73.2 applied to
the nonincreasing residual amplitudes $d_i$, with a zero next amplitude
forcing handoff. Since $B\le\varepsilon$ and $d_i\le u_i$, whenever
$d_i>0$ one has $B+d_i\le\varepsilon+(a_i-\varepsilon)=a_i\le1$.
Thus the thresholds fit inside the remaining interval.

At every $x\in D_n$ its output law is

$$
\widehat\lambda_{A,x}
=(1-B-d_n)\delta_{\theta_0}
 +\sum_{i\ge1}b_i\delta_{\theta_i}
 +d_n\delta_{\theta_n}.
\tag{79.11}
$$

The coefficients are nonnegative and sum to one. Its mass at $\theta_n$
is $b_n+d_n=u_n$, and its total mass outside $\theta_0$ is $B+d_n$.
If $a_n>\varepsilon$, then $B+d_n\le a_n$, and (77.7) gives error
$a_n-u_n=\varepsilon$. If $a_n\le\varepsilon$, then $b_n=d_n=0$ and
the error is $\max\{B,a_n\}\le\varepsilon$. Thus the acquisition lies
in $\mathcal A_\varepsilon(a)$.

All immediate-output intervals and finite-record thresholds are measurable.
There are finitely many nonzero amplitudes. The rule hands off by the first
absence or after at most $h$ requests, for every source and seed, using the
same original tape points and consumer. At $x\in D_n$, request $i$ occurs
with probability $d_i$ for $i\le n$, and never occurs for $i>n$. Hence

$$
\mathsf E_A W_{w,A,x}=\sum_{i=1}^{n(x)}w_i d_i.
\tag{79.12}
$$

An actual source with $n(x)\ge h$ exists, so the uniform mean equals
$\sum_i w_i d_i$. The same acquisition and its sourcewise probabilities
give equality for every weight sequence. Its request and address ceilings
are $h=h_\varepsilon$, completing the proof. $\square$

## 80. Robust common subprobabilities and individually optimal address tails

**Theorem 80.1 (The full-carrier common-subprobability criterion).** Fix
$m\ge0$, $0\le\varepsilon\le1$ and $p\in[0,1]$. For a nonnegative
measure $\rho$ on the original carrier of total mass $1-p$, probabilities
$\sigma_n\ge\rho$ with
$\operatorname{TV}(\sigma_n,\lambda_n)\le\varepsilon$ for every $n>m$
exist if and only if

$$
\rho(\Theta\setminus\{\theta_0\})\le\varepsilon,
\qquad
\rho(\{\theta_n\})\ge(a_n-\varepsilon-p)_+\quad(n>m).
\tag{80.1}
$$

There exists such a common $\rho$ of mass $1-p$ exactly when

$$
S_m(\varepsilon+p)\le\varepsilon.
\tag{80.2}
$$

No atomic-support restriction on $\rho$ or on the probabilities
$\sigma_n$ is part of necessity. When (80.2) holds, one explicit choice,
with $C=S_m(\varepsilon+p)$, is

$$
\begin{aligned}
\rho&=(1-p-C)\delta_{\theta_0}
       +\sum_{j>m}(a_j-\varepsilon-p)_+\delta_{\theta_j},\\
q_n&=\min\{p,(a_n-\varepsilon)_+\},\\
\sigma_n&=\rho+q_n\delta_{\theta_n}+(p-q_n)\delta_{\theta_0}.
\end{aligned}
\tag{80.3}
$$

**Proof.** Write $C_\rho=\rho(\Theta\setminus\{\theta_0\})$ and
$r_n=\rho(\{\theta_n\})$. The positive discrepancy of $\rho$ over
$\lambda_n$ has total mass

$$
\begin{aligned}
e_n&=(a_n-p-C_\rho)_++(r_n-a_n)_++C_\rho-r_n\\
   &=\max\{C_\rho,a_n-p\}-\min\{r_n,a_n\}.
\end{aligned}
\tag{80.4}
$$

The three contributions are respectively the excess on $\theta_0$, the
excess on $\theta_n$, and the mass on their complement. This formula
includes every other original tape. If $\sigma_n\ge\rho$, the positive
mass of $\sigma_n-\lambda_n$ is at least $e_n$. Since $\sigma_n$ and
$\lambda_n$ are probabilities, their TV is that positive mass. Thus
$e_n\le\varepsilon$ is necessary.

It is also sufficient for completion at a fixed $n$. Let
$\Delta_n=(\lambda_n-\rho)_+$ be the positive deficit measure.
Because $\lambda_n(\Theta)-\rho(\Theta)=p$, it has total mass
$p+e_n$. If that mass is positive, put

$$
\sigma_n=\rho+\frac{p}{p+e_n}\Delta_n.
\tag{80.5}
$$

This is a probability dominating $\rho$. The added measure fills only
deficits and fills no more than their full amount. Its remaining positive
discrepancy over $\lambda_n$ is exactly $e_n$, so its TV is $e_n$.
If $p+e_n=0$, then $p=e_n=0$ and $\rho=\lambda_n$; use
$\sigma_n=\rho$ without division. This proves the completion assertion
for an arbitrary full-carrier $\rho$.

As $n\to\infty$, (80.4) tends to $C_\rho$, because $a_n\to0$ and
$\min\{r_n,a_n\}\to0$. Therefore $e_n\le\varepsilon$ for every
occupied $n>m$ forces $C_\rho\le\varepsilon$. Under this bound, if
$a_n-p>\varepsilon$, then $r_n\le C_\rho\le\varepsilon<a_n$ and
(80.4) reduces to $a_n-p-r_n$. Its cap is precisely
$r_n\ge a_n-p-\varepsilon$. If $a_n-p\le\varepsilon$, (80.4) is at
most $\varepsilon$ without any extra marked mass. This proves (80.1).

Summing the required disjoint singleton masses gives
$S_m(\varepsilon+p)\le C_\rho\le\varepsilon$, proving necessity of
(80.2). For its sufficiency the first line of (80.3) has nonnegative base
coefficient. Indeed if $1-p>\varepsilon$, then
$C\le\varepsilon<1-p$; if $1-p\le\varepsilon$, then
$\varepsilon+p\ge1\ge a_j$ and $C=0$. The measure has mass $1-p$
and satisfies (80.1).

The last line of (80.3) is a probability dominating this $\rho$.
For each $n>m$ its mass at $\theta_n$ is

$$
(a_n-\varepsilon-p)_++\min\{p,(a_n-\varepsilon)_+\}
=(a_n-\varepsilon)_+.
$$

Its mass outside $\theta_0$ is $C+q_n$. If $a_n>\varepsilon$,
$C+q_n\le\varepsilon+(a_n-\varepsilon)=a_n$, so (77.7) gives TV
$\varepsilon$. If $a_n\le\varepsilon$, then $q_n=0$ and the marked
mass at $n$ is zero; (77.7) gives $\max\{C,a_n\}\le\varepsilon$.
This proves all of (80.3). $\square$

**Theorem 80.2 (The attained frontier for each fixed address horizon).** For
$0<\varepsilon\le1$ and $m\ge0$, define

$$
\begin{aligned}
\beta_m(\varepsilon)
 &=\inf\{p\in[0,1]:S_m(\varepsilon+p)\le\varepsilon\}\\
 &=\max\left\{0,\sup_{k\ge1}
    \frac{\sum_{j=1}^k a_{m+j}-(k+1)\varepsilon}{k}\right\}.
\end{aligned}
\tag{80.6}
$$

Every $A\in\mathcal A_\varepsilon(a)$ obeys, for every actual $x\in H_m$,

$$
\mathsf P_A\{M_{A,x}>m\}\ge\beta_m(\varepsilon).
\tag{80.7}
$$

For each fixed $m$ there is an acquisition attaining equality throughout
$H_m$, and with $\mathsf P_A\{M_{A,x}>m\}=0$ outside $H_m$. In particular

$$
\min_{A\in\mathcal A_\varepsilon(a)}\sup_x
     \mathsf P_A\{M_{A,x}>m\}=\beta_m(\varepsilon).
\tag{80.8}
$$

Its $K$ and $M$ have a deterministic finite uniform bound. Also
$\beta_m(\varepsilon)=0$ exactly when $\varepsilon\ge R_m$.
The attaining acquisition in (80.8) may depend on $m$.

**Proof.** For a competitor and a fixed actual $x\in H_m$, let $E_{x,m}$
be the whole measurable finite-handoff event with every requested index
at most $m$. Its mass is $1-p_x$, where
$p_x=\mathsf P_A\{M_{A,x}>m\}$, by the nonhandoff convention. Finite
execution transport gives one output submeasure $\rho_{x,m}$ on this
event, dominated by every $\widehat\lambda_{A,y}$ for $y\in H_m$.
Choose one fixed actual source in each occupied $D_n$, $n>m$; its
output probability completes $\rho_{x,m}$ within cap $\varepsilon$.
Theorem 80.1 gives $S_m(\varepsilon+p_x)\le\varepsilon$, so
$p_x\ge\beta_m(\varepsilon)$. This uses a whole measurable event and
fixed actual comparison sources; it makes no exact marked-output
certificate assumption.

For $p\in[0,1]$, equation (77.8) makes feasibility equivalent to

$$
\sum_{j=1}^k a_{m+j}\le(k+1)\varepsilon+kp
\quad\text{for every }k\ge1.
\tag{80.9}
$$

The resulting lower bound on $p$ is the second line of (80.6).
It is at most $a_{m+1}\le1$, and $p=1$ is feasible. The feasible set
is closed, since $S_m(\varepsilon+p)$ is a finite continuous sum on
$[0,1]$. Its infimum is consequently feasible and proves (80.6).
The case $p=0$ is feasible exactly when $S_m(\varepsilon)\le\varepsilon$,
equivalently $\varepsilon\ge R_m$ by Theorem 77.2.

For attainment fix this $m$ and take $p=\beta_m(\varepsilon)$ and the
submeasure and completions (80.3). Put
$L=\max(\{i:a_i>\varepsilon\}\cup\{0\})$. Initially query the first
$m$ primes in order, stopping at the first negative answer. If one occurs
at $n\le m$, hand a sample from the exact $\lambda_n$ and terminate.
If all these answers are positive, use a seed branch of probability
$1-p$ to sample $\rho/(1-p)$ and hand off, and a branch of probability
$p$ for the residual part. A zero-mass branch needs no normalized
probability and is omitted.

On the residual branch, read the consecutive indices $m+1,\ldots,L$,
stopping at the first absence $n$. If an absence is observed, sample
$\theta_n$ with probability $q_n/p$ and otherwise sample $\theta_0$.
If every index through $L$ is positive, emit $\theta_0$, since the actual
first absence then has $a_{n(x)}\le\varepsilon$ and $q_{n(x)}=0$.
When $p>0$, the zero-branch criterion fails, so $S_m(\varepsilon)>\varepsilon$;
in particular $L>m$ and this branch always requests an index above $m$.
When $p=0$, the common-probability sampler alone is used on $H_m$.

The branch choice and output samples are fixed finite probability tables
under coordinates of one common source-independent seed. They use only
the actual prefix answers, with no restart or removal of a failure event.
All records are finite measurable coordinate events, and both resources
are bounded by $\max\{m,L\}$ at every source and seed. At a source
in $H_m$ the law is exactly $\sigma_{n(x)}$ of (80.3), so its error is
at most $\varepsilon$. Its tail probability at this horizon is exactly
$p$. At a source outside $H_m$ the acquisition is exact and has
$M\le m$. This proves (80.8) and its stated attainment. $\square$

## 81. Nonjoint tails, the harmonic zero-query law and the diameter boundary

**Theorem 81.1 (Two individually optimal tails can be incompatible).** For

$$
a_1=a_2=1,\qquad a_n=1/n\quad(n\ge3),\qquad\varepsilon=1/4,
\tag{81.1}
$$

one has $\beta_0(\varepsilon)=5/8$ and
$\beta_1(\varepsilon)=1/2$. Each minimum in (80.8) is attained
individually, but no acquisition simultaneously satisfies

$$
\sup_x\mathsf P_A\{M_{A,x}>0\}=5/8,
\qquad
\sup_x\mathsf P_A\{M_{A,x}>1\}=1/2.
\tag{81.2}
$$

**Proof.** At $p=5/8$, $\varepsilon+p=7/8$ and
$S_0(7/8)=2(1-7/8)=1/4$. For a smaller $p$ the first two terms alone
exceed $1/4$. Thus (80.2) gives $\beta_0=5/8$. Similarly
$S_1(3/4)=1-3/4=1/4$, and a smaller $p<1/2$ makes its $n=2$ term
exceed $1/4$. Thus $\beta_1=1/2$. Individual attainment follows from
Theorem 80.2.

Suppose (81.2) held. The zero-request finite-handoff event and its
output submeasure $\rho_0$ are common to every actual source, since no
source answer has been used. Its mass must be $1-5/8=3/8$.
Theorem 80.1 at $m=0$ forces

$$
\rho_0(\Theta\setminus\{\theta_0\})\le1/4,
\qquad \rho_0(\{\theta_1\}),\rho_0(\{\theta_2\})\ge1/8.
\tag{81.3}
$$

The two required singleton masses exhaust the permitted mass outside
$\theta_0$, so in particular $\rho_0(\{\theta_1\})=1/8$.

Fix one actual $x\in H_1$. Inequality (80.7) and the second supremum
in (81.2) force its tail at horizon one to equal $1/2$. Its finite-handoff
output submeasure $\rho_1$ on $\{M_{A,x}\le1\}$ thus has mass $1/2$,
and transports to every actual source in $H_1$. Theorem 80.1 forces

$$
\rho_1(\Theta\setminus\{\theta_0\})\le1/4,
\qquad \rho_1(\{\theta_2\})\ge1/4.
\tag{81.4}
$$

Therefore $\rho_1(\{\theta_1\})=0$. But at this same fixed $x$ the
zero-request handoff event is contained in $\{M_{A,x}\le1\}$. Restricting
one output map to these nested seed events gives $\rho_0\le\rho_1$,
contradicting their masses at $\theta_1$. The obstruction is a common
execution constraint on nested output submeasures, not a change of
carrier or comparison source. $\square$

**Theorem 81.2 (Harmonic mean correction and equal diameters with unequal
centers).** For $a_n=1/n$, the unique optimal zero-query law is
$(\delta_{\theta_0}+\delta_{\theta_1})/2$, with uniform radius $R_0=1/2$.
At cap $\varepsilon=1/2$ the attained minimum uniform mean count is zero,
whereas $\sum_i(a_i-\varepsilon)_+=1/2$. For every positive cap, putting
$L=\max(\{i:1/i>\varepsilon\}\cup\{0\})$ and
$H_L=\sum_{i=1}^L1/i$, $H_0=0$, gives

$$
\min_{A\in\mathcal A_\varepsilon(a)}\sup_x\mathsf E_A K_{A,x}
=(H_L-(L+1)\varepsilon)_+<\infty.
\tag{81.5}
$$

The harmonic family and the family in (81.1) both have pairwise TV
diameter one on $X$, but their zero-query radii are respectively $1/2$
and $2/3$.

**Proof.** For the harmonic sequence,
$S_0(1/2)=(1-1/2)=1/2$, with all later summands zero. Theorem 77.2 gives
$R_0=1/2$ and the asserted unique law. Its distance to $\lambda_1$ is
$1/2$. For $n\ge2$, (77.7) gives distance
$\max\{1/2,1/n\}=1/2$, so its uniform error is exactly $1/2$ and it
requires no observations. Nonnegativity of request counts proves the
zero mean optimum, also given by Theorem 79.2. The proposed expression
$\sum_i(a_i-\varepsilon)_+$ without a collective allowance therefore
cannot be the approximate count optimum. Theorem 79.2 instead gives
(81.5), since $S_0(\varepsilon)=H_L-L\varepsilon$. At error zero the
existing exact harmonic identity (75.2) is infinite; the positive-error
formula does not change that endpoint.

For distinct $i,j$, direct comparison on the three relevant atoms gives
$\operatorname{TV}(\lambda_i,\lambda_j)=\max\{a_i,a_j\}$.
Both sequences have $a_1=1$, and their occupied $D_i$ realize this
diameter. For (81.1),
$S_0(2/3)=2(1-2/3)=2/3$ with no later positive term, so its radius is
$2/3$ by Theorem 77.2. Thus the diameter gives a necessary half-diameter
bound by the TV triangle inequality, but it does not determine the
multilaw center radius. $\square$

## 82. Original-carrier and resource applicability of the positive-error laws

**Theorem 82.1 (Measurable marked projection and original-target separation).**
Let $H=\{\theta_j:j\ge0\}$, and define $T:\Theta\to\Theta$ to fix every
point in $H$ and send every other original tape to $\theta_0$. Then $T$ is
measurable, fixes every selected $\lambda^a_x$ by pushforward, and for
every original-tape probability $\nu$,

$$
\operatorname{TV}(T_*\nu,\lambda^a_x)
\le\operatorname{TV}(\nu,\lambda^a_x).
\tag{82.1}
$$

Composing a lawful output map with $T$ preserves its request resources
and measurable finite handoff under the contract of Definition 71.1.
For every $A\in\mathcal A_\varepsilon(a)$, without any support
restriction on its output, the unchanged original targets obey

$$
\operatorname{TV}(\widehat\lambda_{A,x},\mu_x)\ge1-\varepsilon
\qquad(x\in X).
\tag{82.2}
$$

All explicit attaining acquisitions in Theorems 78.1, 79.2 and 80.2
instead have distance exactly one from every $\mu_x$. Their tapes remain
in $B_1$, on which the original consumer returns unknown.

**Proof.** The countable marked set and its singletons are Borel on the
original carrier (73.1). For a Borel tape event $E$, its inverse image
under $T$ is $E\cap H$ if $\theta_0\notin E$, and
$(E\cap H)\cup(\Theta\setminus H)$ if $\theta_0\in E$. These are
measurable sets, proving measurability. Since $T$ fixes the selected
support, $T_*\lambda^a_x=\lambda^a_x$. Pulling back each event in the
definition of TV proves (82.1). The output composition is a fixed
measurable terminal map, permitted by the common-rule semantics; it
adds no source observation or request and retains finite handoff.

Every selected $\lambda^a_x$ has $\lambda^a_x(H)=1$, so the cap in
(77.2) implies $\widehat\lambda_{A,x}(H)\ge1-\varepsilon$.
Every original $\mu_x$ of (67.18) is nonatomic, so $\mu_x(H)=0$.
The event $H$ proves (82.2). Each explicit attainer above is supported
on finitely many points of $H$ at every source, hence gives $H$ mass one;
the same event then gives TV exactly one. Those points are the unchanged
original tapes in $B_1$, proving the consumer assertion.
The projection does not fix $\mu_x$, and its selected-law contraction
provides no original-target reduction. $\square$

**Definition 82.2 (Resource and semantic range of the formulas).** The
center and common-subprobability statements concern the whole original
measurable carrier. Their explicit finite marked constructions do not
assert that every approximate competitor is atomic. The all-adaptive
mean identities (79.3) optimize uniform source suprema for this particular
marked family, and simultaneously attain nondecreasing cumulative-weight
means. They do not prescribe sourcewise minimum means or cumulative
optima for arbitrary selected families. The ceiling (78.1) is a maximum
requested index; its finite count attainers do not identify the optimum
deterministic count ceiling among arbitrary nonprefix rules. The minima
(80.8) concern each fixed maximum-index horizon; Theorem 81.1 excludes
a general simultaneous-tail inference. In particular these individual
minima are not a simultaneously attained maximum-charge moment formula.

All constructions use fixed real probability tables under one inherited
seed, and the actual source observations only. The request and numerical
charge statements impose no computability, effective cutoff, finite
description, arithmetic-time or transition-time bound. The exact
$\varepsilon=0$ resources and simultaneous address tails remain the
suppliers in Theorems 71.3, 73.2 and 74.1. Positive-error formulas here
use the finite-pattern supplier, whole-event transport and the
exactness-independent finite request forest together with the displayed
TV mass calculations; they concern (73.4), with no change to (67.18) or
to its required proposal row.

The cited TV overlap identity is a literature ingredient. The marked-family
centers, shared-allowance resource formulas and robust-tail bounds are
`repo-derived` deductions under these suppliers, with no literature-priority
claim.

## 追加锚（本行以下为增补区）


## 83. A complete finite query-tree criterion for positive-error hard counts

**Definition 83.1 (Hard request-count optimum and the active cube).** Retain
Definitions 71.1, 73.1 and 77.1, including the original labeled $X$, static
prime answers, zero advice, original tapes and consumer, and one
source-independent seed with a common deterministic rule after it is fixed.
The amplitudes satisfy (73.3). Define the extended integer

$$
\kappa_\varepsilon=
\inf\{k\in\mathbb N_0:\exists A\in\mathcal A_\varepsilon(a),\quad
       \mathsf P_A\{K_{A,x}\le k\}=1\text{ for every }x\in X\},
\qquad\inf\varnothing=\infty.
\tag{83.1}
$$

This bounds the number of actual requests, counting repetitions, and uses
the nonhandoff convention of Definition 71.2. It does not bound an address
index or an expectation. For $0<\varepsilon\le1$, put

$$
L=\max(\{i\ge1:a_i>\varepsilon\}\cup\{0\}),\qquad
Q=\{0,1\}^L,\qquad J=\{0,1,\ldots,L\}.
\tag{83.2}
$$

The integer $L$ is finite. For $b\in Q$ having a zero, let $n_L(b)$ be
its first zero and set

$$
\eta_b=(1-a_{n_L(b)})\delta_{\theta_0}
                +a_{n_L(b)}\delta_{\theta_{n_L(b)}}.
\qquad
\eta_{1^L}=\delta_{\theta_0}.
\tag{83.3}
$$

When $L=0$, the empty word is $1^L$ and is the only member of $Q$.
These are finite target vectors on the original marked points. In
particular $1^L$ is a finite answer pattern, not an additional infinite
all-positive source. Every pattern in $Q$, including every pattern with
several zeros, is retained.

**Definition 83.2 (One common distribution of executable finite trees).**
For $R\subseteq\{1,\ldots,L\}$ and $d\in\mathbb N_0$, let
$\mathcal T(R,0)$ consist of the leaves labeled by $J$. For $d>0$, let
$\mathcal T(R,d)$ consist of these leaves and all binary nodes

$$
(i,T_0,T_1),\qquad i\in R,\quad
T_0,T_1\in\mathcal T(R\setminus\{i\},d-1).
\tag{83.4}
$$

Thus $\mathcal T(\varnothing,d)$ contains only leaves. Write
$\mathcal T_{L,k}=\mathcal T(\{1,\ldots,L\},k)$. A tree asks coordinate
$i$ at its node and follows the edge labeled by the answer. Its leaf label
on $b$ is $T(b)\in J$, and that label means the original tape
$\theta_{T(b)}$. No index is repeated along a path, whose number of query
nodes is at most $k$. A finite scheme is a single probability vector
$(w_T)_{T\in\mathcal T_{L,k}}$, common to all $b$, with laws

$$
p_b(j)=\sum_{T\in\mathcal T_{L,k}}w_T\mathbf1_{\{T(b)=j\}},
\qquad
\nu_b=\sum_{j=0}^Lp_b(j)\delta_{\theta_j}.
\tag{83.5}
$$

It is feasible at cap $\varepsilon$ when
$\operatorname{TV}(\nu_b,\eta_b)\le\varepsilon$ for every $b\in Q$.
Separate choices of a distribution for each input are not finite schemes.

**Theorem 83.3 (Exact-cap equivalence with arbitrary-address acquisitions).**
For every $0<\varepsilon\le1$ and $k\in\mathbb N_0$, an acquisition in
$\mathcal A_\varepsilon(a)$ has $K_{A,x}\le k$ almost surely at every
actual source if and only if a feasible scheme on $\mathcal T_{L,k}$
exists. Necessity allows arbitrary adaptive addresses, repeated requests
and full-carrier output laws. Sufficiency gives an acquisition handing off
at every source and every seed, with

$$
K_{A,x}\le k,\qquad M_{A,x}\le L.
\tag{83.6}
$$

Consequently $\kappa_\varepsilon$ is the least feasible integer in
$\{0,\ldots,L\}$, and this least value is attained under the original
contract.

**Proof.** Define the finite marked projection on the original carrier by

$$
\pi_L(\theta)=
\begin{cases}
\theta_j,&\theta=\theta_j\text{ for some }1\le j\le L,\\
\theta_0,&\text{otherwise}.
\end{cases}
\tag{83.7}
$$

Its retained singleton fibers and their complement are Borel, so it is
measurable. For any two original-tape probabilities, pulling back events
gives

$$
\operatorname{TV}((\pi_L)_*\nu,(\pi_L)_*\lambda)
\le\operatorname{TV}(\nu,\lambda).
\tag{83.8}
$$

This is the finite coarsening of the projection method in Theorem 82.1.
It fixes $\lambda_n$ when $n\le L$ and sends $\lambda_n$ to
$\delta_{\theta_0}$ when $n>L$. If a probability $p$ is supported on
$\theta_0,\ldots,\theta_L$ and $n>L$, the already supplied overlap
identity (77.7) gives

$$
\operatorname{TV}(p,\lambda_n)=\max\{1-p(\{\theta_0\}),a_n\}.
\tag{83.9}
$$

Indeed its mass at $\theta_n$ is zero. This identity will transport the
finite all-one constraint back to the original tail targets.

Suppose first that $A$ is an original hard-$k$ competitor. All its
probabilities below use its unchanged seed law. Countability of $X$ and
the measurable finite-handoff sublevel events give a common event

$$
G=\bigcap_{x\in X}\{K_{A,x}\le k\},\qquad\mathsf P_A(G)=1.
\tag{83.10}
$$

No source-dependent seed conditioning is involved. For the common
high-address event $J_{A,k,m}$ of (74.4), the exactness-independent
finite-forest supplier (70.3)--(70.4) gives

$$
\gamma_m=\mathsf P_A(J_{A,k,m})\longrightarrow0.
\tag{83.11}
$$

To recall its applicable content, at a fixed seed the first $k$ requests
over all actual sources occupy at most $2^k-1$ binary query nodes.
Processing with no further request adds no node. Their maximum address
is finite; the countable union of measurable request-index events makes
$J_{A,k,m}$ measurable. This uses neither exact output laws nor a uniform
transition bound.

For each integer $m\ge L+1$ and each $b\in Q$, fix an actual source
$x_{b,m}$ whose answers are $b$ through $L$ and zero at every index
$L<i\le m$. Boundaries, Theorem 35.2 supplies these finite patterns.
The entire countable family is chosen independently of the seed. If $b$
has first zero $n\le L$, then $n(x_{b,m})=n$. If $b=1^L$, then
$n(x_{b,m})=L+1$. Hence in both cases

$$
(\pi_L)_*\lambda^a_{x_{b,m}}=\eta_b.
\tag{83.12}
$$

Let $T_{A,x}$ denote the number of transitions to handoff, with value
$\infty$ on nonhandoff. For each fixed $m$, the finite family
$(T_{A,x_{b,m}})_{b\in Q}$ is finite almost surely. Therefore a deterministic
integer $t_m$ can be chosen so that

$$
\max_{b\in Q}\mathsf P_A\{T_{A,x_{b,m}}>t_m\}\le1/m.
\tag{83.13}
$$

This choice is for that finite family only and asserts no uniform bound
on transition counts over $X$.

Construct a finite mathematical truncation of the common rule. For input
$b$, simulate at most $t_m$ transitions of $A$ with its original seed.
At a requested index $i\le L$ supply $b_i$; at $L<i\le m$ supply zero.
Stop with $\theta_0$ before an attempted address above $m$ or an attempted
$(k+1)$st simulated request, or if handoff has not occurred by $t_m$.
A simulated request is counted even if it repeats an index. At an original
handoff apply $\pi_L$ to its tape. This construction specifies a bounded
finite reply table and a truncation, not an execution at a postulated
infinite source. The fixed high-coordinate replies are used to extract a
finite tree; the acquisition constructed from that tree will issue only
its actual low-coordinate requests.

For completeness the finite output label $f_{s,m}(b)\in J$ of this
truncation is measurable in the seed $s$. For every consistent finite
request/answer word choose once an actual witness realizing its finite
pattern, using Theorem 35.2 and a fixed enumeration of $X$. Such words
form a countable set, and all these witnesses are chosen before seeds.
On the whole event of following a word, the original rule at its witness
has the same finite processing and answers, by Lemma 45.3. The record,
cutoff and retained singleton-output events are consequently measurable
finite-record events or countable unions of them. For $j\ge1$, the event
$f_{s,m}(b)=j$ is such a union of original handoff events with output
$\theta_j$; every remaining truncated outcome has label zero. Thus each
label event is measurable, including cutoffs. Since $Q$ is finite, the
joint map $s\mapsto(f_{s,m}(b))_{b\in Q}$ is measurable into the finite
set $J^Q$. No measurable equality diagonal on the unprojected tape carrier
is needed.

After freezing $s$, the truncation is one deterministic decision rule on
the complete cube $Q$. Between low-coordinate questions it has a unique
continuation: all high replies and all previously requested replies are
fixed. Contract these fixed-answer and repeated-query nodes. What remains
is a binary query tree with fresh labels in $\{1,\ldots,L\}$ and path
depth at most $k$, since there were at most $k$ simulated requests before
contraction. Every branch of this finite tree is covered by some $b\in Q$.
Thus $f_{s,m}$ is represented by a member of $\mathcal T_{L,k}$.
Choose one representing tree for each representable function in the
finite set $J^Q$. The preceding measurable function-valued map then
induces a measurable tree-valued map and a probability vector
$w^{(m)}$ on $\mathcal T_{L,k}$.

For each fixed $b$, couple the truncation with $A$ at the fixed actual
$x_{b,m}$ on the original seed space. On the whole measurable event

$$
G\cap\{T_{A,x_{b,m}}\le t_m\}\setminus J_{A,k,m}
\tag{83.14}
$$

the original execution makes at most $k$ requests, all at indices at most
$m$, and hands off by $t_m$. Its answers agree with the finite reply
table, so induction over its complete finite execution identifies the
truncated output with its projected original output. The complement of
(83.14) has probability at most $\gamma_m+1/m$. Event indicators for the
two projected outputs therefore differ in expectation by at most this
number. Using (83.8), (83.12), the original cap and the triangle inequality,
the law $\nu_b^{(m)}$ induced by $w^{(m)}$ satisfies

$$
\begin{aligned}
\operatorname{TV}\bigl(\nu_b^{(m)},
     (\pi_L)_*\widehat\lambda_{A,x_{b,m}}\bigr)
 &\le\gamma_m+1/m,\\
\operatorname{TV}(\nu_b^{(m)},\eta_b)
 &\le\varepsilon+\gamma_m+1/m.
\end{aligned}
\tag{83.15}
$$

All seed mass, including every cutoff outcome, is included in these laws.
The comparison sources are fixed actual sources, never functions of an
individual seed.

There are finitely many trees. Their probability simplex is compact:
successive subsequence selection for its finitely many coordinates gives
a subsequence of $w^{(m)}$ converging to a nonnegative vector $w$ of total
mass one. Each $p_b(j)$ in (83.5) is linear in this vector, and TV on the
finite marked carrier is a continuous finite sum. Letting $m$ tend to
infinity along that subsequence in (83.15) gives
$\operatorname{TV}(\nu_b,\eta_b)\le\varepsilon$ for every $b$.
The limit uses a single vector of weights for all inputs. In particular
it yields the exact cap, rather than only every larger cap. This proves
necessity for full-carrier, arbitrary-address competitors.

Conversely, sample a tree from the fixed weights $w_T$ with one
source-independent uniform seed, using half-open categorical intervals.
Run its node questions as actual requests to the primes $p_i$, and hand
the original tape at its leaf to the unchanged consumer. This is one
common seeded deterministic rule, with zero advice and no further source
observation. Every path is finite and satisfies (83.6). Records and outputs
are measurable finite unions of categorical seed intervals. At $x$ with
$n(x)\le L$, its actual low word has that first zero, and the finite cap
is precisely its selected-law cap. At $n(x)>L$, the word is $1^L$ and its
constraint is $1-p_{1^L}(0)\le\varepsilon$. Since $a_{n(x)}\le\varepsilon$,
(83.9) gives the original tail-target error at most $\varepsilon$.
Thus this is an original member of $\mathcal A_\varepsilon(a)$.

Finally a feasible scheme exists at $k=L$: query the low coordinates in
order until the first zero $n\le L$ and sample $\lambda_n$ there;
otherwise emit $\theta_0$. One common uniform coordinate can decide the
two-point sample for every possible $n$. Freezing that coordinate gives
a labeled depth-$L$ tree, so these samplers form a finite tree mixture.
At a tail source its error is $a_{n(x)}\le\varepsilon$. For $L=0$ the
rule is simply immediate $\theta_0$. The nonempty finite set of feasible
integers has a least member, attained by the preceding converse. $\square$

**Mathematical citation 83.4 (Decision trees and the actual-source bridge).**
Deterministic adaptive query trees, depth as worst path query count, and
randomized trees as distributions over deterministic trees are established
ingredients in Buhrman and de Wolf, [*Complexity Measures and Decision Tree
Complexity: A Survey*, Sections 3.1--3.2](https://homepages.cwi.nl/~rdewolf/publ/qc/dectree.pdf).
The finite input model is obtained here from actual-pattern realization
and the finite-request-forest and whole-event suppliers, not assumed for
$X$. The bidirectional full-carrier transport and exact positive-cap
attainment in Theorem 83.3 are `repo-derived` compositions of those
suppliers. The theorem preserves feasibility at $(k,\varepsilon)$; it does
not preserve an arbitrary competitor's output laws, mean resources or
address usage.

## 84. Explicit TV rows and a complete finite obstruction recurrence

**Theorem 84.1 (The finite row criterion for the original hard count).** Use
(83.2)--(83.5). For every $k\in\mathbb N_0$, $\kappa_\varepsilon\le k$
is equivalent to the following finite linear feasibility system:

$$
\begin{gathered}
w_T\ge0\quad(T\in\mathcal T_{L,k}),\qquad \sum_Tw_T=1,\\
p_b(0)\ge1-a_n-\varepsilon,\qquad
p_b(n)\ge a_n-\varepsilon,\qquad
p_b(0)+p_b(n)\ge1-\varepsilon
\quad\bigl(b\ne1^L,\ n=n_L(b)\bigr),\\
p_{1^L}(0)\ge1-\varepsilon.
\end{gathered}
\tag{84.1}
$$

All $2^L$ inputs occur in these rows. There are $3(2^L-1)+1$ TV rows;
a negative right side is permitted and requires no change of convention.

**Proof.** For a probability $p$ on $J$ and $n\le L$, the target's only
possible negative discrepancies occur at $0$ and $n$. The TV mass
calculation already used in (77.7) therefore gives

$$
\begin{aligned}
\operatorname{TV}\left(\sum_jp(j)\delta_{\theta_j},\lambda_n\right)
 &=(1-a_n-p(0))_++(a_n-p(n))_+\\
 &=\max\{0,\ 1-a_n-p(0),\ a_n-p(n),\ 1-p(0)-p(n)\}.
\end{aligned}
\tag{84.2}
$$

The second equality follows by considering whether neither, one, or both
of the two untruncated deficits are positive. Thus its cap is exactly the
three corresponding rows of (84.1). The distance to $\delta_{\theta_0}$
is $1-p(0)$, giving the last row. Definition 83.2 and Theorem 83.3 now
prove both implications. The whole-carrier necessity is furnished by
Theorem 83.3, not by assuming that the original competitor had finite
support. $\square$

**Definition 84.2 (Nonnegative row weights and depth values).** Let
$\mathcal R$ index the TV rows of (84.1). Write each row as
$p_{b_r}(H_r)\ge d_r$, where $H_r\subseteq J$ is respectively
$\{0\}$, $\{n\}$ or $\{0,n\}$ at a non-all-one input, and $\{0\}$
at the all-one input. For $\alpha=(\alpha_r)_{r\in\mathcal R}\ge0$ set

$$
c_{b,j}=\sum_{r:b_r=b}\alpha_r\mathbf1_{\{j\in H_r\}}.
\tag{84.3}
$$

A partial assignment $\tau$ fixes some subset of the $L$ coordinates;
let $Q(\tau)$ be its consistent inputs. Define

$$
V_0(\tau)=\max_{j\in J}\sum_{b\in Q(\tau)}c_{b,j},
\tag{84.4}
$$

and, for $d\ge1$, define

$$
V_d(\tau)=\max\left\{
V_0(\tau),\quad
\max_{i\notin\operatorname{dom}\tau}
 \left[V_{d-1}(\tau\cup\{i=0\})+
       V_{d-1}(\tau\cup\{i=1\})\right]\right\}.
\tag{84.5}
$$

When every coordinate is assigned the query maximum is omitted. In
particular all these quantities are obtained by a finite recurrence.

**Theorem 84.3 (Complete nonnegative obstructions to hard-count feasibility).**
For $0<\varepsilon\le1$ and $k\in\mathbb N_0$,

$$
\kappa_\varepsilon\le k
\quad\Longleftrightarrow\quad
\sum_{r\in\mathcal R}\alpha_rd_r\le V_k(\varnothing)
\quad\text{for every }\alpha\in[0,\infty)^{\mathcal R}.
\tag{84.6}
$$

If hard-$k$ feasibility fails, one finite nonnegative vector $\alpha$
satisfies the strict reverse inequality. Its value on the right is evaluated
by (84.4)--(84.5), and it obstructs every original arbitrary-address,
full-carrier hard-$k$ competitor.

**Proof.** For a tree $T$, let its row vector be
$v_T(r)=\mathbf1_{\{T(b_r)\in H_r\}}$. Its weighted row value is

$$
\alpha\cdot v_T=\sum_{b\in Q}c_{b,T(b)}.
\tag{84.7}
$$

On inputs consistent with $\tau$, a depth-zero tree must select a single
leaf label, whose optimum value is (84.4). A deeper tree either selects
such a leaf or requests an unassigned coordinate $i$. Its inputs then
split into the disjoint zero and one extensions of $\tau$, and either
child has remaining depth $d-1$. The two optimal child trees can be
chosen independently and attached to that root. Induction on $d$ proves

$$
V_k(\varnothing)=\max_{T\in\mathcal T_{L,k}}\alpha\cdot v_T.
\tag{84.8}
$$

Both children receive depth $d-1$. The recurrence bounds the number of
requests on a path, rather than the sum of the numbers of nodes in the
children, a prefix depth, or the greatest coordinate queried.

Let $C=\operatorname{conv}\{v_T:T\in\mathcal T_{L,k}\}$ and
$U=C-\mathbb R_+^{\mathcal R}$. A mixture satisfying all rows exists
exactly when $d=(d_r)_r\in U$. The convex hull $C$ is compact and $U$
is closed: if $v_m-z_m\to u$ with $v_m\in C$ and $z_m\ge0$, a
subsequence has $v_m\to v\in C$, and then $z_m\to v-u\ge0$.
If $d\in U$, every nonnegative $\alpha$ has
$\alpha\cdot d\le\max_T\alpha\cdot v_T$, proving the forward
implication using (84.8).

If $d\notin U$, choose a nearest point $u\in U$. It exists since a
minimizing sequence for distance to $d$ can be restricted to a closed
bounded ball in a finite-dimensional space, and $U$ is closed. Set
$\alpha=d-u\ne0$. For every $z\in U$, the segment from $u$ to $z$
is in $U$. Minimality of $u$ applied to
$\|d-u-t(z-u)\|^2$ for $t\downarrow0$ gives

$$
\alpha\cdot(z-u)\le0.
\tag{84.9}
$$

Since $u-te_r\in U$ for every $t\ge0$, (84.9) implies
$\alpha_r\ge0$ for every row. For such a vector subtraction of a
nonnegative vector cannot increase the scalar product, so
$\sup_{z\in U}\alpha\cdot z=\max_{v\in C}\alpha\cdot v$.
Equation (84.9) says this supremum is $\alpha\cdot u$, and hence

$$
\alpha\cdot d
=\alpha\cdot u+\|\alpha\|^2
>\max_T\alpha\cdot v_T
=V_k(\varnothing).
\tag{84.10}
$$

This gives the strict obstruction and proves the reverse implication of
(84.6), including equality cases in every row. Theorem 83.3 transfers
this exact finite alternative to the original class. $\square$

**Mathematical citation 84.4 (TV and convex ingredients).** The finite
partition and overlap identity in (84.2) uses the TV ingredients credited
in (77.7): Levin and Peres, with Wilmer, [*Markov Chains and Mixing Times*,
second edition, Chapter 4, Proposition 4.2, Remark 4.3 and equation
(4.13)](https://pages.uoregon.edu/dlevin/MARKOV/mcmt2e.pdf).
Finite convex hulls and separating hyperplanes are mature ingredients;
see Boyd and Vandenberghe, [*Convex Optimization*, Section
2.5.1](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf).
The nearest-point argument above proves the needed separation directly.
The rows, tree recurrence and their exact applicability to the original
marked-source hard-count problem form a `repo-derived` composition;
these citations carry no literature-priority claim for that composition.

## 85. An output-conditioned obstruction using actual comparison sources

**Theorem 85.1 (Hard count bounds the mass of a late correct mark).** Fix
$0\le\varepsilon\le1$ and $k\in\mathbb N_0$. If
$A\in\mathcal A_\varepsilon(a)$ and $K_{A,x}\le k$ almost surely at
every actual $x$, then for every integer $n>k$,

$$
(n-k)(a_n-\varepsilon)_+\le n\varepsilon.
\tag{85.1}
$$

The acquisition may use arbitrary adaptive addresses and may output on
the entire original carrier.

**Proof.** Fix an actual $x\in D_n$. For each integer $m\ge n$, choose
actual sources $y_{i,m}$, $1\le i\le n$, whose answers through $m$
match those of $x$ except that coordinate $i$ is flipped. These finite
patterns are realized by Theorem 35.2, and the sources are fixed before
using any seed. For $i<n$ their first absence is $i$. For $i=n$, all
coordinates through $n$ are positive, so their first absence is greater
than $n$, and is finite by finite prime support. In every case

$$
\lambda^a_{y_{i,m}}(\{\theta_n\})=0,\qquad
\mathsf P_A\{\text{finite output at }y_{i,m}\text{ is }\theta_n\}
\le\varepsilon.
\tag{85.2}
$$

Let $E_m$ be the measurable event of finite output $\theta_n$ at $x$
with at most $k$ requests, outside $J_{A,k,m}$. The cap at $x$ on that
singleton, together with the hard bound, gives

$$
\mathsf P_A(E_m)\ge(a_n-\varepsilon)_+
                         -\mathsf P_A(J_{A,k,m}).
\tag{85.3}
$$

On $E_m$ all requested indices are at most $m$, and at least $n-k$ of
the first $n$ coordinates have not been requested. Write $U_i$ for the
measurable event that index $i$ is unrequested in this finite execution.
On the whole event $E_m\cap U_i$, every requested answer agrees at
$y_{i,m}$. Finite execution transport, with the same seed and zero
advice, therefore hands the same $\theta_n$ there. In particular
$E_m\cap U_i$ is contained in the corresponding output event of
(85.2). Counting the unrequested coordinates on each seed and summing
these event inclusions yields

$$
(n-k)\mathsf P_A(E_m)
\le\sum_{i=1}^n\mathsf P_A(E_m\cap U_i)
\le\sum_{i=1}^n\mathsf P_A\{\text{output at }y_{i,m}\text{ is }\theta_n\}
\le n\varepsilon.
\tag{85.4}
$$

The common finite-forest probability tends to zero as $m\to\infty$.
Combining (85.3)--(85.4) proves (85.1). This comparison concerns one
fixed actual $x$ and, at each $m$, a fixed finite actual comparison family.
It counts whole seed events on which a correct output was made; it never
selects a comparison source depending on an individual seed. $\square$

## 86. Exact hard counts with two active amplitudes

**Theorem 86.1 (Unequal two-amplitude classification and lawful attainers).**
Suppose

$$
a_3\le\varepsilon<a_2\le a_1\le1.
\tag{86.1}
$$

Thus $L=2$, with the positive monotone vanishing tail retained. Then

$$
\kappa_\varepsilon=
\begin{cases}
0,&a_1+a_2\le3\varepsilon,\\
1,&a_1+a_2>3\varepsilon\text{ and }a_2\le3\varepsilon,\\
2,&a_2>3\varepsilon.
\end{cases}
\tag{86.2}
$$

Every case has an everywhere-finite common-seed attainer on the original
tapes. The supplied maximum-address optimum (78.1) specializes to

$$
h_\varepsilon=
\begin{cases}
0,&a_1+a_2\le3\varepsilon,\\
1,&a_1+a_2>3\varepsilon\text{ and }a_2\le2\varepsilon,\\
2,&a_2>2\varepsilon.
\end{cases}
\tag{86.3}
$$

In particular $2\varepsilon<a_2\le3\varepsilon$ gives
$\kappa_\varepsilon=1<h_\varepsilon=2$.

**Proof.** A zero-request acquisition produces one common output law at
all sources. The existing full-carrier center criterion, Theorem 77.2
with $m=0$, makes it feasible exactly when

$$
S_0(\varepsilon)=(a_1-\varepsilon)+(a_2-\varepsilon)
\le\varepsilon,
\tag{86.4}
$$

which is the first condition in (86.2). In that case an explicit immediate
sampler uses masses $a_1-\varepsilon$ and $a_2-\varepsilon$ on
$\theta_1$ and $\theta_2$, and the remaining mass on $\theta_0$.
Its coefficients are nonnegative, since their marked sum is at most
$\varepsilon<1$; Theorem 77.2 supplies its cap for every original source.

Theorem 85.1 at $n=2,k=1$ makes
$a_2-\varepsilon\le2\varepsilon$ necessary for hard one-request
feasibility, because $a_2>\varepsilon$. Thus $a_2\le3\varepsilon$
is necessary, with no address or output-support restriction on the
competitor. The finite obstruction can also be read directly from
Theorem 84.3. Give unit multipliers to the rows $p_{10}(2)\ge
 a_2-\varepsilon$, $p_{00}(\{0,1\})\ge1-\varepsilon$, and
$p_{11}(0)\ge1-\varepsilon$, and zero to every other row. Their right
sides sum to $a_2+2-3\varepsilon$. A depth-one tree has weighted value
at most two: a query to coordinate $1$ gives the same output at $10$ and
$11$, so their first and third row indicators cannot both be one;
a query to coordinate $2$ gives the same output at $00$ and $10$, so
their first and second indicators cannot both be one. Constant trees
satisfy the same bound, and constant output zero attains two. Thus
$V_1(\varnothing)=2$, with strict obstruction exactly when
$a_2>3\varepsilon$.

For sufficiency at this threshold, use one source-independent categorical
seed to mix the following four deterministic trees. A pair of entries
in the output column gives the zero-answer output followed by the
one-answer output.

| Tree | Requested index | Output labels | Weight |
| --- | --- | --- | --- |
| $T_1$ | $1$ | $(1,2)$ | $a_2/3$ |
| $T_2$ | $1$ | $(1,0)$ | $a_1-2a_2/3$ |
| $T_3$ | $2$ | $(2,0)$ | $a_2/3$ |
| $T_0$ | none | $0$ | $1-a_1$ |

All weights are nonnegative and sum to one, using $a_1\ge a_2$.
Each queried branch hands off after one actual request; the constant
branch hands off immediately. With columns ordered as
$(\theta_0,\theta_1,\theta_2)$, the resulting complete law table is

$$
\begin{array}{c|ccc}
b&p_b(0)&p_b(1)&p_b(2)\\\hline
00&1-a_1&a_1-a_2/3&a_2/3\\
01&1-a_1+a_2/3&a_1-a_2/3&0\\
10&1-2a_2/3&0&2a_2/3\\
11&1-a_2/3&0&a_2/3
\end{array}
\tag{86.5}
$$

At $00$, the mass $a_2/3$ missing from the correct mark $\theta_1$
is placed at $\theta_2$, while the base mass is exact. The TV error is
$a_2/3$. At $01$ the same deficit is instead placed at the base, again
with error $a_2/3$. At $10$, the correct mark $\theta_2$ has mass
$2a_2/3$ against target mass $a_2$, so the error is $a_2/3$.
For every actual source with low word $11$, its first absence exceeds
$2$ and its output law has error
$\max\{a_2/3,a_{n(x)}\}$ by (83.9). This is at most $\varepsilon$
when $a_2\le3\varepsilon$ and $a_3\le\varepsilon$. Thus the same
common scheme meets the original cap on every source.

Finally two requests suffice at all parameters in (86.1): query $p_1$,
and on a positive answer query $p_2$; at the first zero sample the exact
$\lambda_n$, and on two positives emit $\theta_0$. Use another
coordinate of the same source-independent seed for the two-point sample.
The tail error is at most $a_3\le\varepsilon$, and every branch hands
off. Combining this upper bound, the one-request obstruction, and the
reused zero-request criterion proves all cases of (86.2).

For (86.3), directly apply the existing address criterion (78.1) to
$S_0(\varepsilon)=a_1+a_2-2\varepsilon$,
$S_1(\varepsilon)=a_2-\varepsilon$, and $S_2(\varepsilon)=0$.
If $a_2>2\varepsilon$, monotonicity also gives
$a_1+a_2\ge2a_2>3\varepsilon$, so the listed cases are exhaustive.
In the stated strict separation interval the same observation excludes
the zero-request case of (86.2). $\square$

**Corollary 86.2 (Equal leading amplitudes and strict resource separations).**
If $a_1=a_2=s\in(0,1]$ and $a_3\le\varepsilon$, then

$$
\begin{aligned}
\kappa_\varepsilon&=
\begin{cases}
0,&\varepsilon\ge2s/3,\\
1,&s/3\le\varepsilon<2s/3,\\
2,&0<\varepsilon<s/3,
\end{cases}\\
h_\varepsilon&=
\begin{cases}
0,&\varepsilon\ge2s/3,\\
1,&s/2\le\varepsilon<2s/3,\\
2,&0<\varepsilon<s/2.
\end{cases}
\end{aligned}
\tag{86.6}
$$

An unequal-amplitude example is

$$
a_1=1,\quad a_2=3/4,\quad
 a_n=\frac1{4(n-2)}\ (n\ge3),\quad\varepsilon=1/4:
\qquad\kappa_\varepsilon=1<h_\varepsilon=2.
\tag{86.7}
$$

A separate example distinguishes the hard count from the ceiling of the
optimal uniform mean:

$$
a_1=a_2=3/4,\quad
 a_n=\frac1{5(n-2)}\ (n\ge3),\quad\varepsilon=1/5:
\qquad D=9/10,\quad\lceil D\rceil=1<\kappa_\varepsilon=2.
\tag{86.8}
$$

**Proof.** If $\varepsilon<s$, (86.1) holds and (86.6) is the
specialization of Theorem 86.1. If $\varepsilon\ge s$, immediate
$\theta_0$ has error at most $s$, so both hard optima are zero as in
the displayed formulas. In (86.7), $L=2$, $a_2=3\varepsilon$ and
$a_2>2\varepsilon$, while $a_1+a_2>3\varepsilon$, proving its two
values. In (86.8), $L=2$ and $a_2>3\varepsilon$, so Theorem 86.1
forces hard count two. The mean formula is exactly the supplier (79.3):
its only positive residuals are $a_1-\varepsilon=a_2-\varepsilon=11/20$,
whence $D=2(11/20)-1/5=9/10$. Thus neither the supplied address optimum
nor integer rounding of the supplied mean optimum identifies the hard
request count. $\square$

## 87. Unit leading plateaus and unbounded address-to-count ratios

**Theorem 87.1 (Exact hard count on a unit plateau).** Suppose $\ell\ge1$,

$$
a_1=\cdots=a_\ell=1,\qquad
 a_{\ell+1}\le\varepsilon<1.
\tag{87.1}
$$

The tail continues to satisfy (73.3); in particular $\varepsilon>0$.
Then

$$
\kappa_\varepsilon=
\max\{0,\lceil\ell-(\ell+1)\varepsilon\rceil\}.
\tag{87.2}
$$

For each $k\in\{0,\ldots,\ell\}$, an original common-seed acquisition
with $K\le k$ everywhere has error

$$
e_k=\frac{\ell-k}{\ell+1}
\tag{87.3}
$$

at every source in $D_1\cup\cdots\cup D_\ell$, and error
$\max\{e_k,a_{n(x)}\}$ at every source in $H_\ell$.
Its count is exactly $k$ on $H_\ell$ for every seed.

**Proof.** The supplied mean theorem (79.3) gives

$$
D=\bigl(\ell(1-\varepsilon)-\varepsilon\bigr)_+
  =\bigl(\ell-(\ell+1)\varepsilon\bigr)_+,
\tag{87.4}
$$

since every tail residual is zero. Any sourcewise almost-sure hard-$k$
competitor has $\sup_x\mathsf E_AK_{A,x}\le k$, and thus $k\ge D$.
Its integer count must be at least the right side of (87.2).

For the matching upper bound, order the finite label set as
$1<\cdots<\ell<\ast$, where label $\ast$ means tape $\theta_0$.
Use one source-independent categorical seed to choose uniformly a subset
$C$ of $k+1$ labels. Query its first $k$ labels in increasing order,
stopping at the first zero and emitting the tape of that queried label.
If all $k$ answers are positive, emit the tape of the maximum label in
$C$, without querying that last label. The label $\ast$ is always last
when it is present, so it is never queried. This includes $k=0$, when
the sole chosen label is emitted without a request. Every branch is finite,
uses at most $k$ actual prime requests, and has indices at most $\ell$.
The records are measurable categorical seed events.

At an actual source with first absence $n\le\ell$, the output is
$\theta_n$ exactly when $n\in C$. To prove the forward assertion, if
$n$ is among the queried labels, every preceding selected label is less
than $n$ and has positive answer, and the query at $n$ stops with its
tape. If $n$ is the final unqueried label, all queried labels are less
than $n$ and positive, and the final emission is again $\theta_n$.
For the converse, if $n\notin C$, every possible emitted label belongs
to $C$ and therefore cannot be $n$, regardless of all suffix answers.
Uniform subsets of size $k+1$ include each particular label with
probability

$$
\frac{\binom{\ell}{k}}{\binom{\ell+1}{k+1}}
=\frac{k+1}{\ell+1}.
\tag{87.5}
$$

Here the target is $\lambda_n=\delta_{\theta_n}$, so its TV error is
one minus this probability, exactly $e_k$.

At any actual source in $H_\ell$, all queried numerical labels have
positive answers and all $k$ requests are made. The output is
$\theta_0$ exactly when $\ast\in C$, also with probability
$(k+1)/(\ell+1)$. No tail mark can be emitted. Equation (83.9) thus
gives error $\max\{e_k,a_{n(x)}\}$. This calculation concerns every
actual tail source, not an added source representing the label $\ast$.

Choose the least integer $k\ge0$ with $e_k\le\varepsilon$; it is at
most $\ell$ and equals the right side of (87.2). Since every tail
amplitude is at most $\varepsilon$, the constructed acquisition belongs
to $\mathcal A_\varepsilon(a)$ and attains this hard count. $\square$

**Corollary 87.2 (Unbounded separation of the optimal hard resources).**
Under (87.1), the supplied address formula is

$$
h_\varepsilon=
\max\left\{0,\left\lceil\ell-
              \frac{\varepsilon}{1-\varepsilon}\right\rceil\right\}.
\tag{87.6}
$$

For every $\ell\ge2$, take

$$
\varepsilon=\frac{\ell-1}{\ell+1},\qquad
 a_1=\cdots=a_\ell=1,\qquad
 a_{\ell+j}=\frac{\varepsilon}{j}\quad(j\ge1).
\tag{87.7}
$$

These are actual-source marked families with

$$
\kappa_\varepsilon=1,\qquad
 h_\varepsilon=\left\lceil\frac{\ell+1}{2}\right\rceil.
\tag{87.8}
$$

In particular $h_\varepsilon/\kappa_\varepsilon$ is unbounded over
this family.

**Proof.** For $0\le m\le\ell$,
$S_m(\varepsilon)=(\ell-m)(1-\varepsilon)$. Its inequality
$S_m(\varepsilon)\le\varepsilon$ is equivalent to
$m\ge\ell-\varepsilon/(1-\varepsilon)$. Apply (78.1), restricting
to nonnegative integer $m$; $m=\ell$ is feasible. This proves (87.6)
as a specialization of the existing address theorem. The sequence in
(87.7) is positive, nonincreasing and vanishes along its tail, so (73.3)
holds. Equation (87.2) gives count one because
$\ell-(\ell+1)\varepsilon=1$. In (87.6) the ratio
$\varepsilon/(1-\varepsilon)=(\ell-1)/2$, giving (87.8).
Its address value tends to infinity while its count value stays one.
The comparison is between two separately optimized hard resources;
it does not identify a query count with the address of that query.
$\square$

## 88. A multiple-zero source defeats a restricted pattern criterion

**Proposition 88.1 (Single-zero and all-one tests are insufficient).** Use
the sequence and cap in (86.8). There is a lawful hard-one-request rule
whose error is at most $1/5$ at every actual source with low word $01$,
$10$ or $11$, but whose error is $1/2$ at an actual source with low
word $00$. Consequently these three pattern classes cannot replace the
complete cube in Theorems 83.3 and 84.1.

**Proof.** Choose $p_1$ or $p_2$ with equal probabilities under a single
source-independent seed. A zero answer emits the corresponding mark
$\theta_i$. A one answer emits the other mark with conditional
probability $1/10$ and otherwise emits $\theta_0$. These choices can
be coordinates of one product seed, or four fixed categorical intervals
of lengths $1/20,9/20,1/20,9/20$ specifying the requested index and the
positive-answer output. No seed is reset or conditioned away.
Every branch makes exactly one actual request and hands off an original
tape, and all its records are measurable finite categorical events.

The complete output table, with the same column order as (86.5), is

$$
\begin{array}{c|ccc}
b&p_b(0)&p_b(1)&p_b(2)\\\hline
00&0&1/2&1/2\\
01&9/20&11/20&0\\
10&9/20&0&11/20\\
11&9/10&1/20&1/20
\end{array}
\tag{88.1}
$$

At $01$ the selected target is
$(1/4)\delta_{\theta_0}+(3/4)\delta_{\theta_1}$, and the missing
$1/5$ at the correct mark is added at the base. Thus TV is $1/5$.
At $10$ the same calculation with $\theta_2$ gives $1/5$.
At every actual source with word $11$, its first absence is $n>2$;
(83.9) gives error $\max\{1/10,a_n\}\le1/5$ for the last row.
The last calculation covers all actual tail targets in that pattern
class, rather than just the abstract target $\delta_{\theta_0}$.
At $00$ the target is again $\lambda_1$, while the first row has deficits
$1/4$ at the base and $1/4$ at $\theta_1$. The sum of these deficits
is $1/2$, which is its TV error by (84.2).

The missing pattern is actually occupied, with a small explicit label.
The prime index $r=11$ has $F_{11}=89$ and permitted window
$9\le g\le17$. For $x=(11,12)$,

$$
N(x)=1+89\cdot12=1069,
\qquad 2\nmid1069,\quad3\nmid1069.
\tag{88.2}
$$

Hence $q_1=q_2=0$ and $n(x)=1$, proving the claimed actual-source
failure. The other words are actual too: $(7,2)$ is allowed since
$F_7=13$ and its window is $\{2\}$, and its value $27$ has word $01$;
$(11,9)$ has value $802$ and word $10$; $(11,13)$ has value $1158$
and word $11$. The source labels are fixed, with static prime answers,
zero advice and the same seed law in all four comparisons. The failure
therefore comes from omitting a joint answer pattern, not from adding an
unrealizable source or an observation outside the contract. $\square$

## 89. Endpoints and the precise range of the finite characterization

**Proposition 89.1 (Zero error and original-target boundaries).** For the
strictly positive sequence (73.3), $\kappa_0=\infty$, although exact
lawful acquisitions exist. At $\varepsilon=1$, and more generally whenever
$L=0$ in (83.2), $\kappa_\varepsilon=0$. Every finite marked acquisition
constructed in Sections 83, 86 and 87 has TV distance one from each
unchanged original nonatomic target $\mu_x$ of Theorem 67.5, and the
unchanged consumer returns unknown on its handed tapes.

**Proof.** If an exact acquisition had a finite hard bound $k$, choose
any actual $x\in D_{k+1}$. The exact certificate (73.7), Theorem 73.3,
would give
$\mathsf P_A\{K_{A,x}\ge k+1\}\ge a_{k+1}>0$, a contradiction.
Theorem 73.2 already supplies exact lawful acquisitions with sourcewise
finite handoff, so this is an obstruction to a uniform hard count, not to
exact acquisition. If $L=0$, every $a_n\le\varepsilon$ and immediate
$\theta_0$ has error $a_{n(x)}\le\varepsilon$ at each source. This
includes $\varepsilon=1$.

Every constructed finite scheme outputs only the original marked points
in $B_1$. The countable Borel set $H=\{\theta_j:j\ge0\}$ has full
mass under each of these output laws and zero mass under every nonatomic
$\mu_x$. The same event argument as Theorems 76.1 and 82.1 gives TV
one. The consumer's definition on $B_1$ gives its unknown output.
Thus these selected-law attainers supply no cap below one for the original
nonatomic targets and do not supply their positive-proposal row.
$\square$

**Definition 89.2 (Quantifiers, suppliers and remaining classification).**
The criterion (84.1), equivalently (84.6), characterizes the existence of
an original acquisition at every prescribed positive cap and finite hard
count. The error is a uniform supremum over all actual sources. The hard
bound is sourcewise almost sure; countability permits its common full-measure
seed event. The finite attainers satisfy the stronger bound at every source
and every seed. No probability distribution on $X$ is introduced.
The full cube records low answers of actual sources; it does not restrict
their high prime support or supply those low answers without requests.
Finite trees encode adaptive pathwise counts and common seeded outputs,
rather than independent marginal decisions or unrestricted leaf covers.

The centers (77.4)--(77.6), address ceiling (78.1), and mean optimum
$D$ in (79.3) retain their original statements and roles. Theorem 86.1
and Theorem 87.1 use them as suppliers and add hard-count conclusions;
(86.7)--(86.8) separate the three resources. Actual finite-pattern
realization remains Boundaries, Theorem 35.2; common whole-event transport
remains Source-Correlated Laws, Lemma 45.3; the common high-address
probability remains (70.3)--(70.4) and (74.4). The mature finite decision-tree,
TV and convex ingredients are credited in 83.4 and 84.4. The source-specific
compositions and restricted count regimes are `repo-derived` deductions,
with no literature-priority assertion.

The finite characterization is exact for real amplitudes and real
probability weights. It asserts no effective discovery of $L$, finite
arithmetic precision for the weights, efficient optimization, transition-time
bound, or physical-time bound. The truncation times in the necessity proof
are mathematical comparison bounds for finite families, not a common
stopping-time promise on the original competitor. A general analytic
closed expression for $\kappa_\varepsilon$ at arbitrary monotone amplitudes
remains a further classification problem; the complete finite criterion
and the two restricted scalar regimes do not assert such an expression.
The original nonatomic-target problem of Theorem 67.5 is unchanged.

## 追加锚（本行以下为增补区）
