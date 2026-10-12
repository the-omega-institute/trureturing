# Stopped-episode calibration unidentifiability on the original common-depth source

## 1. Source, complete forecasts and information access

**Assumption 1.1 (the original source).** Fix any finite or countable
probability prior $\mu$ on positive integers with $\mu(1),\mu(2)>0$.
The original source parameters are $(m,d,\ell,n)=(2,1,2,4)$.
Before the first paid Read, draw one $K\sim\mu$. Conditional on this same
$K=k$, all seed and payload Reads are independent, with alpha probability
$r_k=F_{k+1}/F_{k+3}$, where $F_0=0,F_1=1$. In particular

$$
a=\frac13\le r_k\le\frac25=b,\qquad
r_k(1-r_k)\le\frac6{25}.
\tag{1.1}
$$

Use the entire original finite control $C_0$, writer and event blocks of
[PAIR, §2; PAID, Definitions 1.1–1.3; NATIVE-STATE;
NATIVE-EVENTS]. Equal seed pairs are rejected with both Reads paid;
alpha-beta accepts seed 0 and beta-alpha accepts seed 1. At payload p,
alpha completes marker 0 and beta suspends. At suspension, alpha returns
to p and beta completes marker 1. The first three completions advance
segments. The third completion writes its complete record before its
latch. Fourth completion enters the matching pendingStop; its sole
matching Stop enters deliveredStop. Neither terminal admits Read.

All seeds, marker words, original bare and held $B,Q^+,Z$ records,
selectors, parser, write/latch flags, permissions and delivery events
are retained. Every positive finite rejection history, partial parse and
finite return remains legal. The kernel named $B$ below is unrelated to
the held record also named $B$. All originally supported depths remain
supported targets; no target restriction is imposed by the constructions.

**Definition 1.2 (complete carriers and descriptor spaces).** Reuse the
complete-law spaces of [PAIR, §11.1; REPAIR, Definition 1.2]. Explicitly,
with $\lambda=4/15$, let

$$
\begin{aligned}
w_{j,0}&=(\beta\alpha)^j\alpha,&
w_{j,1}&=(\beta\alpha)^j\beta\beta,\\
\Omega_p&=\{w_{j,t}:j\ge0,\ t=0,1\}\cup\{\infty_p\},\\
\Omega_\beta&=\{\beta\}\cup\{\alpha w_{j,t}:j\ge0,\ t=0,1\}
                 \cup\{\infty_\beta\},\\
T_p(j)&=\{w_{h,t}:h\ge j,\ t=0,1\}\cup\{\infty_p\},\\
T_\beta(j)&=\{\alpha w_{h,t}:h\ge j,\ t=0,1\}\cup\{\infty_\beta\}.
\end{aligned}
\tag{1.2}
$$

All subsets are measurable, TV is half the countable $\ell^1$ distance,
and

$$
\begin{aligned}
\mathcal K_p&=\{Q\in\operatorname{Prob}(\Omega_p):
 a\le Q(\alpha)\le b,\ Q(T_p(j))\le\lambda^j\ (j\ge0)\},\\
\mathcal K_\beta&=\{W\in\operatorname{Prob}(\Omega_\beta):
 a\le1-W(\beta)\le b,\ W(T_\beta(j))\le b\lambda^j\ (j\ge0)\}.
\end{aligned}
\tag{1.3}
$$

Prefixing includes the infinite outcomes. Write

$$
\mathcal R_B(Q)(E)=\frac{Q(\beta E)}{1-Q(\alpha)},\qquad
\mathcal R_A(W)(E)=\frac{W(\alpha E)}{1-W(\beta)}.
\tag{1.4}
$$

At current original record $c_0$, the supplied injective renderer $I_{c_0}$
retains all future letters, inserts their original operation/event blocks
and retains completion, matching Stop and infinite noncompletion. Its
inverse reads back the letters. Thus it preserves TV and commutes with
residual deletion [PAID, Definition 1.2 and Lemma 2.1.1; NATIVE-EVENTS].
Private predictor labels are not reported fields of this original future.

**Definition 1.3 (a forecast audit, distinct from own generation).** An
actual observer is the finite COMPLETE same-update observer of [PAID,
Definition 1.3]. Its actual acquired updates and synthetic decoder updates
are identical; its actual own decoder at configuration $z$ is denoted
$D_z^{\mathrm{own}}$. Separately, a supplied candidate forecast associates
a complete law $\widetilde D_z$ to each returned original operation cut.
A candidate need not be the observer's own law. Auditing that equality is
the statistical task here; the candidate is not substituted into the
observer's definition of its true decoder.

For distinct phase descriptors $Q_i,W_j$, supplied rows $\pi,\tau$ and
actual kernels $B,A$, define the acquired descriptor edges

$$
G_B=\sum_{i,j}\pi_iB_{ij}\delta_{(Q_i,W_j)},\qquad
G_A=\sum_{j,i}\tau_jA_{ji}\delta_{(W_j,Q_i)}.
\tag{1.5}
$$

Their defects are exactly the full-descriptor-conditioned quantities of
[REPAIR, (2.3)]:

$$
e_B=\sum_i\pi_i\operatorname{TV}
       \left(\mathcal R_B(Q_i),\sum_jB_{ij}W_j\right),\qquad
e_A=\sum_j\tau_j\operatorname{TV}
       \left(\mathcal R_A(W_j),\sum_iA_{ji}Q_i\right).
\tag{1.6}
$$

The norm precedes the outgoing-descriptor average. These are analytical
functionals of the actual edge laws, not supplied samples of those laws.

## 2. A rational family with two exact cancellations

**Definition 2.1 (installed hypotheses and common supplied data).** For
an integer $M\ge1$, put $N=4M$ and

$$
X=\{0,\ldots,N-1\},\quad Y=\{-1,+1\},\quad
\pi_i=\frac1N,\quad\tau_j=\frac12,\quad
c=\frac{11}{30},\quad t=c(1-c)=\frac{209}{900}.
\tag{2.1}
$$

The emissions and the known opposite-direction kernel are

$$
u_i=\frac13+\frac{i+1}{15(N+1)},\qquad
v_{-1}=a,\quad v_{+1}=b,\qquad A_{ji}=\frac1N.
\tag{2.2}
$$

Let $s=(1,-1,-1,1)$. The null hypothesis, indexed by $0$, has
$B^0_{ij}=1/2$. Each alternative is a *fixed* installed observer indexed
by $\xi\in\{-1,+1\}^M$, with

$$
\sigma_{4g+h}=\xi_gs_h\quad(0\le g<M,\ 0\le h<4),\qquad
B^\xi_{ij}=\frac12+\frac{j\sigma_i}{4}.
\tag{2.3}
$$

The signs are immutable installed data. The observer does not draw
$\xi$ during its operation. A mixture over these hypotheses will be a
statistical comparison of fixed devices, not additional source draws.

Let $P=P_{p,c}$ be the normalized native-form law

$$
P(w_{n,0})=ct^n,\qquad P(w_{n,1})=(1-c)^2t^n,\qquad P(\infty_p)=0.
\tag{2.4}
$$

The common candidate descriptors are

$$
\begin{aligned}
W_j&=(1-v_j)\delta_\beta+v_j\alpha P,\\
\overline W&=\tfrac12(W_{-1}+W_{+1})
             =(1-c)\delta_\beta+c\alpha P,\\
Q_i&=u_i\delta_\alpha+(1-u_i)\beta\overline W.
\end{aligned}
\tag{2.5}
$$

These formulas are finite rational descriptions of entire measures,
including every completed word and the infinite outcome. At a pre-latch
returned cut, the supplied candidate is the complete law generated by
fair synthetic letters on the current original control, followed by the
original third-write/latch transition, its uniform label sampler and
(2.5). At pending and delivered cuts it is the original deterministic
Stop/delivery or empty future law. At fourth-phase cuts apply the full
current-record renderer to (2.5). This specifies candidates at every
returned original operation cut. In particular $P$ is not a replacement
source prior or a runtime source query.

**Theorem 2.2 (balanced regular actual observers and configured discrepancy).**
Every table in Definition 2.1 has a finite rational original-domain
installation using the product realization [PAID, Lemma 2.1.1]. These
installations have the following simultaneous properties.

For all hypotheses $\theta\in\{0\}\cup\{-1,+1\}^M$,

$$
\pi B^\theta=\tau,\qquad \tau A=\pi,\qquad
B^\theta A=\mathbf1_X\pi,\qquad AB^\theta=\mathbf1_Y\tau.
\tag{2.6}
$$

Moreover $B^\theta(i,\cdot)\ge\tfrac12\tau$ and
$A(j,\cdot)=\pi$. Thus the private return chains mix exactly in one
full return, and their relative minorization constants are uniform in
$M$. All kernel entries are positive; an absolute positive lower bound
on all $A$ entries is not asserted as $N$ increases.

Every supplied $Q_i$ is in the original $\mathcal K_p$, every supplied
$W_j$ is in $\mathcal K_\beta$, and descriptors within each phase are
distinct. Both acquired edges have exactly the same unweighted phase
marginals under every hypothesis. Under the null, all the supplied candidates are
exactly its actual own complete laws at their respective returned cuts.
For every alternative,

$$
e_A=0,\qquad e_B=\frac1{60}.
\tag{2.7}
$$

Writing $Q_i^\theta,W_j^\theta$ for the actual own laws, every alternative
satisfies

$$
\begin{aligned}
W_j^\xi&=W_j,\qquad \sum_i\pi_iQ_i^\xi=P,\\
Q_i^\xi-Q_i&=\frac{(1-u_i)\sigma_i}{4}\,
                    \beta(W_{+1}-W_{-1}),\\
\operatorname{TV}(Q_i^\xi,Q_i)&=\frac{1-u_i}{60}>\frac1{100},\\
\sum_i\pi_i\operatorname{TV}(Q_i^\xi,Q_i)&=\frac{19}{1800}.
\end{aligned}
\tag{2.8}
$$

At every positive original fourth-segment p history $h$, its actual
configuration row has private marginal $\pi$ and hence

$$
\mathcal D_\xi(h):=
 \sum_i\pi_i\operatorname{TV}
 \left((I_{C_0(h)})_*Q_i,(I_{C_0(h)})_*Q_i^\xi\right)
 =\frac{19}{1800}.
\tag{2.9}
$$

At every positive suspended history the corresponding discrepancy is
zero. Thus (2.9) measures a candidate-versus-own configured full-law
error, with TV before averaging, at actual positive histories.

**Proof.** On every block of four labels, the affine formula for $u_i$
gives the two cancellations

$$
\sum_{h=0}^3s_h=0,\qquad
\sum_{h=0}^3s_hu_{4g+h}=0.
\tag{2.10}
$$

Consequently $\sum_i\pi_i\sigma_i=0$ and
$\sum_i\pi_i(1-u_i)\sigma_i=0$, while $\sum_i\pi_i u_i=c$.
The first cancellation proves balance for $B^\xi$; constant rows of $A$
prove the other identities in (2.6). The entries of $B^\xi$ are $1/4$
or $3/4$, so its minorization is immediate. The null has the same
properties.

Normalization of (2.4) follows from
$c+(1-c)^2=1-t$. In particular $P(T_p(j))=t^j$.
Averaging (2.5) gives

$$
\sum_i\pi_iQ_i=c\delta_\alpha+(1-c)\beta\overline W=P.
\tag{2.11}
$$

Both equations hold on every complete coordinate. For $j\ge1$,

$$
Q_i(T_p(j))=(1-u_i)ct^{j-1}\le\lambda^j,
\qquad W_y(T_\beta(j))=v_yt^j\le b\lambda^j.
\tag{2.12}
$$

Here $(1-u_i)c\le(2/3)(2/5)=\lambda$ and $t\le\lambda$;
the $j=0$ constraints follow from normalization and $v_y\le b$.
Their infinite masses are zero without deleting those atoms. The
emission constraints follow from $a<u_i<b$ and $v_y\in[a,b]$.
Distinct $u_i$ distinguish the entire $Q_i$, and distinct $v_y$
distinguish the $W_y$. Thus conditioning on an entire candidate descriptor
in (1.6) really isolates the indicated label; no label-fibre cancellation
is concealed in (2.7).

The null equations are exactly

$$
Q_i=u_i\delta_\alpha+(1-u_i)\beta\sum_jB^0_{ij}W_j,\qquad
W_j=(1-v_j)\delta_\beta+v_j\alpha\sum_iA_{ji}Q_i.
\tag{2.13}
$$

For an alternative define $W_j^\xi=W_j$ and define $Q_i^\xi$ by the
first equation of (2.13) with $B^\xi$. They are normalized nonnegative
laws, since that equation is a probability mixture. Their difference is
(2.8); the second cancellation in (2.10) makes their $\pi$ average
exactly $P$. Consequently the second same-update equation also holds.
Before the latch the candidate and actual own laws also agree under
every hypothesis: the fair pre-latch generator and original event blocks
are common, and its eventual latch continuation is the same law
$\sum_i\pi_iQ_i^\theta=P$ on each record fibre. Pending and delivered
candidates are likewise exact.

These solutions are the actual own laws: the regular same-update series
and uniqueness supplied in [PAIR, proof of Theorem 11.4] apply, since
$\operatorname{diag}(1-u)B^\theta\operatorname{diag}(v)A\mathbf1
\le\lambda\mathbf1$. This also puts all actual own laws in (1.3).

The signed law

$$
W_{+1}-W_{-1}=(b-a)(\alpha P-\delta_\beta)
\tag{2.14}
$$

has disjoint positive and negative supports, so its TV norm is $b-a=1/15$.
Now $\mathcal R_B(Q_i)=\overline W$ and
$\sum_jB^\xi_{ij}W_j=\overline W+\sigma_i(W_{+1}-W_{-1})/4$.
Thus every conditional B defect, before averaging, is $1/60$.
Also $\mathcal R_A(W_j)=P=\sum_iA_{ji}Q_i$ on all complete coordinates;
this is an exact zero opposite-direction defect, not a bound or a
single-event identity. Equation (2.14) proves (2.8).

For the actual installation retain the full $C_0$ of Assumption 1.1 and
use fair synthetic letters before the latch. In the original update
that writes the third record and then latches it, sample $\pi$
independently of the source, after those original events. Subsequently
use $B^\theta$ on p-beta and $A$ on suspended-alpha. Completing letters
clear private labels; pendingStop and its sole delivery remain original.
This is exactly the supplied same-update product construction. Its
projection to $C_0$ commutes with every acquired update, so induction
over original operations retains every record, permission and event,
including both seeds, every paid rejection and all return histories.
There is no operation enabling a source reset or a Read after Stop.

Source conditioning does not use the synthetic probabilities. For a
fixed original positive history $h$, [NATIVE-JOINT,
`ordered_history_factorization` and `conditional_history_product`]
factor its ordered private updates from the same-$K$ posterior source.
Using (2.6), induction gives private row $\pi$ at every active p cut
and $\tau$ at every suspended cut. Every label is positive there.
The full-record renderer preserves TV, giving (2.9). The original target
at this same history remains

$$
(I_{C_0(h)})_*\sum_k\nu_h(k)P_{s,r_k},\qquad
\nu_h(k)=\frac{\mu(k)r_k^{A(h)}(1-r_k)^{B(h)}}
 {\sum_l\mu(l)r_l^{A(h)}(1-r_l)^{B(h)}}.
\tag{2.15}
$$

Both counts include every paid seed and payload Read. Neither (2.9) nor
its proof substitutes a pure target or omits a supported depth.

For rational representation, store the rational emissions, both tables,
rows and fixed signs with their selectors and finite sampler program.
A uniform label on $N$ points uses the finite rejection sampler supplied
in [REPAIR, Corollary 7.1]: sample $\lceil\log_2N\rceil$ fair bits,
accept integers below $N$, otherwise repeat, reusing the same finite
partial-trial workspace. A common denominator gives the same construction
for each emission; B updates use denominator four. All internal states,
fresh bit use and work are charged. Termination is almost sure, not
bounded in worst-case trials. The same represented service implements
acquired and synthetic updates and makes no additional source call.
COMPLETE contains its conditional continuation states as in [PAID,
Lemma 2.1.1]. The explicit rational tables and candidate descriptions
use $O(N\log(N+1))$ bits; the current private label uses
$\lceil\log_2N\rceil$ bits at p. These are finite representation bounds,
not a fixed total-resource bound across the family. $\square$

## 3. The entire stopped observation experiment

**Definition 3.1 (the evaluator and a stronger cut-label experiment).**
For each $M$, the evaluator is supplied the finite representations of
all of (2.1), (2.2), (2.4), (2.5), the original source/control contract
and the hypothesis family (2.3). This public information is identical
under the null and every alternative. The evaluator may also know the
fixed prior $\mu$ as mathematical side information; no algorithmic
representation of an arbitrary countable prior is assumed.

The installed value of $B^\theta$ and the installed sign string are
unavailable. The legal acquired observation $O$ is the entire original
operation transcript, from the initial seed parser through the original
matching Stop and delivery, with every original event block. Infinite
noncompletion paths are included in its measurable path space. There
is one episode, no reset and no post-Stop access.

For a stronger comparison experiment $O^+$, augment $O$ by the current
private phase label at each *returned original operation cut*: the latch
p label, every p label after a suspended-alpha return, and every
suspended label after a p-beta update. Before the latch and after
completion the extra coordinate is a fixed symbol $\bot$. One may
attach the corresponding public candidate descriptor and emission; these
are deterministic functions of this label and the public data.

Precisely, the sigma-field of $O^+$ is generated by these operation/event
blocks and these returned-cut labels. It excludes installed table entries,
program bytes, nuisance signs, sampler microstates, random bits or random
tapes, private service timing, the unacquired source tail and $K$ itself.
It supplies no cloning, state setting, synthetic-query service or access
to the actual own-law decoder as an oracle. Such access defines another
experiment. COMPLETE accounting includes these private objects where
they exist; accounting does not make them observed.

In particular there is a single hypothesis-independent measurable map
$O^+\mapsto O$: erase the extra labels and their deterministic public
annotations. There is also such a map from $O^+$ to any adaptive
prefix observation or randomized statistic of the specified interface,
using independent evaluator randomness. Full table inspection is not
one of these maps.

Write $\mathsf P^+_{\theta,M,\mu}$ for the law of $O^+$, including its
common public data, and

$$
\overline{\mathsf P}^+_{M,\mu}
 =2^{-M}\sum_{\xi\in\{-1,+1\}^M}\mathsf P^+_{\xi,M,\mu}.
\tag{3.1}
$$

This is a mixture of the fixed installed hypotheses of Definition 2.1.
Each constituent retains exactly one original draw of $K$ and the same
prior. The mixture does not grant the evaluator a draw from $G_A$ or
$G_B$, nor any further episode.

**Theorem 3.2 (source-dependent complete stopped-episode bound).** For
every $M\ge1$ and every prior of Assumption 1.1,

$$
\begin{aligned}
\operatorname{TV}(\mathsf P^+_{0,M,\mu},
                         \overline{\mathsf P}^+_{M,\mu})
&\le\frac1M\sum_k\mu(k)
       \frac{(1-r_k)r_k(1-r_k)}{[1-r_k(1-r_k)]^2}\\
&\le\frac{100}{361M}=:\varepsilon_M.
\end{aligned}
\tag{3.2}
$$

The bound also holds after conditioning on any positive original
pre-latch finite history $h$, with $\mu$ in the first line replaced by
its actual posterior $\nu_h$ and the whole remaining episode observed.
There is no bound on the length of $h$ in this assertion. The same
universal bound holds for the original $O$ and for every statistic or
adaptive prefix permitted by Definition 3.1. Indeed the unaugmented
original transcript has identical laws under all hypotheses.

**Proof.** Conditional on $K=k$, the original source is an independent
letter stream, and native scheduling uses only the original control and
the next raw letter [NATIVE-DRIVE, `nextOperation`, `nativeDrive`].
Couple that entire stream identically under all hypotheses. This is a
proof coupling, not an evaluator observation or reset. It couples every
seed rejection, partial pair, accepted seed, early payload return,
record write and latch exactly, together with every paid Read.
The private labels do not alter this schedule.

Seed acceptance occurs almost surely: each successive pair accepts
with probability $2r_k(1-r_k)\ge4/9$. Each of the four payload stages
completes almost surely, since a return has probability
$r_k(1-r_k)\le6/25$. Thus the full stopped transcript is finite almost
surely at every depth and under every countable mixture. Infinite
noncompletion paths remain in the space with mass zero. The latch is
at an almost surely finite stopping time for the same stream. Conditional
on $K$, its future letters have the same independent law: partition by
its finite prefixes and apply the product-law factorization. This is
also the source-tail content of [NATIVE-JOINT,
`ordered_history_factorization`].

Let $L$ be the total number of actual p-beta updates in the fourth
segment. A completed raw fourth word $w_{j,0}$ has $L=j$; a word
$w_{j,1}$ has $L=j+1$. Equivalently, for $\ell\ge1$,

$$
\Pr(L\ge\ell\mid K=k)
 =(1-r_k)[r_k(1-r_k)]^{\ell-1}.
\tag{3.3}
$$

The first beta costs one source Read. Each further such beta requires
the preceding suspended-alpha return and another p-beta, both paid.
This gives (3.3) without conditioning on a future completion.

Conditional on any fixed complete finite original source transcript,
the p label initially sampled at the latch and each p label after an A
return are independent uniform points of $X$. They are independent of
that source transcript. This statement concerns the ordered path, not
just its one-cut marginals: every row of $A$ equals $\pi$, independently
of the preceding suspended label. In particular the p inputs
$I_1,\ldots,I_L$ of the B updates are independent uniform labels.
There can additionally be a final p label followed by completing alpha;
it is uniform and does not consult any sign. All these labels may be
revealed in $O^+$.

For fixed source and p labels, under hypothesis $\xi$ the probabilities
of the successive suspended labels $J_1,\ldots,J_L\in\{-1,+1\}$ multiply
as

$$
\Pr_\xi(J_1=j_1,\ldots,J_L=j_L\mid O,I)
 =2^{-L}\prod_{q=1}^L
    \left(1+\frac12j_qs_{I_q\bmod4}\xi_{\lfloor I_q/4\rfloor}\right).
\tag{3.4}
$$

Here $O$ consists only of the fixed original source/control transcript;
no synthetic emission probability enters (3.4). Under the null the
conditional probability is $2^{-L}$.

Let $C$ be the event that two of these B inputs lie in the same
four-label block. Off $C$, every sign in the product (3.4) occurs just
once, so its average over the independent uniform *hypothesis* signs is
exactly one. Therefore the null and mixture measures agree on every
measurable subset of $C^c$. The source and p-label marginals are common,
so both assign the same probability to $C$ as well. Their TV is at most
that common probability. This argument can alternatively be realized
as equality coupling up to the first repeated B-input block.

Each pair of B inputs shares its block with probability $1/M$.
Conditioning first on the entire source transcript gives

$$
\Pr(C\mid O)\le\frac{\binom L2}{M},\qquad
\operatorname{TV}(\mathsf P^+_0,\overline{\mathsf P}^+)
 \le\frac{\mathbb E_\mu\binom L2}{M}.
\tag{3.5}
$$

This conditioning retains the dependence between the length of the
fourth segment and the once-drawn source depth. By (3.3) and nonnegative
summation, with $t_k=r_k(1-r_k)$,

$$
\mathbb E\left[\binom L2\mid K=k\right]
 =\sum_{\ell\ge2}(\ell-1)(1-r_k)t_k^{\ell-1}
 =\frac{(1-r_k)t_k}{(1-t_k)^2}
 \le\frac{(2/3)(6/25)}{(19/25)^2}=\frac{100}{361}.
\tag{3.6}
$$

Countable summation against $\mu$ proves (3.2). This is a full stopped
path bound, not a deterministic-length independent-edge surrogate.
No rare pre-latch histories were removed: their laws were coupled
identically before the calculation of $L$.

More explicitly, for any positive original pre-latch history $h$, the
source factorization gives posterior $\nu_h$ and, conditional on the
same $K$, independent unread letters. Private signs have not yet been
consulted. The remaining seed and early-payload stages reach the latch
almost surely, including from a partial seed pair or suspended early
phase. Repeat the preceding coupling from this cut with $\nu_h$.
This proves the conditional assertion for every such $h$, including
histories with arbitrarily many paid rejections. It does not claim a
uniform conditional bound after a long label-revealing fourth history
has already exposed repeated blocks.

Finally, measurable postprocessing contracts TV; the erasure map in
Definition 3.1 gives the stated observation direction. The unaugmented
$O$ depends only on the common source and original control, so its laws
are exactly equal. An evaluator choosing when to report or cease
observing cannot manufacture a longer episode or an additional Read.
The resulting record is a function of $O^+$ and its independent
randomness, so (3.2) still applies. $\square$

## 4. Confidence obstruction with an actual configured-law consumer

**Corollary 4.1 (testing and honest confidence).** Fix $M,\mu$ as above.
Let $\varphi\in[0,1]$ be any possibly randomized rejection probability
computed from the interface of Definition 3.1, even from all of $O^+$.
If $\mathbb E_0\varphi\le\alpha$, then

$$
2^{-M}\sum_\xi\mathbb E_\xi\varphi\le\alpha+\varepsilon_M,
\qquad
\inf_\xi\mathbb E_\xi\varphi\le\alpha+\varepsilon_M.
\tag{4.1}
$$

In particular, simultaneous power at least $1-\beta$ for every
alternative requires $\alpha+\beta\ge1-\varepsilon_M$.

Apply this either to the residual parameter $e_B$, with null value zero
and alternative value $d=1/60$, or to the actual configured-law
parameter $\mathcal D(h)$ of (2.9) at any specified positive original
p history, with null value zero and alternative value $d=19/1800$.
If a random confidence set $C$ covers that parameter with probability
at least $1-\gamma$ under every hypothesis, then

$$
\Pr_0(\{0,d\}\subset C)\ge1-2\gamma-\varepsilon_M.
\tag{4.2}
$$

Thus a confidence interval has diameter at least $d$ with at least that
null probability. An honest upper bound $U$ obeys

$$
\Pr_0(U\ge d)\ge1-\gamma-\varepsilon_M.
\tag{4.3}
$$

These bounds are uniform over every permitted finite or countable prior.
For any fixed desired positive error bound in (3.2), a sufficiently
large *finite* $M$ meets it, while both alternative parameters remain
fixed and all installations remain finite rational observers.

**Proof.** For a $[0,1]$-valued statistic, its expectation difference is
at most TV. Theorem 3.2 proves (4.1). For (4.2), coverage at the
alternatives gives $\overline{\mathsf P}(d\in C)\ge1-\gamma$;
transfer to the null loses at most $\varepsilon_M$. Intersect with the
null coverage event $0\in C$ and use the union bound. The same transfer
for $U\ge d$ proves (4.3).

The configured-law consumer is not an additional inferential assumption:
for every alternative, every p label and every positive original p
history, Theorem 2.2 gives the exact relation

$$
\operatorname{TV}(\widetilde D_{h,i},D^{\mathrm{own}}_{h,i})
 =(1-u_i)\operatorname{TV}
    \left(\mathcal R_B(Q_i),\sum_jB^\xi_{ij}W_j\right)
 =\frac{1-u_i}{60}.
\tag{4.4}
$$

The suspended supplied laws are already the actual suspended own laws,
so no unproved residual-to-own-law bridge is used. Averaging (4.4) in
the actual row gives $19/1800$ at all those histories. In contrast,
$\sum_i\pi_iQ_i^\xi=\sum_i\pi_iQ_i=P$, so the error would disappear
if the laws were averaged before TV. $\square$

**Proposition 4.2 (charged acquisition and the scope of certification).**
For each installed hypothesis, the complete original episode has finite
expected paid Read count

$$
\mathbb E_\mu N_R
 =\sum_k\mu(k)\left[
  \frac1{r_k(1-r_k)}+
 4\frac{2-r_k}{1-r_k(1-r_k)}\right]
 \le\frac92+\frac{500}{57}=\frac{1513}{114}.
\tag{4.5}
$$

All Read counts, private random-bit uses, finite representations,
workspace and emitted output lengths are charged. No deterministic
maximum episode length or private rejection time is asserted. No
repeated episode or repeatable synthetic query is part of (3.2)–(4.3).
The supplied candidate generator can be evaluated or sampled offline,
with its costs charged, but this gives no installed B transitions:
its public input and resulting conditional law are the same under every
hypothesis.

The impossibility concerns certification of supplied forecasts against
the actual own configured laws. Every observer in the family has a true
own-law decoder satisfying its own exact recursion. The statements make
no claim of inability to certify that structural recursion, supported
native-target excess, a sign of the common-flow objective $j_c$,
training attainment, or network generalization.

**Proof.** Conditional on $K=k$, seed pairs are independent trials with
success probability $2r_k(1-r_k)$ and cost two Reads, giving the first
term of (4.5). A payload stage's expected Read count $d_k$ satisfies
$d_k=1+(1-r_k)(1+r_kd_k)$, hence
$d_k=(2-r_k)/(1-r_k(1-r_k))$. All four stages occur; conditional
independence after their finite stopping times justifies addition.
Use $r_k(1-r_k)\ge2/9$, $2-r_k\le5/3$ and
$1-r_k(1-r_k)\ge19/25$, then average over the same $K$.
Fresh private services have the finite representations and almost-sure
termination proved in Theorem 2.2; their work was not counted as free
source access. Adding a calculation or simulated output depending only
on the common public input and independent evaluator randomness is
hypothesis-independent postprocessing and cannot increase TV.

Full installed-table access would instead reveal $B^\theta$, allowing
direct evaluation of (1.6) and the recursions; it is expressly excluded
by Definition 3.1. True own generation holds under every hypothesis by
Theorem 2.2. The parameter in (4.4) compares supplied and own forecasts,
not either forecast with the native target (2.15). Accordingly no native
risk inequality or learning conclusion follows from this parameter
identification. $\square$

## 5. Mathematical sources and comparison of hypotheses

**Mathematical citation 5.1 (repository suppliers and exact delta).**
[REPAIR, Theorem 3.1 and §7] supplies repair and transport for given
analytical complete-law edges and explicitly leaves their acquisition
and statistical error control separate. Its cancellation example and
unchanged-kernel obstruction do not specify a stopped observation
experiment. [PAIR, §§11, 20] and [PAID, §§9–10, 16–18] supply complete
law spaces, common-flow regeneration, rational installation and
certificate machinery. They are used here for those constructions;
they are not restated as new regeneration or certificate theorems.

[NATIVE-STATE, `finiteRead`, `writeMarker`, `finiteStop`],
[NATIVE-EVENTS, `completionEvents`, `eventBlock`], and
[NATIVE-DRIVE, `nextOperation`, `nativeDrive`] specify the native
operations and write-before-latch/Stop semantics used in the installation
and observation map. [NATIVE-JOINT, `ordered_history_factorization`,
`conditional_history_product`, `sameK_private_tail`] supply the
source/private separation at positive actual cuts. Theorem 3.2 uses
the pathwise product of the specified kernels as well as this cut
correspondence; a one-cut marginal identity alone would not prove it.

[BLIND] omits B from a coarse event/prefix interface and proves an exact
complete-law identification obstruction. [BRANCH] concerns branching
necessity for common stopped-law calibration. [WHITEBOX, §§1–13] and
[LOSS-FIBRE] distinguish observational fibres from internal mechanism
and learning claims. The additional result here is the balanced
four-label sign construction with both cancellations (2.10), a genuine
zero full A defect, the exact configured consumer (4.4), and the
same-source *whole stopped-episode* comparison (3.2). These are
repo-derived statements, with no worldwide originality assertion.

**Mathematical citation 5.2 (calibration testing and collision suppliers).**
Donghwan Lee, Xinmeng Huang, Hamed Hassani and Edgar Dobriban,
*T-Cal: An optimal test for the calibration of predictive models*,
[arXiv:2203.01850v4](https://arxiv.org/abs/2203.01850v4),
Proposition 5.1, proves impossibility of detecting a fixed positive
$\ell_p$ expected calibration error over general continuous
miscalibration curves from finitely many independent validation samples.
Its Theorem 5.2 imposes a fixed $(s,L)$ Hölder condition and gives the
$n^{-2s/(4s+K-1)}$ separation lower bound for $K$ classes. Its Theorem 3.1
additionally uses Assumption 3.1's upper and lower bounds on marginal
density on the prediction simplex. The present label supports are finite
and growing, and no fixed Hölder regularity is asserted. Those testing
results provide classical context, not a theorem transferring independent
validation samples to this native stopped source.

Jarosław Błasiok, Parikshit Gopalan, Lunjia Hu and Preetum Nakkiran,
*A Unifying Theory of Distance from Calibration*,
[arXiv:2211.16886v2](https://arxiv.org/abs/2211.16886v2),
§§2.1–2.2 distinguish prediction-only access from access to the underlying
input. Theorem 9.10 estimates the *lower* calibration distance from
$n=\Omega(\varepsilon^{-2})$ independent prediction/label pairs with
probability $2/3$. This is a different functional from the full
outgoing-descriptor-conditioned TV in (1.6); the theorem does not supply
a bound for that functional on growing finite descriptor supports.

Mingda Qiao, *Computational and Statistical Hardness of Calibration
Distance*, [arXiv:2603.18391v1](https://arxiv.org/abs/2603.18391v1),
Theorem 5, requires sufficiently large $k$ and
$\varepsilon,\delta\in(0,0.01)$ and gives a
$\sqrt{k}/(25\varepsilon)$ sample lower bound for PAC estimation of
calibration distance on a domain of size $4k+3$. It uses independent
samples with input/prediction/label access. Theorem 3 distinguishes
two-sided estimation from the one-sided empirical-distance bound; the
latter needs only $O(\varepsilon^{-3})$ samples, independent of domain
size. These results concern calibration distance to a calibrated
predictor, not (1.6). Its Lemma 15 couples the two sample experiments
until a repeated input appears, bounding their TV by a collision
probability. Collision and mixture testing arguments are
literature-attested methods. Equations (3.3)–(3.6) prove the additional
native source embedding rather than applying an independent-sample
lower bound to dependent stopped observations without a map.

Konstantina Bairaktari, Lunjia Hu, Huy L. Nguyen and Jonathan Ullman,
*Testable and Actionable Calibration for Full Swap Regret*,
[arXiv:2605.17749v1](https://arxiv.org/abs/2605.17749v1),
Theorem 1.2 bounds expected SCDL estimation error by
$O(T^{-1/2}\log^{3/2}T)$ from $T\ge2$ independent binary
prediction/outcome pairs. Its Theorem 7.1 gives a high-probability bound
for $\delta\in(e^{-T/2},1/T)$. Its actionability Theorem 4.2 uses a
specified softened response, a dyadic $m$ with
$\mathsf{SCDL}(\mathcal D)<2/m$, and utilities in $[0,1]$.
SCDL, its response rule and its independent-sample interface are not
identified with the complete-law residual (1.6) or with a stopped
episode. Theorem 3.2 therefore neither contradicts its testability nor
claims a new generic calibration-testing lower bound.

[PAIR]: RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md
[PAID]: RECURSIVE_RELATIONAL_OBSERVATION_EFFECTIVE_PAID_HISTORY_CERTIFICATES.md
[REPAIR]: RECURSIVE_RELATIONAL_OBSERVATION_JOINT_CALIBRATION_OWN_LAW_REPAIR.md
[BLIND]: RECURSIVE_RELATIONAL_OBSERVATION_ACQUIRED_KERNEL_BLIND_DIRECTIONS_AFTER_PAIRED_CALIBRATION.md
[BRANCH]: RECURSIVE_RELATIONAL_OBSERVATION_FINITE_WORD_BRANCHING_NECESSITY.md
[WHITEBOX]: FIB_ATOM_MACHINE_LEARNING_WHITEBOX.md
[LOSS-FIBRE]: WHITE_BOX_LOSS_FIBER_LAW.md
[NATIVE-STATE]: ../../../D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixState.lean
[NATIVE-EVENTS]: ../../../D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFullResidual.lean
[NATIVE-DRIVE]: ../../../D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeAcquiredPrefixCylinder.lean
[NATIVE-JOINT]: ../../../D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeObserverJointLaw.lean

## 追加锚（本行以下为增补区）
