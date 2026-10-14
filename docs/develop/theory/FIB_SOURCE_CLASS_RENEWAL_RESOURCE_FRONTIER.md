# Exact source classes and the renewal state/read frontier

## 1. Result, interpretation and mathematical ownership

This volume determines a complete-configuration versus paid-read frontier for a fixed positive two-term renewal source pair. Fix integers $d\ge1$ and $1\le r\le d$, a real $c>0$, and a risk allowance $0<\alpha<1/2$. Write $a=d+1$. The shapes are exactly

$$
F_0(k)=k^d,\qquad F_1(k)=k^d+c k^{d-r}\qquad(k=1,2,\ldots).
\tag{1.1}
$$

The parameter $q=e^{-s}$ is known and common to the two hypotheses. One source-blind observer design at that parameter must satisfy both risks, both almost-sure stops and both finite paid means. Its mutable resource is the number $M$ of all possible complete persistent configurations, including its internally emitted labels. Every bit of one consecutive stationary history that it reads is paid. Immutable real transition probabilities have unrestricted precision in this abstract model.

For $a>2r$, define

$$
\kappa=\frac{a-2r}{r},\qquad
\Phi(s,M)=\max\{s^{-(2r+1)},\ s^{-(a+1)}M^{-\kappa}\}.
\tag{1.2}
$$

Theorems 7.1 and 10.1 establish constants $A_-,A_+>0$, a finite sufficient budget $M_0$, and one neighborhood $0<s<s_0$, all depending only on the fixed $(d,r,c,\alpha)$, with the following quantifiers. Every compliant observer at every finite $M\ge2$ has each paid mean at least $A_-\Phi(s,M)$. For every $M\ge M_0$ and every $s$ in that same neighborhood, one common observer with at most $M$ configurations has both paid means at most $A_+\Phi(s,M)$. Thus each separate mean infimum and the infimum of the maximum of the two means have this order, uniformly over all sufficient finite budgets. Achieving the bulk order $s^{-(2r+1)}$ under even one fixed target, with one fixed eventual upper constant and all opposing compliance conditions, requires $M(s)=\Omega(s^{-r})$; a common family achieves it with $M(s)=O(s^{-r})$.

For $a<2r$, every finite-budget compliant observer pays $\Omega(s^{-(a+1)})$ under each source, and a family of q-retuned tables with one fixed sufficient configuration budget achieves that order under both. At $a=2r$, the proved result is the logarithmic sandwich in Section 11. A lawful multiscale controller attaining the logarithmic gain remains open. Section 12 gives a sparse pair with paid order $s^{-(d+2)}$ and a fixed sufficient budget. That pair satisfies the same tail upper envelope as (1.1), showing exactly why an upper envelope alone does not determine the matched frontier.

These are ordinary mathematical derivations. Their source-relative content follows the source-class proposal's S1–S6, U1–U3 and C1–C2, whose independent handwritten check concerns that proposal. The proofs below state every model and applicability hypothesis and develop the required interfaces in full. They do not inherit approval of this authored source. The additional q-independent-table bridge in that check is outside the mathematical delivery here. The old rational-center polynomial pair remains a separate source with separate hypotheses. Section 13 identifies the supplied results and classical methods; no kernel certificate or worldwide originality claim accompanies this volume.

## 2. The exact stationary sources and their scalar estimates

**Definition 2.1 (Fixed positive shapes and the observed law).** Keep (1.1) fixed independently of $q$, $M$ and the observer, and put $B=1+c$. For every positive integer $k$,

$$
k^d\le F_i(k)\le Bk^d,\qquad
\frac{F_1(k)}{F_0(k)}-1=c k^{-r}.
\tag{2.1}
$$

For $0<q<1$ define

$$
\begin{aligned}
Z_i(q)&=\sum_{k\ge1}F_i(k)q^k,&
f_i(k)&=\frac{F_i(k)q^k}{Z_i(q)}\quad(k\ge1),& f_i(0)&=0,\\
S_i(b)&=\sum_{k\ge b}f_i(k)\quad(b\ge0),&
\mu_i(q)&=\sum_{k\ge1}(k+1)f_i(k),\\
\beta_i(q)&=\frac{\sum_{k\ge1}k(k+1)f_i(k)}{2\mu_i(q)}.
\end{aligned}
\tag{2.2}
$$

Draw $\tau$ with $\mathsf P_{i,q}(\tau=b)=S_i(b)/\mu_i(q)$ for $b\ge0$. Independently draw iid $K_1,K_2,\ldots$ with law $f_i$. Put ones at

$$
\tau_0=\tau,\qquad
\tau_n=\tau+\sum_{j=1}^n(K_j+1)\quad(n\ge1),
\tag{2.3}
$$

and zeros at every other site of $X_0,X_1,\ldots$. The variables $K_j$ count zeros; $K_j+1$ counts a whole post-tick interval through its closing tick. The first wait has its own equilibrium law and is not a draw from $f_i$.

**Lemma 2.2 (Normalization, stationarity and the initial mean).** The law in Definition 2.1 is stationary. Its defining sums and moments are finite at every interior $q$, and

$$
S_i(0)=S_i(1)=1,\qquad
\sum_{b\ge0}S_i(b)=\mu_i,\qquad
\mathbb E_{i,q}\tau=\beta_i.
\tag{2.4}
$$

Proof. Polynomial growth times $q^k$ is summable with every fixed polynomial weight. For each $k\ge1$, its mass occurs in $S_i(b)$ for $b=0,\ldots,k$. Interchanging nonnegative sums gives the middle identity in (2.4). Weighting by $b$ instead gives $\sum_b bS_i(b)=\sum_k k(k+1)f_i(k)/2$, proving the last identity.

For stationarity, consider only as a proof variable the countdown $R_t$ to the next tick. From a positive value $b$ it moves to $b-1$; from zero it draws a fresh value $K$ with law $f_i$. Its candidate stationary mass is $\pi(b)=S_i(b)/\mu_i$. Its incoming mass at $b\ge0$ is

$$
\pi(b+1)+\pi(0)f_i(b)
=\frac{S_i(b+1)+f_i(b)}{\mu_i}
=\pi(b).
\tag{2.5}
$$

Here $f_i(0)=0$ and $S_i(0)=S_i(1)$ handle $b=0$. Start this chain with $\pi$ and take $X_t=\mathbf1_{\{R_t=0\}}$. Its first zero value occurs at $\tau=R_0$, and the future renewals use independent draws of $K$. This is (2.3), so the observed process is stationary. Equivalently, size-bias a cycle by its $K+1$ sites and choose a uniform site: each possible forward wait $0,\ldots,K$ receives one site. Neither construction supplies the observer with a countdown or initial age. $\square$

Write

$$
R_m(t)=\sum_{k\ge1}k^m e^{-tk},\qquad
g(t)=\frac{R_{d-r}(t)}{R_d(t)},\qquad A_r=\frac{(d-r)!}{d!}.
\tag{2.6}
$$

For nonnegative integer $m$ this is the ordinary power sum. Negative indices will be used only in the explicitly bounded sums of Section 6.

**Lemma 2.3 (Power quotients, their derivatives and source moments).** As $t\downarrow0$, for every fixed nonnegative integer $m$,

$$
\begin{aligned}
R_m(t)&=m!t^{-(m+1)}(1+O(t)),\\
g(t)&=A_r t^r+O(t^{r+1}),&
g'(t)&=rA_r t^{r-1}+O(t^r).
\end{aligned}
\tag{2.7}
$$

There is a source-only $t_0>0$ on which

$$
\frac{rA_r}{2}t^{r-1}\le g'(t)\le2rA_r t^{r-1}.
\tag{2.8}
$$

Both sources satisfy

$$
Z_i(e^{-s})=d!s^{-a}(1+O(s)),\qquad
\mu_i(e^{-s})=\frac a s+O(1),\qquad
\beta_i(e^{-s})=\frac{a+1}{2s}+O(1).
\tag{2.9}
$$

All constants here concern the fixed source parameters.

Proof. The geometric series gives $R_0(t)=1/(e^t-1)$. At every positive $t$, local absolute convergence permits differentiation, giving $R_m=(-d/dt)^mR_0$. The analytic function $(e^t-1)/t$ has value one at zero. Its reciprocal shows that $R_0(t)-1/t$ is analytic there. Differentiating that analytic remainder proves (2.7) for $R_m$, including derivative control after factoring the leading power. In particular $t^{m+1}R_m(t)$ has an analytic extension with nonzero value $m!$. Taking the quotient of these analytic factors proves both the expansion of $g$ and its differentiated expansion; no differentiation of an uncontrolled remainder is involved. Since $rA_r>0$, decreasing $t_0$ proves (2.8).

Exactly $Z_0=R_d(s)$ and $Z_1=R_d(s)+cR_{d-r}(s)$. The unnormalized numerator of $\mu_i$ has leading term $(d+1)!s^{-(a+1)}$. The numerator $\sum k(k+1)F_i(k)e^{-sk}$ has leading term $(d+2)!s^{-(a+2)}$. Dividing the first by $Z_i$, and the second by twice the first, gives (2.9). Each perturbation lowers degree by at least one because $r\ge1$, so these ratio remainders are $O(1)$. $\square$

## 3. Complete configurations, actual epochs and actual payment

**Definition 3.1 (The pointwise compliant class).** At known common $q$, the observer has one design and one source-independent initialization used under both labels. It may retune its finite state set, initialization and bit-transition probabilities arbitrarily with $(q,d,r,c,\alpha,M)$. At most $M$ complete persistent configurations count every initialization state, active state, control phase, register, retained random choice, stored seed and both emitted decision labels. Fresh update randomness is independent of the source and previous fresh randomness. The fixed table and known $q$ are immutable design data; their real precision is unpriced. All mutable information belongs to the counted configurations.

Each action reads the next actual bit or stops with an internally emitted $D\in\{0,1\}$. The only source access is the uninterrupted consecutive history of Definition 2.1. There is no external time, age, read or action counter, program counter, archive, skipped bit, free gap, source reset, second source, hidden-state observation, true-label advice, probability response or parameter query. The cost tally is not an input, and there is no decision decoder from stopping time. Updates use the current configuration, the bit just read when applicable, and fresh randomness.

If the read prefix is $X_0,\ldots,X_{T-1}$, its paid cost is $T$, including the initial wait, all read zeros and ticks, and any terminal partial gap. Initial stopping has $T=0$. Write $\mathfrak A_M(q,\alpha)$ for the observers satisfying all six obligations

$$
\begin{gathered}
\mathsf P_{0,q}(D=1)\le\alpha,\qquad
\mathsf P_{1,q}(D=0)\le\alpha,\\
\mathsf P_{0,q}(T<\infty)=1,\qquad
\mathsf P_{1,q}(T<\infty)=1,\\
\mathbb E_{0,q}T<\infty,\qquad
\mathbb E_{1,q}T<\infty.
\end{gathered}
\tag{3.1}
$$

These are selected-pair, pointwise conditions. They do not require one q-independent table or correctness over two separate unknown nuisance-parameter families.

**Lemma 3.2 (Same-budget normal form and initial variation).** An observer has a common row $\eta$ and stochastic zero and one matrices $A,C$ on at most $M$ configurations, with two distinct absorbing labels $d_0,d_1$. Every other state commits to a next paid read. This preserves $(T,D)$. Put

$$
B_k=A^kC,\qquad
U_i=\sum_{k\ge1}f_i(k)B_k,\qquad
\nu_i=\sum_{b\ge0}\frac{S_i(b)}{\mu_i}\eta A^bC.
\tag{3.2}
$$

The kernels and rows are stochastic and fix the labels. Uniformly over all retuned designs,

$$
\|\nu_1-\nu_0\|_{\rm TV}\le r_{\rm init}(s):=
c\frac{R_{d-r+1}(s)+R_{d-r}(s)}{R_{d+1}(s)+R_d(s)}
\le C_{\rm init}s^r
\tag{3.3}
$$

on a source-only neighborhood.

Proof. Compose initialization with its read/stop choice; after each read compose the bit update with its ensuing read/stop choice. Send stopping mass to its actual label and merge terminal configurations with that same label. Read-ready configurations and retained control already belong to the counted set, so composition adds no persistent state. Marginalizing independent update coins supplies stochastic rows, without a retained random tape. Make both labels fixed on unused future bits. Before absorption this reproduces the actions and afterwards changes neither cost nor label.

The unnormalized first-wait weights are $G_i(b)=\sum_{k\ge\max(1,b)}F_i(k)e^{-sk}$, with totals $\mathcal W_i=\sum(k+1)F_i(k)e^{-sk}$. Here $G_1\ge G_0$ and

$$
\mathcal W_1-\mathcal W_0=c(R_{d-r+1}+R_{d-r}),\qquad
\mathcal W_0=R_{d+1}+R_d.
\tag{3.4}
$$

Normalizing the positive addition makes $G_1/\mathcal W_1$ a mixture of $G_0/\mathcal W_0$ and the normalized addition. Thus their variation is at most $(\mathcal W_1-\mathcal W_0)/\mathcal W_1$, bounded by (3.3). Passing both through the common stochastic map $b\mapsto\eta A^bC$ contracts variation: each output event has conditional value in $[0,1]$. Lemma 2.3 bounds the ratio in (3.3) by $C_{\rm init}s^r$, independently of that map. The independent future gaps give $U_i$. $\square$

**Lemma 3.3 (Live epochs and predictable tick payment).** Follow the full source history, freezing any actually emitted label afterwards. Let $Y_n$ be the resulting analytical state after tick $\tau_n$, and define

$$
N=\inf\{n\ge0:Y_n\in\{d_0,d_1\}\},\qquad
Q_T=\sum_{t\ge0}\mathbf1_{\{T>t\}}X_t.
\tag{3.5}
$$

Under source $i$, the initial row is $\nu_i$ and the epoch kernel is $U_i$. For a compliant observer,

$$
N<\infty\ \text{almost surely},\quad Y_N=d_D,\quad
N\le Q_T\le T,\quad
\mathbb E_iN\le B(1-q)\mathbb E_iT\le Bs\mathbb E_iT.
\tag{3.6}
$$

Proof. The independent gaps and fresh coins give (3.2). If the stop precedes or coincides with the first tick, $N=0$. Otherwise each of $Y_0,\ldots,Y_{N-1}$ is immediately after an actually read tick and commits to a further read. These are $N$ distinct paid ticks. A stop during zeros is recorded at the next analytical tick by its frozen label; that unread tick is not added to $Q_T$. Finiteness of individual source intervals and actual almost-sure stopping give finite $N$ and its claimed terminal label. The finite paid mean gives finite $\mathbb E_iN$.

After a read tick and $b\ge1$ subsequent zeros, the next-one hazard is

$$
\frac{f_i(b)}{S_i(b)}
=\frac{F_i(b)q^b}{\sum_{k\ge b}F_i(k)q^k}
\le\frac{Bb^dq^b}{\sum_{k\ge b}b^dq^k}
=B(1-q).
\tag{3.7}
$$

At $b=0$ it is zero since $K\ge1$. Earlier gaps are independent of the current one, so this conditions on the entire bit history. Before any read tick, $b$ zeros say $\tau\ge b$ and the hazard instead is $S_i(b)/\sum_{v\ge b}S_i(v)$. The envelope gives $F_i(k+j)\ge B^{-1}F_i(k)$. Shift the tail terms to get $S_i(b+j)\ge B^{-1}q^jS_i(b)$. When $b=0$, the shifted terms start at $j+1$ and are contained in the tail at $j$, which gives the same inequality. Sum over $j\ge0$ to bound this initial hazard by $B(1-q)$ too.

Expose all independent observer coins only on the proof probability space. In the filtration containing them and $X_0,\ldots,X_{t-1}$, the event $\{T>t\}$ that the next read is undertaken is measurable. Coin independence leaves the source hazard unchanged. Tonelli and conditional expectation give

$$
\mathbb E_iQ_T
=\sum_{t\ge0}\mathbb E_i\left[\mathbf1_{\{T>t\}}
\mathbb E_i(X_t\mid\text{prefix, coins})\right]
\le B(1-q)\sum_{t\ge0}\mathsf P_i(T>t)
=B(1-q)\mathbb E_iT.
\tag{3.8}
$$

Finally $1-e^{-s}\le s$. This charges actual reads, including the terminal read and any interrupted gap prefix. It supplies neither a coin archive to the observer nor an identity $\mu_i\mathbb E_iN$ for arbitrary observers. $\square$

## 4. A general positive-forest comparison

**Theorem 4.1 (Actual hitting stability on a finite configuration set).** Let $P,Q$ be stochastic matrices on the same set of at most $M$ vertices, with distinct common absorbing labels $d_0,d_1$. Suppose $\gamma\ge1$ and

$$
\gamma^{-1}P(x,y)\le Q(x,y)\le\gamma P(x,y)
\quad\text{for every }x,y.
\tag{4.1}
$$

Let $h_P,h_Q$ be actual probabilities of ever hitting $d_1$, including time zero. There is an integer $n\le M-2$ determined by their common support such that

$$
\gamma^{-2n}h_P(x)\le h_Q(x)\le\gamma^{2n}h_P(x),\qquad
|h_Q(x)-h_P(x)|\le\frac{\gamma^n-1}{\gamma^n+1}.
\tag{4.2}
$$

No absorption from all states or lower bound on a positive exit is required.

Proof. The positive-edge supports coincide. Let $\mathcal Z$ consist of vertices with no positive directed path to $t=d_1$. A countable union over finite paths shows their hitting values are zero under both kernels. Replace their rows in both kernels by identity rows; this leaves hitting probabilities unchanged because $t$ is inaccessible after entering $\mathcal Z$. The comparison survives. The boundary is $\partial=\mathcal Z\cup\{t\}$, and its complement $V$ has $n\le M-2$ vertices since $d_0\in\mathcal Z$.

A forest chooses one non-self successor $\phi(u)$ for each $u\in V$, with no cycle within $V$. Every chosen path then ends in $\partial$. Set

$$
w_P(\phi)=\prod_{u\in V}P(u,\phi(u)),\qquad
\mathcal D_P=\sum_\phi w_P(\phi),\qquad
\mathcal A_P(x)=\sum_{\phi:\ x\text{ ends at }t}w_P(\phi),
\tag{4.3}
$$

and let $\mathcal C_P(x)$ be the complementary sum ending in $\mathcal Z$. Use the identical forest family for $Q$. Choosing first edges of shortest paths to $t$ gives a positive forest with every path ending at $t$, so $\mathcal D_P$ and $\mathcal A_P(x)$ are positive for $x\in V$.

For completeness the determinant identities follow directly. Put $L_P=I-P_{VV}$ and $b_P(u)=P(u,t)$. Its row decomposition is

$$
L_P(u,\cdot)=\sum_{v\ne u}P(u,v)
\left(e_u^{\mathsf T}-\mathbf1_{\{v\in V\}}e_v^{\mathsf T}\right).
\tag{4.4}
$$

Multilinearity chooses one successor per row. If these choices contain an internal cycle, the rows on that cycle sum to zero, and the determinant term vanishes. Otherwise order vertices by path length to the boundary, simultaneously permuting rows and columns. The matrix is triangular with diagonal one; its determinant is one. Thus $\det L_P=\mathcal D_P>0$. Self-loops are accounted for by $1-P(u,u)=\sum_{v\ne u}P(u,v)$ in (4.4).

Replace column $x$ by $b_P$. The same expansion assigns that column the value $\mathbf1_{\{\phi(u)=t\}}$ in row $u$. Cycle rows still sum to zero, including that column. For a forest, let $z_\phi(u)$ indicate that its path ends at $t$. Its successor matrix satisfies $L_\phi z_\phi=b_\phi$ with $b_\phi(u)=\mathbf1_{\{\phi(u)=t\}}$. Expressing the replacement column as a linear combination of the original columns annihilates every term except column $x$, whose coefficient is $z_\phi(x)$. Consequently the replaced determinant is $\mathcal A_P(x)$, with positive sign. Actual first-step hitting equations have the boundary values zero on $\mathcal Z$ and one on $t$, and satisfy $L_Ph_P=b_P$ on $V$. The positive determinant makes this boundary solution unique, giving

$$
h_P(x)=\frac{\mathcal A_P(x)}{\mathcal D_P}
=\frac{\mathcal A_P(x)}{\mathcal A_P(x)+\mathcal C_P(x)}.
\tag{4.5}
$$

The same reasoning gives this identity for $Q$. Each forest has exactly $n$ edges; its two weights lie within factors $\gamma^{-n},\gamma^n$. Summing proves that comparison for each positive denominator, marked sum and complementary sum. It gives the multiplicative part of (4.2).

If a complementary sum vanishes, it vanishes for both matrices and both hitting values equal one. Otherwise put $z=\mathcal A_P/\mathcal C_P>0$ and $\rho=(\mathcal A_Q/\mathcal A_P)/(\mathcal C_Q/\mathcal C_P)$. Then $\gamma^{-2n}\le\rho\le\gamma^{2n}$. Interchanging $P,Q$ if needed reduces to $\rho\ge1$. The hitting difference is

$$
\frac{(\rho-1)z}{(1+z)(1+\rho z)}
\le\frac{\rho-1}{(1+\sqrt\rho)^2}
=\frac{\sqrt\rho-1}{\sqrt\rho+1}
\le\frac{\gamma^n-1}{\gamma^n+1}.
\tag{4.6}
$$

The middle bound uses $z^{-1}+\rho z\ge2\sqrt\rho$. Boundary values agree. If $V$ is empty, all vertices are boundary; the empty forest has weight one and the bound is zero. Zero edges, reducible closed classes and arbitrarily small positive weights have all remained in this argument. $\square$

## 5. Normalized clipping and finite-path entropy

Relative entropy uses natural logarithms: $D(p\|q)=\sum_x p(x)\log(p(x)/q(x))$, with zero mass contributing zero. For two finite laws write $\|p-q\|_{\rm TV}=\frac12\sum_x|p(x)-q(x)|$.

**Lemma 5.1 (Lawful clipping and its scalar entropy).** For a finite integer $L\ge1$, define

$$
\pi_i=\sum_{k\le L}f_i(k),\qquad
J_i=\pi_i^{-1}\sum_{k\le L}f_i(k)B_k,\qquad
V_i=(1-\pi_i)^{-1}\sum_{k>L}f_i(k)B_k.
\tag{5.1}
$$

For target $i$ and $j=1-i$ put

$$
W_i=\pi_jJ_j+(1-\pi_j)V_i,\qquad
\gamma_L=1+\frac{c}{(L+1)^r},\qquad
\chi_{M,L}=\frac{\gamma_L^{M-2}-1}{\gamma_L^{M-2}+1}.
\tag{5.2}
$$

These matrices are stochastic and fix both labels. The matrices $W_i,U_j$ have common support and are entrywise comparable by $\gamma_L$. Their hitting functions differ by at most $\chi_{M,L}$.

Let $a_i^L$ be the law on $\{1,\ldots,L,\star\}$ with masses $f_i(k)$ and tail mass $1-\pi_i$, and put $D_i(s,L)=D(a_i^L\|a_j^L)$. Then $U_i,W_i$ also have common support, and for every configuration $x$,

$$
D(U_i(x,\cdot)\|W_i(x,\cdot))\le D_i(s,L).
\tag{5.3}
$$

Proof. Positivity of every $f_i(k)$ gives $0<\pi_i<1$. On $k>L$, the conditional tail likelihood ratio is exactly

$$
\frac{f_1(k)/(1-\pi_1)}{f_0(k)/(1-\pi_0)}
=\frac{1+c k^{-r}}{\displaystyle\sum_{\ell>L}
\frac{f_0(\ell)}{1-\pi_0}(1+c\ell^{-r})}.
\tag{5.4}
$$

Both numerator and denominator lie in $[1,\gamma_L]$. Averaging common nonnegative $B_k$ entries compares $V_0,V_1$ in both directions. Adding the opponent's entire short term $\pi_jJ_j$ gives the comparison of $W_i$ with $U_j$. Theorem 4.1 then supplies the hitting bound.

Define the positive full mass

$$
\widetilde f_i^L(k)=
\begin{cases}
f_j(k),&k\le L,\\
\dfrac{1-\pi_j}{1-\pi_i}f_i(k),&k>L.
\end{cases}
\tag{5.5}
$$

It sums to one and averages the $B_k$ to $W_i$. Directly,

$$
D(f_i\|\widetilde f_i^L)
=\sum_{k\le L}f_i(k)\log\frac{f_i(k)}{f_j(k)}
+(1-\pi_i)\log\frac{1-\pi_i}{1-\pi_j}
=D_i(s,L).
\tag{5.6}
$$

In particular the tail normalizer is retained. The joint laws $f_i(k)B_k(x,y)$ and $\widetilde f_i^L(k)B_k(x,y)$ have this entropy. Marginalizing $k$ proves (5.3) by log-sum: for nonnegative lists with sums $A,B>0$, concavity of logarithm gives $\sum a_\ell\log(a_\ell/b_\ell)\ge A\log(A/B)$. Apply it at each output $y$ and sum. The countable sums are legitimate since scalar ratios are bounded at each fixed $s,L$. Both full masses are strictly positive, so the two averages have identical positive support, including zero entries. Label rows agree and have entropy zero. All comparison laws are analytical; no operational gap or source is replaced. $\square$

**Lemma 5.2 (Entropy charged by actual live occupation).** Let $P,Q$ be finite stochastic kernels with common positive support and distinct fixed label rows $d_0,d_1$, starting from the same row $\nu$. Fix $0\le D_*<\infty$ and suppose every live row has $D(P(x,\cdot)\|Q(x,\cdot))\le D_*$. Suppose the actual $P$ chain first reaches a label at a time $N$ with $\mathbb E_PN<\infty$, and write $D\in\{0,1\}$ for that label's index. If $h$ is $Q$-harmonic, valued in $[0,1]$, and has $h(d_0)=0,h(d_1)=1$, then

$$
\left|\mathbb E_P D-\nu h\right|
\le\sqrt{D_*\mathbb E_PN/2}.
\tag{5.7}
$$

No termination property of $Q$ is a hypothesis.

Proof. For a finite $m$, let $\mathcal P_m,\mathcal R_m$ be the path laws through time $m$ of $P,Q$ from $\nu$. Their initial likelihood factors cancel. Expanding the finite products of Markov transition probabilities gives the entropy chain rule

$$
D(\mathcal P_m\|\mathcal R_m)
=\sum_{j=0}^{m-1}\mathbb E_P D(P(Y_j,\cdot)\|Q(Y_j,\cdot))
\le D_*\mathbb E_P(N\wedge m).
\tag{5.8}
$$

Only actual live rows contribute; absorbed rows have zero entropy.

Here is the needed Pinsker bound with its constant. For finite laws $p,q$, choose $E=\{x:p(x)\ge q(x)\}$. Then $p(E)-q(E)=\|p-q\|_{\rm TV}$. Log-sum onto $E,E^c$ bounds full entropy below by binary entropy. At fixed $v\in(0,1)$, the latter as a function of $u$ has value and first derivative zero at $u=v$, and second derivative $1/[u(1-u)]\ge4$. Integrating twice gives $D_{\rm Bern}(u\|v)\ge2(u-v)^2$. Endpoint cases follow by limits or absolute continuity. Thus $\|p-q\|_{\rm TV}\le\sqrt{D(p\|q)/2}$. Any $[0,1]$-valued function has expectation difference at most this variation, by splitting the positive and negative signed masses.

Apply this to $h(Y_m)$ on the path space. Harmonicity gives $\mathbb E_{\mathcal R_m}h(Y_m)=\nu h$ at every finite horizon. Under $P$, actual stopping and frozen labels give $h(Y_m)\to D$ almost surely. Bounded convergence, (5.8) and $\mathbb E_P(N\wedge m)\le\mathbb E_PN$ prove (5.7). No likelihood at an auxiliary stop and no auxiliary expected stopping time were used. $\square$

**Theorem 5.3 (Finite-parameter converse for each actual paid mean).** Put $b=1-2\alpha$. For every compliant observer, finite $M\ge2$, finite $L\ge1$ and target $i$,

$$
b\le r_{\rm init}(s)+\chi_{M,L}
+\sqrt{D_i(s,L)B(1-q)\mathbb E_iT/2}
\le r_{\rm init}(s)+\chi_{M,L}
+\sqrt{D_i(s,L)Bs\mathbb E_iT/2}.
\tag{5.9}
$$

There is also the direct full-law version

$$
b\le r_{\rm init}(s)
+\sqrt{D(f_i\|f_j)Bs\mathbb E_iT/2}.
\tag{5.10}
$$

Proof. For the first assertion, take $h$ to be the actual probability of ever hitting $d_1$ under $W_i$. It is bounded, harmonic and has the required label values by first-step conditioning. Lemmas 5.1–5.2 on the actual chain $U_i$ give $|p_i-\nu_i h|\le\sqrt{D_i\mathbb E_iN/2}$, where $p_i=\mathsf P_i(D=1)$. Let $h_j$ be the opponent's actual hitting function for $U_j$. Opponent almost-sure stopping from $\nu_j$ gives $p_j=\nu_jh_j$. Decompose

$$
p_i-p_j=(p_i-\nu_i h)+\nu_i(h-h_j)+(\nu_i-\nu_j)h_j.
\tag{5.11}
$$

Use the hitting comparison, initial variation and (3.6). Both risks give $p_1-p_0\ge b$. These steps prove (5.9) separately for each target of the same observer. For (5.10), use $Q=U_j$ and row log-sum with the full masses $f_i,f_j$. The hitting-comparison term is then zero. If an exact entropy is zero while the remaining separation is positive, these formulas prove emptiness of the compliant class; no division by zero is implicit. $\square$

## 6. The entropy phase estimates for every cutoff

**Theorem 6.1 (Normalization-aware phase bounds).** For the fixed source pair there are $C_D<\infty$ and $s_D\in(0,1)$, chosen before every cutoff, such that for every $0<s<s_D$, every finite integer $L\ge1$ and each direction $i,j=1-i$,

$$
D_i(s,L)\le
\begin{cases}
C_D\min\{s^{2r},s^aL^{a-2r}\},&a>2r,\\
C_Ds^a[1+\log(\min\{L,1/s\})],&a=2r,\\
C_Ds^a,&a<2r.
\end{cases}
\tag{6.1}
$$

The full-gap entropies are bounded respectively by $C_Ds^{2r}$, $C_Ds^a\log(e/s)$ and $C_Ds^a$, after enlarging $C_D$ if needed.

Proof. The exact normalized difference, including its signed drift, is

$$
w_k=f_1(k)-f_0(k)
=\frac{c[k^{d-r}-g(s)k^d]e^{-sk}}{Z_1(e^{-s})}.
\tag{6.2}
$$

Indeed $Z_1=(1+cg(s))Z_0$. For either reference direction $j$, $F_j(k)\ge k^d$ and $Z_j\le Z_1$. Hence

$$
\frac{w_k^2}{f_j(k)}
\le\frac{2c^2}{Z_0}e^{-sk}
\left(k^{d-2r}+g(s)^2k^d\right).
\tag{6.3}
$$

Lemma 2.3 provides a source-only neighborhood with $Z_0\ge C_0s^{-a}$ and $g(s)\le C_gs^r$. We use $C$ below for finite source-only constants, allowing a finite enlargement.

The elementary inequality $\log x\le x-1$ gives, for positive reference probabilities,

$$
D(p\|q)\le\sum_x\frac{(p(x)-q(x))^2}{q(x)}.
\tag{6.4}
$$

Summing (6.3) over all positive integers yields

$$
D(f_i\|f_j)\le C\left(\frac{R_{d-2r}(s)}{R_d(s)}+s^{2r}\right).
\tag{6.5}
$$

If $a>2r$, the integer $d-2r\ge0$, and the power sums of Lemma 2.3 give $Cs^{2r}$. If $a=2r$, its value is $-1$. Integrating the geometric series on $(0,e^{-s})$ gives

$$
R_{-1}(s)=\sum_{k\ge1}\frac{e^{-sk}}{k}
=-\log(1-e^{-s})\le C\log(e/s).
\tag{6.6}
$$

The inequality follows from $1-e^{-s}$ being comparable to $s$ near zero. If $a<2r$, the integer $d-2r\le-2$, and $R_{d-2r}(s)\le\sum k^{-2}\le1+\int_1^\infty x^{-2}\,dx=2$. Also $s^{2r}\le s^a$ for $s\le1$. These prove the full-law bounds. Log-sum shows that collapsing a tail cannot increase them.

To refine small cutoffs, first choose a fixed $\eta\in(0,1/2)$ such that

$$
\pi_j\le\frac{BL^a}{Z_0}\le C(sL)^a\le\frac12
\quad\text{whenever }sL\le\eta.
\tag{6.7}
$$

This uses $\sum_{k\le L}k^d\le L^{d+1}=L^a$ and the source-only lower bound for $Z_0$. The choice of $\eta$ precedes every $L$. Put

$$
S_j^L=\sum_{k\le L}\frac{w_k^2}{f_j(k)},\qquad
m_L=\sum_{k\le L}w_k=\pi_1-\pi_0.
\tag{6.8}
$$

The collapsed chi-square, with its full tail contribution, is $S_j^L+m_L^2/(1-\pi_j)$. Weighted Cauchy–Schwarz gives $m_L^2\le\pi_jS_j^L$. Consequently

$$
D_i(s,L)\le\frac{S_j^L}{1-\pi_j}\le2S_j^L
\le Cs^a\left(\sum_{k\le L}k^{d-2r}+s^{2r}L^a\right)
\quad(sL\le\eta).
\tag{6.9}
$$

The first inequality applies in either direction; the difference changes sign but its squared short and tail masses do not. It is precisely the normalized tail mass in (6.8), rather than an omitted drift, that makes the first bound valid.

For $a>2r$, the sum in (6.9) is at most $L^{a-2r}$ and $s^{2r}L^a=(sL)^{2r}L^{a-2r}\le L^{a-2r}$. For $a=2r$, the sum is at most $1+\log L$, and the second term is $(sL)^a\le1$. For $a<2r$, the sum is at most two and $s^{2r}L^a=(sL)^{2r}L^{a-2r}\le1$. These give (6.1) for $sL\le\eta$.

Every remaining cutoff is handled on the same neighborhood. If $a>2r$ and $\eta<sL<1$, the global bound satisfies $s^{2r}\le\eta^{-(a-2r)}s^aL^{a-2r}$. If $sL\ge1$, the minimum in (6.1) is its global term. At criticality shrink $s_D$ so $s\le\eta^2$. In the intermediate case $\eta<sL<1$,

$$
\log L>\log(\eta/s)\ge\tfrac12\log(1/s),
\tag{6.10}
$$

so the global logarithm is bounded by a constant times $1+\log L$. For $sL\ge1$, the minimum in (6.1) is $1/s$ and the global bound applies directly. In the rare-event case the global bound already handles every remaining cutoff. A finite enlargement of $C_D$ completes all cases simultaneously. There is no assumption that $L$ is fixed as $s\to0$, or that a growing budget has small $sL$. $\square$

## 7. Uniform lower bounds and their empty cases

**Theorem 7.1 (One neighborhood for all finite budgets).** Fix $(d,r,c,\alpha)$ as in Section 1. There exist $s_-\in(0,1)$ and $A_->0$, independent of all budgets and observers, such that for every $0<s<s_-$, finite integer $M\ge2$, observer $\mathcal A\in\mathfrak A_M(e^{-s},\alpha)$ and target $i$, the following bounds hold. With $b=1-2\alpha$ and

$$
L_M=\max\left\{1,\left\lceil\left(\frac{2c(M-2)}b\right)^{1/r}\right\rceil\right\},
\tag{7.1}
$$

they are

$$
\mathbb E_i^{\mathcal A}T\ge
\begin{cases}
A_-\max\{s^{-(2r+1)},s^{-(a+1)}M^{-(a-2r)/r}\},&a>2r,\\
\dfrac{A_-s^{-(a+1)}}{1+\log(\min\{L_M,1/s\})},&a=2r,\\
A_-s^{-(a+1)},&a<2r.
\end{cases}
\tag{7.2}
$$

Proof. Select $s_-$ from the source estimates and Theorem 6.1 so $r_{\rm init}(s)\le b/4$. This selection precedes $M$. For any finite $M$, choose $L=L_M$ before its observer. The function $f(u)=(e^u-1)/(e^u+1)$ has $f(0)=0$ and $f'(u)=2e^u/(e^u+1)^2\le1/2$, so $f(u)\le u/2$ for $u\ge0$. Also $\log(1+v)\le v$. Therefore

$$
\chi_{M,L}\le\frac{M-2}{2}\log\left(1+\frac{c}{(L+1)^r}\right)
\le\frac{(M-2)c}{2(L+1)^r}\le\frac b4.
\tag{7.3}
$$

For $M=2$, the expression is exactly zero. For $M>2$, the cutoff ensures $L^r\ge2c(M-2)/b$.

Theorem 5.3 leaves $b/2\le\sqrt{D_i(s,L)Bs\mathbb E_iT/2}$. Squaring nonnegative sides gives

$$
\frac{b^2}{4}\le\frac{D_i(s,L)Bs\mathbb E_iT}{2}.
\tag{7.4}
$$

Insert the corresponding strictly positive upper bound of Theorem 6.1 and divide by that upper bound. In the subcritical case the result is a constant times

$$
\max\{s^{-(2r+1)},s^{-(a+1)}L_M^{-(a-2r)}\}.
\tag{7.5}
$$

The ceiling, including the maximum with one, gives

$$
L_M\le1+\left(\frac{2c(M-2)}b\right)^{1/r}\le C_LM^{1/r},
\tag{7.6}
$$

with a source/risk constant $C_L$. This proves the first line of (7.2) after reducing $A_-$. The critical line follows directly from its positive logarithmic denominator. The rare-event line also follows this way; alternatively (5.10) and the full-law bound yield it with no forest loss at all. In every case all constants and the neighborhood precede every finite budget and design, and both directions concern the same actual observer. If an exact entropy vanished, (7.4) would contradict compliance; division was only by a positive source upper coefficient. $\square$

**Proposition 7.2 (Two labels and nonemptiness boundaries).** For $M=2$, the class $\mathfrak A_2(q,\alpha)$ is empty. The universal lower theorem supplies no nonemptiness conclusion for any budget.

Proof. The two internally emitted labels exhaust two complete configurations. A common initial choice emits one with some probability $p$, and the two risks would require $p\le\alpha$ and $1-p\le\alpha$, impossible when $2\alpha<1$. A statement universally quantified over an empty class is vacuous. For larger budgets, nonemptiness will follow from a constructed table at the stated sufficient threshold; this does not classify the minimum threshold or intermediate budgets. $\square$

## 8. Uniform geometric marks on actual gaps

**Lemma 8.1 (All-scale contrast).** There exist a real $\ell_0\ge1$, a source-only $s_U>0$, and positive finite comparison constants, all fixed before choosing a scale, such that for every $0<s<s_U$ and every real $\ell_0\le\lambda\le1/s$, put

$$
v=1/\lambda,\qquad z=e^{-v},\qquad
p_i=\frac{Z_i(e^{-(s+v)})}{Z_i(e^{-s})},\qquad \Delta=p_1-p_0.
\tag{8.1}
$$

Then uniformly on that entire interval,

$$
p_0\asymp(s\lambda)^a,\qquad
p_1\asymp p_0,\qquad
0<p_0<p_1\le\tfrac12,\qquad
\frac{\Delta}{p_0}\asymp\lambda^{-r}.
\tag{8.2}
$$

Here $u\asymp v$ means two positive inequalities with the stated uniform source-only constants. An actual-bit survival flag produces potential iid Bernoulli marks of means $p_i$, independently of the stationary first wait.

Proof. Start a flag at one after a paid tick. At each ensuing read zero, an alive flag survives with fresh probability $z$ and otherwise becomes zero. A failed flag stays zero while every remaining bit is read. At the closing paid tick, flag one has conditional probability $z^k$ if the gap has $K=k$ zeros. Averaging its law gives $\mathbb E_i z^K=p_i$. Reset the flag to one at each nonterminal closing tick. Disjoint iid gap and fresh-coin blocks define a potential iid mark sequence independent of $\tau$; the actual use is its stopped prefix. A mark is not independent of its own length.

Put $t=s+v$. The scale range gives $s\le v$ and $v\le t\le2v$, with $t\ge2s$. Choose $\ell_0$ large enough that all $t\le2/\ell_0$ lie in the source-only interval of (2.8) and have small uniform power-sum relative errors. Then

$$
p_0=\frac{R_d(t)}{R_d(s)}\asymp(s/t)^a\asymp(s\lambda)^a,
\qquad
\frac{\Delta}{p_0}=\frac{c[g(t)-g(s)]}{1+cg(s)}.
\tag{8.3}
$$

Integrating (2.8) between $s$ and $t$ bounds $g(t)-g(s)$ above and below by positive constant multiples of $t^r-s^r$. Since $r\ge1$ and $s\le v$,

$$
v^r\le(s+v)^r-s^r\le(2v)^r.
\tag{8.4}
$$

This proves the uniform contrast and its strict positivity. The denominator in (8.3) stays bounded above and below, and the same formula bounds $p_1/p_0$.

For the upper margin $p_1\le1/2$, the leading ratio $(s/t)^a$ is at most $2^{-a}\le1/4$, since $a\ge2$. Decrease the source interval so the two $R_d$ relative errors and the factor $(1+cg(t))/(1+cg(s))$ multiply to a number strictly less than two. This makes the desired bound uniform, even at $\lambda=1/s$. Finally choose $s_U\le1/\ell_0$ so the scale interval is nonempty. No threshold has depended on $\lambda$, a budget or an observer. The flag uses no length counter or accessible coin tape. $\square$

## 9. The complete controller, both risks and exact paid mean

**Definition 9.1 (The q-retuned survival and midpoint table).** Fix $s,\lambda$ in Lemma 8.1 and define immutable constants

$$
\theta=\frac{p_0+p_1}{2},\qquad
h_\alpha=\log\frac{1-\alpha}{\alpha}>0,\qquad
H=\left\lceil\frac{2h_\alpha p_1}{\Delta}\right\rceil\ge1.
\tag{9.1}
$$

The entire state set is a waiting state $w$, the two absorbing labels $d_0,d_1$, and

$$
(j,h),\qquad j\in\mathbb Z,\ -H<j<H,\qquad h\in\{0,1\}.
\tag{9.2}
$$

Initialize in $w$ under both sources. Every nonlabel state undertakes its next actual paid read. Entry into $d_i$ emits $D=i$ and stops immediately. Both label rows are identity rows on both bits for analytical continuation. Define upward and downward successors from an interior $j$ to be respectively $d_1$ when $j+1=H$ and $d_0$ when $j-1=-H$, or $(j+1,1)$ and $(j-1,1)$ otherwise. The complete bit rows are:

| State and read bit | Destinations and probabilities |
| --- | --- |
| $w$, zero | $w$ with probability one |
| $w$, one | $(0,1)$ with probability one |
| $(j,1)$, zero | $(j,1)$ with probability $z$; $(j,0)$ with probability $1-z$ |
| $(j,0)$, zero | $(j,0)$ with probability one |
| $(j,1)$, one | upward successor with probability $1-\theta$; $(j,1)$ with probability $\theta$ |
| $(j,0)$, one | downward successor with probability $\theta$; $(j,1)$ with probability $1-\theta$ |
| Either label, either bit | that label with probability one |

The held one successor resets the flag too. The table defines impossible consecutive-one inputs as well. The thresholds, successors and real probabilities are immutable design data selected from common $q$ and the public pair. No source label enters their selection.

**Theorem 9.2 (Full resource count, stopping, exact risks and payment).** This one table has exactly $4H+1$ listed complete configurations. It satisfies all six obligations at its selected $q$. Let $G$ be its number of completed post-first-tick gaps through absorption. With

$$
u_i=p_i(1-\theta),\qquad v_i=(1-p_i)\theta,\qquad
\rho_i=v_i/u_i,
\tag{9.3}
$$

its wrong-label probabilities and means are

$$
\begin{aligned}
e_0&=\frac1{1+\rho_0^H},&
e_1&=\frac1{1+\rho_1^{-H}},& e_i&\le\alpha,\\
\mathbb E_iG&=\frac{2H}{\Delta}(1-2e_i)\le\frac{2H}{\Delta},\\
\mathbb E_iT&=1+\beta_i+\mu_i\mathbb E_iG<\infty.
\end{aligned}
\tag{9.4}
$$

After decreasing $s_U$ independently of every scale, there are source/risk constants $K,C_U>0$ such that throughout the whole scale interval,

$$
4H+1\le K\lambda^r,\qquad
\mathbb E_iG\le C_U s^{-a}\lambda^{2r-a},\qquad
\mathbb E_iT\le C_U s^{-(a+1)}\lambda^{2r-a}.
\tag{9.5}
$$

Proof. The count is $1+2+2(2H-1)=4H+1$, including $H=1$. Every row in the table is nonnegative and sums to one. The pre-one flag is the mark; no separate mark register is required. Failed flags continue to read the entire gap. Each nonterminal one starts the next flag at one.

Use the potential independent gap/coin blocks of Lemma 8.1 to define the gap-boundary walk $J_n$, freezing it at $\pm H$ after its first boundary time $G$. Before absorption, its step law is upward $u_i$, downward $v_i$ and holding $1-u_i-v_i$. Both move probabilities are strictly positive. The drift is $u_i-v_i=p_i-\theta$, equal to $-\Delta/2$ under source zero and $+\Delta/2$ under source one. In the proof only, sign $J_n$ toward the correct label, giving $Z_n=-J_n$ or $Z_n=J_n$. This sign is not controller information. Let $\mathcal F_n$ contain the first wait and the first $n$ complete gap/coin blocks. Independence of the next block gives $\mathbb E_i[Z_{n+1}-Z_n\mid\mathcal F_n]=(\Delta/2)\mathbf1_{\{G>n\}}$. Summing these finite conditional expectations from $Z_0=0$ gives

$$
\mathbb E_i Z_{G\wedge m}=\frac\Delta2\mathbb E_i(G\wedge m)\le H
\quad(m\ge1).
\tag{9.6}
$$

Monotone convergence proves $\mathbb E_iG\le2H/\Delta<\infty$, hence $G<\infty$ almost surely, before any unbounded stopping formula is invoked. All individual gaps and $\tau$ are finite almost surely, so this is also a finite actual stop at a read closing tick.

The ratios satisfy $\rho_0>1$ and $0<\rho_1<1$. At each interior coordinate, $\rho_i^{J_n}$ is a martingale because

$$
u_i\rho_i+v_i/\rho_i+1-u_i-v_i=1.
\tag{9.7}
$$

The stopped value is bounded between its two finite boundary powers at this selected $q,H$. Bounded convergence at the already proved finite $G$ gives $1=P_i(J_G=H)\rho_i^H+(1-P_i(J_G=H))\rho_i^{-H}$. Solving gives the first two formulas in (9.4), with the appropriate wrong boundary under each law. For $0<x<y$, integrating $1/u$ gives $\log(y/x)\ge(y-x)/y$. Here $v_0\le\theta\le p_1$ and $u_1\le p_1$, so

$$
\log\rho_0\ge\frac{\Delta}{2v_0}\ge\frac{\Delta}{2p_1},\qquad
\log\rho_1^{-1}\ge\frac{\Delta}{2u_1}\ge\frac{\Delta}{2p_1}.
\tag{9.8}
$$

The ceiling in (9.1) makes each favorable boundary exponent at least $h_\alpha$. Hence each error is at most $1/(1+e^{h_\alpha})=\alpha$. The factor $p_1$ in the threshold is essential for rare marks. Passing to the limit in (9.6), with bounded convergence on its left and monotone convergence on its right, yields $(\Delta/2)\mathbb E_iG=H(1-2e_i)$.

On each terminating path this particular controller has the exact cost

$$
T=1+\tau+\sum_{n=1}^{G}(K_n+1).
\tag{9.9}
$$

The event $\{G\ge n\}$ is determined before gap $n$ from preceding completed gaps and coins and the independent first wait. It is independent of the next $K_n$. Tonelli thus gives

$$
\mathbb E_i\sum_{n=1}^{G}(K_n+1)
=\sum_{n\ge1}\mu_i\mathsf P_i(G\ge n)
=\mu_i\mathbb E_iG.
\tag{9.10}
$$

This is predictable inclusion, not independence of the current duration from its mark or absorption decision. It pays every holding gap, every failed-flag suffix, the first wait and first tick, and the terminal closing tick. Pointwise finite source moments and finite $\mathbb E_iG$ prove both finite paid means.

By (8.2), $p_1/\Delta\le C\lambda^r$ and $\Delta\ge C' (s\lambda)^a\lambda^{-r}$. The ceiling contributes at most one; since $\lambda\ge1$, it and all waiting/label/flag states are absorbed into one $K$ fixed before any budget. The gap-mean bound then gives $C s^{-a}\lambda^{2r-a}$. Lemma 2.3 gives $\mu_i\le C/s$ and $1+\beta_i\le C/s$. The initial term is absorbed uniformly: $s^{-a}\lambda^{2r-a}\ge1$ for $s\le1$. If $2r-a\ge0$, use $\lambda\ge1$; otherwise $\lambda\le1/s$ gives the stronger lower bound $s^{-2r}\ge1$. This proves (9.5) on a single source/risk neighborhood.

All possible histories remain in (9.2), even with indefinitely many zeros or holds. There is no unbounded gap or gap-number register, retained seed, coin index, arithmetic workspace, additional program phase, unread suffix or external decoder. Gap indices and coin blocks are analytical variables only. $\square$

## 10. Matching every sufficient subcritical budget

**Theorem 10.1 (The strict-subcritical matched frontier).** Suppose $a>2r$. There are $s_0>0$, $A_-,A_+>0$ and a finite integer $M_0$, depending only on the fixed $(d,r,c,\alpha)$, such that

$$
\begin{gathered}
\forall s\in(0,s_0)\ \forall M\in\mathbb Z,\ M\ge2\ 
\forall\mathcal A\in\mathfrak A_M(e^{-s},\alpha)\ \forall i\in\{0,1\}:\\
\mathbb E_i^{\mathcal A}T\ge A_-\Phi(s,M),\\[2mm]
\forall s\in(0,s_0)\ \forall M\in\mathbb Z,\ M\ge M_0\ 
\exists\mathcal A_{s,M}\in\mathfrak A_M(e^{-s},\alpha):\\
\max_{i\in\{0,1\}}\mathbb E_i^{\mathcal A_{s,M}}T\le A_+\Phi(s,M).
\end{gathered}
\tag{10.1}
$$

Both upper means are attained by the same controller at the selected $s,M$.

Proof. Use the lower theorem, and take the constants $\ell_0,K,C_U$ of Sections 8–9, enlarging $K$ to at least one if necessary. Choose an integer $M_0\ge K\ell_0^r$. Select $s_0$ inside both previously chosen neighborhoods with $s_0\le1/\ell_0$. All these choices precede $M$. For every $M\ge M_0$ put

$$
\lambda=\min\{(M/K)^{1/r},1/s\}.
\tag{10.2}
$$

This lies in the whole permitted scale range and gives $K\lambda^r\le M$, including the capped case. It is immutable probability design information; no continuously valued scale register is retained by the observer. With $h=a-2r>0$, the cost bound becomes

$$
\begin{aligned}
s^{-(a+1)}\lambda^{-h}
&=\max\{K^{h/r}s^{-(a+1)}M^{-h/r},\ s^{-(a+1)}s^h\}\\
&=\max\{K^\kappa s^{-(a+1)}M^{-\kappa},\ s^{-(2r+1)}\}.
\end{aligned}
\tag{10.3}
$$

One source/risk constant absorbs $K^\kappa$. Theorem 9.2 gives all six compliance conditions for this table and its two upper means. This proves (10.1) for every finite sufficient budget, with no budget-dependent shrinkage of $s_0$. $\square$

**Corollary 10.2 (Separate and joint infima).** For $M\ge M_0$, define

$$
\begin{aligned}
\mathfrak m_i(s,M)&=\inf_{\mathcal A\in\mathfrak A_M(e^{-s},\alpha)}\mathbb E_i^{\mathcal A}T,\\
\mathfrak m_{\max}(s,M)&=\inf_{\mathcal A\in\mathfrak A_M(e^{-s},\alpha)}
\max\{\mathbb E_0^{\mathcal A}T,\mathbb E_1^{\mathcal A}T\}.
\end{aligned}
\tag{10.4}
$$

Each of these three quantities lies in $[A_-\Phi(s,M),A_+\Phi(s,M)]$ on (10.1), with constants independent of $s,M$.

Proof. The lower inequality holds for each mean of every actual observer, so it also holds for their maximum and for each stated infimum. The one common table in (10.1) makes the class nonempty and bounds each of the three infima above. No separate optimizers have been combined, and no exact optimizer is asserted. $\square$

**Corollary 10.3 (Necessary and sufficient bulk-rate state order).** Keep $a>2r$. Suppose for every sufficiently small $s>0$ a family chooses a finite integer $M(s)$ and $\mathcal A_s\in\mathfrak A_{M(s)}(e^{-s},\alpha)$. Suppose, in addition, that for one fixed target $i_\star$ and one fixed $0<C_T<\infty$,

$$
\mathbb E_{i_\star}^{\mathcal A_s}T\le C_Ts^{-(2r+1)}
\quad\text{eventually for every sufficiently small }s.
\tag{10.5}
$$

Then $M(s)\ge C_*s^{-r}$ eventually for a positive constant depending only on the fixed source, risk and $C_T$. Conversely one common family has at most $K s^{-r}$ listed configurations and both paid means $O(s^{-(2r+1)})$.

Proof. Apply the all-budget lower bound to each selected actual observer in the intersection of its family neighborhood and (10.1). Its budget term and (10.5) give

$$
M(s)^\kappa\ge\frac{A_-}{C_T}s^{-(a-2r)}.
\tag{10.6}
$$

Taking the increasing positive root gives $C_*=(A_-/C_T)^{1/\kappa}$ and $M(s)\ge C_*s^{-r}$. This includes every growing regime, without assuming a power law or small $sM$. All opposing risk, stop and finite-mean conditions remain part of $\mathcal A_s$; no opposing bulk upper was required. For sufficiency set $\lambda=1/s$ in Theorem 9.2. Its common table has count at most $K s^{-r}$ and paid mean at most $C_Us^{-(2r+1)}$ under both labels. $\square$

For example, $(d,r)=(2,1)$ gives $\Phi(s,M)=\max\{s^{-3},s^{-4}/M\}$ and bulk budget order $s^{-1}$. The pair $(d,r)=(4,2)$ gives $\max\{s^{-5},s^{-6}/\sqrt M\}$ and budget order $s^{-2}$. These are source-dependent relations. Neither is a relabeling of the older rational-center polynomial theorem.

## 11. Strict rare-event order and the unresolved critical implementation

**Theorem 11.1 (The strict rare-event phase).** If $a<2r$, there are a fixed sufficient integer $M_0$, one $s_0>0$ and positive constants $A_-,A_+$, all independent of budgets, such that every compliant finite-budget observer pays at least $A_-s^{-(a+1)}$ under each source. For every $M\ge M_0$, a common q-retuned family with at most $M_0$ configurations pays at most $A_+s^{-(a+1)}$ under both. Each separate infimum and the joint infimum in (10.4) therefore have order $s^{-(a+1)}$, uniformly over all $M\ge M_0$ and $0<s<s_0$.

Proof. The budget-independent lower bound is Theorem 7.1, or directly (5.10) with the summable full-gap entropy of Theorem 6.1. For the upper choose $\lambda=\ell_0$ for every small $s$. Theorem 9.2 bounds its count by $K\ell_0^r$ and its two means by $C_U\ell_0^{2r-a}s^{-(a+1)}$. Take $M_0$ to be an integer at least that fixed count and choose the common neighborhood inside the lower and upper ones. The proof for the infima is the same quantified argument as Corollary 10.2. The state capacity is fixed; $\theta$ and possibly $H$ still retune with $q$. This asserts no single q-independent transition table. $\square$

Thus $(d,r)=(2,2)$ has paid order $s^{-4}$ with fixed sufficient capacity. Growing the capacity cannot improve this exponent under the stated model.

**Theorem 11.2 (Critical sandwich with budget dependence).** If $a=2r$, on one source/risk neighborhood every finite-budget compliant observer satisfies

$$
\mathbb E_iT\ge
\frac{A_-s^{-(a+1)}}{1+\log(\min\{L_M,1/s\})}
\ge\frac{A_-s^{-(a+1)}}{\log(e/s)},
\tag{11.1}
$$

where $L_M$ is (7.1). There is a common q-retuned family with one fixed sufficient capacity and both means $O(s^{-(a+1)})$. For every fixed sufficient $M$, the separate and joint infima have order $s^{-(a+1)}$, with lower constants allowed to depend on that fixed $M$.

Proof. The first bound is the critical line of Theorem 7.1. Since $1\le\min\{L_M,1/s\}\le1/s$, the second follows. With $\lambda=\ell_0$, Theorem 9.2 has fixed sufficient count and upper $C_Us^{-(a+1)}$, since $2r-a=0$. For fixed $M$, the first denominator is at most $1+\log L_M$, a constant, and the one upper table gives the corresponding infimum orders. These are fixed-capacity q-retuned families. $\square$

**Open problem 11.3 (The critical multiscale bridge).** At equality, the leading entropy density of Section 6 is $k^{d-2r}=1/k$. Summing through the typical length $1/s$ yields a logarithm. The bound for a single geometric scale in (9.5) has $\lambda^{2r-a}=1$ and supplies no logarithmic improvement. The full-gap entropy lower calculation alone supplies no attainable upper rate.

Closing the critical case requires a lawful actual-bit controller that combines enough scales on one history, counts its scale-selection state, every retained evidence coordinate, all phases and both labels, and proves both errors, both almost-sure actual stops and both finite actual paid means. It must either attain $s^{-(a+1)}/\log(e/s)$ with a declared complete budget or establish that the gain is unavailable under a specified budget. Separate per-scale optimal costs cannot be treated as simultaneously attainable or aggregated without an implementation proof. The one-scale estimate's lack of gain is also not an impossibility theorem for all controllers.

A precise necessary condition already follows. If a compliant critical family with fixed $C_T$ and fixed target attained an upper $C_Ts^{-(a+1)}/\log(e/s)$, (11.1) would force

$$
1+\log(\min\{L_{M(s)},1/s\})
\ge\frac{A_-}{C_T}\log(e/s).
\tag{11.2}
$$

By (7.6), $1+\log L_{M(s)}\le C+\frac1r\log(1+M(s))$. Hence budgets with $\log(1+M(s))=o(\log(1/s))$ cannot attain that proposed gain. This identifies a necessary obstruction without supplying a sharp necessary power, a sufficient multiscale budget, or the full critical frontier. For $(d,r)=(1,1)$, the retained sandwich is $s^{-3}/\log(e/s)$ versus $s^{-3}$.

## 12. A sparse perturbation with the same upper envelope

**Definition 12.1 (The distinct sparse pair).** Fix $d\ge1$ and $c>0$, put $a=d+1$ and $B=1+c$, and define

$$
F_0(k)=k^d,\qquad F_1^{\rm sp}(k)=k^d+c\mathbf1_{\{k=1\}}.
\tag{12.1}
$$

Use exactly Definition 2.1's stationary law, Definition 3.1's observer contract and its paid prefix convention with these shapes. For every integer $1\le r\le d$ this pair obeys

$$
k^d\le F_i(k)\le Bk^d,\qquad
0\le F_1^{\rm sp}(k)/F_0(k)-1\le c k^{-r}.
\tag{12.2}
$$

Its tail is zero after $k=1$, so it does not satisfy the persistent equality in (2.1).

**Theorem 12.2 (Matching sparse paid order with fixed sufficient capacity).** There exist $s_{\rm sp}>0$, $A_{{\rm sp},-},A_{{\rm sp},+}>0$ and a finite integer $M_{\rm sp}$, depending only on fixed $(d,c,\alpha)$, such that every compliant finite-budget observer has each mean at least $A_{{\rm sp},-}s^{-(d+2)}$. A common q-retuned family with at most $M_{\rm sp}$ configurations has both means at most $A_{{\rm sp},+}s^{-(d+2)}$. Consequently all three infima for $M\ge M_{\rm sp}$ have that order, uniformly over such budgets on $0<s<s_{\rm sp}$.

Proof. The partition functions are $Z_0=R_d(s)$ and $Z_1^{\rm sp}=R_d(s)+ce^{-s}$. All sums remain finite and the stationary normalization proof of Lemma 2.2 applies. Differentiating these partition functions or inserting the single exceptional term in the moment numerators gives

$$
\mu_i=\frac a s+O(1),\qquad \beta_i=\frac{a+1}{2s}+O(1).
\tag{12.3}
$$

The total added first-wait weight is $2ce^{-s}$, so the positive-mixture argument gives initial variation at most $2ce^{-s}/(R_{d+1}+R_d)=O(s^{a+1})$. The envelope verifies both hazards and predictable tick payment exactly as in Lemma 3.3: its proof used the growth bounds, not the persistent tail equality.

Put $\varepsilon=ce^{-s}/R_d(s)=O(s^a)$. The normalized difference is

$$
w_k=\frac{[c\mathbf1_{\{k=1\}}-\varepsilon k^d]e^{-sk}}{Z_1^{\rm sp}}.
\tag{12.4}
$$

For either reference direction, the same denominator comparison as (6.3) yields

$$
\sum_{k\ge1}\frac{w_k^2}{f_j(k)}
\le\frac{2}{R_d(s)}\left(c^2e^{-s}+\varepsilon^2R_d(s)\right)
\le C s^a.
\tag{12.5}
$$

Thus both full entropies are at most $Cs^a$. The direct finite-path harmonic comparison (5.10) applies to this pair: the full-gap row entropy is bounded by log-sum, the initial row comparison has just been established, and the actual tick price is still $Bs$. Select a source/risk neighborhood with initial variation at most $b/2$. Squaring the remaining separation gives the lower $A_{{\rm sp},-}s^{-(a+1)}$ for every finite budget.

For the upper, mark exactly the actual completed event $K=1$. Its potential iid Bernoulli probabilities are

$$
p_0=\frac{e^{-s}}{R_d(s)},\qquad
p_1=\frac{(1+c)e^{-s}}{R_d(s)+ce^{-s}},\qquad
\frac{p_1}{p_0}=\frac{1+c}{1+cp_0}.
\tag{12.6}
$$

They satisfy $p_0\asymp s^a$, $p_1\asymp p_0$, and, with $\Delta=p_1-p_0$,

$$
\frac{\Delta}{p_1}=\frac{c(1-p_0)}{1+c}\longrightarrow\frac{c}{1+c}>0.
\tag{12.7}
$$

Set $\theta=(p_0+p_1)/2$ and $H=\lceil2h_\alpha p_1/\Delta\rceil$. Shrinking the neighborhood to $p_0\le1/2$ bounds $H$ by the fixed finite integer $\lceil4h_\alpha(1+c)/c\rceil$.

Here is the whole category-table realization. Use $w,d_0,d_1$ and $(j,z)$ for $-H<j<H$, with $z\in\{0,1,2\}$. Category two means at least two zeros since the last tick. Initialize $w$ and have every nonlabel state read. In $w$, zero loops and one enters $(0,0)$. In any active state, zero changes $z$ to $\min\{z+1,2\}$ and keeps $j$. On a one with $z=1$, move upward with probability $1-\theta$ and hold with probability $\theta$. On a one with $z=0$ or $z=2$, move downward with probability $\theta$ and hold with probability $1-\theta$. Every nonterminal successor has category zero. Moving into $H$ emits $d_1$ and moving into $-H$ emits $d_0$; both labels absorb on both bits. These rules define every bit row, including the impossible consecutive-one case. Long gaps remain fully read after saturation.

The exact listed count is

$$
1+2+3(2H-1)=6H.
\tag{12.8}
$$

Take $M_{\rm sp}$ to be six times the preceding fixed integer bound. Each actual completed gap yields mark one precisely for $K=1$, and independent gaps yield the potential iid marks of (12.6). The midpoint step law is exactly (9.3), with drift $\pm\Delta/2$. The finite signed-drift calculation (9.6), the bounded boundary-power martingale (9.7), and the log-ratio inequalities (9.8) therefore apply to these marks, proving both risks and $\mathbb E_iG\le2H/\Delta\le Cs^{-a}$. This reuse requires only the proved Bernoulli block law, midpoint table and positive contrast, all established here; geometric survival is not a premise of that walk calculation.

This table completes every undertaken gap and stops on a read tick. The identical predictable event $\{G\ge n\}$ is fixed before gap $n$, so (9.9)–(9.10) give $\mathbb E_iT=1+\beta_i+\mu_i\mathbb E_iG\le Cs^{-(a+1)}$. They also give almost-sure actual stopping and finite paid means. The family has fixed sufficient capacity while its midpoint probabilities may retune with known $q$. Passing the universal lower and this one simultaneous upper to the three infima proves the assertion. $\square$

**Corollary 12.3 (The envelope does not determine the frontier).** If $a>2r$, the common upper bounds $k^d\le F_i(k)\le Bk^d$ and $0\le F_1/F_0-1\le c k^{-r}$ do not imply the persistent pair's matched frontier.

Proof. Both (1.1) and (12.1) obey those bounds. For the persistent pair, a finite growing budget of order $s^{-r}$ attains paid order $s^{-(2r+1)}$ under both sources. For the sparse pair, every compliant finite budget pays at least a positive multiple of $s^{-(a+1)}$. Since $a+1>2r+1$, these orders differ strictly. The exact persistent equality and its differentiated quotient contrast were used in Lemma 8.1; (12.2) provides neither. This is an obstruction to an envelope-only inference, and preserves all hypotheses of the persistent-pair theorem. $\square$

## 13. Supplier correspondence, resources and remaining source bridges

**Definition 13.1 (Mathematical supplier map).** The following identifiers denote the supplied texts and their mathematical ports. References inside them remain supplier attributions; they are not additional premises silently imported into this volume.

| Supplied text | Port and precise role |
| --- | --- |
| `lower-source.md`, “Growing state budgets in the renewal paid-mean tradeoff” | Sections 3–7 supply the same-budget representation, positive directed-forest and complementary-sum theorem, stationary mixture, normalized target clipping, live epochs and predictable tick payment. Sections 9–10 concern an older exact polynomial and its earlier necessary exponent. Sections 3–5 here develop the general interfaces and verify their hypotheses for the new pair. |
| `uniform-source.md`, “Retuned bounded-memory uniform renewal converse” | Definition 3.1 and Lemma 3.2 specify known-common-q source-blind retuning, complete configurations and real precision. Sections 5–7 give the clipping, initial-row and actual-stop/payment architecture. Its fixed-degree and nuisance-parameter results retain their original sources and quantifiers. |
| `fixed-observer-source.md`, “Real renewal instruments and detector rank: finite observer memory” | Definitions 23.2–23.3 and Lemma 23.4 identify stationary consecutive reads, fixed versus retuned observers, and normal form. Lemmas 25.1–25.3 give actual epoch and tick pricing; Section 26 gives predictable completed-gap pricing for its explicit construction. Proposition 27.2 supplies the geometric-kernel coordinate idea. Its rational-center shape, sum-four certificate and producer dimension are separate results. |
| `upper-proposal.json`, “A paid geometric-mark controller with O(s^(-1)) complete states and O(s^(-3)) mean under both exact renewal sources” | The mark, walk, risk and actual-bit-payment arguments supply the fully paid two-flag midpoint mechanism for the older pair. The new uniform scale contrast and rare-mark boundary proportional to $p_1/\Delta$ are explicit additions in Sections 8–9. |
| `upper-check.json` | A fallible handwritten check of that older upper proposal. Its judgment supplies no scalar estimate or approval for a different pair or for this authored source. |
| `refinement-proposal.json`, “Signed short-component clipping yields necessary Omega(s^(-8/9)) complete-state growth for an eventual cubic paid mean” | F2–F3 emphasize the normalized signed short difference and tail drift. Its proposal-wide older-pair exponent is not a premise here; (6.2) and (6.8) establish the needed normalization directly. |
| `entropy-proposal.json`, “Relative entropy of the clipped short law gives an eighth-power joint converse and necessary complete-state growth Omega(s^(-1))” | E1–E5 give the candidate finite-path/log-sum/Pinsker/harmonic route. Section 5 supplies the full ordinary bridge here, without assuming a separate checker outcome for that candidate. The new phase estimates are proved in Section 6. |
| `source-class-proposal.json`, “A scale-dependent paid controller gives a matched source-class state/read frontier, with a rare-event phase and a critical logarithmic gap” | S1–S6, U1–U3 and C1–C2 are the source-class deductions developed throughout this volume: exact positive sources, differentiated quotient, all-cutoff entropy phases, all-scale actual controller, matched resource curve and sparse obstruction. Its critical missing bridge is retained in Open problem 11.3. |
| `source-class-check.json`, “Independent handwritten approval of the conditional source-class frontier, strict phases and sparse-envelope obstruction” | Its bounded check concerns those proposal statements and their exact conditions. Fixed capacity is expressed here as a q-retuned family. Its additional `fixed_controller_wording_bridge` is excluded; no separate q-independent-table theorem is delivered. Proposal checking and final-source approval remain different acts. |

Power-series and geometric-series identities, equilibrium renewal normalization, stochastic kernels, directed matrix-tree/forest expansions, determinant multilinearity and column replacement, total-variation contraction, log-sum/data processing, entropy chain rules, Pinsker, chi-square domination, Cauchy–Schwarz, first-step harmonic equations, gambler's ruin, finite conditional drift, bounded convergence and predictable nonnegative summation are classical methods. The source-class contribution is their particular proved composition and the uniform source/resource statements, rather than invention of those methods.

The fixed-observer supplier attributes finite-statistic stochastic testing models to R. A. Flower and M. E. Hellman, “Hypothesis Testing With Finite Memory in Finite Time,” and stationary renewal conventions to S. Marzen and J. P. Crutchfield, “Informational and Causal Architecture of Discrete-Time Renewal Processes.” These are secondary source credits. The former concerns iid observations and finite-horizon error, while this volume requires renewal dependence, actual unbounded stopping and payment. No renewal paid-mean frontier is attributed to that paper, and those external papers' exact scopes are not independently certified here. The source-relative results are deductions from the stated model and displayed proofs, without an external priority audit.

**Definition 13.2 (Resource and applicability boundaries).** Complete configurations count all possible persistent states at the selected parameter, including low-probability histories. They are not expected or typical-history memory. A listed table can be indexed by $\lceil\log_2 M\rceil$ mutable bits, but this encoding does not price immutable real transition precision, design computation, exact-coin realization or physical storage. The survival flags and category saturation are counted mutable states; proof lengths, gap indices and independent coin arrays are not observer inputs. The paid resource counts actual source bits through the internally emitted label, rather than physical elapsed time.

The sufficient budgets are not minimum nonempty budgets. Intermediate capacities are not classified by the upper constructions. Matching order does not identify an exact optimizer or sharp constants. The critical all-budget frontier and multiscale logarithmic implementation remain open as specified in Section 11. There is no assertion of empirical machine-learning improvement, neural hidden dimension, producer state dimension, physical memory, finite-precision implementation or broader-project completion.

The parameters $d,r,c,\alpha$ stay fixed before every neighborhood, budget, scale and observer. No uniformity over changing parameters is claimed. Positivity of $c$ prevents tail cancellation and supplies (2.8)'s positive scale contrast. If $c=0$, the laws coincide and a common decision rule cannot meet both risks below one half. Signed or oscillating perturbations, fractional exponents, $r>d$, source resets, extra histories, hidden-state observations, unpaid gaps, archives, clocks and stopping-time decoders require different theorems.

**Open problem 13.3 (Transfer to other shapes).** A transfer to the older rational-center polynomial $H_c$, or to a general positive perturbation, requires its own bridge. One must verify the same observed stationary law and common-design contract, normalization and moment/hazard bounds, conditional-tail comparison and all-cutoff entropy estimates, and a two-sided differentiated partition-quotient contrast uniform over the whole scale interval. The needed upper conclusions must then be realized by one counted actual-bit controller with both risks and both paid means. A tail upper bound or a single kernel-coordinate separation does not supply these obligations. The sparse pair proves one concrete failure of the envelope-only route. No automatic transfer or new source-wide classification follows from sharing a degree, a leading coefficient or a suggestive analogy.

## 追加锚（本行以下为增补区）


