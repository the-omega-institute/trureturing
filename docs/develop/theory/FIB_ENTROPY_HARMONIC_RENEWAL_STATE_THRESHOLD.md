# Entropy-harmonic renewal converse and complete-state threshold

## 1. Result, mathematical ownership and reading conventions

For the fixed rational polynomial and stationary binary renewal laws specified below, a finite observer may be retuned arbitrarily at each known common parameter $q=e^{-s}$. Its budget counts every possible persistent configuration, including both internally emitted decision labels. Under the two selected risk bounds, both almost-sure stopping requirements and both finite pointwise paid means, this volume proves, on one neighborhood independent of the finite budget and observer,

$$
\mathbb E_{i,e^{-s}}^{\mathcal A}T
\ge C_\alpha\max\left\{s^{-3},\frac{s^{-11}}{L_M^8}\right\}
\ge C_\alpha\max\left\{s^{-3},\frac{s^{-11}}{X_M^8}\right\}
\quad(i=0,1),
\tag{1.1}
$$

where

$$
\begin{aligned}
b&=1-2\alpha>0,& C_\alpha&=\frac{b^2}{8B\delta^2},\\
L_M&=\max\left\{1,\left\lceil\frac{2\delta(M-2)}b\right\rceil\right\},
&X_M&=1+\frac{2\delta(M-2)}b.
\end{aligned}
\tag{1.2}
$$

Consequently, a family with an eventual cubic paid-mean upper bound $C_Ts^{-3}$ under one fixed target, with one fixed finite $C_T>0$, requires $M(s)=\Omega(s^{-1})$. The opposing source retains all its risk, stopping and finite-mean obligations. No cubic upper bound on that opposing mean is needed for this implication.

The proof compares the actual target epoch kernel with a source-clipped auxiliary kernel in relative entropy. At finite horizons, a bounded harmonic hitting function converts that entropy into a difference of expectations. Actual stopping supplies the limit; auxiliary stopping is unnecessary. The entropy coefficient retains the normalized signed short-law difference and its collapsed tail drift. Its small-cutoff estimate and a separate full-law estimate together cover every finite cutoff, including arbitrarily large $sL$.

The mathematical formulation and entropy argument are supplied by `entropy-proposal.json`, E1–E7, together with the distinct conditional handwritten assessment in `entropy-check.json`. The present E1–E7 give their complete ordinary proofs. The normal form, stationary comparison, directed-forest comparison and actual-read payment interfaces are supplied by the three source texts identified in Section 15 and exhibited here with their mathematical justification. Those existing results retain their ownership. The signed-short refinement supplies overlapping normalization structure; its proposed eighth-ninths growth consequence is not a premise of this proof.

The additional source-relative composition is the entropy-harmonic comparison, its all-cutoff eighth-power coefficient, the simultaneous paid converse and the necessary first-power state growth. Relative entropy, log-sum, Pinsker, chi-square bounds, Cauchy–Schwarz, harmonic hitting probabilities, directed forests, bounded convergence and predictable payment are classical methods. Their use is not a claim of invention or external priority. The classification here is `repo-derived`: ordinary deductions relative to explicitly credited handwritten premises.

All conclusions are conditional ordinary mathematics. In particular, the all-integer polynomial envelope and source moment estimates remain premises; their nested suppliers are not newly certified here. This text is reference theory without a Lean kernel certificate. A supplied proposal and its independent assessment do not constitute approval of this manuscript, or of any unsupplied final upper manuscript. The conditional upper comparison in Section 14 uses only its expressly stated mathematical supplier, and is not a dependency of the lower proof.

## 2. Exact source and stationary consecutive history

**Definition 2.1 (Fixed rational-center polynomial).** For a real argument $x$, fix exactly

$$
\begin{aligned}
H_c(x)=x^9+\frac1{35\cdot10^{24}}\bigl(&55800726477138x-224986136658885x^2
+420664314485485x^3\\
&-540138133491075x^4+518234977000797x^5
-254383031435085x^6\\
&+77668004560980x^7+43377331415040x^8\bigr).
\end{aligned}
\tag{2.1}
$$

Write $H=H_c$, $F_0(x)=x^9$, $F_1(x)=H(x)$, and retain

$$
\delta=\frac{2749658638697}{10^{24}}>0,
\qquad B=1+\delta,
\qquad a=\frac{43377331415040}{35\cdot10^{24}}>0.
\tag{2.2}
$$

This is the rational-center polynomial, with degree-eight coefficient $a$, rather than a limiting residual-zero vector. The constants are independent of $q$, the risk and the observer. Their displayed rational values give $0<\delta<1$ and $1<B<2$.

**Assumption 2.2 (All-integer source envelope).** The supplied envelope is

$$
\begin{gathered}
k^9\le F_i(k)\le Bk^9\quad(i=0,1),\\
1\le\frac{H(k)}{k^9}\le1+\frac\delta k
\qquad\text{for every integer }k\ge1.
\end{gathered}
\tag{2.3}
$$

The finite-observer continuation, Definition 23.1 and equation (23.3), supplies this premise and attributes its envelope proof to its owning source's Theorem 15.5. Both other supplied source texts retain it. No finite set of evaluations substitutes for its universal integer quantifier.

**Definition 2.3 (The two stationary renewal laws).** For $i\in\{0,1\}$ and $q\in(0,1)$, put

$$
\begin{aligned}
Z_i(q)&=\sum_{k\ge1}F_i(k)q^k,
&f_{i,q}(k)&=\frac{F_i(k)q^k}{Z_i(q)}\quad(k\ge1),
&f_{i,q}(0)&=0,\\
S_{i,q}(u)&=\sum_{k\ge u}f_{i,q}(k)\quad(u\ge0),
&\mu_i(q)&=\sum_{k\ge1}(k+1)f_{i,q}(k),\\
\beta_i(q)&=\frac{\sum_{k\ge1}k(k+1)f_{i,q}(k)}{2\mu_i(q)}.
\end{aligned}
\tag{2.4}
$$

All indices in these sums are integers. Positivity and the polynomial-geometric envelope give positive finite $Z_i$, full support $f_{i,q}(k)>0$ on the positive integers, and finite moments at every interior $q$.

The one-sided source law $\mathsf P_{i,q}$ first draws the first tick time $\tau$ with

$$
\mathsf P_{i,q}(\tau=u)=\frac{S_{i,q}(u)}{\mu_i(q)}
\quad(u=0,1,\ldots).
\tag{2.5}
$$

It places zeros before $\tau$ and a one at $\tau$. Independently of $\tau$, draw iid zero counts $K_1,K_2,\ldots$ with law $f_{i,q}$ and put all subsequent ones at

$$
\tau_0=\tau,
\qquad \tau_n=\tau+\sum_{r=1}^n(K_r+1)\quad(n\ge1).
\tag{2.6}
$$

All other bits of $X_0,X_1,\ldots$ are zero. Thus $K_r$ is a zero count and $K_r+1$ is a complete post-tick interval. The first stationary wait has law (2.5), not law $f_{i,q}$.

To verify its normalization and mean within the specified law, note $S_i(0)=S_i(1)=1$. Nonnegative summation counts each $k$ for $u=0,\ldots,k$ and gives

$$
\begin{aligned}
\sum_{u\ge0}S_i(u)&=\sum_{k\ge1}(k+1)f_i(k)=\mu_i,\\
\mathbb E_i\tau&=\frac1{\mu_i}\sum_{k\ge1}
\left(\sum_{u=0}^ku\right)f_i(k)
=\frac1{2\mu_i}\sum_{k\ge1}k(k+1)f_i(k)=\beta_i.
\end{aligned}
\tag{2.7}
$$

These formulas specify the experiment without giving the observer an initial age. The stationary interpretation and conventions are supplied by the continuation's Definition 23.2; its references to earlier renewal results remain supplier attributions.

**Assumption 2.4 (Source moment orders).** With $s=-\log q\downarrow0$, retain the supplied estimates

$$
Z_i(e^{-s})=9!s^{-10}(1+O_H(s)),
\qquad \mu_i(e^{-s})=\frac{10}s+O_H(1),
\qquad \beta_i(e^{-s})=\frac{11}{2s}+O_H(1).
\tag{2.8}
$$

These are the continuation's equation (23.7) and the two companions' corresponding source assumptions. Their nested polynomial-geometric moment derivations are credited. The lower argument needs only the consequences

$$
Z_0(e^{-s})\ge\frac{9!}{2}s^{-10},
\qquad \mu_0(e^{-s})\ge\frac5s
\quad(0<s<s_H)
\tag{2.9}
$$

for one sufficiently small $s_H>0$ depending only on the fixed source. Scalar power-sum inequalities used later are proved from their absolutely convergent series, rather than introduced as further moment premises.

## 3. Source-blind retuning and the complete configuration budget

**Definition 3.1 (Compliant finite observer).** Fix an integer $M\ge2$, a risk $0<\alpha<1/2$, and a known common parameter $q\in(0,1)$. A design may depend arbitrarily on $(q,H,\alpha,M)$, including its state set, real transition probabilities and initialization. The same design and the same source-independent initial distribution serve both true labels. Known $q$ and the public shapes are immutable design information; the true label and source-dependent advice are unavailable.

There are at most $M$ complete persistent configurations over all possible histories. This counts initialization configurations, every active configuration, both emitted labels, all control phases, registers, stored seeds and retained random choices. A counter or program phase is permitted only as part of these counted configurations. Fresh independent randomness may drive updates; every retained consequence of it must be represented by a counted configuration. Immutable real transition probabilities have unrestricted precision, and that precision is unpriced in this abstract model. No continuity in $q$, uniform positive exit bound or spectral-gap assumption is imposed.

An action reads the next actual bit or stops and internally emits $D\in\{0,1\}$. Choices depend only on the current configuration, the bit just read when applicable, and fresh randomness independent of the source and prior fresh randomness. Access is to the one uninterrupted consecutive history of Definition 2.3. There is no additional clock, external age, elapsed-read counter, program state, archive, skipped bit, free gap, source reset, extra source, hidden-state response, probability response or source oracle. The mathematical cost tally is not an input. The emitted label is the decision; no external decoder infers it from stopping time or read length.

If precisely $X_0,\ldots,X_{T-1}$ are read, the paid cost is $T$. It includes every read initial zero, subsequent zero, tick and terminal partial gap. Initial stopping has cost zero. Write $\mathfrak A_M(q,\alpha)$ for designs satisfying all six conditions

$$
\begin{gathered}
\mathsf P_{0,q}(D=1)\le\alpha,
\qquad \mathsf P_{1,q}(D=0)\le\alpha,\\
\mathsf P_{i,q}(T<\infty)=1,
\qquad \mathbb E_{i,q}T<\infty
\quad(i=0,1).
\end{gathered}
\tag{3.1}
$$

These are pointwise selected-pair promises at known common $q$, not a single $q$-free machine's full-family promises over separate unknown nuisance parameters. This class is the uniform companion's Definition 3.1, also retained by the growing-budget source and both entropy suppliers.

**Lemma 3.2 (Same-budget read-ready normal form).** At the selected $q$, such a design is represented by a common row distribution $\eta$ and common row-stochastic zero and one matrices $A,C$ on a finite set $\mathcal S$, with $|\mathcal S|\le M$. Two distinct configurations $d_0,d_1$ carry the decisions and are absorbing for both matrices. Every other configuration is committed to its next paid read. This preserves the joint law of $(T,D)$ under both sources.

Proof. Compose initialization with the state-based choice to read or stop, placing stopping probability on its emitted label. After a bit read, compose the update with the ensuing choice to read or stop. All information retained through that choice is already in the complete configuration, so these stochastic compositions add no persistent state. Merge terminal configurations with the same label, retaining distinct labels $d_0,d_1$, and fix their rows under both bit matrices. Before a label is reached, the read sequence and decision agree with the original design. Holding the label fixed on unused future bits changes neither actual $T$ nor $D$. Fresh update randomness is marginalized into each stochastic row; it is not replaced by a deterministic machine with an accessible random tape. This is the continuation's Lemma 23.4 as applied pointwise by the uniform companion's Lemma 3.2. $\square$

Suppress $q$ in $f_i,S_i,\mu_i$ and the actual machine when convenient. For analytical purposes define

$$
K_k=A^kC,
\qquad U_i=\sum_{k\ge1}f_i(k)K_k,
\qquad \nu_i=\sum_{u\ge0}\frac{S_i(u)}{\mu_i}\eta A^uC.
\tag{3.2}
$$

These stochastic averages retain the absorbing labels. The map $k\mapsto K_k$ is common to both source laws; the first-wait map $u\mapsto\eta A^uC$ is also common. The analytical continuation after a stop supplies no new operational observation or paid read.

## 4. The supplied positive-forest hitting comparison

**Lemma 4.1 (Common-support hitting bound).** Let $P,Q$ be stochastic matrices on the same finite set $\mathcal S$, with $|\mathcal S|\le M$ and the two common absorbing labels. Suppose $\gamma\ge1$ and

$$
\gamma^{-1}P(x,y)\le Q(x,y)\le\gamma P(x,y)
\quad(x,y\in\mathcal S).
\tag{4.1}
$$

Let $h_P,h_Q$ be the actual probabilities of ever reaching $t=d_1$, allowing time zero. Let $\mathcal Z$ be the common set of vertices with no positive directed path to $t$, let $\partial=\mathcal Z\cup\{t\}$, and put $V=\mathcal S\setminus\partial$, $n=|V|$. Then $d_0\in\mathcal Z$, so $n\le M-2$, and

$$
\gamma^{-2n}h_P(x)\le h_Q(x)\le\gamma^{2n}h_P(x),
\qquad |h_Q(x)-h_P(x)|\le\frac{\gamma^n-1}{\gamma^n+1}.
\tag{4.2}
$$

This is the growing-budget source's Theorem 5.1, with its positive-forest proof supplied in Sections 4–5. The following argument exhibits that interface independently of global absorption assumptions.

Proof. Entrywise comparison makes the two positive directed supports identical. Each hitting value is zero on $\mathcal Z$ and one at $t$. Indeed, hitting is a countable union of finite-time events, each requiring a positive finite path; conversely a positive path has positive probability. Replace rows on $\mathcal Z$ by identity rows in both matrices. Once $\mathcal Z$ is entered the target is inaccessible, so this replacement preserves hitting probabilities, comparison and the vertex set. All boundary vertices now absorb.

For each $u\in V$, choose one positive edge $u\to\phi(u)$ with $\phi(u)\ne u$, with no directed cycle in $V$. Such a choice is a directed forest rooted in $\partial$. Every forest has exactly $n$ edges. For either matrix $P$, define its weight and three sums

$$
\begin{aligned}
w_P(\phi)&=\prod_{u\in V}P(u,\phi(u)),
&\mathcal D_P&=\sum_\phi w_P(\phi),\\
\mathcal A_P(x)&=\sum_{\phi:\,x\text{ ends at }t}w_P(\phi),
&\mathcal C_P(x)&=\sum_{\phi:\,x\text{ ends in }\mathcal Z}w_P(\phi).
\end{aligned}
\tag{4.3}
$$

Thus $\mathcal D_P=\mathcal A_P(x)+\mathcal C_P(x)$. Every vertex in $V$ has a path to $t$. Choosing first edges of shortest such paths gives a forest with every path ending at $t$, since distances decrease along those edges. Hence $\mathcal D_P$ and every $\mathcal A_P(x)$ are positive; the complementary sum may be zero.

Index coordinates by $V$ and put $L_P=I-P_{VV}$ and $r_P(u)=P(u,t)$. Stochastic row sums give

$$
L_P(u,\cdot)=\sum_{v\ne u}P(u,v)
\left(e_u^{\mathsf T}-\mathbf1_{\{v\in V\}}e_v^{\mathsf T}\right).
\tag{4.4}
$$

Expand the determinant in these rows. A cyclic successor choice contributes zero because its cycle rows sum to zero. For an acyclic choice, order vertices by increasing distance along its chosen path to the boundary. The selected-row matrix is triangular with diagonal one, so its determinant is one. Permuting rows and columns together introduces no sign. Thus $\det L_P=\mathcal D_P>0$. Self-loops are accounted for by $1-P(u,u)=\sum_{v\ne u}P(u,v)$, rather than removed from the stochastic experiment.

For the matrix $L_P^{[x]}$ with column $x$ replaced by $r_P$, expand by the same row coefficients. Cycle rows still sum to zero, including in the replaced column, whose cycle entries are zero. For a forest $\phi$, write $L_\phi$ for its selected-row matrix and $z_\phi(u)$ for the indicator that $u$ ends at $t$. Directly along each edge,

$$
L_\phi z_\phi=r_\phi,
\qquad r_\phi(u)=\mathbf1_{\{\phi(u)=t\}}.
\tag{4.5}
$$

Replacing column $x$ by $r_\phi$ and expanding it as the weighted sum of columns of $L_\phi$ annihilates every duplicated-column term except $x$. The surviving determinant is $z_\phi(x)\det L_\phi=z_\phi(x)$. Therefore $\det L_P^{[x]}=\mathcal A_P(x)$.

First-step conditioning of the actual hitting probability yields $L_P(h_P|_V)=r_P$ with the stated boundary values. The positive determinant makes this boundary problem invertible. The column-replacement identity then gives

$$
h_P(x)=\frac{\mathcal A_P(x)}{\mathcal D_P}
=\frac{\mathcal A_P(x)}{\mathcal A_P(x)+\mathcal C_P(x)}.
\tag{4.6}
$$

The same facts hold for $Q$ using the identical forest family. This identifies actual hitting probabilities without imposing uniqueness on arbitrary harmonic functions on the original reducible chain.

Each forest weight changes by a factor between $\gamma^{-n}$ and $\gamma^n$. Summing over the full, marked or complementary forest family gives the same comparison for $\mathcal D$, $\mathcal A$ and $\mathcal C$. Taking the marked-to-full quotient proves the multiplicative assertion with exponent $2n$.

For the additive assertion, if $\mathcal C_P(x)=0$, comparison also makes $\mathcal C_Q(x)=0$ and both values equal one. Otherwise set

$$
z=\frac{\mathcal A_P(x)}{\mathcal C_P(x)}>0,
\qquad r=\frac{\mathcal A_Q(x)/\mathcal A_P(x)}
{\mathcal C_Q(x)/\mathcal C_P(x)}\in[\gamma^{-2n},\gamma^{2n}].
\tag{4.7}
$$

Interchanging $P,Q$ when needed reduces to $1\le r\le\gamma^{2n}$. The difference is $(r-1)z/[(1+z)(1+rz)]$. Since $z^{-1}+rz\ge2\sqrt r$,

$$
\frac{(1+z)(1+rz)}z\ge(1+\sqrt r)^2,
\qquad h_Q(x)-h_P(x)
\le\frac{\sqrt r-1}{\sqrt r+1}
\le\frac{\gamma^n-1}{\gamma^n+1}.
\tag{4.8}
$$

The last fraction increases with its nonnegative argument. Boundary values agree. If $V$ is empty, take the empty forest weight to be one; all states already have boundary values and the difference is zero. This also handles $n=0$ and $\gamma=1$. Zero edges, closed non-target classes and arbitrarily small positive exits introduce no exception. $\square$

## 5. Stationary initial comparison and source clipping

**Lemma 5.1 (Common stationary first-row estimate).** For the actual rows in (3.2), define

$$
R_m(q)=\sum_{k\ge1}k^mq^k,
\qquad r_H(q)=\delta\frac{R_9(q)+R_8(q)}{R_{10}(q)+R_9(q)}.
\tag{5.1}
$$

With $\|u-v\|_{\rm TV}=\tfrac12\sum_x|u(x)-v(x)|$,

$$
\|\nu_0-\nu_1\|_{\rm TV}\le r_H(q)\le\frac{2\delta}{\mu_0(q)}.
\tag{5.2}
$$

Proof. Use unnormalized first-wait weights

$$
G_i(u)=\sum_{k\ge\max(1,u)}F_i(k)q^k,
\qquad \mathcal W_i=Z_i\mu_i=\sum_{k\ge1}(k+1)F_i(k)q^k.
\tag{5.3}
$$

Nonnegative summation gives $\sum_uG_i(u)=\mathcal W_i$; the exact first-wait law is $G_i/\mathcal W_i$. The envelope gives $G_1\ge G_0$ and

$$
0\le\mathcal W_1-\mathcal W_0\le\delta(R_9+R_8),
\qquad\mathcal W_0=R_{10}+R_9.
\tag{5.4}
$$

When the difference is positive, normalize $G_1-G_0$ to a probability law $v$. Then $G_1/\mathcal W_1$ is the mixture of $G_0/\mathcal W_0$ and $v$ with respective weights $\mathcal W_0/\mathcal W_1$ and $(\mathcal W_1-\mathcal W_0)/\mathcal W_1$. Its variation from the first law is at most the latter weight, hence at most $r_H$. If the difference is zero the laws agree.

The common stochastic map $u\mapsto\eta A^uC$ contracts variation: for every state event its conditional probability lies in $[0,1]$, so the difference of its averages is at most input variation. This proves the first inequality. Since $R_8\le R_9$ and $\mu_0=(R_{10}+R_9)/R_9$, the second follows. This is the uniform companion's Lemma 5.1 and the growing-budget source's Lemma 6.1. It remains uniform over arbitrary common initialization and retuning. $\square$

**Definition 5.2 (Per-target clipped kernel).** For a finite integer $L\ge1$, put

$$
\begin{aligned}
\pi_i&=\sum_{k=1}^Lf_i(k),
&J_i^L&=\frac1{\pi_i}\sum_{k=1}^Lf_i(k)K_k,\\
V_i^L&=\frac1{1-\pi_i}\sum_{k>L}f_i(k)K_k,
&\gamma_L&=1+\frac\delta{L+1}.
\end{aligned}
\tag{5.5}
$$

Every mass is positive and $0<\pi_i<1$. These matrices are stochastic and fix both labels. For target $i$ and opponent $j=1-i$, define the proof kernel

$$
W_i=\pi_jJ_j^L+(1-\pi_j)V_i^L.
\tag{5.6}
$$

**Lemma 5.3 (Comparison to the actual opponent).** For both target choices,

$$
\gamma_L^{-1}U_j(x,y)\le W_i(x,y)\le\gamma_LU_j(x,y).
\tag{5.7}
$$

Proof. On $k>L$, $t(k)=H(k)/k^9$ lies in $[1,\gamma_L]$. The exact ratio of conditional tail laws is

$$
\frac{f_1(k)/(1-\pi_1)}{f_0(k)/(1-\pi_0)}
=\frac{t(k)}{\displaystyle\sum_{\ell>L}
\frac{f_0(\ell)}{1-\pi_0}t(\ell)}.
\tag{5.8}
$$

Its denominator is in the same interval, so both conditional tail laws are comparable by $\gamma_L$ in either direction. Averaging the same nonnegative $K_k(x,y)$ transfers comparison to $V_0^L,V_1^L$. The opponent kernel is $U_j=\pi_jJ_j^L+(1-\pi_j)V_j^L$. Adding its identical nonnegative short term to the two compared tails proves (5.7), including all zero entries. This is the clipping comparison of the uniform companion's Lemma 5.2 and the growing-budget source's Lemma 6.2. The proof kernel keeps the entire opponent short term; it neither deletes an actual gap nor supplies a tail-only source. $\square$

## 6. Analytical epochs and actual paid reads

**Lemma 6.1 (Live epochs of the actual observer).** Follow the full source history analytically while holding any actually emitted label fixed thereafter. Let $Y_n$ be the state immediately after the tick at $\tau_n$, and define

$$
N=\inf\{n\ge0:Y_n\in\{d_0,d_1\}\},
\qquad Q_T=\sum_{t\ge0}\mathbf1_{\{T>t\}}X_t,
\qquad p_i=\mathsf P_{i,q}(D=1).
\tag{6.1}
$$

Under source $i$, $Y_0$ has law $\nu_i$ and $Y_n$ has kernel $U_i$. For a compliant actual observer,

$$
N<\infty\ \text{almost surely},
\qquad Y_N=d_D,
\qquad N\le Q_T\le T,
\qquad\mathbb E_iN<\infty.
\tag{6.2}
$$

Proof. The actual first-wait law and independence of subsequent gaps give (3.2), with ordinary fresh update randomness along each analytical epoch. If stopping is before or at the first tick, $N=0$. Otherwise each $Y_r$, $r<N$, is a live read-ready state immediately after a distinct actually read tick, and commits to another read. These $N$ ticks are included in $Q_T$, proving $N\le Q_T\le T$.

If the stop occurs during zeros, the next analytical tick records only the already fixed label; that tick may be unread and is not added to $Q_T$. Every source interval is finite almost surely. Actual almost-sure stopping therefore gives finite $N$ and the recorded label $Y_N=d_D$. The finite actual paid mean gives finite $\mathbb E_iN$. These are the continuation's Lemma 25.1 and the two companions' actual-epoch interface. $\square$

**Lemma 6.2 (Predictable payment for actual ticks).** For every legal read/stop rule in the specified experiment,

$$
\mathbb E_{i,q}Q_T\le B(1-q)\mathbb E_{i,q}T,
\qquad \mathbb E_{i,q}N\le B(1-q)\mathbb E_{i,q}T
\text{ for compliant finite observers}.
\tag{6.3}
$$

Proof. After an observed tick and exactly $u\ge1$ subsequent zeros, the conditional next-one probability, given the entire preceding history, is

$$
\frac{f_i(u)}{S_i(u)}
=\frac{F_i(u)q^u}{\sum_{k\ge u}F_i(k)q^k}
\le\frac{Bu^9q^u}{\sum_{k\ge u}u^9q^k}
=B(1-q).
\tag{6.4}
$$

At $u=0$ it is zero because $K\ge1$. Earlier completed gaps are independent of the current gap, justifying conditioning on the whole preceding history.

Before any tick, $u$ zeros mean $\tau\ge u$. The actual stationary next-one hazard is

$$
\frac{S_i(u)}{\sum_{v\ge u}S_i(v)}.
\tag{6.5}
$$

For integers $k\ge1,r\ge0$, the envelope gives $F_i(k+r)\ge(k+r)^9\ge k^9\ge B^{-1}F_i(k)$. Shifting each tail term by $r$ yields $S_i(u+r)\ge B^{-1}q^rS_i(u)$. At $u=0$ the shifted terms start at $r+1$ and are contained in the tail defining $S_i(r)$, which suffices for the same inequality. Summing over $r$ bounds the denominator of (6.5) below by $B^{-1}S_i(u)/(1-q)$. Thus the stationary first-wait hazard also is at most $B(1-q)$.

For payment alone, expose an independent supply of the observer's coins on the analytical probability space, and let $\mathcal F_t$ contain them and the prefix $X_0,\ldots,X_{t-1}$. Independence preserves the source hazard bounds. The event $\{T>t\}$ that the next read is undertaken is $\mathcal F_t$-measurable. Tonelli and conditional expectation give

$$
\begin{aligned}
\mathbb E_iQ_T
&=\sum_{t\ge0}\mathbb E_i\left[
\mathbf1_{\{T>t\}}\mathbb E_i(X_t\mid\mathcal F_t)\right]\\
&\le B(1-q)\sum_{t\ge0}\mathsf P_i(T>t)
=B(1-q)\mathbb E_iT.
\end{aligned}
\tag{6.6}
$$

Combine with (6.2) for the second assertion. The enlarged filtration is solely a predictability device; it gives the machine no retained tape and is not the epoch filtration used for the Markov entropy argument. Only reads actually undertaken are charged, including the terminal read. No unread closing tick or full expected gap is substituted for an interrupted gap. This is the continuation's Lemma 25.3 and the companions' predictable-payment interface. $\square$

## 7. E1: normalized signed difference and exact collapsed entropy

Use natural logarithms throughout. For probability laws $p,r$ on a finite or countable set, relative entropy is

$$
\operatorname{KL}(p\Vert r)=\sum_zp(z)\log\frac{p(z)}{r(z)},
\tag{7.1}
$$

with zero terms interpreted as zero and positive mass against a zero reference giving infinite entropy. All scalar laws below have strictly positive masses and bounded likelihood ratios at fixed interior $q$ and finite $L$, so their entropy series are finite and absolutely convergent.

**Lemma 7.1 (E1: exact normalization and lawful source clipping).** Define

$$
\Delta_H(k)=H(k)-k^9,
\qquad \epsilon=\frac{Z_1-Z_0}{Z_0},
\qquad w_k=f_1(k)-f_0(k).
\tag{7.2}
$$

Then $0\le\Delta_H(k)\le\delta k^8$, $Z_0=R_9$, $Z_1=(1+\epsilon)Z_0$, $\epsilon\ge0$, and

$$
w_k=\frac{[\Delta_H(k)-\epsilon k^9]q^k}{Z_1}.
\tag{7.3}
$$

For a finite integer $L\ge1$, let the collapsed laws on $\{1,\ldots,L,\star\}$ be

$$
a_i^L(k)=f_i(k)\quad(1\le k\le L),
\qquad a_i^L(\star)=1-\pi_i,
\qquad d_i(q,L)=\operatorname{KL}(a_i^L\Vert a_j^L),\quad j=1-i.
\tag{7.4}
$$

Define on all positive integers the source-clipped probability law

$$
g_i^L(k)=
\begin{cases}
f_j(k),&k\le L,\\
\dfrac{1-\pi_j}{1-\pi_i}f_i(k),&k>L.
\end{cases}
\tag{7.5}
$$

It has positive masses, its common stochastic image is exactly $W_i$, and

$$
W_i=\sum_{k\ge1}g_i^L(k)K_k,
\qquad \operatorname{KL}(f_i\Vert g_i^L)=d_i(q,L),
\qquad \operatorname{KL}(U_i(x,\cdot)\Vert W_i(x,\cdot))\le d_i(q,L).
\tag{7.6}
$$

In particular, $U_i,W_i$ have the same positive support; their absorbing label rows agree and have entropy zero.

Proof. Subtracting the two normalized source masses using $Z_1=(1+\epsilon)Z_0$ gives

$$
\frac{H(k)q^k}{Z_1}-\frac{k^9q^k}{Z_0}
=\frac{[H(k)-(1+\epsilon)k^9]q^k}{Z_1},
\tag{7.7}
$$

which is (7.3). Normalization drift remains in every signed coefficient; the normalized difference is not the unnormalized nonnegative polynomial difference.

The short mass of $g_i^L$ is $\pi_j$, and its tail mass is $1-\pi_j$. It is therefore a probability law with positive masses. Averaging $K_k$ under its short and tail parts gives (5.6), exactly. On the tail $f_i(k)/g_i^L(k)$ is the constant $(1-\pi_i)/(1-\pi_j)$. Hence

$$
\begin{aligned}
\operatorname{KL}(f_i\Vert g_i^L)
&=\sum_{k=1}^Lf_i(k)\log\frac{f_i(k)}{f_j(k)}
+(1-\pi_i)\log\frac{1-\pi_i}{1-\pi_j}\\
&=d_i(q,L).
\end{aligned}
\tag{7.8}
$$

The data-processing step can be proved directly with zero entries and the countable gap index. For nonnegative lists $a_k,b_k$ having the same positive support, sums $A,B>0$, and ratios bounded above and away from zero on that support, put $\lambda_k=a_k/A$. Concavity of $\log$ yields

$$
\sum_k\lambda_k\log\frac{b_k}{a_k}
\le\log\left(\sum_k\lambda_k\frac{b_k}{a_k}\right)
=\log\frac BA.
\tag{7.9}
$$

Thus $\sum_ka_k\log(a_k/b_k)\ge A\log(A/B)$. Taking $A=B=1$ also proves nonnegativity of the scalar entropies used here. Countable Jensen applies because the logarithms are bounded and the weights sum to one; finite truncation with a remainder atom followed by a limit gives the same inequality. If $A=0$, all $a_k$ vanish and the zero contribution convention applies. With common support, $B=0$ occurs exactly in that same case. The positive-against-zero case would give infinite entropy, but does not arise here.

At a fixed configuration $x$, use joint masses $f_i(k)K_k(x,y)$ and $g_i^L(k)K_k(x,y)$. A zero $K_k(x,y)$ contributes zero under both laws. Where it is positive, the joint likelihood ratio is $f_i(k)/g_i^L(k)$. The finitely many short ratios and the single positive tail ratio are bounded above and away from zero. Consequently all relevant logarithmic sums are absolutely summable. The joint entropy is $\operatorname{KL}(f_i\Vert g_i^L)$, since $\sum_yK_k(x,y)=1$. Apply (7.9) for each output $y$ and sum over the finite output set to obtain (7.6). This uses a common stochastic map, with no rowwise selection of different gap laws.

Both kernels average every $K_k$ with positive weights, so an entry is positive in one exactly when some $K_k$ entry is positive, equivalently when it is positive in the other. At either label all $K_k$ rows are the same identity row. Its entropy is zero. The source clipping is an analytical law, not an additional source available to the observer. $\square$

The tail drift is also visible in the signed image. Put $m_L=\sum_{k\le L}w_k=\pi_1-\pi_0$. Exact subtraction gives

$$
U_1-W_1=\sum_{k\le L}w_kK_k-m_LV_1^L,
\qquad U_0-W_0=-\sum_{k\le L}w_kK_k+m_LV_0^L.
\tag{7.10}
$$

These are the signed-short identities exposed in the refinement supplier. The collapsed signed measure has coefficients $w_k$ on short symbols and $-m_L$ on the tail symbol, with total mass zero. Its variation is

$$
\kappa_L=\frac12\left(\sum_{k\le L}|w_k|+|m_L|\right).
\tag{7.11}
$$

Its stochastic image has variation at most $\kappa_L$: for any state event the image's conditional values lie in $[0,1]$, and the positive and negative masses of the signed measure both equal $\kappa_L$. If $\kappa_L=0$, the collapsed laws agree, hence both entropies $d_i(q,L)$ vanish. No cancellation or sign of $m_L$ is assumed. The entropy proof keeps this drift through the collapsed tail mass.

## 8. E2: all-parameter power sums and both entropy directions

**Lemma 8.1 (E2: global scalar entropy bound).** At every $q\in(0,1)$, writing $r=1-q$,

$$
\frac{R_8}{R_9}\le r,
\qquad \frac{R_7}{R_9}\le r^2,
\qquad \epsilon\le\delta r,
\qquad d_i(q,L)\le4\delta^2r^2
\tag{8.1}
$$

for both targets and every finite integer $L\ge1$.

Proof. Absolute convergence permits shifting the power sums. For integers $m\ge1$,

$$
(1-q)R_m(q)=\sum_{k\ge1}[k^m-(k-1)^m]q^k.
\tag{8.2}
$$

Since $(k-1)^m\le(k-1)k^{m-1}$, each bracket is at least $k^{m-1}$. Therefore $R_{m-1}/R_m\le r$. Use $m=9$ and $m=8$ consecutively to obtain $R_8/R_9\le r$ and $R_7/R_9\le r^2$. The envelope gives

$$
\epsilon=\frac{\sum_{k\ge1}\Delta_H(k)q^k}{R_9}
\le\delta\frac{R_8}{R_9}\le\delta r.
\tag{8.3}
$$

For either reference $j$, $F_j(k)\ge k^9$ and $Z_0\le Z_j\le Z_1$, so $Z_j/Z_1^2\le1/Z_0$. By the exact normalized difference,

$$
\begin{aligned}
\sum_{k\ge1}\frac{w_k^2}{f_j(k)}
&=\sum_{k\ge1}\frac{Z_j}{Z_1^2F_j(k)}
[\Delta_H(k)-\epsilon k^9]^2q^k\\
&\le\frac1{Z_0}\sum_{k\ge1}
\frac{[\Delta_H(k)-\epsilon k^9]^2q^k}{k^9}\\
&\le\delta^2\frac{R_7+2rR_8+r^2R_9}{R_9}
\le4\delta^2r^2.
\end{aligned}
\tag{8.4}
$$

Here $|\Delta_H(k)-\epsilon k^9|\le\delta k^8+\delta r k^9$ supplies the third line. All series converge. This calculation covers both reference labels, and hence both entropy directions.

For positive probability masses $p,r_0$, $\log x\le x-1$ gives

$$
\operatorname{KL}(p\Vert r_0)
\le\sum_zp(z)\left(\frac{p(z)}{r_0(z)}-1\right)
=\sum_z\frac{[p(z)-r_0(z)]^2}{r_0(z)}.
\tag{8.5}
$$

For the full source laws their ratios are bounded, since the envelope compares both $F_i$ and $Z_i$ by $B$. The sums and equality are therefore legitimate. Their difference is $w$ or $-w$. Applying (8.4)–(8.5), and then (7.9) to the tail masses while retaining the short terms, yields

$$
d_i(q,L)\le\operatorname{KL}(f_i\Vert f_j)
\le\sum_{k\ge1}\frac{w_k^2}{f_j(k)}\le4\delta^2r^2.
\tag{8.6}
$$

This remains valid when the collapsed reference tail is very small. No endpoint approximation or small-cutoff condition enters. $\square$

## 9. E3: tail drift and one envelope for every finite cutoff

**Lemma 9.1 (E3: uniform eighth-power collapsed entropy).** On the source-only neighborhood (2.9), for every finite integer $L\ge1$ and both targets,

$$
d_i(e^{-s},L)\le4\delta^2s^2\min\{1,(sL)^8\}
\quad(0<s<s_H).
\tag{9.1}
$$

Proof. First take $sL\le1$. Put

$$
\Sigma_j^L=\sum_{k=1}^L\frac{w_k^2}{f_j(k)},
\qquad m_L=\sum_{k=1}^Lw_k=\pi_1-\pi_0.
\tag{9.2}
$$

Since $r=1-e^{-s}\le s$ and $\epsilon\le\delta r$, for $k\le L$,

$$
|\Delta_H(k)-\epsilon k^9|\le\delta k^8(1+sk)\le2\delta k^8.
\tag{9.3}
$$

The denominator inequality from (8.4), $R_7^L=\sum_{k\le L}k^7q^k\le L^8$, and (2.9) give

$$
\Sigma_j^L\le\frac{4\delta^2R_7^L}{Z_0}
\le\frac{4\delta^2L^8}{Z_0}
\le\frac{8\delta^2}{9!}s^{10}L^8.
\tag{9.4}
$$

For the same reference,

$$
\pi_j\le\frac{B\sum_{k\le L}k^9q^k}{Z_0}
\le\frac{BL^{10}}{Z_0}
\le\frac{2B}{9!}(sL)^{10}\le\frac12.
\tag{9.5}
$$

The last step follows from $B<2$, $9!\ge8$ and $sL\le1$. Thus the collapsed reference tail has probability at least one half in this case.

The collapsed short difference is $w$ or $-w$ and the corresponding tail difference is $-m_L$ or $m_L$. Applying (8.5) to the collapsed laws gives

$$
d_i\le\Sigma_j^L+\frac{m_L^2}{1-\pi_j}.
\tag{9.6}
$$

Weighted Cauchy–Schwarz on these same short reference masses gives

$$
m_L^2
=\left(\sum_{k\le L}\sqrt{f_j(k)}\frac{w_k}{\sqrt{f_j(k)}}\right)^2
\le\pi_j\Sigma_j^L.
\tag{9.7}
$$

Consequently,

$$
d_i\le\frac{\Sigma_j^L}{1-\pi_j}
\le2\Sigma_j^L
\le\frac{16\delta^2}{9!}s^{10}L^8
\le4\delta^2s^{10}L^8.
\tag{9.8}
$$

The last inequality uses $9!\ge4$. The tail normalization drift has been bounded explicitly, not deleted. Arbitrary signs of individual $w_k$ and of their sum are allowed.

If $sL>1$, Lemma 8.1 instead gives

$$
d_i\le4\delta^2(1-e^{-s})^2\le4\delta^2s^2.
\tag{9.9}
$$

Combining the cases proves (9.1) on the same $s_H$ neighborhood. Only the first case needs a lower tail-mass bound; the second uses full-law entropy contraction. There is no restriction on a growing cutoff in the result. $\square$

## 10. E4: finite-path entropy and a bounded harmonic comparison

**Theorem 10.1 (E4: actual occupation pays for harmonic separation).** For a compliant observer, take the actual target epoch chain $U_i$ from its actual row $\nu_i$, with first label epoch $N$. Let $h$ satisfy

$$
0\le h\le1,
\qquad W_ih=h,
\qquad h(d_0)=0,
\qquad h(d_1)=1.
\tag{10.1}
$$

Then

$$
|p_i-\nu_ih|\le\sqrt{\frac{d_i(q,L)\mathbb E_iN}{2}}.
\tag{10.2}
$$

Only the actual target's almost-sure stopping supplies the limiting decision. Its finite paid mean supplies finite occupation. No termination or finite mean of the auxiliary $W_i$ chain is required.

Proof. For an integer $m\ge1$, let $P_m$ be the law of $(Y_0,\ldots,Y_m)$ under $U_i$ from $\nu_i$, with fixed label rows. Let $R_m$ be the law on the same finite path space from the same row $\nu_i$, with kernel $W_i$ and the same fixed labels. Common row support from Lemma 7.1 gives common positive path support. Initial zero masses vanish under both laws.

For a positive path the initial factor cancels, and its likelihood ratio is the product of its $m$ transition ratios. Expanding the logarithm and summing over the finite path space proves the chain rule

$$
\begin{aligned}
\operatorname{KL}(P_m\Vert R_m)
&=\sum_{r=0}^{m-1}\mathbb E_i
\operatorname{KL}(U_i(Y_r,\cdot)\Vert W_i(Y_r,\cdot))\\
&\le d_i(q,L)\sum_{r=0}^{m-1}\mathsf P_i(N>r)
=d_i(q,L)\mathbb E_i(N\wedge m).
\end{aligned}
\tag{10.3}
$$

Each live row costs at most $d_i$; every row after the actual label costs zero. The expectation is under the actual target, not an auxiliary stopping law. By (6.2), $\mathbb E_iN<\infty$.

For completeness, the variation inequality has the following precise constant. For finite laws $P,R$, take $A=\{z:P(z)\ge R(z)\}$ and $t=\|P-R\|_{\rm TV}=P(A)-R(A)$. Log-sum on $A$ and its complement gives

$$
\operatorname{KL}(P\Vert R)
\ge\operatorname{KL}(\operatorname{Bern}(u)\Vert\operatorname{Bern}(v)),
\quad u=P(A),\quad v=R(A).
\tag{10.4}
$$

For $0<v<1$, the right side as a function $F_v(u)$ has $F_v(v)=F_v'(v)=0$ and

$$
F_v''(u)=\frac1{u(1-u)}\ge4\quad(0<u<1).
\tag{10.5}
$$

Integrating twice from $v$ to $u\ge v$ gives $F_v(u)\ge2(u-v)^2$. Endpoint values of $u$ follow by continuity. If $v$ is zero or one, absolute continuity either forces $t=0$ or entropy is infinite. Thus

$$
\|P-R\|_{\rm TV}\le\sqrt{\frac{\operatorname{KL}(P\Vert R)}2}.
\tag{10.6}
$$

For any $[0,1]$-valued $F$, its expectation difference is at most variation: split $P-R$ into positive and negative mass, each of total mass $t$. This proves the expectation form of Pinsker with the stated constant.

Apply it to $F(y_0,\ldots,y_m)=h(y_m)$. Harmonicity by finite-step conditioning under $R_m$ gives

$$
\mathbb E_{R_m}h(Y_m)=\nu_iW_i^mh=\nu_ih.
\tag{10.7}
$$

It holds at every finite $m$ whether or not the auxiliary chain ever reaches a label. Hence

$$
\left|\mathbb E_i h(Y_m)-\nu_ih\right|
\le\sqrt{\frac{d_i(q,L)\mathbb E_i(N\wedge m)}2}
\le\sqrt{\frac{d_i(q,L)\mathbb E_iN}2}.
\tag{10.8}
$$

Under the actual target, $N<\infty$ almost surely and labels remain fixed. Thus $h(Y_m)\to h(Y_N)=D$ almost surely. Bounded convergence gives $\mathbb E_i h(Y_m)\to p_i$ and proves (10.2). Monotone convergence also gives the corresponding limit of $\mathbb E_i(N\wedge m)$.

Conditioning here uses the ordinary epoch filtration, with fresh future gaps and coins unexposed. No likelihood at an unproved auxiliary stop, auxiliary optional stopping or full-gap payment identity appears. A stop in zeros is represented by its frozen label at a later analytical tick, with no additional operational observation. $\square$

For any stochastic kernel fixing both labels, the actual probability of ever reaching $d_1$ is a $[0,1]$-valued function with those boundary values. First-step conditioning makes it harmonic, even with reducible or nonabsorbing classes. This supplies $h=h_{W_i}$ in (10.1) without auxiliary termination.

## 11. E5: the two actual source probabilities and each paid mean

**Theorem 11.1 (E5: finite-parameter entropy paid converse).** For any finite $M\ge2$, finite integer $L\ge1$, interior known common $q$, fixed $0<\alpha<1/2$, and actual $\mathcal A\in\mathfrak A_M(q,\alpha)$, define

$$
b=1-2\alpha,
\qquad\chi_{M,L}=\frac{\gamma_L^{M-2}-1}{\gamma_L^{M-2}+1}.
\tag{11.1}
$$

Separately for each $i\in\{0,1\}$,

$$
b\le r_H(q)+\chi_{M,L}
+\sqrt{\frac{d_i(q,L)B(1-q)\mathbb E_{i,q}^{\mathcal A}T}{2}}.
\tag{11.2}
$$

Proof. Fix target $i$ and opponent $j=1-i$. Take $h=h_{W_i}$ and $h_j=h_{U_j}$ as actual ever-hit probabilities. Lemma 5.3 permits Lemma 4.1 on the same configuration set with interior size $n\le M-2$. Since $(v-1)/(v+1)$ increases for $v\ge1$,

$$
\sup_x|h(x)-h_j(x)|\le\frac{\gamma_L^n-1}{\gamma_L^n+1}
\le\chi_{M,L}.
\tag{11.3}
$$

Theorem 10.1 gives $|p_i-\nu_ih|\le\sqrt{d_i\mathbb E_iN/2}$. The actual opponent stops almost surely from its actual initial row, so its epoch chain reaches its emitted label almost surely and $p_j=\nu_jh_j$. Decompose the two actual probabilities exactly as

$$
p_i-p_j=(p_i-\nu_ih)+\nu_i(h-h_j)+(\nu_i-\nu_j)h_j.
\tag{11.4}
$$

These are probabilities of the same machine at the same selected $q$. Bounds (5.2), (11.3) and (10.2) give

$$
|p_i-p_j|\le\sqrt{\frac{d_i\mathbb E_iN}2}+\chi_{M,L}+r_H(q).
\tag{11.5}
$$

Both risks imply $p_0\le\alpha$, $p_1\ge1-\alpha$ and $p_1-p_0\ge b$. Lemma 6.2 prices actual target occupation by $\mathbb E_iN\le B(1-q)\mathbb E_iT$. Substitution proves (11.2). For the other target use its own $W_j,d_j$ and its own actual expectation; $\eta,A,C$ and the experiment remain the same. This yields two individual mean bounds, not a bound on their sum or a combination of unrelated designs. The target index chooses a proof comparison, not runtime advice or source-dependent initialization. $\square$

If $d_i(q,L)>0$, rearrangement gives

$$
\mathbb E_{i,q}^{\mathcal A}T
\ge\frac{2[b-r_H(q)-\chi_{M,L}]_+^2}{B(1-q)d_i(q,L)},
\qquad [x]_+=\max\{x,0\}.
\tag{11.6}
$$

If $d_i=0$ while $b>r_H+\chi_{M,L}$, (11.2) instead rules out a compliant observer. If $d_i=0$ and the residual separation is nonpositive, the interface gives only the trivial nonnegative mean bound. No division by possibly zero entropy is allowed. A zero signed coefficient $\kappa_L$ in (7.11) supplies no singular exception.

## 12. E6: simultaneous endpoint bound for every finite budget

**Theorem 12.1 (E6: joint budget and paid-mean converse).** Fix the exact $H_c$, envelope, stationary law and source moment premises. Choose $s_H$ satisfying (2.9), and for a fixed $0<\alpha<1/2$ put

$$
b=1-2\alpha,
\quad s_\alpha=\min\left\{s_H,1,\frac{5b}{8\delta}\right\},
\quad C_\alpha=\frac{b^2}{8B\delta^2}.
\tag{12.1}
$$

For every finite integer $M\ge2$, use $L_M,X_M$ from (1.2). Then simultaneously

$$
\begin{gathered}
\forall M\in\mathbb Z,\ M\ge2\quad
\forall s\in(0,s_\alpha)\quad
\forall\mathcal A\in\mathfrak A_M(e^{-s},\alpha)\quad
\forall i\in\{0,1\}:\\
\mathbb E_{i,e^{-s}}^{\mathcal A}T
\ge C_\alpha\max\left\{s^{-3},\frac{s^{-11}}{L_M^8}\right\}
\ge C_\alpha\max\left\{s^{-3},\frac{s^{-11}}{X_M^8}\right\}.
\end{gathered}
\tag{12.2}
$$

The single neighborhood depends on the fixed source and risk, and precedes all budgets and machines.

Proof. After choosing $s_H$ from the source moments and fixing $\alpha$, fix any finite $M$ and set $n_M=M-2$, $L=L_M$. This finite positive integer cutoff does not inspect the actual machine. The ceiling and maximum give

$$
L_M\le1+\frac{2\delta n_M}b=X_M.
\tag{12.3}
$$

Indeed $\lceil x\rceil\le x+1$ and $1\le x+1$ for $x\ge0$, including $x=0$.

For $u\ge0$, set $F(u)=(e^u-1)/(e^u+1)$. Its value at zero is zero and $F'(u)=2e^u/(e^u+1)^2\le1/2$, so $F(u)\le u/2$. Also $\log(1+v)\le v$ for $v\ge0$. With $u=n_M\log(1+\delta/(L+1))$,

$$
\chi_{M,L}\le\frac{n_M}{2}\log\left(1+\frac\delta{L+1}\right)
\le\frac{n_M\delta}{2(L+1)}\le\frac b4.
\tag{12.4}
$$

For $n_M=0$ the left side is exactly zero. For $n_M>0$, $L\ge2\delta n_M/b$ proves the last inequality. On the same neighborhood,

$$
r_H(e^{-s})\le\frac{2\delta}{\mu_0(e^{-s})}
\le\frac{2\delta}{5}s\le\frac b4.
\tag{12.5}
$$

This uses the actual stationary law and the machine-uniform estimate, rather than a fixed-machine initial $O(s^2)$ estimate.

Consequently (11.2) leaves $b/2$ for the target entropy contribution. Squaring the nonnegative inequality, then using (9.1) and $1-e^{-s}\le s$, gives

$$
\begin{aligned}
\frac{b^2}4
&\le\frac{d_i(e^{-s},L)B(1-e^{-s})\mathbb E_iT}{2}\\
&\le2B\delta^2s^3\min\{1,(sL)^8\}\mathbb E_iT.
\end{aligned}
\tag{12.6}
$$

The upper coefficient is strictly positive for $s>0,L\ge1$. Dividing by that explicit coefficient, without dividing by exact $d_i$, yields

$$
\mathbb E_iT\ge\frac{b^2}{8B\delta^2}
\frac{s^{-3}}{\min\{1,(sL)^8\}}
=C_\alpha\max\left\{s^{-3},\frac{s^{-11}}{L^8}\right\}.
\tag{12.7}
$$

Since $L\le X_M$, replacing only $L^{-8}$ by $X_M^{-8}$ weakens the bound in the asserted direction and proves the second inequality in (12.2).

Every estimate holds for every finite cutoff on one source-only moment neighborhood. The argument therefore applies pointwise to every finite $M=M(s)$, even with unbounded $sL_M$, discontinuous retuning, unrestricted immutable probability precision and arbitrarily small positive transitions. It exchanges no fixed-$M$ limit with $M\to\infty$. If exact $d_i$ were zero for a compliant observer here, (11.2) would contradict the positive residual $b/2$; no zero-denominator convention is used. Reducible supports, initial stopping and closed non-target classes are included by the interfaces. $\square$

**Proposition 12.2 (The two-label budget).** For $0<\alpha<1/2$, $\mathfrak A_2(q,\alpha)=\varnothing$ at every interior $q$.

Proof. The two labels exhaust the budget, leaving no active configuration. If the source-independent initial choice emits one with probability $p$, the risks require $p\le\alpha$ and $1-p\le\alpha$, contrary to $1>2\alpha$. This is also the supplied small-budget result. Accordingly (12.2) at $M=2$, where $n_M=0$ and $L_M=X_M=1$, is a statement over an empty class. No universal lower bound asserts nonemptiness at another budget. $\square$

## 13. E7: necessary first-power growth for a fixed cubic target

**Theorem 13.1 (E7: complete-state threshold).** Fix exactly this source pair and one $0<\alpha<1/2$, independently of $s$. Suppose that for every sufficiently small $s>0$ there is a finite integer $M(s)\ge2$ and a design

$$
\mathcal A_s\in\mathfrak A_{M(s)}(e^{-s},\alpha).
\tag{13.1}
$$

Thus both risks, both almost-sure stops and both finite pointwise paid means hold at each selected $s$. Suppose additionally that one fixed target $i_\star\in\{0,1\}$ and one fixed constant $0<C_T<\infty$ satisfy

$$
\mathbb E_{i_\star,e^{-s}}^{\mathcal A_s}T\le C_Ts^{-3}
\quad\text{for every sufficiently small }s>0.
\tag{13.2}
$$

Set $c_T=(C_\alpha/C_T)^{1/8}>0$. Then, eventually,

$$
C_T\ge C_\alpha,
\qquad M(s)\ge2+\frac b{2\delta}\left(\frac{c_T}s-1\right),
\tag{13.3}
$$

and once $c_T/s\ge2$,

$$
M(s)-2\ge\frac{bc_T}{4\delta}s^{-1}.
\tag{13.4}
$$

In particular $M(s)=\Omega_{H_c,\alpha,C_T}(s^{-1})$.

Proof. Intersect the family and upper-bound neighborhoods with $s_\alpha$ from Theorem 12.1. At each $s$ there, apply that theorem to the selected actual finite budget and fixed target. Its eighth-power term and (13.2) imply

$$
C_Ts^{-3}\ge\frac{C_\alpha s^{-11}}{X_{M(s)}^8},
\qquad X_{M(s)}^8\ge\frac{C_\alpha}{C_T}s^{-8}.
\tag{13.5}
$$

All divided quantities are positive. The increasing eighth root gives $X_{M(s)}\ge c_T/s$. Substitute $X_{M(s)}=1+2\delta(M(s)-2)/b$ and divide by $2\delta/b>0$ to obtain (13.3). When $c_T/s\ge2$, $c_T/s-1\ge c_T/(2s)$, proving (13.4). Independently, the cubic term of (12.2) and (13.2) imply $C_T\ge C_\alpha$. A family with a smaller fixed cubic constant cannot meet the hypotheses. $\square$

No power-law form, monotonicity or regularity of $M(s)$ is used. Both $sL_M\le1$ and $sL_M>1$ regimes are covered by Theorem 12.1. The target, risk, polynomial and eventual upper constant are fixed; pointwise finite means alone do not imply (13.2). The opposing mean is finite pointwise but need not be cubic. A changing target, varying risk, changing polynomial or removal of opposing compliance is a different statement.

At a fixed budget, (12.2) retains eleventh-power order with explicit eighth-power deterioration in the affine budget. For a cubic paid mean, predictable payment permits only $O(s^{-2})$ live epochs under that target. The small-cutoff entropy is bounded by a multiple of $s^{10}L^8$, and Pinsker uses its product with actual live occupation. This explains the necessary $sL$ scale; (12.2)–(13.5) give the full all-regime proof rather than relying on that diagnostic calculation.

## 14. Separate supplied upper and conditional matching growth order

**Assumption 14.1 (Paid geometric-mark upper supplier).** The mathematical supplier `upper-proposal.json`, its `complete_new_controller` and `handwritten_results_and_proofs`, supplies the following construction and performance under exactly Definitions 2.3 and 3.1. `upper-check.json` supplies a distinct fallible handwritten assessment of that proposal. Both are separate from the entropy lower argument, and neither is a supplied final upper manuscript.

For its exact correspondence, rename the upper proposal's mark probabilities $p_i$ to $z_i$ to distinguish them from the actual decision probabilities in (6.1), and rename its boundary $L$ to $R$ to distinguish it from the lower cutoff. Put

$$
\begin{aligned}
z_i(q)&=\frac{Z_i(q^2)}{Z_i(q)},
&\Delta(q)&=z_1(q)-z_0(q),\\
t(q)&=\frac{z_0(q)+z_1(q)}2,
&d(q)&=\frac{\Delta(q)}2,\\
\ell&=\log\frac{1-\alpha}{\alpha}>0,
&R(q)&=\left\lceil\frac{\ell}{d(q)}\right\rceil
=\left\lceil\frac{2\ell}{\Delta(q)}\right\rceil.
\end{aligned}
\tag{14.1}
$$

The new branch applies at parameters with $\Delta(q)>0$. Its listed complete configurations are one waiting state $w$, both labels, and $(j,h)$ with integers $-R<j<R$ and $h\in\{0,1\}$. Their total number is $4R+1$. The source-blind initialization is deterministically $w$. Every nonlabel state reads the next actual bit. In $w$, zero loops and one enters $(0,1)$. In $(j,1)$, zero preserves the flag with probability $q$ and changes it to zero with probability $1-q$; in $(j,0)$, zero loops. The coordinate $j$ is unchanged on zeros. On a one, flag one moves up with probability $1-t$ and holds with probability $t$; flag zero moves down with probability $t$ and holds with probability $1-t$. Every nonterminal one successor resets the internal flag to one. A move reaching $R$ emits $d_1$; a move reaching $-R$ emits $d_0$. Labels absorb, and emission requires no additional read. All successor choices are compiled into one finite table at this known $q$.

This is an internal flag reset, not a source reset. A survival failure still pays every remaining zero and the closing one. Conditional on a real gap $K=k$, its potential mark is one with probability $q^k$, giving $z_i=\mathbb E_iq^K$. Potential mark and evidence-coin blocks are iid across gaps and independent of $\tau$, but a mark is not independent of its own duration. The upper supplier proves the resulting lazy walk, its risks and stopping by finite-horizon drift and bounded gambler's-ruin arguments. With

$$
u_i^{\rm up}=z_i(1-t),\qquad v_i^{\rm up}=(1-z_i)t,
\qquad \rho_i=\frac{v_i^{\rm up}}{u_i^{\rm up}},
\tag{14.2}
$$

its supplied errors and completed-gap count $G$ satisfy

$$
\begin{aligned}
e_0&=\frac1{1+\rho_0^R}\le\alpha,
&e_1&=\frac1{1+\rho_1^{-R}}\le\alpha,\\
\mathbb E_iG&=\frac{2R}{\Delta}(1-2e_i),
&\mathbb E_iT&=1+\beta_i+\frac{2\mu_iR}{\Delta}(1-2e_i).
\end{aligned}
\tag{14.3}
$$

Here $G$ is the upper construction's number of completed post-first-tick gaps through its terminal tick. It is not substituted for the generic live-epoch count $N$ of an observer that may stop in zeros. For this particular table, all begun gaps are completed and

$$
T=1+\tau+\sum_{r=1}^G(K_r+1).
\tag{14.4}
$$

The event $\{G\ge r\}$ is determined by preceding gaps and coins, hence independent of the next $K_r$. This is the supplied predictable-inclusion justification of its mean identity. It does not assume independence of the terminal decision and terminal gap duration. Both source laws have almost-sure stopping and finite paid means at every interior parameter where this branch applies.

The fixed-observer continuation's Proposition 27.2 supplies the geometric separation

$$
\Delta(e^{-s})=c_{\rm sep}s+O_H(s^2),
\qquad c_{\rm sep}=\frac{a}{9\cdot2^{10}}>0.
\tag{14.5}
$$

It originally concerns a changing-machine kernel coordinate; by itself it is not a compliant classifier. The upper proposal supplies the flag-and-walk realization needed to use that coordinate for testing. Combining the credited separation with the source moment premises, its upper theorem provides one source-only $s_U>0$, chosen at most one, such that for every $0<s<s_U$ this one common table has both errors at most $\alpha$, both almost-sure stops, both finite means, and

$$
\begin{aligned}
M_U(s)&=4R(e^{-s})+1\le K_U s^{-1},
&K_U&=\frac{16\ell}{c_{\rm sep}}+5,\\
\mathbb E_{i,e^{-s}}T&\le C_U s^{-3}\quad(i=0,1),
&C_U&=\frac{176\ell}{c_{\rm sep}^2}+\frac{44}{c_{\rm sep}}+7.
\end{aligned}
\tag{14.6}
$$

The precision of $q,t$ and the transition description is immutable and unpriced, exactly as in Definition 3.1. There is no separate mark register, unbounded gap counter, coin-tape index, clock or elapsed-read decoder. A supplied optional all-interior-$q$ extension selects the continuation's credited fixed sum-four classifier when $\Delta\le0$, using that classifier's additional sum-four certificate and confidence premise. No such fallback is needed for (14.6) or the comparison below. No cubic claim away from the endpoint follows from (14.6).

**Corollary 14.2 (Conditional matching state growth order).** Conditional also on Assumption 14.1, there exists a retuned finite-budget family with $M_U(s)=O_{H_c,\alpha}(s^{-1})$ and both paid means of order $\Theta_{H_c,\alpha}(s^{-3})$ near the endpoint. Under the same fixed source, risk, stationary start, known-common-$q$ design, complete-state counting, permitted immutable precision and actual paid-read contract, any compliant finite-budget family with an eventual cubic upper constant under one fixed target requires $\Omega_{H_c,\alpha,C_T}(s^{-1})$ states.

Proof. Intersect $s_U$ with $s_\alpha$. The supplied table belongs to $\mathfrak A_{M_U(s)}(e^{-s},\alpha)$ with all six obligations, because its listed configurations and actual reads satisfy the same definition. Formula (14.6) gives an upper cubic mean under both laws using that same family. The cubic term of (12.2) gives a lower $C_\alpha s^{-3}$ under each law for this family. Thus both means have cubic order. Its state budget is at most $K_Us^{-1}$, while Theorem 13.1 applies even with either one fixed target and $C_T=C_U$ to give a positive inverse-$s$ state lower bound. The general necessary assertion is precisely Theorem 13.1. $\square$

This is a conditional matching comparison of growth exponents. It excludes $o(s^{-1})$ budgets for the stipulated cubic target and supplies one $O(s^{-1})$ sufficient family through the separate upper premise. It does not say that every constant multiple of $s^{-1}$ suffices, identify the least budget at a given $s$, match leading constants, or give an exact budget-performance frontier. In particular the lower theorem is established without assuming Assumption 14.1, and the conditional comparison is not final-source approval of that upper construction.

## 15. Supplier correspondence and overlap

**Definition 15.1 (Mathematical credit map).** The eight supplied items have the following roles. References inside them are secondary supplier attributions, rather than additional independently certified sources.

| Supplied item | Exact contribution and boundary |
| --- | --- |
| `fixed-observer-source.md`, *Real renewal instruments and detector rank: finite observer memory*, revision `303bcf74526bab511d2175d5e302205d43654ab6`, Definitions 23.1–23.2, equations (23.1)–(23.7) | Exact $H_c$, $\delta,B,a$, all-integer envelope, stationary first-wait law, independent subsequent gaps and source moment orders in Section 2. Its nested envelope and moment proofs remain premises. |
| The same supplied continuation, Lemma 23.4, Lemmas 25.1–25.3 | Same-budget stochastic normal form and actual epoch/stopping/payment methods, applied pointwise at known common $q$ in Sections 3 and 6. Its original fixed $q$-free full-family quantifiers are distinct from Definition 3.1. |
| The same continuation, Lemma 24.2, Theorem 25.4, Definition 26.1 through Theorem 26.4, Proposition 27.2 | Existing fixed-machine eleventh-power converse, credited fixed sum-four upper classifier and its additional certificate, and geometric row-separation coefficient (14.5). Fixed-machine spectral constants are not treated as uniform over retuned matrices. |
| `uniform-source.md`, *Retuned bounded-memory uniform renewal converse*, Definitions 2.1–3.1 and Lemma 3.2; Sections 5–7 | Known-common-$q$, source-blind complete-state class; common normal form; stationary mixture; lawful target clipping; actual stopped-history and payment interfaces. Its observer-uniform fixed-budget eleventh-power result retains its ownership. |
| `lower-source.md`, *Growing state budgets in the renewal paid-mean tradeoff*, Sections 4–5 | Directed positive forests, marked and complementary sums, exponent $2n\le2(M-2)$ and additive hitting loss in Lemma 4.1. The argument is reproduced as a supplied interface, not reclassified as new entropy content. |
| The same growing-budget source, Sections 6–7 and Theorems 9.1–10.1 | Stationary comparison, target-specific $W_i$, actual live epochs, predictable payment, and the prior simultaneous mass-based converse and necessary exponent $4/5$. Those results remain valid and credited. |
| `refinement-proposal.json`, F1–F4 and G1–G3 | Signed-short normalization identity and proposed variation refinement with necessary exponent $8/9$. Its proposal-wide conclusion is conditional context, not a lower-proof premise. Equations (7.3), (7.10), (8.2)–(8.3) independently justify the overlapping algebra actually used here. No distinct assessment of this refinement is supplied here. |
| `entropy-proposal.json`, E1–E7 | Mathematical formulation of the clipped-entropy bound, finite-path harmonic comparison, simultaneous eighth-power paid converse and necessary exponent one. Sections 7–13 present those complete ordinary proofs and the exact parameter substitutions. |
| `entropy-check.json`, confirmed statements and E1–E7 acceptance analysis | A distinct fallible handwritten assessment of that mathematical proposal, under the same source conditions. It contributes an independent conditional assessment, not a new theorem, kernel certificate or final-manuscript approval. |
| `upper-proposal.json`, complete controller and mark/separation/walk/risk/payment/resource results | The separate paid survival-flag and lazy-walk sufficient family summarized exactly in Assumption 14.1. Its $p_i$ is $z_i$ here, its boundary $L$ is $R$, and its completed-gap count is $G$. Both cubic means and complete-state count are explicit supplied upper statements. |
| `upper-check.json`, approved mathematical statement and proof analysis | A distinct fallible handwritten assessment of the upper proposal. It concerns that proposal; it supplies no unsupplied final upper source and adjudicates neither this manuscript nor its lower proofs. |

For comparison with the older lower results, the growing-budget source's simultaneous mass bound is

$$
\mathbb E_iT\ge
\frac{9!b^{11}}{8B^2[b+2\delta(M-2)]^{10}}s^{-11}
\tag{15.1}
$$

on its common source/risk neighborhood. That gives its credited necessary exponent $4/5$ for a fixed eventual cubic target. The signed-short refinement proposes instead

$$
\mathbb E_iT\ge\frac{b\,9!}{4B\delta}
\frac{s^{-11}}{X_M^9\max\{1,sX_M\}},
\tag{15.2}
$$

and its conditional $8/9$ consequence. No assumption of (15.2) is used to prove (12.2). The new argument changes the charge: finite-path entropy replaces the accumulated absolute harmonic drift, while the actual $W_i$, initial law, forest comparison and payment experiment are preserved. Its necessary exponent one is therefore not a renaming of either earlier growth consequence. No assertion of optimal constants, or of pointwise domination between every displayed bound with their differing constants, follows from this exponent comparison.

The continuation and companions also credit unrestricted cubic procedures and prefix-entropy benchmarks to [Real renewal instruments and detector rank](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK.md), including the supplied append's Definition 22.8 through Definition 22.12 at revision `07123ef6f510e6df2d990240c55e29ed9d7c2485`. Those nested results are contextual suppliers, not dependencies of E1–E7. Their unbounded possible counters and growing arithmetic precision do not provide a finite complete-state budget merely because they use finitely many named registers. The separate finite upper comparison here is exactly Assumption 14.1.

The continuation attributes time-invariant randomized finite-statistic updates to Flower and Hellman's *Hypothesis Testing With Finite Memory in Finite Time*, and stationary renewal conventions to Marzen and Crutchfield's *Informational and Causal Architecture of Discrete-Time Renewal Processes*. Those are secondary attributions here. Their exact external scopes and any priority for the present source-relative converse are not independently certified. In particular, iid finite-horizon testing and expected stopping on renewal-dependent raw bits are different experiments.

## 16. Resource and evidence boundaries

**Definition 16.1 (What the threshold counts).** $M$ counts complete persistent configurations over all possible histories at the chosen parameter. It is neither an expected nor a typical-history memory count. A finite state index admits a mathematical encoding with $\lceil\log_2M\rceil$ mutable bits, but such an encoding does not price immutable table size, real transition precision or physical storage. Known $q$, fixed shapes, risk and thresholds are design information; no bound on the computation or precision needed to choose that design is part of the theorem. Fresh coins have no uncounted retained index, seed or archive.

The lower theorem permits unrestricted immutable precision. The separate upper uses that same permission for $q$ and its midpoint $t$. A finite-precision implementation, rational-coin approximation or bounded transition-description model requires additional error and resource analysis. No such physical realization is inferred from the abstract stochastic tables.

**Open question 16.2 (Constants and exact budgets).** The optimal hitting stability within this class, exact budget dependence of optimal paid means, least nonempty budget, sharp cubic constant and least leading inverse-$s$ state coefficient are not determined here. Besides the proved two-label impossibility and the separately supplied sufficient constructions, intermediate-budget nonemptiness is not classified. The conditional matching growth order is not an exact optimizer or exact threshold at a finite parameter.

**Definition 16.3 (Applicability limits).** The conclusions concern the one fixed rational-center $H_c$, one exact stationary binary renewal pair, both selected risks, both pointwise stops and finite means, and one consecutive paid-read history. They give no varying-$H$, residual-uniform, general-parity, hidden-state, reset, extra-source, free-gap, archive-assisted or externally clocked conclusion. The source's producer dimension, neural hidden dimension, physical memory and immutable description precision are different resources from this complete observer state count. Neither a training benefit nor empirical machine-learning behavior is established. Paid reads are not elapsed physical time. The internal label cannot be replaced by an external stopping-time decoder without changing the theorem.

The all-integer envelope, moment orders, geometric-separation and optional upper certificates retain their explicit handwritten source boundaries. The ordinary proofs here certify no generating instrument or nested external reference, carry no Lean kernel verification and establish no external novelty claim. Auxiliary laws, completed-gap indices, source lengths, future coins and post-stop analytical ticks are proof variables only, with no operational extra access. The lower argument prices occupation by actual conditional next-bit hazards, while the particular supplied upper prices its own completed gaps by predictable inclusion. Keeping those two payment arguments distinct is essential to both claims.

## 追加锚（本行以下为增补区）
