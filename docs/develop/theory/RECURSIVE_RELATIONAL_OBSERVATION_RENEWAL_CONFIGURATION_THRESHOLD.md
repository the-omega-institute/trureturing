# Recursive relational observation: two normalized likelihood caps and a quantitative renewal converse

## 1. Mathematical scope and ownership

For the fixed rational polynomial and stationary renewal experiment below, [Entropy-harmonic renewal converse and complete-state threshold](https://github.com/the-omega-institute/trureturing/blob/55bd69959604fd168733fbf1ea976765c9303010/docs/develop/theory/FIB_ENTROPY_HARMONIC_RENEWAL_STATE_THRESHOLD.md), abbreviated E, already establishes the all-budget eighth-power entropy lower bound, the necessity of $M(s)=\Omega(s^{-1})$ for a fixed cubic paid-mean target, and conditional matching state growth. Its Theorems 12.1–13.1 give the lower and necessity without its separate upper premise; its Corollary 14.2 gives the matching growth order conditional on that premise.

The distinct contribution here is the two normalized likelihood-cap construction in Section 4, its directed entropy control at every interior $q$ and every finite cutoff, and the resulting explicit quantitative converse in Sections 5–6. Its squared cap-excess charge is bounded by a weighted sum of seventh powers, with both normalization factors included. The eighth-power budget order and necessary exponent one are credited to E; Section 11 compares the two analytical laws and the displayed coefficients exactly.

Combining the established necessity with the counted upper in [Retuned finite-state cubic renewal upper bounds](FIB_RETUNED_FINITE_STATE_CUBIC_RENEWAL_UPPER.md), Theorem 8.1, abbreviated U, gives the credited consequence

$$
\gamma_c=1,
$$

and exponent one is attained, in the precise sense of Definition 2.5. Necessity holds even when the uniform cubic bound is imposed under only one fixed target label, while all six compliance conditions remain in force. Sufficiency uses one common observer under both labels at each known common parameter. Section 7 retains an alternative derivation through the paired-cap quantitative bound and an explicit correspondence with U. References to a new converse in the ensuing derivation denote this construction and its quantitative bound, not a previously absent growth exponent or eighth-power budget order.

The exact source, complete-state normal form, initial-row estimate, positive-forest comparison and predictable tick payment are supplied by [Growing state budgets in the renewal paid-mean tradeoff](FIB_GROWING_STATE_BUDGET_RENEWAL_TRADEOFF.md), Sections 2–7, abbreviated G. Its Theorems 9.1–10.1 give the earlier all-budget eleventh-power lower bound with tenth-power budget deterioration and necessary configuration growth of order $s^{-4/5}$. E already improves that budget order to eighth power. The older deterministic bit-controller bridge uses Sections 28–30 of [Real renewal instruments and detector rank: finite observer memory](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK_CONTINUATION.md), abbreviated C. Its logarithmic bit sufficiency, and the consequences of converting that count to configurations, are credited reuse.

This is ordinary mathematical reference theory, conditional on the explicitly credited all-integer envelope and source moment premises. Its proofs are not independent review or Lean kernel certification. Entropy contraction, sequential information charging, directed forest formulas and absorbing random walks are classical methods. No worldwide originality or completion of the broader relational-observation programme is asserted. Existing source statements retain their own hypotheses and remain unchanged.

## 2. Fixed experiment and the original threshold

**Definition 2.1 (Fixed shapes).** For a real argument $x$, fix

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

Put $F_0(x)=x^9$, $F_1(x)=H_c(x)$, and

$$
\delta=\frac{2749658638697}{10^{24}}>0,\qquad
B=1+\delta,\qquad
a=\frac{43377331415040}{35\cdot10^{24}}>0.
\tag{2.2}
$$

Retain exactly G's all-integer envelope premise:

$$
1\le r(k):=\frac{H_c(k)}{k^9}\le1+\frac{\delta}{k},
\qquad k=1,2,\ldots.
\tag{2.3}
$$

In particular $k^9\le F_i(k)\le Bk^9$. No polynomial coefficient varies with the endpoint parameter, an observer budget or a residual limit.

**Definition 2.2 (One stationary consecutive-bit source).** At $q=e^{-s}$, $s>0$, define

$$
\begin{aligned}
Z_i(q)&=\sum_{k\ge1}F_i(k)q^k,&
f_{i,q}(k)&=\frac{F_i(k)q^k}{Z_i(q)}\quad(k\ge1),\\
S_{i,q}(b)&=\sum_{k\ge\max(1,b)}f_{i,q}(k)\quad(b\ge0),&
\mu_i(q)&=\sum_{k\ge1}(k+1)f_{i,q}(k),\\
\beta_i(q)&=\frac{\sum_{k\ge1}k(k+1)f_{i,q}(k)}{2\mu_i(q)}.&
\end{aligned}
\tag{2.4}
$$

All indices in these sums are integers. Under label $i$, first draw $\tau$ with

$$
\mathsf P_{i,q}(\tau=b)=S_{i,q}(b)/\mu_i(q),\qquad b=0,1,\ldots.
\tag{2.5}
$$

Independently of $\tau$, draw iid positive zero counts $K_1,K_2,\ldots$ with law $f_{i,q}$. Put ones at

$$
\tau_0=\tau,\qquad
\tau_n=\tau+\sum_{r=1}^n(K_r+1)\quad(n\ge1),
\tag{2.6}
$$

and zeros at every other nonnegative integer position. The actual source is this one uninterrupted stationary history.

Nonnegative summation gives $\sum_{b\ge0}S_{i,q}(b)=\mu_i(q)$ and $\mathbb E_i\tau=\beta_i(q)$: each $k$ contributes at $b=0,\ldots,k$, with total first-moment weight $k(k+1)/2$. Thus the first wait is normalized, including $b=0$, and differs from a complete gap. The first tick still costs one read when $\tau=0$.

**Assumption 2.3 (Credited moments).** G, Assumption 2.3, supplies

$$
Z_i(e^{-s})=9!s^{-10}(1+O_H(s)),\qquad
\mu_i(e^{-s})=10/s+O_H(1),\qquad
\beta_i(e^{-s})=11/(2s)+O_H(1).
\tag{2.7}
$$

Constants concern only the fixed $H_c$. Choose a source-only $s_H>0$ so that

$$
Z_0(e^{-s})\ge(9!/2)s^{-10},\qquad
\mu_0(e^{-s})\ge5/s\quad(0<s<s_H).
\tag{2.8}
$$

**Definition 2.4 (Complete configurations and six obligations).** Fix one $0<\alpha<1/2$, independent of $s$. At each selected known common $q$, one observer and one source-independent initialization are used under both possible labels. The complete persistent configuration set includes every initialization and control state, register, phase, retained random consequence, stored seed and both internally emitted decision labels. Fresh independent coins may be marginalized into transition rows. Every retained part of randomness counts.

Immutable source-independent transition probabilities may be arbitrary real functions of known $q,H_c,\alpha$ and the finite budget. Retuning may be discontinuous, and positive entries may be arbitrarily small. Immutable description and its precision are separate resources. There is no hidden mutable clock, read count, program counter, address, archive, seed position or work tape. No extra history, source copy, reset, skipped bit, free gap, hidden age, probability response or label advice is available. The cost tally is not an input.

An active action reads the next actual bit or stops and emits a label $D\in\{0,1\}$. If exactly $X_0,\ldots,X_{T-1}$ are read, their paid count is $T$. Initial stopping costs zero. Every read zero, tick, initial wait and terminal partial interval is charged. The output is the internally emitted label; stopping time is not externally decoded into a label.

Write $\mathfrak A_M(q,\alpha)$ for observers with at most the finite integer $M\ge2$ complete configurations satisfying

$$
\begin{gathered}
\mathsf P_{0,q}(D=1)\le\alpha,\qquad
\mathsf P_{1,q}(D=0)\le\alpha,\\
\mathsf P_{i,q}(T<\infty)=1,\qquad
\mathbb E_{i,q}T<\infty\quad(i=0,1).
\end{gathered}
\tag{2.9}
$$

These are precisely G, Definition 3.1. A single unchanged parameter-free machine or guarantees over two separately varying nuisance parameters would be different requirements.

**Definition 2.5 (The unchanged cubic configuration exponent).** Let $\Gamma$ consist of the real numbers $\gamma\ge0$ for which there exist $C_M,C_T,s_0>0$ and, for every real $0<s<s_0$, one compliant observer $\mathcal A_s$ with finite complete count $M(s)$ such that

$$
M(s)\le C_Ms^{-\gamma},\qquad
\max_{i=0,1}\mathbb E_{i,e^{-s}}^{\mathcal A_s}T\le C_Ts^{-3}.
\tag{2.10}
$$

Set $\gamma_c=\inf\Gamma$. Constants may depend on fixed $H_c,\alpha$ and the chosen exponent, never on $s$. Attainment means $1\in\Gamma$ when $\gamma_c=1$; it does not mean exact finite-parameter optimizers exist. Section 7 proves both assertions.

## 3. The supplied complete-state interface

The following statements are reused from G. Their normalizations and stopping conventions are essential to applying the new scalar estimate to the full competitor class.

**Proposition 3.1 (Same-budget normal form and stationary initial row).** A compliant machine has a common initialization row $\eta$ and row-stochastic matrices $A,C$ on $\mathcal S$, $|\mathcal S|\le M$. Distinct states $d_0,d_1$ are absorbing under both matrices. Every other state is ready for another paid read. $A$ consumes a zero and $C$ consumes a one. This representation preserves $(T,D)$ and uses the same $\eta,A,C$ under both labels.

At the selected $q$, suppress its index and set

$$
U_i=\sum_{k\ge1}f_i(k)A^kC,\qquad
\nu_i=\sum_{b\ge0}\frac{S_i(b)}{\mu_i}\eta A^bC.
\tag{3.1}
$$

If $R_j(q)=\sum_{k\ge1}k^jq^k$, then

$$
\|\nu_0-\nu_1\|_{\rm TV}\le r_H(q):=
\delta\frac{R_9(q)+R_8(q)}{R_{10}(q)+R_9(q)}
\le\frac{2\delta}{\mu_0(q)}.
\tag{3.2}
$$

Here total variation is one half of the sum of absolute differences.

Proof and correspondence. Compose source-independent initialization and each current-state read/stop choice into a distribution on existing read-ready configurations and emitted labels. Compose the choice after each bit into that bit's transition. All information retained in a choice already belongs to a complete configuration. Identifying terminal configurations with the same label cannot increase their number. Fixing labels on unused future bits preserves the actual paid prefix and output. This is G, Lemma 3.2; it neither retains a random tape nor adds a mutable control coordinate.

For the initial comparison, the unnormalized first-wait weights are

$$
w_i(b)=\sum_{k\ge\max(1,b)}F_i(k)q^k,\qquad
W_i=\sum_b w_i(b)=Z_i\mu_i.
$$

The envelope gives $w_1\ge w_0$ and $0\le W_1-W_0\le\delta(R_9+R_8)$, while $W_0=R_{10}+R_9$. Normalizing $w_1=w_0+(w_1-w_0)$ expresses its law as a mixture with the normalized $w_0$ law, with extra weight at most $(W_1-W_0)/W_0$. Variation contracts under the common map $b\mapsto\eta A^bC$. Finally $R_8\le R_9$ and $\mu_0=(R_{10}+R_9)/R_9$ give (3.2). This is G, Lemma 6.1, and applies equally to arbitrarily retuned matrices. $\square$

**Theorem 3.2 (Credited positive-forest comparison).** Let $P,Q$ be stochastic matrices on the same set of at most $M$ states, with distinct common absorbing labels $d_0,d_1$. If $G\ge1$ and

$$
G^{-1}P(x,y)\le Q(x,y)\le GP(x,y)\quad(x,y\in\mathcal S),
\tag{3.3}
$$

their actual eventual $d_1$-hitting functions satisfy

$$
\|h_P-h_Q\|_\infty
\le\frac{G^{M-2}-1}{G^{M-2}+1}.
\tag{3.4}
$$

No global absorption, irreducibility or positive-edge lower bound is required.

This is G, Theorem 5.1. Its mechanism is the positive directed-forest representation after making every state with no path to $d_1$ a zero boundary. Every forest has $n\le M-2$ edges. Both the marked forest sum and its complementary sum are multiplied by factors in $[G^{-n},G^n]$. Their odds therefore change by at most $G^{2n}$; maximizing the difference of the corresponding two probabilities gives $(G^n-1)/(G^n+1)$. Zero marked complements, boundary states and $n=0$ are included in that theorem. This is a supplied comparison theorem, with no new forest-optimality assertion.

**Proposition 3.3 (Analytical epochs and paid ticks).** Freeze the emitted label on the unobserved continuation of the actual source. Let $Y_n$ be the configuration immediately after $\tau_n$, and define

$$
N=\inf\{n\ge0:Y_n\in\{d_0,d_1\}\},\qquad
Q_T=\sum_{t\ge0}\mathbf1_{\{T>t\}}X_t.
\tag{3.5}
$$

Under the actual source $i$, $(Y_n)$ has initial row $\nu_i$ and kernel $U_i$. For a compliant observer,

$$
Y_N=d_D,\quad N<\infty\ {\rm a.s.},\qquad
\mathbb E_iN\le\mathbb E_iQ_T
\le B(1-q)\mathbb E_iT<\infty.
\tag{3.6}
$$

Proof and payment audit. Independence of successive gaps and fresh update coins gives (3.1). A stop before or at the first tick has $N=0$. Otherwise the $N$ live configurations $Y_0,\ldots,Y_{N-1}$ follow $N$ distinct actually read ticks, giving $N\le Q_T\le T$. If stopping occurs inside zeros, the next analytical tick records the frozen label; that unread tick is not included in $Q_T$. Almost-sure actual stopping and finite source intervals imply $Y_N=d_D$ and finite $N$.

For the sharper expectation bound, after a read tick and $b\ge1$ read zeros the next-one hazard is

$$
\frac{F_i(b)q^b}{\sum_{k\ge b}F_i(k)q^k}
\le\frac{Bb^9q^b}{\sum_{k\ge b}b^9q^k}
=B(1-q).
\tag{3.7}
$$

At age zero the hazard is zero because $K\ge1$. Before any tick, $b$ read zeros instead give hazard $S_i(b)/\sum_{v\ge b}S_i(v)$. From $F_i(k+r)\ge B^{-1}F_i(k)$, shifting tail sums gives $S_i(b+r)\ge B^{-1}q^rS_i(b)$ for $b,r\ge0$, including $b=0$. This stationary hazard is also at most $B(1-q)$. With source-independent fresh coins exposed only for the payment calculation, the event of undertaking read $t+1$ is measurable before seeing $X_t$. Conditional expectation and Tonelli therefore give

$$
\mathbb E_iQ_T
=\sum_{t\ge0}\mathbb E_i[\mathbf1_{\{T>t\}}X_t]
\le B(1-q)\sum_{t\ge0}\mathsf P_i(T>t).
$$

This is G, Lemmas 7.1–7.2. It charges the actual observed prefix, including an interrupted final gap, and does not substitute a complete mean gap for it. The enlarged payment filtration is not an observer-accessible random tape or the filtration used for the epoch chain. $\square$

## 4. Two normalized scalar likelihood caps

All logarithms in relative entropy are natural. For probability masses $p,g$ with common support, write $D(p\Vert g)=\sum p\log(p/g)$ and $\chi^2(p\Vert g)=\sum(p-g)^2/g$.

**Lemma 4.1 (Clipping in both target directions).** Fix any $0<q<1$ and any integer $L\ge1$. Let $P=f_{0,q}$, use $r(k)$ from (2.3), and take expectations below under $P$. Define

$$
\begin{aligned}
G_L&=1+\frac{\delta}{L+1},&
v(k)&=\min\{r(k),G_L\},&
e(k)&=r(k)-v(k),\\
m&=\mathbb E_P r=Z_1/Z_0,&
c_L&=\mathbb E_P v,&
z_L&=\mathbb E_P(r/v).
\end{aligned}
\tag{4.1}
$$

The two laws

$$
g_1(k)=\frac{P(k)v(k)}{c_L},\qquad
g_0(k)=\frac{P(k)r(k)/v(k)}{z_L}
\tag{4.2}
$$

are positive and normalized. In the target index $i$, each is comparable to the opposite actual law:

$$
G_L^{-1}f_{1-i,q}(k)\le g_i(k)\le G_Lf_{1-i,q}(k)
\quad(i=0,1;\ k\ge1).
\tag{4.3}
$$

Moreover, with the positive finite quantity

$$
d_L(q)=\frac{\delta^2}{Z_0(q)}
\sum_{k=1}^L k^7q^k,
\tag{4.4}
$$

the needed directed entropies obey

$$
D(f_{1,q}\Vert g_1)\le d_L(q),\qquad
D(f_{0,q}\Vert g_0)\le d_L(q)/2\le d_L(q).
\tag{4.5}
$$

These statements hold for every finite $L$ at every interior $q$. There is no condition on $sL$.

Proof. The envelope gives $1\le v\le G_L$ and $r\le B$. Thus $1\le c_L\le m\le B$ and $1\le z_L\le B$. All normalizers are finite and positive, and summing (4.2) gives one. For $k>L$, $r(k)\le1+\delta/k\le G_L$, so

$$
e(k)=0\ (k>L),\qquad
0\le e(k)\le\delta/k\ (1\le k\le L).
\tag{4.6}
$$

For target one, $g_1/P=v/c_L$ lies in $[G_L^{-1},G_L]$. For target zero, since $f_1=Pr/m$,

$$
\frac{g_0(k)}{f_1(k)}
=\frac{1/v(k)}{\mathbb E_{f_1}(1/v)}.
\tag{4.7}
$$

The numerator and denominator in (4.7) both lie in $[G_L^{-1},1]$. This proves (4.3) in both directions, including every normalization factor.

We prove the two entropy estimates separately. The elementary inequality $\log u\le u-1$ yields $D(p\Vert g)\le\chi^2(p\Vert g)$ for normalized positive laws: its upper sum is $\sum p^2/g-1=\chi^2(p\Vert g)$. Write $a_L=\mathbb E_P e$, so $m=c_L+a_L$. Expanding $r=v+e$ gives the exact identity

$$
\begin{aligned}
\chi^2(f_1\Vert g_1)
&=\frac{c_L}{m^2}\mathbb E_P(r^2/v)-1\\
&=\frac{c_L\mathbb E_P(e^2/v)-a_L^2}{m^2}\\
&\le\mathbb E_P e^2.
\end{aligned}
\tag{4.8}
$$

For the last inequality use $v\ge1$, discard the nonpositive term, and use $c_L/m^2\le1$, which follows from $1\le c_L\le m$. Thus $D(f_1\Vert g_1)\le\mathbb E_Pe^2$.

For the other target put $x=e/v\ge0$. Then $r/v=1+x$, $z_L=1+\mathbb E_Px$, and

$$
D(P\Vert g_0)
=\log(1+\mathbb E_Px)-\mathbb E_P\log(1+x).
\tag{4.9}
$$

For all $x\ge0$, $\log(1+x)\ge x-x^2/2$; the difference has derivative $x^2/(1+x)\ge0$ and vanishes at zero. Combining this with $\log(1+y)\le y$ gives

$$
D(P\Vert g_0)\le\frac12\mathbb E_Px^2
\le\frac12\mathbb E_Pe^2.
\tag{4.10}
$$

Finally (4.6) and $P(k)=k^9q^k/Z_0$ imply

$$
\mathbb E_Pe^2\le
\frac{\delta^2}{Z_0}\sum_{k=1}^L k^7q^k=d_L.
\tag{4.11}
$$

This proves (4.5) using the two actual target-to-comparison entropy directions. No symmetric KL inequality is assumed. $\square$

The laws $g_i$ are analytical comparisons. They are neither operational sources nor a filtering rule imposed on the competitor. In particular an arbitrary observer still reads all actual raw bits and may stop inside any gap.

## 5. Entropy of finite epoch paths and eventual labels

**Lemma 5.1 (Common channel and finite paths).** Use any one machine's actual $\eta,A,C$ from Proposition 3.1, at one selected $q$. For $i=0,1$ put

$$
V_i=\sum_{k\ge1}g_i(k)A^kC.
\tag{5.1}
$$

Every $V_i$ is stochastic and fixes both labels. Its entries are $G_L$-comparable to those of $U_{1-i}$. For every row,

$$
D(U_i(x,\cdot)\Vert V_i(x,\cdot))\le d_L,
\tag{5.2}
$$

and the divergence is zero on either label row.

Start a $U_i$ chain and a $V_i$ chain from the same actual initial row $\nu_i$. Let $\mathcal P_i^{(n)},\mathcal V_i^{(n)}$ be their path laws through $n$ transitions, including the initial state. Then, under the actual target,

$$
D(\mathcal P_i^{(n)}\Vert\mathcal V_i^{(n)})
\le d_L\,\mathbb E_i\min(N,n)
\quad(n\ge0).
\tag{5.3}
$$

Proof. Each matrix $A^kC$ is a common channel from the gap index to a successor state. Nonnegative averaging of (4.3) gives the entrywise comparison with the opponent. Positivity of all $f_i(k),g_i(k)$ implies common row supports, including simultaneous zero entries. For the entropy contraction, joint masses $f_i(k)(A^kC)(x,y)$ and $g_i(k)(A^kC)(x,y)$ have joint divergence $D(f_i\Vert g_i)$. Summing out $k$ cannot increase it by the log-sum inequality, giving (5.2). One can apply that inequality to the conditional distributions of $k$ at each positive successor mass; countable nonnegative relative entropies give the same result by truncation. Equivalently the joint divergence equals the marginal divergence plus a sum of nonnegative conditional divergences. All involved gap likelihood ratios are bounded for fixed $q,L$, so this calculation is finite. Labels have the identical point-mass rows.

On a positive finite path, the initial-row factors cancel in its likelihood ratio. The log ratio is the sum of the $n$ transition log ratios. Finite summation and conditioning under $U_i$ give exactly

$$
D(\mathcal P_i^{(n)}\Vert\mathcal V_i^{(n)})
=\sum_{r=0}^{n-1}\mathbb E_i
D(U_i(Y_r,\cdot)\Vert V_i(Y_r,\cdot)).
\tag{5.4}
$$

If an initial entry is zero, both path laws assign it zero; it contributes nothing. At an actual label all subsequent divergences are zero. Before $N$ use (5.2). Since $\sum_{r=0}^{n-1}\mathsf P_i(N>r)=\mathbb E_i\min(N,n)$, (5.3) follows. No lower bound on a positive transition, and no infinite-horizon likelihood identity, is used. $\square$

**Lemma 5.2 (Eventual decision comparison without comparison absorption).** Let $h_{V_i}$ be the actual probability of ever hitting $d_1$ under $V_i$, with hitting at time zero allowed. If $p_i=\mathsf P_{i,q}(D=1)$ for the actual compliant machine, then

$$
|p_i-\nu_i h_{V_i}|
\le\sqrt{d_L\mathbb E_iN/2}.
\tag{5.5}
$$

Proof. For finite probability laws $P,Q$ and an event $E$, log-sum gives $D(P\Vert Q)\ge d(P(E),Q(E))$, where $d$ is binary relative entropy. For $0<v<1$, the second derivative in $u$ of $d(u,v)-2(u-v)^2$ is $1/[u(1-u)]-4\ge0$; its value and first derivative at $u=v$ vanish. Hence $d(u,v)\ge2(u-v)^2$. Endpoint cases follow by limits, including infinite divergence when appropriate. Therefore

$$
|P(E)-Q(E)|\le\sqrt{D(P\Vert Q)/2}.
\tag{5.6}
$$

Apply (5.6) to the path event $Y_n=d_1$ in Lemma 5.1. The actual target absorbs almost surely and records its actual output, so its event probability tends to $p_i$. Under $V_i$, $d_1$ is absorbing, so the events increase to ever hitting $d_1$ and their probabilities tend to $\nu_i h_{V_i}$, whether or not any other paths absorb. Monotone convergence gives $\mathbb E_i\min(N,n)\to\mathbb E_iN<\infty$. Taking limits proves (5.5). Only finite path entropies were compared. No absorption or mean assumption is imposed on the comparison chain from arbitrary states. $\square$

The common initial row in this lemma is $\nu_i$, not $\nu_{1-i}$. The initial laws are compared only after the finite-path argument. This avoids placing an uncharged stationary-wait discrepancy inside the epoch information budget.

## 6. A new all-budget paid-mean converse

**Theorem 6.1 (Finite-parameter entropy converse).** For every finite integer $M\ge2$, $0<\alpha<1/2$, $0<q<1$, observer $\mathcal A\in\mathfrak A_M(q,\alpha)$, integer $L\ge1$ and target $i\in\{0,1\}$, put

$$
b=1-2\alpha,\qquad
\chi_{M,L}=\frac{G_L^{M-2}-1}{G_L^{M-2}+1}.
$$

Then

$$
b\le r_H(q)+\chi_{M,L}
+\sqrt{\frac{d_L(q)B(1-q)\mathbb E_{i,q}^{\mathcal A}T}{2}},
\tag{6.1}
$$

and consequently

$$
\mathbb E_{i,q}^{\mathcal A}T
\ge\frac{2[b-r_H(q)-\chi_{M,L}]_+^2}
{B(1-q)d_L(q)}.
\tag{6.2}
$$

The same actual machine satisfies the two target-specific conclusions; the auxiliary $V_i$ may differ.

Proof. Let $j=1-i$. Lemma 5.1 and the credited forest theorem give $\|h_{V_i}-h_{U_j}\|_\infty\le\chi_{M,L}$. Opponent almost-sure stopping gives $p_j=\nu_jh_{U_j}$. Decompose the actual probability difference as

$$
p_i-p_j
=(p_i-\nu_i h_{V_i})
+\nu_i(h_{V_i}-h_{U_j})
+(\nu_i-\nu_j)h_{U_j}.
\tag{6.3}
$$

The three absolute differences are bounded respectively by Lemma 5.2, the forest comparison, and (3.2), since $0\le h_{U_j}\le1$. Both risks in (2.9) imply $p_1-p_0\ge b$. Apply (3.6) to $\mathbb E_iN$ in (5.5) to obtain (6.1). All factors in the denominator of (6.2) are positive: $\delta>0$, $L\ge1$, $q\in(0,1)$ and $Z_0>0$ imply $d_L>0$. When the bracket is positive, square the nonnegative inequality and divide; otherwise (6.2) is the nonnegativity of the paid mean. Both target and opposing compliance conditions remain in the quantified class. $\square$

**Theorem 6.2 (Uniform neighborhood for every finite budget).** Fix the one $H_c$ and one $0<\alpha<1/2$. With $s_H$ as in (2.8), set

$$
\begin{aligned}
b&=1-2\alpha,&
s_\alpha&=\min\{s_H,1,5b/(8\delta)\},\\
n_M&=M-2,&
L_M&=\max\{1,\lceil2\delta n_M/b\rceil\}.
\end{aligned}
\tag{6.4}
$$

Simultaneously for every finite integer $M\ge2$, every $0<s<s_\alpha$, every $\mathcal A\in\mathfrak A_M(e^{-s},\alpha)$ and each $i=0,1$,

$$
\begin{aligned}
\mathbb E_{i,e^{-s}}^{\mathcal A}T
&\ge\frac{9!b^2}{4B\delta^2L_M^8}s^{-11}\\
&\ge
\frac{9!b^{10}}{4B\delta^2\bigl(b+2\delta(M-2)\bigr)^8}s^{-11}.
\end{aligned}
\tag{6.5}
$$

The endpoint neighborhood is independent of the budget, the machine, transition precision and the way its design varies with $q$.

Proof. For $u\ge0$, $(e^u-1)/(e^u+1)\le u/2$, since its derivative is at most $1/2$ and its value at zero is zero. Also $\log(1+v)\le v$ for $v\ge0$. Hence

$$
\chi_{M,L_M}
\le\frac{n_M}{2}\log(1+\delta/(L_M+1))
\le\frac{n_M\delta}{2(L_M+1)}
\le b/4.
\tag{6.6}
$$

For $n_M=0$ the left side is zero. For $n_M>0$, use $L_M\ge2\delta n_M/b$. The common neighborhood and (3.2) give

$$
r_H(e^{-s})\le2\delta s/5\le b/4.
\tag{6.7}
$$

For every finite $L\ge1$, on that same neighborhood,

$$
d_L(e^{-s})
\le\frac{\delta^2L^8}{Z_0(e^{-s})}
\le\frac{2\delta^2L^8}{9!}s^{10},
\tag{6.8}
$$

because $e^{-sk}\le1$ and $\sum_{k=1}^L k^7\le L^8$. This is a finite-cutoff inequality valid even when $sL$ is large; no asymptotic with fixed $L$ is being transferred to a growing cutoff.

Equations (6.1), (6.6) and (6.7) leave $b/2$ for the square-root term. Therefore

$$
\mathbb E_iT\ge\frac{b^2}{2B(1-e^{-s})d_{L_M}}
\ge\frac{9!b^2}{4B\delta^2L_M^8}s^{-11},
\tag{6.9}
$$

where $1-e^{-s}\le s$ was used. Finally

$$
L_M\le1+2\delta n_M/b
=\frac{b+2\delta n_M}{b}
\tag{6.10}
$$

holds also at zero and at ceiling discontinuities. Substitution proves (6.5). The selections in (6.4) depend only on the fixed source and risk until the finite cutoff is selected from $M$. All inequalities then apply to any actual machine with that budget. $\square$

For $M=2$ there are only the two emitted labels, and a source-independent initial choice cannot have both risks below $1/2$. Thus the quantified compliant class is empty; no division by $M-2$ is made in (6.4)–(6.10). This corner does not claim a two-state detector.

The published G bound remains valid:

$$
\mathbb E_iT\ge
\frac{9!b^{11}}{8B^2(b+2\delta(M-2))^{10}}s^{-11}.
\tag{6.11}
$$

On their common neighborhood the ratio of the displayed new coefficient in (6.5) to (6.11) is $2B(b+2\delta(M-2))^2/(b\delta^2)$, growing quadratically with the budget. The mathematical gain is the squared clipping discrepancy in (4.8)–(4.11), rather than a renamed bookkeeping constant or an assumed uniform likelihood bound for raw bits.

## 7. The sharp cubic threshold and credited attainment

**Theorem 7.1 (Necessary linear configuration growth).** Suppose that for every sufficiently small $s>0$ a selected observer $\mathcal A_s\in\mathfrak A_{M(s)}(e^{-s},\alpha)$ satisfies, for one fixed target $i_\star$ and one finite positive constant $C_T$ independent of $s$,

$$
\mathbb E_{i_\star,e^{-s}}^{\mathcal A_s}T\le C_Ts^{-3}.
\tag{7.1}
$$

Set

$$
A_T=\left(\frac{9!b^{10}}{4B\delta^2C_T}\right)^{1/8}>0.
\tag{7.2}
$$

Throughout a sufficiently small neighborhood,

$$
M(s)\ge2+\frac{A_Ts^{-1}-b}{2\delta}.
\tag{7.3}
$$

Consequently $M(s)=\Omega_{H_c,\alpha,C_T}(s^{-1})$. Both selected risks, both almost-sure stops and both finite pointwise means remain required, even though (7.1) is imposed under only one fixed label.

Proof. Apply Theorem 6.2 to this actual observer at this actual $s$ and to the target $i_\star$. Comparing with (7.1) gives

$$
\bigl(b+2\delta(M(s)-2)\bigr)^8
\ge\frac{9!b^{10}}{4B\delta^2C_T}s^{-8}.
\tag{7.4}
$$

All factors divided are positive. The increasing eighth root on nonnegative numbers proves (7.3). Once $s\le A_T/(2b)$, it also gives

$$
M(s)\ge2+\frac{A_T}{4\delta}s^{-1}.
\tag{7.5}
$$

The neighborhood in this last step may depend on $C_T$; the neighborhood of Theorem 6.2 does not. There is no interchange of a fixed-budget limit with a growing budget. $\square$

**Proposition 7.2 (The supplied upper has exactly this interface).** Under the fixed source premises, U, Theorem 8.1, supplies positive constants $C_M^{\rm up},C_T^{\rm up},s_*$ and, for every $0<s<s_*$, one observer in $\mathfrak A_{M(s)}(e^{-s},\alpha)$ such that

$$
M(s)\le C_M^{\rm up}s^{-1},\qquad
\max_i\mathbb E_{i,e^{-s}}T\le C_T^{\rm up}s^{-3}.
\tag{7.6}
$$

In its notation a permissible choice is

$$
\begin{aligned}
c&=\frac{a}{9\cdot2^{10}}>0,&
\ell&=\log\frac{1-\alpha}{\alpha}>0,\\
C_M^{\rm up}&=\frac{16\ell}{c}+5,&
C_T^{\rm up}&=\frac{176\ell}{c^2}+\frac{44}{c}+7.
\end{aligned}
\tag{7.7}
$$

The radius $s_*$ depends only on the fixed source. These constants are independent of $s$.

Proof by explicit supplier correspondence. U's Definitions 2.1–3.1 use exactly (2.1)–(2.9), including the stationary wait, positive iid zero counts, known common $q$, identical source-blind initialization, permitted immutable real probabilities and all six obligations. In particular its $a$ is the fixed positive degree-eight coefficient, and its source radius is independent of all selected machines.

U sets

$$
u_i(q)=Z_i(q^2)/Z_i(q),\qquad
\Delta(q)=u_1(q)-u_0(q),\qquad
t=(u_0+u_1)/2,\qquad
L=\lceil2\ell/\Delta(q)\rceil.
\tag{7.8}
$$

Its supplied separation is $\Delta(e^{-s})=cs+O_H(s^2)>0$ sufficiently near the endpoint. These are immutable calibrations of the two promised models at the same known $q$, and are not measurements of the actual source or true-label advice.

The complete table in U, Definition 4.2, has one first-tick waiting state, both emitted labels, and pairs $(j,h)$ with $-L<j<L$, $h\in\{0,1\}$. Its full count is $4L+1$. The waiting state pays every initial zero and the first tick. On a zero, a live survival flag survives with probability $q$, and a failed flag remains failed; no suffix is skipped. On a closing tick the current flag and a fresh midpoint coin select an upward, downward or holding score update. An interior successor rearms the flag within that transition; a boundary emits its label immediately. These are direct finite-state rows, with no online arithmetic workspace, uncounted clock, seed position or additional initialization microstates. Resetting a counted flag changes the observer, not the source.

U, Lemma 5.1, proves the same-gap conditional survival probability $q^{K_r}$ and iid potential marks of law Bernoulli$(u_i(q))$. Its Theorems 6.2 and 7.1 separately establish both risks, both almost-sure stops and both finite paid means. In particular, if $N_{\rm up}$ counts its completed post-first-tick gaps, its actual paid cost and mean are

$$
T=1+\tau+\sum_{r=1}^{N_{\rm up}}(K_r+1),\qquad
\mathbb E_iT=1+\beta_i+\mu_i\mathbb E_iN_{\rm up}.
\tag{7.9}
$$

The inclusion of gap $r$ is determined before that gap begins. Its duration need not be independent of its own mark or stopping decision. Thus (7.9) uses the same actual history under its selected true label and pays the closing terminal tick. The table remains finite on every bit/coin history, including arbitrarily long initial and failed-survival zero runs. It does not require a deterministic paid cap.

U, Theorem 8.1, now gives precisely (7.6)–(7.7) for this same table, simultaneously under both labels. No optional all-interior fallback or sum-four certificate from its Section 9 is needed here. This is application and resource verification of an existing upper theorem, not an additional upper construction or a reproof claimed as new content. $\square$

**Theorem 7.3 (Exact configuration exponent, attained).** For Definition 2.5, $\gamma_c=1$ and $1\in\Gamma$.

Proof. Proposition 7.2 proves $1\in\Gamma$ using a single family satisfying the two mean bounds simultaneously. If $0\le\gamma<1$ belonged to $\Gamma$, Theorem 7.1 applied to that family's fixed $C_T$ and either fixed target would give $M(s)\ge c_T/s$ for some $c_T>0$ eventually. Together with $M(s)\le C_Ms^{-\gamma}$ this would imply $c_T\le C_Ms^{1-\gamma}\to0$, a contradiction. Thus every member of $\Gamma$ is at least one, and its attained infimum is one. No individually optimized designs are multiplied or assumed jointly realizable. $\square$

**Corollary 7.4 (Leading logarithm of mutable encoding capacity).** For any compliant family with a fixed cubic constant $C_T$ under even one fixed target, let $r_s$ be the capacity in mutable bits of an encoding of all its complete persistent configurations, including control and labels. Then, for sufficiently small $s$,

$$
r_s\ge\log_2(1/s)+\log_2\!\left(\frac{A_T}{4\delta}\right).
\tag{7.10}
$$

A compliant family attaining both cubic means has an encoding with

$$
r_s\le\log_2(1/s)+\log_2 C_M^{\rm up}+1.
\tag{7.11}
$$

Proof. Apply Theorem 7.1 to the actual number of complete configurations, not merely an oversized announced budget. Capacity $r_s$ permits at most $2^{r_s}$ configurations, and (7.5) gives (7.10). The supplied upper's $4L+1$ states can be indexed with $\lceil\log_2(4L+1)\rceil$ bits; (7.6) gives (7.11). This encoding is an abstract state index. It supplies no finite-precision exact-coin implementation, bit-local transition cost or physical-storage equivalence. The lower additive constant may depend on the family's cubic constant; the upper constants depend only on fixed $H_c,\alpha$. $\square$

## 8. The older rational-band controller as a faithful baseline

**Proposition 8.1 (Credited band-to-known-parameter bridge).** C, Sections 28–30, implies a family in the exact class of Definition 2.4 with both cubic paid means and complete mutable bits $O_{H_c,\alpha}(1+\log(1/s))$. Its displayed full configuration bound alone permits every polynomial exponent strictly greater than $368640$. Neither the optimal threshold nor attainment of that loose bookkeeping exponent follows from this bound alone.

Proof. Choose once a rational $\rho\in[\alpha/2,\alpha]$. Given known $q=e^{-s}$, let $\xi=1-q$ and select a dyadic rational $\varepsilon$ with $\xi/2\le\varepsilon\le\xi$. Then

$$
q\in[1-2\varepsilon,1-\varepsilon],\qquad
s/4\le\varepsilon\le s\quad(0<s\le1),
\tag{8.1}
$$

because $s/2\le1-e^{-s}\le s$. All sufficiently small $s$ therefore select sufficiently small supplied rational bands. This is an existence selection using the known common parameter; it does not assert an effective calibration algorithm for an arbitrary real encoding of $q$.

Compile the one C controller for this $\varepsilon,\rho$. Its two separate band risks imply both selected-pair risks at this same $q$. C, Theorem 28.4 and Corollary 30.1, give a paid cap $W=O_{H_c,\alpha}(\varepsilon^{-3})$, both almost-sure stops, both finite means and both per-parameter means of order $\varepsilon^{-3}$. Under (8.1) these are of order $s^{-3}$ with constants independent of $s$. The controller pays the stationary first interval and every read in a partial last gap or pair. A deciding pair update at read $W$ receives its ordinary decision before the timeout default.

The passage from C's internal bit computations to the normal form is a finite-state correspondence, not an assumption of free computational storage. Its Lemma 29.5 proves that initialization and each internal segment terminate without reading a new source bit on every legitimate capped history. The complete bank includes 256 words, 32 heads/pointers, operand copies, scratch, Boolean flags, input/output latches, return sites, phases, 30 control bits and initialization. All online source-dependent information lies in those counted coordinates.

At each read boundary, compose the finite deterministic internal segment following that read until the next read-ready configuration or emitted label. Compose initialization into the common initial row. The read-ready configurations form a subset of the full counted microconfiguration set; identifying terminal configurations with the same label cannot enlarge it. Totalize rows never used on a legal source history arbitrarily, using existing labels. The construction preserves the ordered paid bits and emitted label pathwise on every legal history, including all-zero histories and timeout during a stationary initial wait or partial pair. In particular it preserves the joint law of $(T,D)$ under both actual laws.

There is no source observation during an internal segment. Composition changes neither the logical next unread bit nor the paid tally; this discrete observation contract makes no assertion about a physical source evolving during computation. All transient internal storage was counted before composition. Source-dependent intermediates are not transferred to immutable description or to an external archive. Compiler work, deployed immutable descriptor, internal work and paid reads retain their separate meanings.

For a justified conversion of the supplied bit count, rename C's fixed risk-width integer and coefficient-width integer as $b_{\rm ctrl}$ and $B_{\rm coef}$, and its pointer width as $a_{\rm ptr}$. These are distinct from this volume's $b,B,a$. C's (29.1) simplifies exactly to

$$
\begin{aligned}
m_{\rm ctrl}&=\lceil\log_2(2W+2)\rceil,\\
w&=480m_{\rm ctrl}+16b_{\rm ctrl}+32B_{\rm coef}+536,\\
a_{\rm ptr}&=8+\lceil\log_2(w+1)\rceil.
\end{aligned}
\tag{8.2}
$$

For fixed model and the once-chosen controlled risk surrogate, C, Theorem 29.6, therefore gives

$$
\begin{aligned}
M_{\rm band}
&\le2^{256w+32a_{\rm ptr}+97}\\
&\le C(W+1)^{122880}(1+\log(W+2))^{32}\\
&\le C's^{-368640}(1+\log(1/s))^{32}
\end{aligned}
\tag{8.3}
$$

near the endpoint, with constants independent of $s$. Indeed $2^{m_{\rm ctrl}}<4W+4$, the term $256\cdot480m_{\rm ctrl}$ contributes exponent $122880$ in $W+1$, and the pointer term contributes the indicated logarithmic factor. For any fixed positive exponent slack, that logarithmic factor is absorbed by its extra power of $1/s$. This proves the assertion about every exponent greater than $368640$, and only bounds the corresponding infimum by $368640$ using this count. It does not prove attainment at $368640$. $\square$

This bridge reconciles the deterministic rational-band implementation with the retuned known-$q$ class. The original G necessity and C sufficiency already imply order $\log(1/s)$ necessary and sufficient mutable bits after that correspondence. This useful map is credited reuse. Theorem 7.3 resolves the sharper configuration exponent by the new all-competitor converse and U's already counted upper, rather than by optimizing (8.3).

## 9. Why raw-bit likelihoods cannot all be treated as small perturbations

**Proposition 9.1 (A short-gap counterexample to a universal shortcut).** There is a fixed finite raw-bit sensor, using only paid consecutive bits, for which an induced gap-kernel event has source likelihood ratio tending to $1+\delta$, rather than to one. Hence a universal entrywise $1+O(s)$ comparison of every raw-bit-induced gap kernel is false, even for a fixed small sensor. This does not refute Theorem 6.2.

Proof. After an actually read tick, keep a zero count saturated at two and, at the next actually read tick, emit a marker exactly when the count is one. This finite table recognizes $K=1$ while paying all zeros and the closing tick. It may be preceded by one first-tick waiting state. Its two event probabilities are $f_{i,q}(1)$.

Direct addition of the eight coefficients in (2.1) gives

$$
H_c(1)=1+\delta.
$$

Consequently

$$
\frac{f_{1,e^{-s}}(1)}{f_{0,e^{-s}}(1)}
=(1+\delta)\frac{Z_0(e^{-s})}{Z_1(e^{-s})}
\longrightarrow1+\delta>1.
\tag{9.1}
$$

The denominator ratio tends to one by the fixed-source moment premise. For every fixed finite $C$, a bound by $1+Cs$ therefore fails eventually. But the event itself has probability

$$
f_{0,e^{-s}}(1)\sim s^{10}/9!,
\qquad
f_{1,e^{-s}}(1)\sim(1+\delta)s^{10}/9!.
\tag{9.2}
$$

This sensor alone does not satisfy both fixed risks at small $s$: both event probabilities vanish. Its likelihood contrast comes with a rare-event charge. Lemma 4.1 retains that contrast in $e$ and pays its squared contribution, and the finite-path argument prices the actual live epochs. No bound on raw-bit likelihood ratios by $1+O(s)$ appears in that proof. $\square$

A converse for machines that see only U's one geometric mark per completed gap would concern a restricted channel. No assertion that arbitrary raw-bit observers factor through that channel is used here. Similarly a lower bound confined to deterministic counters, likelihood-score registers or product-state designs would not establish Theorem 7.1's quantifiers. The common-channel contraction in Lemma 5.1 is an analytical bound on every actual row, rather than a restriction on what raw histories the observer may use.

## 10. Stationary initialization and dependent payment

**Example 10.1 (A two-point gap law).** To illustrate the stationary initialization in (2.5) and the payment identity (7.9), take $\mathsf P(K=1)=1/3$ and $\mathsf P(K=3)=2/3$. Then

$$
\mu=\mathbb E(K+1)=\frac13\cdot2+\frac23\cdot4=\frac{10}{3},
\qquad S(0)=S(1)=1,\qquad S(2)=S(3)=\frac23,
$$

and $S(b)=0$ for $b\ge4$. Hence the stationary first-wait law and its mean are

$$
\begin{aligned}
\bigl(\mathsf P(\tau=0),\ldots,\mathsf P(\tau=3)\bigr)
&=\frac1\mu\left(1,1,\frac23,\frac23\right)
=\left(\frac3{10},\frac3{10},\frac15,\frac15\right),\\
\beta=\mathbb E\tau&=\frac3{10}+2\cdot\frac15+3\cdot\frac15=\frac{13}{10}.
\end{aligned}
$$

For subsequent iid gaps $K_r$, form survival marks $Y_r$ using fresh independent coins with $q=2/3$, so $\mathsf P(Y_r=1\mid K_r)=q^{K_r}$. The pairs $(K_r,Y_r)$ are iid, and their success probability is

$$
p=\mathbb E q^K=\frac13\cdot\frac23+\frac23\left(\frac23\right)^3=\frac{34}{81}.
$$

The mean interval conditional on its own successful mark is

$$
\mathbb E[K+1\mid Y=1]
=\frac{\frac13\cdot2\cdot\frac23+\frac23\cdot4\left(\frac23\right)^3}{34/81}
=\frac{100/81}{34/81}=\frac{50}{17}\ne\mu.
$$

Let $J=\min\{r\ge1:Y_r=1\}$. Reading through the closing tick of the first successful gap has paid duration $T=1+\tau+\sum_{r=1}^J(K_r+1)$. The event $\{J\ge r\}$ depends only on earlier marks, so it is independent of $K_r$. Therefore

$$
\mathbb E\sum_{r=1}^J(K_r+1)
=\sum_{r\ge1}\mathbb E\bigl[(K_r+1)\mathbf1_{\{J\ge r\}}\bigr]
=\mu\sum_{r\ge1}(1-p)^{r-1}=\frac\mu p,
$$

and thus

$$
\mathbb ET=1+\beta+\frac\mu p
=1+\frac{13}{10}+\frac{10/3}{34/81}=\frac{1741}{170}.
$$

The payment identity uses inclusion decided before each interval; it does not require duration to be independent of that interval's own mark.

## 11. Source and primary-literature correspondence

**Definition 11.1 (Evidence scope).** The distinct repo-derived contribution is Lemma 4.1's two normalized likelihood caps, the directed entropy control (4.5) at every interior $q$ and every finite cutoff, and the resulting explicit quantitative converse (6.2)–(6.5). E already supplies the all-budget eighth-power entropy lower, the $\Omega(s^{-1})$ necessity and conditional matching growth order. Theorem 7.1 is an alternative derivation of that necessity; Theorem 7.3 expresses the credited consequence with U's attainment in Definition 2.5's notation. Proposition 8.1 is an interface consequence of C, and Proposition 9.1 identifies the failure of a proposed universal shortcut. Generic entropy, finite-memory, forest and renewal methods are literature-attested background. The bounded primary search below does not certify global priority.

| Repository supplier | Correspondence and boundary |
| --- | --- |
| G, Definitions 2.1–3.1 and Lemma 3.2 | Identical fixed rational $H_c$, envelope, stationary first wait, iid positive zero counts, known common $q$, complete configurations, both emitted labels and all six pointwise conditions. Normal form preserves $(T,D)$ within the same budget. |
| G, Theorem 5.1 | Positive-forest eventual-label comparison on a common finite state set, including reducible supports, zero edges and nonabsorbing abstract classes. Applied to $V_i,U_{1-i}$ for the same actual $A,C$. |
| G, Lemmas 6.1 and 7.1–7.2 | Initial-row total variation, actual analytical epoch count, and predictable hazard payment including the stationary first interval and interrupted final gaps. |
| G, Theorems 9.1–10.1 | Published $M^{-10}s^{-11}$ converse and necessary exponent $4/5$, retained as credited baseline. Their simultaneous all-budget neighborhood is not replaced by a fixed-$M$ limit. |
| E, Definitions 2.1–3.1, Lemmas 3.2 and 5.1, Section 6 | The same source, parameter, complete-state class, stationary initial row, stopping and actual-read payment contract, as mapped explicitly below. |
| E, Sections 7–13, especially Theorems 12.1–13.1 | Already established collapsed-law directed entropy control, all-budget eighth-power paid converse and necessary first-power state growth, including a cubic bound under only one fixed target with opposing compliance retained. |
| E, Assumption 14.1 and Corollary 14.2 | Conditional matching inverse-$s$ state growth and both cubic mean orders through its separate geometric-mark upper premise. The present Section 7 uses U's published upper theorem for the corresponding sufficient family. |
| U, Sections 2–8, especially Theorem 8.1 | Already sufficient exponent one with the full $4L+1$ count, both risks, both stops and both cubic paid means, on the same actual stationary experiment. Its exact stochastic matrix model is retained. |
| C, Sections 28–30 | Rational-band deterministic controller, cap, two separate band risks, all-history terminating bit-computation refinement, complete bank/heads/control/initialization count and separate compilation/internal-work resources. |
| Retuned bounded-memory uniform renewal converse, Definitions 3.1–3.2 and Sections 5–7 | The selected-common-parameter retuned class and the initial/payment interface corroborate the same quantifiers. A fixed parameter-free machine across nuisance families is not identified with this class. |

**Definition 11.2 (Exact correspondence with E).** E's $H,F_i,\delta,B,a,Z_i,f_i,\mu_i,\beta_i,\tau,K_r$ are respectively the $H_c,F_i,\delta,B,a,Z_i,f_i,\mu_i,\beta_i,\tau,K_r$ of Section 2, with identical rational coefficients and labels. Its convention $f_i(0)=0$ makes $S_i(u)=\sum_{k\ge u}f_i(k)$ equal the present $\sum_{k\ge\max(1,u)}f_i(k)$, including $u=0$. Both first waits have mass $S_i(u)/\mu_i$, independently followed by the same iid positive zero counts; the first wait is not a complete gap.

E's $\mathfrak A_M(q,\alpha)$ in Definition 3.1 is exactly Definition 2.4's class: $q=e^{-s}$ is known and common, $0<\alpha<1/2$ and $H_c$ are fixed independently of $s$, the same source-blind design serves both labels, and $M$ counts every persistent configuration, initialization, retained random consequence and both labels. Both classes allow arbitrary real immutable transition probabilities, discontinuous retuning and arbitrarily small positive edges, and prohibit hidden mutable storage, additional source access and a stopping-time label decoder. All six risks, stops and finite pointwise means coincide; a uniform cubic target is a further eventual condition under one fixed label, not a replacement for opposing compliance.

Their common $\eta,A,C$ give the same $U_i,\nu_i$ and stationary variation bound $r_H$. E's Section 6 and Proposition 3.3 use the same $N,Q_T,T,D$: $N$ counts actual live epochs, $Q_T$ counts actually read ticks, and $T$ counts the whole paid prefix. Initial stopping gives $N=0$; stopping in zeros freezes the label until a later analytical tick, which is not charged as a read. Both proofs use $\mathbb E_iN\le B(1-q)\mathbb E_iT$, including the stationary first wait and terminal partial gap. Their auxiliary kernels provide neither observations nor a stopping promise. E's finite-path harmonic argument and Section 5's finite-path label-event limit both start from the actual target row $\nu_i$ and require only actual target absorption; the opponent's actual absorption is used separately in the probability decomposition.

For the separate upper comparison, E's $z_i$ and $R$ in (14.1) are $u_i$ and the upper boundary $L$ in (7.8), not the lower cutoff. Its $c_{\rm sep},K_U,C_U$ in (14.5)–(14.6) equal $c,C_M^{\rm up},C_T^{\rm up}$ in (7.7). Its completed-gap count $G$ is $N_{\rm up}$ in (7.9), giving the identical payment $T=1+\tau+\sum_{r=1}^{N_{\rm up}}(K_r+1)$; this upper-specific count is not the generic live-epoch count $N$. E's conditional comparison retains Assumption 14.1, while Section 7 explicitly cites U for the sufficient family.

**Definition 11.3 (Different normalized comparison laws).** To distinguish E's law from (4.2), write it as $\widetilde g_i^L$. With $j=1-i$ and $\pi_i=\sum_{k=1}^Lf_i(k)$, E's (7.4)–(7.8) are exactly

$$
\widetilde g_i^L(k)=
\begin{cases}
f_j(k),&k\le L,\\
\dfrac{1-\pi_j}{1-\pi_i}f_i(k),&k>L,
\end{cases}
\qquad
\widetilde d_i(q,L)=D(a_i^L\Vert a_j^L)
=D(f_i\Vert\widetilde g_i^L),
\tag{11.1}
$$

where $a_i^L=(f_i(1),\ldots,f_i(L),1-\pi_i)$. This copies the opponent's entire short law and rescales the target tail to the opponent's tail mass. The normalization drift is retained in the collapsed tail symbol. Its stochastic image is E's $W_i$.

Equations (4.1)–(4.2) instead use $P=f_0$, $r(k)=H_c(k)/k^9$, $G_L=1+\delta/(L+1)$ and $v=\min\{r,G_L\}$ to form

$$
g_1=\frac{Pv}{\mathbb E_Pv},\qquad
g_0=\frac{Pr/v}{\mathbb E_P(r/v)}.
\tag{11.2}
$$

The cap excess $e=r-v$ is nonnegative and supported on $k\le L$, but need not be nonzero at every short index. These laws normalize two different modifications of the shape ratio, rather than copying every short opponent mass. Normalization affects the full law. Equations (4.8)–(4.10) retain it exactly and give the separate bounds $D(f_1\Vert g_1)\le\mathbb E_Pe^2$ and $D(f_0\Vert g_0)\le\tfrac12\mathbb E_P(e/v)^2$. Thus both directions are controlled by $d_L(q)=\delta^2Z_0(q)^{-1}\sum_{k\le L}k^7q^k$ for every interior $q$ and finite $L$, without a small-$sL$ condition. This $d_L$ is an upper coefficient, not E's exact collapsed entropy $\widetilde d_i$. Both pairs are $G_L$-comparable to the actual opponent and are averaged through the same channel $k\mapsto A^kC$ of the same actual observer; their images $V_i$ and $W_i$ need not coincide.

For an exact coefficient comparison, choose one source-only $s_H$ satisfying (2.8) and E's (2.9), and use the identical

$$
s_\alpha=\min\{s_H,1,5b/(8\delta)\},\qquad
L_M=\max\{1,\lceil2\delta(M-2)/b\rceil\},\qquad
X_M=1+2\delta(M-2)/b.
\tag{11.3}
$$

Since $b+2\delta(M-2)=bX_M$, on $0<s<s_\alpha$, for the same compliant observer and each target, E's (12.2) and the second bound in (6.5) give, respectively,

$$
\begin{aligned}
\mathbb E_iT&\ge C_\alpha\max\{s^{-3},s^{-11}/X_M^8\},
&C_\alpha&=\frac{b^2}{8B\delta^2},\\
\mathbb E_iT&\ge\frac{9!b^2}{4B\delta^2}\frac{s^{-11}}{X_M^8}
=2\cdot9!\,C_\alpha\frac{s^{-11}}{X_M^8}.
\end{aligned}
\tag{11.4}
$$

The eighth-power displayed coefficients therefore have ratio $2\cdot9!$ with the same neighborhood and denominator. This algebraic comparison concerns those two estimates only; it orders neither their exact directed entropies nor optimal constants. E's proof (9.8) also retains the sharper intermediate estimate $\widetilde d_i\le(16\delta^2/9!)s^{10}L^8$ when $sL\le1$, so the displayed ratio does not compare every refinement available in that proof. E also retains its separate cubic floor, so (11.4) asserts no universal ordering of the whole lower bounds. The two-label budget $M=2$ is empty in both classes. The necessity exponent and E's conditional matching order remain established results; the paired-cap construction supplies the distinct explicit quantitative derivation.

Public mathematical-code context includes [StoppedLikelihoodAbsorption](../../../D5/S3/Estimation/SequentialDecisionRisk/StoppedLikelihoodAbsorption.lean), [BernoulliCommonEndpointCharge](../../../D5/S3/Estimation/SequentialDecisionRisk/BernoulliCommonEndpointCharge.lean), and [SequentialHellingerLocalization](../../../D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SequentialHellingerLocalization.lean). These concern stopped likelihood/moment, Bernoulli common-endpoint and sequential Hellinger interfaces, with no compiled exact application asserted here. E supplies the already established renewal-state converse and growth consequence; these related code interfaces are not premises of the distinct paired-cap estimate.

The primary papers below have their model interfaces checked from their original texts. No finite-memory testing theorem for an incompatible observation or decision criterion is transferred as a theorem about this experiment.

| Primary source | Verified interface and use |
| --- | --- |
| Flower and Hellman, *Hypothesis Testing With Finite Memory in Finite Time*, IEEE Transactions on Information Theory 18, 429–431, [author copy](https://ee.stanford.edu/~hellman/publications/10.pdf), DOI [10.1109/TIT.1972.1054820](https://doi.org/10.1109/TIT.1972.1054820) | The problem statement uses iid observations, a finite-valued statistic, observation-dependent stochastic update matrices and a decision at a specified horizon. Its finite-state and randomized-counter methods are background; its reported structural conjectures and finite searches supply no renewal paid-stopping converse. |
| Berg, Ordentlich and Shayevitz, *Binary Hypothesis Testing with Deterministic Finite-Memory Decision Rules*, [arXiv:2005.07445v1](https://arxiv.org/pdf/2005.07445v1), Section I and main model | Iid Bernoulli input, deterministic time-invariant transitions and long-time Bayes error. Its lower results do not quantify over the stochastic stopped raw-bit class used here. Deterministic and stochastic state requirements are not interchanged. |
| Kaufmann, Cappé and Garivier, *On the Complexity of Best-Arm Identification in Multi-Armed Bandit Models*, [arXiv:1407.4443v2](https://arxiv.org/pdf/1407.4443v2), Lemma 1 and Remark 2 | Expected acquisition counts times directed KL control decision-event binary entropy, with a Pinsker consequence. This is mature sequential information charging. Here Lemmas 5.1–5.2 prove the needed common-initial-row finite Markov-path version directly; no bandit action, free gap sample or comparison stopping assumption is imported. |
| Zamparo, *Renewal model for dependent binary sequences*, [arXiv:2108.11293v2](https://arxiv.org/pdf/2108.11293v2), Theorem 2.1 and Proposition 2.1 | Stationarity is $\mathbb E[S_2]\mathsf P(S_1=n)=\mathsf P(S_2\ge n)$. With its interval $S_2=K+1$ and initial delay $S_1=\tau+1$, this is exactly (2.5) after shifting the time origin. Dependent visible bits are not automatically a fully observed finite-state Markov source, and this renewal model supplies no testing-memory exponent. |

Primary author/arXiv retrieval and bounded bibliographic queries cover finite-memory sequential testing, stochastic automata and dependent renewal inference. Within these inspected interfaces, none supplies the exact fixed-$H_c$ configuration threshold. Results about predictive causal-state memory, quantizer alphabet size, fully observed Markov transitions, fixed-horizon error or deterministic automata do not by themselves control the full mutable state and stopped paid reads here. The entropy and binary inequalities needed in this volume have explicit proofs, so unread or inapplicable external theorem statements are not load-bearing premises.

## 12. Observer memory as a boundary for future observations

The all-state converse describes a limit on retaining enough evidence to make a future paid decision. At the fixed risk and uniform cubic paid mean, complete observer configurations must grow linearly in $1/s$, and the supplied stochastic observer meets that exponent. A geometric flag is a lossy relation to an actual gap; a bounded score retains accumulated task-relevant evidence. Neither coordinate reconstructs the entire past. The lower proof permits every alternative finite stochastic representation and therefore does not assume the flag/score architecture is universally sufficient for other observation tasks.

This result separates a number of resource coordinates. Configurations are the worst-case number of possible persistent states over all histories; mutable bits are the logarithmic capacity of an encoding of those states. Paid reads count acquired source symbols. Internal computation, immutable description, transition-probability precision, calibration effort and physical elapsed time are separate. Exact source-independent probabilities retuned to known $q$ are permitted by this model. Their existence does not imply effective exact-real calibration, finite-precision implementation, unknown-$q$ adaptation or a physical memory/time realization.

**Open question 12.1 (Remaining resource and recovery boundaries).** Sharp multiplicative constants, exact finite-parameter minimum budgets, the complete frontier for noncubic paid targets, the deterministic-only sharp configuration exponent, precision-constrained calibration and unknown-common-parameter adaptation are unresolved here. The displayed converse can be applied to other target bounds, but this alone does not give matching constructions or their full frontier. The independent native-tree sharp rate and the larger minimal-relations/internal-observer/mutual-recovery programme remain separate unresolved questions.

No theorem here recovers physical time, space, a hidden source state or the full observation history from a finite testing configuration. The terminal label is an internally realized action under the two promised laws. The sharp exponent concerns this specific future-observation task and preserves those broader recovery obligations.

## 追加锚（本行以下为增补区）
