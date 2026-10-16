# Actual CP reset stability and quantitative rank horizons

This companion volume concerns finite homogeneous binary completely positive instruments, their actual post-tick states, and the trace norm of the entire calibrated tick Choi matrix. Its quantitative conclusions allow arbitrary complex matrices. The exact support and renewal suppliers are identified in Section 2; the quantitative proofs and all obstruction families are given in Sections 3–5.

The source format is `generic-v1`, with numbered declarations and an empty final append anchor. The text is ordinary handwritten mathematics and a reference input, not a kernel verification. No worldwide originality claim is made. Norm bounds, exact algebraic properties, classical output laws and implementation resources retain their separate meanings.

## 1. Standalone memory, instrument and probability conventions

Fix a finite complex Hilbert space $H=\mathbb C^D$ with a fixed orthonormal basis. All persistent quantum or classical registers, retained Kraus records and controllers that influence future steps belong to this memory. The matrices are fixed in time. There is no uncounted correlated input or time-dependent external controller. Summed Kraus labels within a visible branch do not persist. Real examples below remain maps on the full complex matrix algebra, including nonreal coherences.

An operator $X\ge0$ is positive semidefinite; a density is a positive operator with $\operatorname{Tr}X=1$, and an effect satisfies $0\le X\le I$. A density is faithful if it is positive definite and pure if it has rank one. The adjoint of a matrix is $A^\dagger$. A linear map is completely positive (CP) if all its tensor ampliations by identity maps preserve positivity. In finite dimension it has a finite Kraus representation, proved in Lemma 3.2. A complete binary instrument consists of CP maps

$$
\Phi(X)=\sum_a K_aXK_a^\dagger,
\qquad \Psi(X)=\sum_b L_bXL_b^\dagger,
\qquad \sum_aK_a^\dagger K_a+\sum_bL_b^\dagger L_b=I.
$$

The symbols zero and one denote, respectively, the no-tick branch $\Phi$ and tick branch $\Psi$. Completeness means that $\Phi+\Psi$ is trace preserving; each branch is trace nonincreasing on positive inputs. The trace dual is characterized by $\operatorname{Tr}[Y\Lambda(X)]=\operatorname{Tr}[\Lambda^*(Y)X]$, so $\Phi^*(Y)=\sum_aK_a^\dagger YK_a$. The Choi rank is the minimum Kraus count, equivalently the rank of the Choi matrix defined in Section 3. It is distinct from the rank of a Kraus matrix and from the rank of a branch effect.

For a specified initializer $\rho_0$, a positive-probability initial tick defines

$$
\nu=\operatorname{Tr}\Psi(\rho_0)>0,
\qquad \tau=\Psi(\rho_0)/\nu,
\qquad F=\Psi^*(I),
\qquad w_k=\operatorname{Tr}[F\Phi^k(\tau)].
$$

These are actual instrument quantities. The density $\tau$ is not a freely selected seed, and $\rho_0$ need not be invariant. The index $k\ge0$ counts zeros before the next tick; the interevent duration is $k+1$. Thus $w_0$ is an immediate consecutive tick. A first-hit index $h$ means $w_0=\cdots=w_{h-1}=0$ and $w_h>0$, with no assertion about later indices. Writing $s_k=\operatorname{Tr}\Phi^k(\tau)$ gives $s_0=1$, $s_k-s_{k+1}=w_k$ and $\sum_{k=0}^Nw_k=1-s_{N+1}\le1$. The next-gap distribution is proper exactly when $s_k\to0$. None of properness, renewal independence, purity or a common reset is a default hypothesis.

For any density $\rho$ and binary word, the actual probability is

$$
\mathbb P_\rho(x_1\cdots x_N)
=\operatorname{Tr}[\mathcal E_{x_N}\cdots\mathcal E_{x_1}(\rho)],
\qquad \mathcal E_0=\Phi,\quad\mathcal E_1=\Psi.
$$

The empty word has probability one. An invariant density satisfies $(\Phi+\Psi)(\rho)=\rho$ and produces stationary cylinders. A global reset to a density $\tau$ means $\Psi(X)=\tau\operatorname{Tr}(FX)$ for every complex matrix $X$. It fixes the normalized output of every positive-probability tick. If the next gap is proper, repeated ticks then yield independent gaps with the same law; an arbitrary instrument's one-gap marginal alone does not prove that independence.

For orientation, a proper gap law $\gamma_k$ of finite interval mean $\mu=\sum_{k\ge0}(k+1)\gamma_k$ has tails $S_a=\sum_{k\ge a}\gamma_k$. Its equilibrium renewal cylinders are

$$
\begin{aligned}
\mathbb P(0^a1\,0^{g_1}1\cdots0^{g_{r-1}}1\,0^b)
&=\frac{S_aS_b}{\mu}\prod_{j=1}^{r-1}\gamma_{g_j}\quad(r\ge1),\\
\mathbb P(0^N)&=\frac1\mu\sum_{k\ge N}(k-N+1)\gamma_k.
\end{aligned}
$$

All run lengths are nonnegative integers, and the product is empty when there is only one tick. These formulas include boundary tails and stationary length bias. They are not imposed on the arbitrary instruments in Section 4. The notation $d_{\rm TV}$ below means half the $\ell^1$ distance between classical probability distributions. It is not the Choi trace norm.

## 2. Exact suppliers, parameter correspondence and distinct output boundaries

Write **O** for [Real renewal instruments and detector rank](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK.md), the original volume. Every reference prefixed by **O** belongs to that volume. Unprefixed section, declaration and equation numbers belong to this companion. This convention separates O's published Section 21 on a joint delay limit from the quantitative rank-horizon results here.

### 2.1. Reachability and the exact rank telescope

[O, Definition 13.1 and Theorem 13.2](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK.md#13-detector-dead-time-reachable-support-and-actual-reset-rigidity) allow a CP map $\Phi(X)=\sum_iK_iXK_i^\dagger$ on a $D$-dimensional complex space, with a finite possibly empty Kraus family, and arbitrary positive seed $\sigma$ and positive detector $B$. Neither is required to be normalized. This is a raw CP map, without the completeness premise of Section 1. Set

$$
\begin{aligned}
U&=\operatorname{ran}\sigma,\quad u=\operatorname{rank}\sigma,\\
R&=\operatorname{span}\{K_wU:w\text{ a finite word, including the empty word}\},
\quad r=\dim R,\\
R^\vee&=\operatorname{span}\{K_{i_k}^\dagger\cdots K_{i_1}^\dagger
\operatorname{ran}B:k\ge0\},\quad r^\vee=\dim R^\vee.
\end{aligned}
$$

A word $w=(i_1,\ldots,i_k)$ acts as $K_w=K_{i_k}\cdots K_{i_1}$. O's exact conclusion is that $\sum_{k=0}^{r-u}\Phi^k(\sigma)$ has range $R$ and kernel $R^\perp$. Vanishing detector weights through $r-u$ is equivalent to vanishing forever. If detection occurs, its first index obeys

$$
h\le\min\{r-\operatorname{rank}\sigma,
 r^\vee-\operatorname{rank}B\}
\le D-\max\{\operatorname{rank}\sigma,\operatorname{rank}B\}.
$$

There are no completeness, contraction, stability or commutation assumptions in this exact supplier. With $W_j=\operatorname{span}\{K_wU:|w|\le j\}$, its proof uses $W_{j+1}=W_j+\sum_iK_iW_j$, the fact that a plateau makes $W_j$ invariant, and the positive-sum range identity. Theorem 3.3 uses a quantitative approximate-basis argument under its additional subunital and normalized hypotheses; it does not assume a condition number for these exact reachable spans.

[O, Theorem 16.4](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK.md#16-nonnegative-anchored-squares-exact-delay-and-general-real-renewal-instruments) gives the stronger joint positive-delay statement for arbitrary raw CP detection: if $a=\operatorname{rank}\sigma$, $b=\operatorname{rank}B$ and the first positive index is $h\ge1$, then $a,b\ge1$ and $h\le D-a-b+1$. Its proof places the strictly growing pre-hit reachable space of dimension at least $a+h-1$ inside $\ker B$. The bound is sharp for raw CP detection in dimension $a+b+h-1$; O's chain with seed and detector spectators is not a complete-instrument sharpness claim for arbitrary ranks. The case $h=0$ is excluded. No approximate rank or uniform norm conclusion follows from replacing the exact zeros in this statement by small positive values.

### 2.2. The exact actual-output endpoint used in Section 4

[O, Theorem 13.3](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK.md#13-detector-dead-time-reachable-support-and-actual-reset-rigidity) has the following complete telescope: $D\ge1$; a finite homogeneous complete binary CP instrument on $M_D(\mathbb C)$; a density $\rho_0$ with $\nu=\operatorname{Tr}\Psi(\rho_0)>0$; the actual density $\tau=\Psi(\rho_0)/\nu$; effect $F=\Psi^*(I)$; and first positive value of $\operatorname{Tr}[F\Phi^k(\tau)]$ at $h=D-1$. It concludes

$$
\operatorname{rank}\tau=\operatorname{rank}F=1,
\qquad R=R^\vee=H,
\qquad \Psi(X)=\tau\operatorname{Tr}(FX)\quad(X\in M_D(\mathbb C)).
$$

The tick Choi rank is one, and every nonzero operator in any tick Kraus representation has rank one and lies in a single operator direction. Any invariant density with positive tick rate is faithful, and is mixed if $D>1$. The correspondence in Corollary 4.4 is the identity on $D,\Phi,\Psi,\rho_0,\nu,\tau,F$, with $h=D-1$ supplied by $\epsilon=0$ and $w_{D-1}>0$. For $w_{D-1}=1$, completeness first forces all earlier weights to zero. The separate $D=2$ late-free conclusion in that corollary does not invoke full reachability without a positive late weight.

The actual-output premise is essential even in the exact supplier. If $F=\lambda|\eta\rangle\langle\eta|$, every tick Kraus matrix has the form $v_i\eta^\dagger$, so $\Psi(X)=(\eta^\dagger X\eta)M$ with $M=\sum_i v_iv_i^\dagger$ and $\operatorname{Tr}M=\lambda$. The positive actual tick identifies $\tau=M/\lambda$. An independently chosen pure seed cannot make this identification. Section 4 quantitatively controls this same calibration, including off-diagonal blocks, and Proposition 5.4 gives the exact counterexample for a substituted seed.

### 2.3. Renewal examples do not restrict the arbitrary-instrument theorem

[O, Section 14](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK.md#14-a-delayed-squared-falling-factorial-renewal-law-with-exact-memory-dimension) fixes $m\ge1$, $0<q<1$ and

$$
P_m(k)=\sum_{t=0}^{k-1}(t)_{\underline m}^{2},
\qquad (t)_{\underline m}=t(t-1)\cdots(t-m+1),
\qquad \gamma_k=\frac{q^kP_m(k)}{\sum_{j\ge0}q^jP_m(j)}.
$$

Its first positive index is $h=m+1$. O, Theorems 14.2–14.4 supply a real complete instrument in $D=m+2$, with zero Choi rank two, a single pure resetting tick, full reachable span and a faithful mixed stationary initializer, producing every cylinder of Section 1. O, Theorem 14.5 obtains the same dimension minimum for arbitrary complex competitors reproducing all those cylinders, using their actual posterior extracted from $\mathbb P(10^k1)/\mathbb P(1)$. It assumes neither their hidden invariance nor their reset. Its exact minimizers meet the telescope of Section 2.2. This delayed law is not the monomial law $k^nq^k/Z_n(q)$, where $n\ge1$ and $Z_n(q)=\sum_{k\ge0}k^nq^k$.

For the wider family, [O, Definitions 16.1 and 16.5, Theorems 16.2–16.4 and 16.6–16.9, and Proposition 16.10](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK.md#16-nonnegative-anchored-squares-exact-delay-and-general-real-renewal-instruments) take a nonzero globally nonnegative real polynomial $d$ of degree $2m$, $m\ge0$, with positive leading coefficient $\delta$. They supply real polynomials $p,s$ with degrees at most $m$, $s(0)=0$ and $d=p^2+\Delta(s^2)$, where $\Delta v(t)=v(t+1)-v(t)$. The unique anchored discrete integral $P(0)=0$, $\Delta P=d$ has degree $2m+1$ and leading coefficient $\delta/(2m+1)$. Its integer values are $P(k)=s(k)^2+\sum_{j<k}p(j)^2$. The exact delay is $h=1+\min\{j\ge0:d(j)>0\}\le m+1$; every pair has $(t)_{\underline{h-1}}\mid p$ and $(t)_{\underline h}\mid s$. Maximal delay means precisely $d=c(t)_{\underline m}^2$ with $c>0$.

For $0<q<1$, O completes the law $\gamma_k=q^kP(k)/Z$, $Z=\sum_{k\ge0}q^kP(k)>0$, in dimension $m+2$, with zero and tick Choi ranks two and one and the full stationary interface. All moments are finite, and $\gamma_k>0$ exactly for $k\ge h$. Its actual-posterior dimension bound is $D'\ge h+a+b-1$, where $a,b$ are the ranks of the competitor's actual posterior and tick effect; its memory minimum is proved to be $m+2$ at maximal delay. Its no-tick Choi minimum two uses the previously supplied finite-vector-recurrence squared-norm parity argument; no such parity or CP-growth premise enters Sections 3–5 here. At $m=0$, $d=c>0$ gives the dimension-two law $\gamma_k=k(1-q)^2q^{k-1}$ for $k\ge1$. The zero polynomial has $Z=0$ and gives no normalized law. These exact constructions establish examples and supplier boundaries, not restrictions on the arbitrary instruments below.

### 2.4. Scalar perturbation and actual-history inference are different objects

[O, Section 15](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK.md#15-polynomial-residuals-control-actual-stationary-output) fixes $m\ge2$, $n=2m+1$, a real monic degree-$m$ polynomial $P$ and a real polynomial $S$ of degree at most $m$, anchored by $S(0)=0$. Its residual and nonnegative integer weight are

$$
e=P^2+\Delta(S^2)-\Delta(t^n)/n,
\qquad H(k)=k^n+n\sum_{t<k}e(t)
=n\left(S(k)^2+\sum_{t<k}P(t)^2\right).
$$

For $0<q<1$, O, Theorems 15.2–15.3 supply an actual complete Newton/Gramian instrument with law $H(k)q^k/Z_H(q)$, where $Z_H(q)=\sum_{k\ge0}H(k)q^k$, and its own faithful stationary initialization, even when $e\ne0$. Under a scalar envelope $0<\ell\le H(k)/k^n\le u$ for $k\ge1$, its gap, length-biased interval and initial-wait distances from the monomial law are at most $c=(\sqrt u-\sqrt\ell)/(\sqrt u+\sqrt\ell)$, and its stationary $W$-window distance is at most $1-(1-c)^{\lceil W/2\rceil}$. The finite residual certificates and rational ninth-degree center in O, Theorems 15.4–15.5 supply instances of that envelope. This is a scalar classical output comparison between specified stationary laws. It gives no entire-tick Choi estimate and no permission to substitute a scalar TV bound for the quantity $E$ in Section 4.

[O, Sections 17–19](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK.md#17-information-and-testing-from-one-actual-stationary-history) concern the two fixed scalar laws, with bounded positive tilt and known common $q$, observed through consecutive stationary bits. They derive relative-entropy rates, finite-record converse and attainable testing bounds, fixed-pair endpoint record orders and a rational-center observer. Their initial wait, complete-gap acquisition and unfinished terminal gap are charged; no hidden age or free probability query is available. [O, Section 20](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK.md#20-unknown-parameter-identification-by-paid-conditional-gap-pairs) instead fixes that rational center and permits independent unknown nuisance parameters under the two labels. Conditioning actually acquired gap pairs on sum four removes the nuisance; it gives uniform risk, pointwise finite mean acquisition, compact-band deadlines and a composite small-band order. These statistical results assume their specified stationary renewal laws. They supply neither a hidden-map estimate nor an additional hypothesis for Theorem 4.2. Their exact arithmetic and observer-resource conclusions are not conclusions of this companion.

### 2.5. The published joint-delay limit and its rank discontinuity

[O, published Section 21](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK.md#21-the-joint-delay-boundary-and-its-rank-one-limiting-consumer) is a separate existing result. O, Definition 21.1 fixes globally nonnegative real polynomials $d_0\ne0,d_1$ and $P_i(k)=\sum_{t=0}^{k-1}d_i(t)$; the first positive weight of $P_0$ is $P_0(h)=A>0$ at $h\ge2$, and $a=d_1(0)>0$. For $d_\varepsilon=d_0+\varepsilon d_1$, $\varepsilon>0$, set $P_\varepsilon=P_0+\varepsilon P_1$ and $\gamma_{\varepsilon,q}(k)=q^kP_\varepsilon(k)/\sum_{j\ge0}q^jP_\varepsilon(j)$ for $0<q<1$. With $\delta_j$ denoting point mass at the gap count $j$, O uses

$$
R=\frac{Aq^{h-1}}{\varepsilon a},\qquad
\bar\gamma_R=\frac1{1+R}\delta_1+\frac R{1+R}\delta_h.
$$

O, Theorem 21.2 gives, for every fixed integer moment order $s\ge0$, a bound $\sum_k(k+1)^s|\gamma_{\varepsilon,q}(k)-\bar\gamma_R(k)|\le C_s q$ uniform in $\varepsilon>0$ and $0<q\le1/2$, with constants depending on the fixed polynomial pair. It transfers to stationary interval-and-phase laws and to $W$-windows with bound $\min\{1,CWq\}$. The limiting mean is $[2+(h+1)R]/(1+R)$, and the stationary interval probabilities are length biased, not the unweighted mixing coefficients of $\bar\gamma_R$.

O, Theorem 21.3 gives the four-window distance from the delayed boundary as $2/[2+(h+1)R]+O(q)$ uniformly in $R$, and agreement on every fixed window along $q,\varepsilon\downarrow0$ precisely when $\varepsilon/q^{h-1}\to0$. Its four-window mixture of the two periodic endpoint laws is not a mixture identity for the full process: the cylinder $10101$ differs for $0<R<\infty$. O, Proposition 21.4 keeps the fixed-pair assumption essential: with $d_0(t)=t^2(t-1)^2$, $d_{1,\varepsilon}(t)=1+\varepsilon^{-3/4}t^2$ and $q=\sqrt\varepsilon/2$, one has $R=1$ but limit $\delta_2$, not $(\delta_1+\delta_3)/2$. It also establishes the fixed-$\varepsilon$ supremum-one four-window separation, nonattainment at positive $q$, and noncommuting endpoint limits.

O, Definition 21.5 and Theorems 21.6 and 21.8 treat $\gamma^*=\alpha\delta_1+(1-\alpha)\delta_h$. For $0\le\alpha<1$, the complete nilpotent single-zero-Kraus construction has memory minimum $h+1$ and both Choi ranks one. At $\alpha=1$ the memory minimum is two, again with both Choi ranks one. The lower bound uses the actual posterior, positive survival at $h$ and extinction at $h+1$, or at one and two for the endpoint, through a kernel chain or nilpotent restriction to the reachable space. At every finite polynomial parameter the no-tick Choi minimum remains two by O, Theorem 16.9. This is convergence of stationary classical cylinder laws with separate finite-parameter and limiting realizations. It asserts no Choi convergence between those realizations. These published delay results are not new quantitative results of this volume and are not premises of the proofs below.

### 2.6. Attribution at the precise interfaces

The exact support-growth antecedents of O, Theorem 13.2 are Nengkun Yu and Mingsheng Ying, [*Reachability and Termination Analysis of Concurrent Quantum Programs*, arXiv:1206.1935v1, Theorem 1, pp. 7–8](https://arxiv.org/pdf/1206.1935v1), and Shenggang Ying, Yuan Feng, Nengkun Yu and Mingsheng Ying, [*Reachability Probabilities of Quantum Markov Chains*, arXiv:1304.0060v2, Lemma 1(2), p. 5](https://arxiv.org/pdf/1304.0060v2). Their displayed $D-1$ horizons have respectively the continuation-program and trace-preserving quantum-Markov-chain interfaces described in O, Theorem 16.4. The unrestricted raw positive-seed/detector rank telescope is O's derivation, not an attribution of that stronger statement to those papers.

The CP representation is credited to Choi in Lemma 3.2. Spectral decomposition, singular-value decomposition, finite-dimensional Jordan estimates, Cauchy–Schwarz and the root-of-unity sum used below are classical. O's renewal conventions retain the credit to Monras–Beige–Wiesner, *Hidden Quantum Markov Models and non-adaptive read-out of many-body states*, arXiv:1002.2337v2, equations (25)–(27), and its renewal/coupling comparisons retain the credit to Thorisson, *Coupling, Stationarity, and Regeneration*. The stationary gap and length-bias correspondences in O, Sections 17–21 retain their cited Marzen–Crutchfield and Zamparo sources. O's finite-termination comparison in published Theorem 21.8 retains Yu–Ying, Theorem 5, and Bhat–Mallick, *Nilpotent Completely Positive Maps*, arXiv:1310.0591v1, Proposition 2.2 and Corollary 2.5, with the nilpotence premise checked on the actual reachable restriction. None of these attributions replaces the quantitative coefficient, leakage, cross-block or calibration proofs below.

## 3. A quantitative detector-rank horizon

**Definition 3.1 (Norms and the output-first Choi convention).** Fix the basis of Section 1, put $E_{ij}=|e_i\rangle\langle e_j|$, and use

$$
\begin{aligned}
J(\Lambda)&=\sum_{i,j=0}^{D-1}\Lambda(E_{ij})\otimes E_{ij},\\
|A\rangle\!\rangle&=\sum_{i,j=0}^{D-1}A_{ij}e_i\otimes e_j,\\
J(X\mapsto AXA^\dagger)&=|A\rangle\!\rangle\langle\!\langle A|.
\end{aligned} \tag{3.1}
$$

The output factor comes first, with no division by $D$. Coordinate conjugation and transpose ${}^{\mathsf T}$ refer to this basis. Interchanging the tensor factors converts the input-first convention mentioned in O, Theorem 2.1 to this one. The reset map $X\mapsto\tau\operatorname{Tr}(FX)$ therefore has Choi matrix $\tau\otimes F^{\mathsf T}$.

The norms $\|\cdot\|_1,\|\cdot\|_2,\|\cdot\|_\infty$ denote trace norm, Hilbert–Schmidt norm and operator norm. Eigenvalues of $B\ge0$ are numbered $\lambda_1(B)\ge\cdots\ge\lambda_D(B)\ge0$. A CP map $T$ is subunital if $T(I)\le I$. The following results concern arbitrary complex maps; the real Gramian constructions in O are not assumed. The full-map metric is separate from the scalar-output and actual-history results in Sections 2.4–2.5.

**Lemma 3.2 (Finite Kraus representations and trace-norm tools).** Every CP map on $M_D(\mathbb C)$ has a representation with at most $D^2$ Kraus matrices. For compatible finite matrices,

$$
\begin{aligned}
\|AB^\dagger\|_1&\le\|A\|_2\|B\|_2,\\
\|AZB\|_1&\le\|A\|_\infty\|Z\|_1\|B\|_\infty,\\
\|A\otimes B\|_1&=\|A\|_1\|B\|_1.
\end{aligned} \tag{3.2}
$$

For Hermitian $Y$ on a tensor product,

$$
\|\operatorname{Tr}_{\rm in}Y\|_1\le\|Y\|_1.
\tag{3.3}
$$

A subunital CP map contracts the operator norm on every complex matrix.

Proof. With $\Omega=\sum_i e_i\otimes e_i$, complete positivity gives $J(\Lambda)=(\Lambda\otimes\mathrm{id})(|\Omega\rangle\langle\Omega|)\ge0$. Spectral decomposition absorbs square roots of eigenvalues into vectors and writes it as $\sum_{a=1}^M v_av_a^\dagger$, $M\le D^2$. Unvectorize $v_a=|A_a\rangle\!\rangle$. Comparing the coefficient of each input matrix unit $E_{ij}$ gives $\Lambda(E_{ij})=\sum_a A_aE_{ij}A_a^\dagger$, hence the representation on every $X$. The range of a positive sum of outer products is the span of its vectors: its kernel is the intersection of their orthogonal complements. Thus the Choi range is the Kraus-vectorization span, and its rank is the minimum Kraus count. The finite representation is a proof device, not a restriction on other Kraus families.

This is the finite-dimensional representation associated with M.-D. Choi, [*Completely positive linear maps on complex matrices*, Linear Algebra and its Applications **10**, 285–290 (1975)](https://doi.org/10.1016/0024-3795(75)90075-0); the needed convention and argument have been given explicitly.

Singular-value decomposition proves the dual formula

$$
\|Z\|_1=\sup_{\|W\|_\infty\le1}|\operatorname{Tr}(W^\dagger Z)|.
\tag{3.4}
$$

In singular-vector coordinates the diagonal entries of a contraction have modulus at most one, giving the sum-of-singular-values upper bound, and the polar partial isometry attains it. Hilbert–Schmidt Cauchy–Schwarz applied to $\operatorname{Tr}(B^\dagger W^\dagger A)$ gives the first inequality in (3.2). For the second write $Z=\sum_j s_ju_jv_j^\dagger$ with unit singular vectors; the trace norm of each $Au_jv_j^\dagger B$ is $\|Au_j\|\|B^\dagger v_j\|$, and sum. Tensoring singular-value decompositions makes all singular values pairwise products, proving the third. Also $\|Z\|_\infty\le\|Z\|_2$, and $Z\ge0$ has trace norm $\operatorname{Tr}Z$.

For (3.3), decompose $Y=Y_+-Y_-$ into positive parts. Partial trace is positive and trace preserving, so the triangle inequality bounds the result by $\operatorname{Tr}Y_++\operatorname{Tr}Y_-=\|Y\|_1$. Only the Hermitian assertion is needed here.

For $T(X)=\sum_a A_aXA_a^\dagger$ let $V=[A_1\ \cdots\ A_M]$ be the Kraus row from $H^{\oplus M}$ to $H$. Then

$$
VV^\dagger=T(I)\le I,\qquad
T(X)=V\operatorname{diag}(X,\ldots,X)V^\dagger.
\tag{3.5}
$$

Thus $\|V\|_\infty\le1$, each $\|A_a\|_\infty\le1$, and $\|T(X)\|_\infty\le\|X\|_\infty$. The zero map, with an empty Kraus sum, has the same property directly. $\square$

**Theorem 3.3 (Quantitative rank-horizon estimate without a conditioning hypothesis).** Let $D\ge2$, $2\le r\le D$ and $n\ge1$ be integers. Let $T:M_D(\mathbb C)\to M_D(\mathbb C)$ be subunital and CP, $B$ an effect, and $\sigma$ a density. If $\epsilon\ge0$, $0<p\le1$ and

$$
\operatorname{Tr}[\sigma T^k(B)]\le\epsilon\quad(0\le k\le D-r),
\qquad \operatorname{Tr}[\sigma T^n(B)]\ge p,
\tag{3.6}
$$

then

$$
\begin{aligned}
\lambda_r(B)&\le A_{D,r,n}(p)\epsilon,\\
A_{D,r,n}(p)&=\frac{8D}{p^2}
\left(\frac{8nD^{5/2}}p\right)^{2(D-r)}.
\end{aligned} \tag{3.7}
$$

For $r=D$, the stronger $\lambda_D(B)\le\epsilon$ requires no late condition. No separation of $n$ from the early indices is required. There is no eigenvalue-gap, diagonalizability, commutation, real-coordinate, single-Kraus or word-Gramian hypothesis.

Proof. Put $s=\lambda_r(B)$. The case $s=0$ is immediate. If $s>0$, choose

$$
t=\frac{ps}{4},\qquad
\delta=\frac{p}{8nD^{3/2}},\qquad
C=\left(\frac D\delta\right)^{D-r}
=\left(\frac{8nD^{5/2}}p\right)^{D-r}.
\tag{3.8}
$$

Since $B$ is an effect, $0<s\le1$, so $0<t\le p/4$ and $0<\delta<1$. Let $B_+$ retain, with their original values, all eigenvalues of $B$ at least $t$, and put $B_-=B-B_+$. For an orthonormal eigenbasis of its support,

$$
r'\ge r,\qquad
B_+=\sum_{b=1}^{r'}\lambda_b'|\eta_b\rangle\langle\eta_b|,
\quad t\le\lambda_b'\le1,\qquad 0\le B_-\le tI.
\tag{3.9}
$$

The cutoff is chosen inside the proof, with no spectral-gap premise.

Use Lemma 3.2 to write $T(X)=\sum_{a=1}^M A_aXA_a^\dagger$, $M\le D^2$. For $w=(a_1,\ldots,a_k)$ put $A_w=A_{a_k}\cdots A_{a_1}$, including the identity for the empty word. Start an orthonormal list with $\eta_1,\ldots,\eta_{r'}$. For its current span $W$, projection $P_W$ and basis $e_1,\ldots,e_m$, whenever some residual $(I-P_W)A_ae_j$ has norm $\beta>\delta$, adjoin its normalization. Keep all earlier vectors. Each addition raises the dimension, so there are at most $D-r'\le D-r$ additions. At termination, for the final projection $P$ and $Q=I-P$,

$$
\|QA_ae_j\|\le\delta\quad(1\le a\le M,\ 1\le j\le m).
\tag{3.10}
$$

If the whole space has been reached then $Q=0$; otherwise no residual exceeds the threshold. This finite argument uses dimension, not a lower singular value of a word collection.

After $\ell$ additions, every basis vector has an expansion in $A_w\eta_b$ with $|w|\le\ell$ and coefficient absolute sum at most $(D/\delta)^\ell$. Initially its coefficient sum is one. The new vector at an addition is

$$
e_{m+1}=\frac{A_ae_j-\sum_{h=1}^m
\langle e_h,A_ae_j\rangle e_h}{\beta}.
\tag{3.11}
$$

Each projection coefficient has modulus at most one because $\|A_a\|_\infty\le1$. There are $m+1\le D$ contributions in the numerator, and $\beta>\delta$. Substituting the preceding expansions therefore multiplies their absolute coefficient bound by at most $D/\delta$ and increases word length by at most one. Old expansions remain bounded since $D/\delta\ge1$. Induction proves the claim. Every final vector consequently uses words of length at most $D-r$ with coefficient absolute sum at most $C$.

Positivity of every Kraus-word summand and (3.9) give, for every such word of length $k$ and every initial eigenvector,

$$
t\|\sigma^{1/2}A_w\eta_b\|^2
\le\operatorname{Tr}[\sigma T^k(B)]\le\epsilon.
\tag{3.12}
$$

This includes the empty word. Substitution and the vector triangle inequality give $\|\sigma^{1/2}e_j\|\le C\sqrt{\epsilon/t}$. Hence

$$
\operatorname{Tr}(\sigma P)
=\sum_{j=1}^m\|\sigma^{1/2}e_j\|^2
\le DC^2\frac\epsilon t.
\tag{3.13}
$$

To control the entire leakage from this approximately invariant space, use the Kraus row $V$ in (3.5) and $\widehat P=\operatorname{diag}(P,\ldots,P)$ on $H^{\oplus M}$. Then

$$
\begin{aligned}
\|QV\widehat P\|_\infty^2
&\le\|QV\widehat P\|_2^2
=\sum_{a=1}^M\sum_{j=1}^m\|QA_ae_j\|^2
\le D^3\delta^2,\\
\alpha&:=D^{3/2}\delta=\frac p{8n}.
\end{aligned} \tag{3.14}
$$

For $X=PXP$, set $\widehat X=\operatorname{diag}(X,\ldots,X)$. The identity $T(X)-PT(X)P=QT(X)+PT(X)Q$ gives

$$
\begin{aligned}
T(X)-PT(X)P
={}&QV\widehat P\widehat X\widehat P V^\dagger\\
&+PV\widehat P\widehat X\widehat P V^\dagger Q.
\end{aligned} \tag{3.15}
$$

The first term includes the $Q$-$Q$ and $Q$-$P$ blocks once each, and the second the $P$-$Q$ block. The projections and $V$ are contractions; (3.14), also applied to the adjoint factor, bounds each term by $\alpha\|X\|_\infty$. Thus all leakage, including coherences, is at most $2\alpha\|X\|_\infty$.

Define $T_P(X)=PT(PXP)P$. Its Kraus matrices $PA_aP$ satisfy

$$
\sum_a PA_aP A_a^\dagger P\le PT(I)P\le P\le I.
\tag{3.16}
$$

It is subunital and contracts operator norm. Since $0\le B_+\le P$ and $T_P(P)\le P$, positivity gives $0\le T_P^j(B_+)\le P$ for all $j$. Put $Y_j=T_P^j(B_+)$. The iterate difference is

$$
T^{j+1}(B_+)-Y_{j+1}
=T\big(T^j(B_+)-Y_j\big)+T(Y_j)-PT(Y_j)P.
\tag{3.17}
$$

The first term has norm at most the preceding error; the second at most $2\alpha$ by (3.15), since $Y_j=PY_jP$ and $\|Y_j\|_\infty\le1$. The initial error is zero, giving $\|T^n(B_+)-T_P^n(B_+)\|_\infty\le2n\alpha=p/4$. Also $0\le T^n(B_-)\le tI$ by subunitality. Trace against $\sigma$ to get

$$
\begin{aligned}
p&\le\operatorname{Tr}[\sigma T^n(B)]\\
&\le\operatorname{Tr}(\sigma P)+2n\alpha+t\\
&\le DC^2\frac\epsilon t+\frac p4+\frac p4.
\end{aligned} \tag{3.18}
$$

Both $p,t$ are positive, so $t\le2DC^2\epsilon/p$. Using $t=ps/4$ yields $s\le8DC^2\epsilon/p^2$, which is (3.7). At $\epsilon=0$ the argument contradicts $s>0$ without dividing by $\epsilon$.

For $r=D$, $B\ge\lambda_D(B)I$ and the first early inequality give $\lambda_D(B)\le\operatorname{Tr}(\sigma B)\le\epsilon$. If $n$ is an early index, the hypotheses can force $p\le\epsilon$ but the proof is unchanged. An empty Kraus family makes the positive late condition impossible for $n\ge1$; it creates no exceptional nonzero case. $\square$

## 4. Stability of the entire actual calibrated tick map

**Definition 4.1 (Actual instrument data and the comparison map).** Let $D\ge2$ and let $\Phi,\Psi:M_D(\mathbb C)\to M_D(\mathbb C)$ be arbitrary CP maps whose sum preserves trace. For a density $\rho_0$, assume and define

$$
\nu=\operatorname{Tr}\Psi(\rho_0)>0,\qquad
\tau=\frac{\Psi(\rho_0)}\nu,\qquad
F=\Psi^*(I),\qquad
w_k=\operatorname{Tr}[F\Phi^k(\tau)]\quad(k\ge0).
\tag{4.1}
$$

The state $\tau$ is the actual output after that tick. Completeness gives $\Phi^*(I)+F=I$, $0\le F\le I$ and $0<\nu\le1$. The weights are actual probabilities of $k$ zeros followed by a tick from $\tau$, and can be a subprobability law. With $s_k=\operatorname{Tr}\Phi^k(\tau)$,

$$
s_0=1,\qquad s_k-s_{k+1}=w_k,\qquad
\sum_{k=0}^Nw_k=1-s_{N+1}\le1.
\tag{4.2}
$$

The comparison map and its entire Choi error are

$$
\mathcal R_\tau(X)=\tau\operatorname{Tr}(FX),\qquad
E=\|J(\Psi)-\tau\otimes F^{\mathsf T}\|_1.
\tag{4.3}
$$

Here $J$ and the trace norm have exactly the unnormalized output-first convention of Definition 3.1. There are no assumptions of hidden invariance, purity, reset, proper gaps, renewal independence, real coordinates, restricted Kraus count, commutation, diagonalizability, spectral gap or Gramian conditioning.

**Theorem 4.2 (Quantitative whole-map reset stability).** For $D\ge3$, suppose $\epsilon\ge0$, $0<p\le1$ and

$$
\max_{0\le k\le D-2}w_k\le\epsilon,\qquad w_{D-1}\ge p.
\tag{4.4}
$$

Define

$$
A_D(p)=\frac{8D}{p^2}
\left(\frac{8(D-1)D^{5/2}}p\right)^{2(D-2)},
\qquad z=\min\{1,A_D(p)\epsilon\}.
\tag{4.5}
$$

For $D=2$, assume only $w_0\le\epsilon$ with $\epsilon\ge0$, and define instead $z=\min\{1,\epsilon\}$. There is no late-probability condition in dimension two. In both cases put

$$
\begin{aligned}
a&=(D-1)z,\\
B_D(z,\nu)&=\min\left\{
2(1+a),\quad
2a+2\sqrt a+2(1+a)
\left(\frac z\nu+\sqrt{\frac z\nu}\right)
\right\}.
\end{aligned} \tag{4.6}
$$

Then

$$
\lambda_2(F)\le z,\qquad E\le B_D(z,\nu)\le2D.
\tag{4.7}
$$

In particular,

$$
\begin{aligned}
D\ge3:\quad& E\le\min\left\{2D,\,
8D\sqrt{\frac{A_D(p)\epsilon}{\nu}}\right\},\\
D=2:\quad& E\le\min\left\{4,\,
16\sqrt{\frac{\epsilon}{\nu}}\right\}.
\end{aligned} \tag{4.8}
$$

The function $B_D$ gives a sharper valid bound; its constants are not asserted optimal.

Proof. The CP map $T=\Phi^*$ has $T(I)=I-F\le I$. The trace-dual identity is

$$
\operatorname{Tr}[\tau T^k(F)]
=\operatorname{Tr}[F\Phi^k(\tau)]=w_k.
\tag{4.9}
$$

For $D\ge3$, Theorem 3.3 applies with $B=F$, $\sigma=\tau$, $r=2$ and $n=D-1$, giving $\lambda_2(F)\le A_D(p)\epsilon$. The effect bound also gives $\lambda_2(F)\le1$. For $D=2$, $F\ge\lambda_2(F)I$ directly gives $\lambda_2(F)\le\operatorname{Tr}(\tau F)=w_0\le\epsilon$, with no late observation.

Put $s=\lambda_2(F)$ and $\lambda=\lambda_1(F)$. The actual rate $\nu>0$ implies $0<\lambda\le1$. Choose any unit top eigenvector $\eta$ and set

$$
\begin{aligned}
P&=|\eta\rangle\langle\eta|,\qquad Q=I-P,\\
F&=\lambda P+F_Q,\qquad F_Q=QFQ,\qquad 0\le F_Q\le sQ,\\
a_0&=\operatorname{Tr}F_Q\le(D-1)s,\qquad
\mu=\frac{\Psi(P)}\lambda.
\end{aligned} \tag{4.10}
$$

The symbol $\mu$ in this proof is a density, not the interval mean in Section 1: $\operatorname{Tr}\Psi(P)=\operatorname{Tr}(FP)=\lambda$. A repeated top eigenvalue causes no exception; the remaining eigenvalues are still at most $s$. Neither $\mu$ nor $\tau$ is assumed pure.

Choose finite tick Kraus matrices $L_i$. Let $W,Z$ be the column matrices with columns respectively $|L_iP\rangle\!\rangle$ and $|L_iQ\rangle\!\rangle$. Since

$$
|L_iP\rangle\!\rangle=L_i\eta\otimes\overline\eta,
\tag{4.11}
$$

the fixed Choi convention gives

$$
WW^\dagger=\lambda\mu\otimes P^{\mathsf T},\qquad
\|W\|_2^2=\lambda,\qquad
\|Z\|_2^2=\sum_i\operatorname{Tr}(QL_i^\dagger L_iQ)=a_0.
\tag{4.12}
$$

Expansion of the entire matrix yields

$$
J(\Psi)-\mu\otimes F^{\mathsf T}
=WZ^\dagger+ZW^\dagger+
\big(ZZ^\dagger-\mu\otimes F_Q^{\mathsf T}\big).
\tag{4.13}
$$

The last two positive matrices each have trace $a_0$, so the trace norm of their difference is at most $2a_0$. The two cross terms each have trace norm at most $\sqrt{\lambda a_0}$ by Lemma 3.2. Hence

$$
\|J(\Psi)-\mu\otimes F^{\mathsf T}\|_1
\le2a_0+2\sqrt{\lambda a_0}.
\tag{4.14}
$$

This includes the Choi coherences between the input directions $P$ and $Q$. Controlling only the diagonal compressions would not prove (4.14).

The density $\mu$ obtained from the top effect direction must be compared with the prescribed actual output. Form the horizontal block matrices

$$
U=[L_iP\rho_0^{1/2}]_i,\qquad
V_0=[L_iQ\rho_0^{1/2}]_i,
\qquad q_0=\lambda\langle\eta,\rho_0\eta\rangle,
\qquad d=\operatorname{Tr}(F_Q\rho_0).
\tag{4.15}
$$

The identity $P\rho_0P=\langle\eta,\rho_0\eta\rangle P$ implies

$$
UU^\dagger=q_0\mu,\qquad
\|U\|_2^2=q_0,\qquad
\|V_0\|_2^2=d\le s,\qquad \nu=q_0+d.
\tag{4.16}
$$

The last equality follows by tracing $F\rho_0$ in (4.10); the effect has no $P$-$Q$ block even when the initializer has coherences. The actual calibration is the full matrix identity

$$
\nu\tau=UU^\dagger+V_0V_0^\dagger+UV_0^\dagger+V_0U^\dagger.
\tag{4.17}
$$

Subtract $\nu\mu$. The positive terms $V_0V_0^\dagger$ and $d\mu$ have trace $d$, and the two cross terms have trace norm at most $\sqrt{q_0d}$. Therefore

$$
\begin{aligned}
\nu\|\tau-\mu\|_1&\le2d+2\sqrt{q_0d},\\
\|\tau-\mu\|_1&\le\frac{2s}{\nu}+2\sqrt{\frac s\nu}.
\end{aligned} \tag{4.18}
$$

Here $q_0\le\nu$ was used. Calibration divides only by the assumed positive $\nu$. If $q_0=0$ the estimate still applies, and if $s=0$ it gives $d=0$ and $\tau=\mu$.

The tensor trace-norm identity and the triangle inequality combine (4.14) and (4.18) into

$$
E\le2a_0+2\sqrt{\lambda a_0}
+2(\lambda+a_0)\left(\frac s\nu+\sqrt{\frac s\nu}\right).
\tag{4.19}
$$

Substitute $\lambda\le1$, $s\le z$ and $a_0\le(D-1)z=a$ to get the second entry of (4.6). Independently, $J(\Psi)$ and $\tau\otimes F^{\mathsf T}$ are positive and have the same trace $\operatorname{Tr}F=\lambda+a_0$. Thus

$$
E\le2\operatorname{Tr}F\le2(1+a)\le2D.
\tag{4.20}
$$

This supplies the other entry of (4.6) and proves (4.7).

For (4.8), put $u=z/\nu$. If $0\le u\le1$, then $\nu\le1$ gives $z\le u$, $a\le(D-1)u$ and $1+a\le D$. Since $u\le\sqrt u$ on that interval, the second entry of (4.6) is at most

$$
\big(2(D-1)+2\sqrt{D-1}+4D\big)\sqrt u\le8D\sqrt u.
\tag{4.21}
$$

The final comparison follows from $\sqrt{D-1}\le D-1$ and $D\ge2$. If $u>1$, (4.20) instead gives $E\le2D\le8D\sqrt u$. The argument includes $u=0$. Use $z\le A_D(p)\epsilon$ or, for $D=2$, $z\le\epsilon$, retaining the independent cap $2D$, to obtain (4.8). $\square$

**Corollary 4.3 (Actual input outputs and the conditional denominator).** The comparison map $\mathcal R_\tau$ is CP with the same effect $F$ as $\Psi$, and

$$
J(\mathcal R_\tau)=\tau\otimes F^{\mathsf T},\qquad
\mathcal R_\tau(\rho_0)=\nu\tau=\Psi(\rho_0).
\tag{4.22}
$$

Consequently $(\Phi,\mathcal R_\tau)$ is a complete binary instrument and agrees at the actual calibration input. For every density $\rho$,

$$
\|\Psi(\rho)-\tau\operatorname{Tr}(F\rho)\|_1
\le\|\rho\|_\infty E\le E.
\tag{4.23}
$$

If $q_\rho=\operatorname{Tr}(F\rho)>0$, then

$$
\left\|\frac{\Psi(\rho)}{q_\rho}-\tau\right\|_1
\le\min\left\{2,\frac{\|\rho\|_\infty E}{q_\rho}\right\}
\le\min\left\{2,\frac E{q_\rho}\right\}.
\tag{4.24}
$$

A lower bound $q_\rho\ge q_{\min}>0$ thus gives uniform conditional control. At $q_\rho=0$ there is no normalized conditional state.

Proof. Diagonalize $\tau=\sum_a t_a|u_a\rangle\langle u_a|$ and $F=\sum_b f_b|v_b\rangle\langle v_b|$. The matrices $\sqrt{t_af_b}|u_a\rangle\langle v_b|$ represent $\mathcal R_\tau$, and their effects sum to $F$ because $\sum_a t_a=1$. This proves CP and completeness with the same zero branch. Evaluation on $E_{ij}$ uses $\operatorname{Tr}(FE_{ij})=F_{ji}$, proving the Choi identity and its transpose. Evaluation at $\rho_0$ gives the calibration since $\operatorname{Tr}(F\rho_0)=\nu$.

Set $\Delta=\Psi-\mathcal R_\tau$. Matrix-unit expansion gives

$$
\Delta(\rho)=\operatorname{Tr}_{\rm in}
\left[(I\otimes\sqrt{\rho^{\mathsf T}})\,
J(\Delta)\,(I\otimes\sqrt{\rho^{\mathsf T}})\right].
\tag{4.25}
$$

Indeed the input trace for $E_{ij}$ is $\operatorname{Tr}(\sqrt{\rho^{\mathsf T}}E_{ij}\sqrt{\rho^{\mathsf T}})=\operatorname{Tr}(E_{ij}\rho^{\mathsf T})=\rho_{ij}$. Both the Choi difference and its sandwich are Hermitian. Equations (3.2)–(3.3) bound its output trace norm by $\|\sqrt{\rho^{\mathsf T}}\|_\infty^2\|J(\Delta)\|_1=\|\rho\|_\infty E$. A density has operator norm at most one. For positive $q_\rho$ divide by that scalar; the normalized outputs are densities, whose distance is also at most two. No division by a zero probability occurs. This gives ordinary-input consequences of the stated Choi metric, without a diamond-norm assertion. $\square$

**Corollary 4.4 (Uniform ranges, exact endpoints and nonempty classes).** Fix $D\ge3$ and $0<\nu_0,p_0\le1$. The class in Definition 4.1 with $\nu\ge\nu_0$, early maximum at most $\epsilon$ and $w_{D-1}\ge p_0$ satisfies

$$
E\le\min\left\{2D,8D\sqrt{\frac{A_D(p_0)\epsilon}{\nu_0}}\right\}.
\tag{4.26}
$$

For $D=2$, only the lower bound on $\nu$ is needed, giving $\min\{4,16\sqrt{\epsilon/\nu_0}\}$. A fixed positive lower bound on $\nu$ is sufficient but is not necessary for every convergent family: for fixed $D\ge3$ and $p_0>0$, $\epsilon/\nu\to0$ suffices even if $\nu\to0$. In dimension two the same ratio condition requires no late bound. For fixed $D\ge3$ with both rates varying, the proved sufficient condition is

$$
\frac{\epsilon}{\nu p^{2D-2}}\longrightarrow0,
\qquad A_D(p)=C_Dp^{-(2D-2)},\qquad
C_D=8D[8(D-1)D^{5/2}]^{2(D-2)}.
\tag{4.27}
$$

No optimal dependence on $p$ or $D$ is asserted.

Proof. The expression $A_D(p)$ decreases with $p>0$. Substituting the two lower bounds into (4.8) proves (4.26). Collecting the powers of $p$ gives (4.27), and the same estimates imply the convergence statements.

The classes are nonempty for every allowed $D,\epsilon,\nu_0,p_0$. Put $n=D-1$, $P_j=|e_j\rangle\langle e_j|$, and

$$
S=\sum_{j=0}^{n-1}|e_{j+1}\rangle\langle e_j|,
\qquad L=|e_0\rangle\langle e_n|,
\qquad \Phi(X)=SXS^\dagger,\qquad\Psi(X)=LXL^\dagger.
\tag{4.28}
$$

Since $S^\dagger S+L^\dagger L=(I-P_n)+P_n=I$, the instrument is complete. With $\rho_0=P_n$ its actual quantities are $\nu=1$, $\tau=P_0$ and $\Phi^k(\tau)=P_k$ for $0\le k\le n$. Thus all early weights vanish and $w_n=1$. More generally $\rho_0=vP_n+(1-v)P_0$ realizes every prescribed $0<v\le1$ as $\nu=v$, with unchanged $\tau$ and weights. Since $\Phi^{n+1}(\tau)=0$, the next gap is proper. Negative $\epsilon$, or required probability lower bounds $\nu_0>1$ or $p_0>1$, are incompatible with the respective conditions.

For $D\ge3$, $\epsilon=0$ and $p>0$ give exact first-hit index $D-1$. Apply O, Theorem 13.3 with the full telescope in Section 2.2: $\tau,F$ have rank one, both reachable spaces are full, and the entire tick is an exact reset of Choi rank one. Independently, the quantitative estimate gives $E=0$, and the matrix-unit definition (3.1) makes equality of Choi matrices equality of maps. The extra exact rank and reachability claims belong to that exact supplier; small positive error does not imply them.

For $D=2$, $w_0=0$ gives $\lambda_2(F)=0$ and $E=0$ with no later observation. Since $\nu>0$, $F\ne0$ has rank one. Moreover $\operatorname{Tr}(F\tau)=\|F^{1/2}\tau^{1/2}\|_2^2=0$ places $\operatorname{ran}\tau$ in the one-dimensional kernel of $F$. Thus $\tau$ is pure and the exact reset Choi rank is one. Full reachability does not follow: take $\Phi(X)=P_0XP_0$, $\Psi(X)=|e_0\rangle\langle e_1|X|e_1\rangle\langle e_0|$ and $\rho_0=P_1$. The effects are $P_0,P_1$, so the instrument is complete, $\nu=1$, $\tau=P_0$ and every zero power remains $P_0$. All $w_k$ vanish and the reachable span is only $\mathbb C e_0$.

At the exact late endpoint $w_{D-1}=1$, (4.2) forces every earlier weight to be zero regardless of the declared $\epsilon$. O, Theorem 13.3 therefore applies for every actual $\nu>0$. Rate-collapse counterexamples satisfying a fixed lower bound $p_0<1$ do not extend to $p_0=1$.

At $\nu=0$ the actual density $\tau$ is undefined. For $D\ge3$, $A_D(p)$ is undefined at $p=0$; that substitution cannot repair a missing late bound. Dimension two has no $p$ parameter. In the separate scalar case $D=1$, a CP tick map is multiplication by a nonnegative scalar and the sole density is $1$; a positive actual tick makes it identical to its reset map, so $E=0$. Dimension zero admits no density. $\square$

## 5. Sharpness and nonuniformity through actual binary instruments

**Theorem 5.1 (A rotating single-Kraus tick: sharp square-root order and rare-event failure).** For every fixed $D\ge2$, there are complete binary instruments satisfying Theorem 4.2 with $\epsilon\downarrow0$, $\nu=1$ and $w_{D-1}\ge1/2$, whose entire Choi errors satisfy $E/\sqrt\epsilon\to2$. Hence the exponent $1/2$ cannot be increased, and no uniform $o(\sqrt\epsilon)$ bound holds on that class. Actual instruments also show the need to control a collapsing $\nu$, and the sharp worst-case order $\sqrt{\epsilon/\nu}$ when this ratio tends to zero. Individual Kraus matrix rank and Choi rank remain different quantities.

Proof. Put $n=D-1$, use $e_0,\ldots,e_n$, and write $P_j=|e_j\rangle\langle e_j|$. Choose $0<s<1$ and $s\le v\le1$. There is a unique $\theta\in[0,\pi/2]$ with

$$
\sin^2\theta=\frac{s(1-v)}{v(1-s)}.
\tag{5.1}
$$

The denominator is positive and the right side belongs to $[0,1]$ precisely because $s\le v$. Define orthonormal output vectors and Kraus matrices by

$$
\begin{aligned}
u&=\cos\theta\,e_0+\sin\theta\,e_n,&
z_\theta&=-\sin\theta\,e_0+\cos\theta\,e_n,\\
K&=\sqrt{1-s}\,|e_1\rangle\langle e_0|
+\sum_{j=1}^{n-1}|e_{j+1}\rangle\langle e_j|,&
L&=\sqrt s\,|z_\theta\rangle\langle e_0|+|u\rangle\langle e_n|,\\
\Phi(X)&=KXK^\dagger,&\Psi(X)&=LXL^\dagger.
\end{aligned} \tag{5.2}
$$

Here $u$ is a vector and $\nu$ below is the actual scalar rate. The intermediate sum is empty when $D=2$. Orthogonality of $u,z_\theta$ and of the shift outputs gives

$$
F=L^\dagger L=sP_0+P_n,\qquad
K^\dagger K=(1-s)P_0+\sum_{j=1}^{n-1}P_j,\qquad
K^\dagger K+L^\dagger L=I.
\tag{5.3}
$$

These Kraus maps form a complete instrument on the full complex algebra.

Specify the initializer by

$$
r=-\sqrt{\frac vs}\sin\theta\,e_0+\sqrt v\cos\theta\,e_n,
\qquad \rho_0=|r\rangle\langle r|.
\tag{5.4}
$$

Equation (5.1) gives

$$
\|r\|^2=v+\frac{v(1-s)}s\sin^2\theta=1,
\tag{5.5}
$$

and direct application of $L$ gives

$$
Lr=\sqrt v\,(-\sin\theta\,z_\theta+\cos\theta\,u)
=\sqrt v\,e_0.
\tag{5.6}
$$

Thus the actual quantities are exactly $\nu=v$ and $\tau=P_0$. Powers of the zero shift yield

$$
\Phi^0(\tau)=P_0,\qquad
\Phi^k(\tau)=(1-s)P_k\ (1\le k\le n),\qquad
\Phi^{n+1}(\tau)=0.
\tag{5.7}
$$

The entire next-gap law is therefore

$$
w_0=s,\qquad w_k=0\ (1\le k<n),\qquad
w_n=1-s,\qquad w_k=0\ (k>n).
\tag{5.8}
$$

It is proper. The formulas include $n=1$ with no intermediate indices, and give early maximum $\epsilon=s$ and late probability $1-s$ in every stated dimension.

Input $P_n$ has tick probability one and output $|u\rangle\langle u|$. In the span of $e_0,e_n$ its difference from $\tau=P_0$ is

$$
|u\rangle\langle u|-P_0
=\begin{pmatrix}
-\sin^2\theta&\sin\theta\cos\theta\\
\sin\theta\cos\theta&\sin^2\theta
\end{pmatrix}.
\tag{5.9}
$$

It has trace zero and determinant $-\sin^2\theta$, so its eigenvalues are $\pm\sin\theta$. Corollary 4.3 at this probability-one input gives

$$
E\ge2\sin\theta
=2\sqrt{\frac{s(1-v)}{v(1-s)}}.
\tag{5.10}
$$

For $v=1$, the angle is zero, $\rho_0=P_n$ and $\nu=1$. To calculate the entire Choi norm in this subfamily, put

$$
a=e_0\otimes e_n,\qquad
b=e_n\otimes e_0,\qquad
c=e_0\otimes e_0.
\tag{5.11}
$$

These vectors are orthonormal, $|L\rangle\!\rangle=a+\sqrt s\,b$, and $\tau\otimes F^{\mathsf T}=|a\rangle\langle a|+s|c\rangle\langle c|$. Hence

$$
J(\Psi)-\tau\otimes F^{\mathsf T}
=\sqrt s\,(|a\rangle\langle b|+|b\rangle\langle a|)
+s|b\rangle\langle b|-s|c\rangle\langle c|.
\tag{5.12}
$$

The $a,b$ block is $\left(\begin{smallmatrix}0&\sqrt s\\\sqrt s&s\end{smallmatrix}\right)$, with eigenvalues $(s\pm\sqrt{s^2+4s})/2$ of opposite signs. The $c$ eigenvalue is $-s$, and the matrix vanishes on the remaining orthogonal complement. Therefore

$$
E=s+\sqrt{s^2+4s},\qquad
\frac E{\sqrt\epsilon}=\sqrt s+\sqrt{s+4}\longrightarrow2.
\tag{5.13}
$$

For $s\le1/2$ the late weight is at least $1/2$. This proves square-root sharpness with fixed dimension, fixed calibration rate and a fixed positive late lower bound.

For collapse of the actual rate, choose $v=s$. Then $\theta=\pi/2$, and (5.10) gives $E\ge2$ despite $\epsilon=s\to0$ and $w_n=1-s\to1$. Each actual rate is $\nu=s>0$. Also (4.20) gives $E\le2\operatorname{Tr}F=2(1+s)$, so $E\to2$. Mere positivity of each actual rate does not yield uniform convergence, even at fixed $D$ and any fixed late lower bound $p_0<1$.

For $s\le v\le1/2$, (5.10) gives

$$
E\ge\sqrt{\frac{2s}{v}}=\sqrt{\frac{2\epsilon}{\nu}},
\tag{5.14}
$$

since $(1-v)/(1-s)\ge1/2$. Combine with (4.8) and $w_n\ge1/2$ for $s\le1/2$ to obtain matching square-root order in $\epsilon/\nu$, up to constants depending on fixed dimension and the late lower bound. Vanishing rates with vanishing ratios occur by setting $v=s^\alpha$ for any fixed $0<\alpha<1$. Eventually $s\le v\le1/2$, while $\nu\to0$ and $\epsilon/\nu=s^{1-\alpha}\to0$. Both bounds have power $(1-\alpha)/2$. This is a worst-case order statement, without an optimal leading-constant assertion.

The $v=1$ subfamily also shows why a conditional output needs its own event denominator. Input $P_0$ has tick probability $s$, and

$$
\Psi(P_0)=sP_n,\qquad
\left\|\frac{\Psi(P_0)}s-\tau\right\|_1
=\|P_n-P_0\|_1=2,
\tag{5.15}
$$

even as (5.13) tends to zero with actual calibration rate one. This small event probability is at the compared input, distinct from the rate at $\rho_0$.

For every $s>0$, the two nonzero input columns of $L$ have independent outputs $z_\theta,u$. Thus $L$ and $F$ have rank two. Nevertheless $\Psi$ has Choi rank one because it has a single nonzero Kraus vectorization. At $v=1$ it is not an exact reset: $P_0$ and $P_n$ have normalized tick outputs $P_n$ and $P_0$, respectively, even with arbitrarily small positive $E$.

There is also actual failure of renewal independence. Let $G_1,G_2$ be successive zero-gap counts starting from the actual $\tau=P_0$ in this subfamily. Since $K^D=0$, both gaps are proper. The event $G_1=0$ has probability $s$ and leaves $P_n$, so $G_2=0$ then has probability one. The event $G_1=n$ has probability $1-s$ and leaves $P_0$, so $G_2=0$ then has probability $s$. Thus

$$
\mathbb P(G_1=0,G_2=0)=s,\qquad
\mathbb P(G_1=0)\mathbb P(G_2=0)=s(2s-s^2)<s.
\tag{5.16}
$$

The gaps are not independent. Small Choi error therefore forces neither exact renewal nor the exact forbidden zero-gap support. Finally $\Phi$ is a nonzero nilpotent superoperator: $K^D=0$ and $K\ne0$. Such a superoperator is not diagonalizable. No automatic diagonalizability premise is available even in these examples. $\square$

**Proposition 5.2 (A merely positive late weight does not give uniformity in fixed dimension).** For every fixed $D\ge3$, there is a family of complete actual instruments with $\nu=1$, early maximum $\epsilon\to0$, and $w_{D-1}>0$ at each member, but $E=2(D-2)$. Positivity of the late weight without a quantitative lower bound is insufficient.

Proof. Use $e_0,\ldots,e_{D-1}$ with projections $P_j$. For $0<a<1$, define on every complex input

$$
\begin{aligned}
\Phi_a(X)&=X_{00}\big((1-a)P_0+aP_1\big),\\
\Psi(X)&=X_{11}P_0+\sum_{j=2}^{D-1}X_{jj}P_j,
\qquad \rho_0=P_1.
\end{aligned} \tag{5.17}
$$

The zero Kraus matrices are $\sqrt{1-a}|e_0\rangle\langle e_0|$ and $\sqrt a|e_1\rangle\langle e_0|$, whose effects sum to $P_0$. The tick matrices are $|e_0\rangle\langle e_1|$ and $|e_j\rangle\langle e_j|$ for $2\le j\le D-1$, with effect $F=I-P_0$. The total effect is $I$, proving complete positivity and completeness on all complex inputs.

The given initializer satisfies $\Psi(\rho_0)=P_0$, so actual $\nu=1$ and $\tau=P_0$. Since $\Phi_a$ reads only the $00$ entry, induction gives

$$
\Phi_a^k(\tau)=(1-a)^kP_0+a(1-a)^{k-1}P_1\quad(k\ge1).
\tag{5.18}
$$

Its trace is $(1-a)^{k-1}$, and all next-gap probabilities are

$$
w_0=0,\qquad w_k=a(1-a)^{k-1}\quad(k\ge1),
\qquad \sum_{k\ge0}w_k=1.
\tag{5.19}
$$

The last equality is the geometric series. Because $D-2\ge1$, the early maximum is exactly $a$, whereas $w_{D-1}=a(1-a)^{D-2}>0$.

Matrix-unit evaluation gives

$$
\begin{aligned}
J(\Psi)&=P_0\otimes P_1+\sum_{j=2}^{D-1}P_j\otimes P_j,\\
J(\Psi)-\tau\otimes F^{\mathsf T}
&=\sum_{j=2}^{D-1}(P_j-P_0)\otimes P_j.
\end{aligned} \tag{5.20}
$$

All these projections are real in the displayed basis. The input directions in the sum are orthogonal. Each output block $P_j-P_0$ has eigenvalues $1,-1$ and zeros, with trace norm two. Singular values of this orthogonal block sum combine by union, giving exactly $E=2(D-2)$. Let $a\downarrow0$ to get the claimed failure with fixed $D$ and actual rate.

At $a=0$ the formulas still define a complete instrument, but $\Phi_0^k(\tau)=P_0$ and every $w_k=0$: the same nonreset tick map has the same error, while no next tick occurs from $\tau$. For $D=2$ the sum in (5.20) is empty and $E=0$, in agreement with the late-free theorem. $\square$

**Proposition 5.3 (Growing dimension prevents a dimension-free modulus).** There are complete actual instruments with $D\to\infty$, $\nu=1$, $w_{D-1}\ge1/4$, and $\max_{0\le k\le D-2}w_k\to0$, but $E=2$ throughout. The effect trace is two throughout, so an increasing Choi trace is not responsible for this obstruction.

Proof. Let $N\ge4$ be an integer and $D=N+1$. The memory is the orthogonal sum of an $N$-dimensional clock space $C_N$ with basis $f_1,\ldots,f_N$, and a unit vector $z$. On the clock put

$$
\omega=\exp\left(\frac{2\pi i}{N+1}\right),\qquad
Uf_r=\omega^r f_r,\qquad
x=\frac1{\sqrt N}\sum_{r=1}^N f_r,\qquad
\eta=U^{-1}x.
\tag{5.21}
$$

Here $U$ is unitary and $x,\eta,z$ are unit vectors. For any unit vector in use write $P_y=|y\rangle\langle y|$. Define

$$
\begin{aligned}
K|_{C_N}&=U(I_{C_N}-P_\eta),\qquad Kz=0,\\
L_0&=|x\rangle\langle\eta|,\qquad L_z=|z\rangle\langle z|,\\
\Phi(X)&=KXK^\dagger,\qquad
\Psi(X)=L_0XL_0^\dagger+L_zXL_z^\dagger,
\qquad \rho_0=P_\eta.
\end{aligned} \tag{5.22}
$$

Their effects satisfy

$$
K^\dagger K=I_{C_N}-P_\eta,\qquad
F=L_0^\dagger L_0+L_z^\dagger L_z=P_\eta+P_z.
\tag{5.23}
$$

They sum to $I_H$, so this is a complete binary CP instrument on the full complex algebra. Moreover $\Psi(\rho_0)=P_x$, giving actual $\nu=1$ and $\tau=P_x$. The zero states from this density stay in the clock.

For all indices set

$$
a_k=\langle\eta,K^k x\rangle,\qquad
b_k=\langle\eta,U^k x\rangle,\qquad
c_\ell=\langle\eta,U^\ell\eta\rangle.
\tag{5.24}
$$

Then $\Phi^k(\tau)=|K^kx\rangle\langle K^kx|$ and $w_k=|a_k|^2$. The root-of-unity sum gives

$$
c_\ell=\frac1N\sum_{r=1}^N\omega^{r\ell}
=\begin{cases}
1,&(N+1)\text{ divides }\ell,\\
-1/N,&(N+1)\text{ does not divide }\ell,
\end{cases}
\qquad b_k=c_{k+1}.
\tag{5.25}
$$

If $\omega^\ell\ne1$, the sum from $r=0$ to $N$ equals $(1-(\omega^\ell)^{N+1})/(1-\omega^\ell)=0$; removing its first term leaves $-1$. This proves the nontrivial case exactly.

On $C_N$ one has $U-K=UP_\eta$. The difference-of-powers identity, without a commutation assumption, yields

$$
K^k=U^k-\sum_{j=0}^{k-1}U^{k-j}P_\eta K^j,
\qquad a_k=b_k-\sum_{j=0}^{k-1}c_{k-j}a_j.
\tag{5.26}
$$

The sum at $k=0$ is empty. These formulas determine the full amplitude sequence. For $0<k-j\le N$ each coefficient $c_{k-j}$ is $-1/N$, and $b_k=-1/N$ for $0\le k<N$, while $b_N=1$. With $R=1+1/N$, this gives

$$
a_k=-\frac1N R^k\quad(0\le k<N),\qquad
 a_N=1-\frac{R^N-1}{N}.
\tag{5.27}
$$

Indeed, if the first formula holds at all $j<k$, then $\sum_{j<k}a_j=-(R^k-1)$ by the geometric sum, so $a_k=-1/N+(1/N)\sum_{j<k}a_j=-R^k/N$. At $k=N$ use the same preceding sum and $b_N=1$.

The required elementary bound is

$$
R^N=\sum_{j=0}^N\binom NjN^{-j}
\le\sum_{j=0}^N\frac1{j!}<3.
\tag{5.28}
$$

Termwise, $\binom NjN^{-j}\le1/j!$. For $j\ge2$, the $j-1$ factors $2,\ldots,j$ are at least two, so $j!\ge2^{j-1}$ and $\sum_{j=2}^N1/j!\le\sum_{j=2}^N2^{-(j-1)}<1$. Adding the first two terms proves the strict bound. It follows that

$$
\begin{aligned}
\max_{0\le k\le D-2}w_k
&=\frac{R^{2(N-1)}}{N^2}<\frac9{N^2}=: \epsilon_N,\\
a_N&>1-\frac2N\ge\frac12,
\qquad w_{D-1}=w_N>\frac14.
\end{aligned} \tag{5.29}
$$

Thus early error tends to zero while the actual rate and a late lower bound remain fixed.

The next-gap laws are also proper. The clock restriction of $K$ is a contraction. If $Ky=\lambda y$ for $y\ne0$ and $|\lambda|=1$, then

$$
\|Ky\|^2=\|(I-P_\eta)y\|^2
=\|y\|^2-|\langle\eta,y\rangle|^2
\tag{5.30}
$$

forces $\langle\eta,y\rangle=0$. Hence $Ky=Uy$, so $y$ is an eigenvector of $U$. The eigenvalues $\omega,\ldots,\omega^N$ are distinct, with eigenvectors proportional to $f_r$, but $\langle\eta,f_r\rangle=\omega^r/\sqrt N\ne0$. This is a contradiction. All eigenvalues of the clock restriction of $K$ therefore have modulus strictly below one. The powers of each nonzero-eigenvalue Jordan block are bounded by a polynomial times a decaying geometric sequence; a zero-eigenvalue block is nilpotent. Thus $K^kx\to0$, and (4.2) gives

$$
\sum_{k\ge0}w_k=1-\lim_{k\to\infty}\|K^{k+1}x\|^2=1.
\tag{5.31}
$$

This decay is established for each example. No uniform spectral gap is assumed in this family or in Theorem 4.2.

The entire Choi matrix and its calibrated difference are

$$
\begin{aligned}
J(\Psi)&=P_x\otimes P_\eta^{\mathsf T}+P_z\otimes P_z^{\mathsf T},\\
J(\Psi)-\tau\otimes F^{\mathsf T}
&=(P_z-P_x)\otimes P_z^{\mathsf T}.
\end{aligned} \tag{5.32}
$$

Since $x\perp z$, the first factor has eigenvalues $1,-1$ and zeros; the second is a rank-one projection. The tensor trace-norm identity gives $E=2$. Both Choi matrices have trace $\operatorname{Tr}F=2$; even dividing each by two leaves trace-norm distance one. The convention remains the unnormalized one of (3.1). Thus no dimension-free modulus tending to zero with early error follows from these fixed positive rates, even with bounded Choi trace. $\square$

**Proposition 5.4 (An unrelated chosen seed cannot replace the actual post-tick state).** Exact zero early weights and a unit late weight, when computed from an unrelated chosen seed, need not make the tick map reset to that seed.

Proof. For $D\ge2$ put $n=D-1$ and use the shift $S$ in (4.28). Set

$$
\Phi(X)=SXS^\dagger,\qquad
\Psi(X)=P_nXP_n,\qquad F=P_n,\qquad \rho_0=P_n.
\tag{5.33}
$$

The total effect is $S^\dagger S+P_n=I$. Starting from the chosen seed $\chi=P_0$, the zero powers are $P_k$ for $0\le k\le n$, and zero afterwards. Thus its detector weights vanish through $n-1$ and equal one at $n$, forming a proper gap distribution from that seed.

The specified initializer instead gives $\Psi(\rho_0)=P_n$, so actual $\nu=1$, $\tau=P_n$, $w_0=1$ and $w_k=0$ for $k\ge1$, since $SP_n=0$. Every positive-probability tick from every input has normalized output $P_n$. Consequently

$$
\begin{aligned}
J(\Psi)-\chi\otimes F^{\mathsf T}
&=(P_n-P_0)\otimes P_n^{\mathsf T},&
\|J(\Psi)-\chi\otimes F^{\mathsf T}\|_1&=2,\\
J(\Psi)-\tau\otimes F^{\mathsf T}&=0.
\end{aligned} \tag{5.34}
$$

Orthogonality of $e_0,e_n$ gives the first norm. The second identity is exact reset to the actual density. The failed inference has substituted the calibration target; it has not met the actual small-early-weight hypothesis. $\square$

**Proposition 5.5 (Mixed exact reset separates purity from approximate dead time).** In every $D\ge2$, arbitrarily small positive early error and a late weight tending to one can coexist with exact global reset, a rank-one effect, and a mixed actual post-tick density of rank two. The tick Choi rank is two.

Proof. Put $n=D-1$, use the shift $S$ of (4.28), and choose $0<s<1$. Let

$$
\begin{aligned}
L_0&=\sqrt{1-s}\,|e_0\rangle\langle e_n|,
\qquad L_1=\sqrt s\,|e_n\rangle\langle e_n|,\\
\Phi(X)&=SXS^\dagger,
\qquad \Psi(X)=L_0XL_0^\dagger+L_1XL_1^\dagger,
\qquad \rho_0=P_n.
\end{aligned} \tag{5.35}
$$

The tick effect is $F=P_n$, with $S^\dagger S+F=I$, proving completeness on all complex inputs. The initializer gives actual $\nu=1$ and

$$
\tau=(1-s)P_0+sP_n,\qquad
\Psi(X)=\tau X_{nn}=\tau\operatorname{Tr}(FX)\quad\text{for every }X.
\tag{5.36}
$$

Hence $E=0$. Both eigenvalues $1-s,s$ on the support of $\tau$ are positive, so its rank is two, while $F$ has rank one. The Choi identity is

$$
J(\Psi)=\tau\otimes P_n^{\mathsf T}.
\tag{5.37}
$$

Its two positive eigenvalues are $1-s,s$, giving Choi rank two. Equivalently the displayed tick matrices are independent. Each individually has matrix rank one, unlike the rank-two single Kraus matrix and Choi-rank-one map in Theorem 5.1.

The zero powers and entire actual gap law are

$$
\begin{aligned}
\Phi^k(\tau)&=(1-s)P_k\quad(1\le k\le n),&
\Phi^{n+1}(\tau)&=0,\\
w_0&=s,&w_k&=0\quad(1\le k<n),\\
w_n&=1-s,&w_k&=0\quad(k>n).
\end{aligned} \tag{5.38}
$$

The law is proper and its early maximum is $s$, including in dimension two. Every tick resets to the same mixed density, yet no positive $s$ makes that density pure or its tick Choi rank one. Also $w_0=s>0$ removes the exact forbidden early support. Together with Theorem 5.1, this separates approximate map control from exact purity, exact ranks, exact support, exact reset and exact renewal independence. $\square$

**Definition 5.6 (Mathematical credit, proved scope and remaining boundaries).** The exact support and actual-output suppliers are O, Theorems 13.2–13.3, with the full correspondence in Sections 2.1–2.2. O, Section 14 gives their delayed-law application; O, Section 16 gives nonnegative polynomial closure, exact delay, divisibility, positive-delay rank tradeoffs and general polynomial renewal instruments. Their cited support-growth antecedents retain the conditions stated in Section 2.6. Theorem 3.3 supplies its quantitative basis-coefficient and entire-leakage proof. Theorem 4.2 supplies the entire Choi estimate and actual-output calibration. Choi representation, spectral and singular-value facts are classical tools, with the required conventions and proofs in Lemma 3.2.

O, Section 15 controls a scalar polynomial residual and finite stationary classical output windows of its own completed family. Its Newton, Gramian and renewal/coupling suppliers retain their original credit. That result is not a whole Choi-map bound and is not a replacement for (4.1). Conversely, small $E$ and (4.4) do not make the specified initializer stationary, or impose exact renewal independence or an exact support pattern. O's actual-history testing results in Sections 17–20 and its published joint-delay results in Section 21 have the separate scopes and parameter correspondences in Sections 2.4–2.5. They are existing results, not claims of additional quantitative mathematics here.

Theorem 5.1 establishes square-root sharpness at fixed dimension and nonvanishing rates, and the worst-case square-root order in $\epsilon/\nu$. The constants in $B_D$, the best dependence on $p$, and the best dependence on $D$ remain undetermined. Proposition 5.2 proves the need for a quantitative late lower bound for general uniformity in fixed $D\ge3$; dimension two is exempt. Proposition 5.3 gives a separate dimension obstruction with fixed positive rates and bounded effect trace. Conditional outputs require their own positive input-event denominator, as (4.24) and (5.15) show. No positive tolerance promotes norm control to the exact rank, purity, support or reset statements of saturation.

The metric throughout is the unnormalized output-first Choi trace norm (4.3), with the ordinary-input implications (4.23)–(4.24). There is no diamond-norm claim, empirical machine-learning transfer, finite-bit or physical implementation claim, or new original-monomial hidden-memory minimum. These are ordinary mathematical proofs about finite homogeneous complex CP instruments and actual conditional probabilities, without a kernel-verification or worldwide novelty claim. Quantitative optimization and the separate implementation and interpretation questions remain unresolved.

## 追加锚（本行以下为增补区）

## 6. Coherent compression and density observations

**Theorem 6.1 (Coherent compression and trace transfer).** Let $D\in\mathbb N$, including $D=0$, and equip $M_D(\mathbb C)$ with the operator norm on complex Euclidean space. The order $U\le V$ means that $V-U$ is positive semidefinite. Let $T:M_D(\mathbb C)\to M_D(\mathbb C)$ be any complex-linear completely positive map satisfying $T(I)\le I$. Let $P,X,\sigma\in M_D(\mathbb C)$ satisfy

$$
P^\dagger=P,\qquad P^2=P,\qquad X\le P,
\qquad \sigma\ge0,\qquad \operatorname{Tr}\sigma=1.
$$

Thus $P$ is an actual orthogonal projection; no positivity assumption is imposed on $X$. Define

$$
Q=I-P,\qquad
\alpha=\sqrt{\|QT(P)Q\|_\infty}.
\tag{6.1}
$$

Then, for every $n\in\mathbb N$, including $n=0$, both inequalities hold:

$$
\begin{aligned}
T^n(X)&\le P+2n\alpha I,\\
\operatorname{Re}\operatorname{Tr}\bigl[\sigma T^n(X)\bigr]
&\le \operatorname{Re}\operatorname{Tr}(\sigma P)+2n\alpha.
\end{aligned}
\tag{6.2}
$$

Here $T^0$ is the identity map. The projection determining the corner defect in (6.1) is the same projection in both comparisons in (6.2).

Proof. First take a positive input $0\le Y\le P$ and put $Z=T(Y)$. Positivity, monotonicity and subunitality give

$$
0\le Z\le T(P),\qquad Z\le T(I)\le I,
\qquad 0\le PZP\le P.
\tag{6.3}
$$

Let $S=Z^{1/2}$ be the positive square root, so $S^\dagger=S$ and $S^2=Z$. The $C^*$-norm identities and the positive-contraction bound give

$$
\|S\|_\infty^2=\|Z\|_\infty\le1.
\tag{6.4}
$$

Conjugating $Z\le T(P)$ by the self-adjoint projection $Q$ gives $0\le QZQ\le QT(P)Q$. Monotonicity of the norm on positive matrices therefore yields

$$
\|QS\|_\infty^2
=\|(QS)(QS)^\dagger\|_\infty
=\|QZQ\|_\infty
\le\|QT(P)Q\|_\infty=\alpha^2.
\tag{6.5}
$$

Since $\alpha\ge0$, it follows that $\|QS\|_\infty\le\alpha$. Factoring $QZ=(QS)S$ and using (6.4) gives $\|QZ\|_\infty\le\alpha$. Taking adjoints gives $\|ZQ\|_\infty\le\alpha$. Now $\|P\|_\infty\le1$ and

$$
Z-PZP=QZ+PZQ,
\qquad
\|Z-PZP\|_\infty\le2\alpha.
\tag{6.6}
$$

This identity includes the off-diagonal blocks, as well as the complementary diagonal block. The matrix $Z-PZP$ is self-adjoint, so its norm bound implies

$$
T(Y)=Z\le PZP+2\alpha I\le P+2\alpha I.
\tag{6.7}
$$

In particular, applying this argument to $Y=P$ gives $T(P)\le P+2\alpha I$.

For the orbit comparison, the case $n=0$ is exactly $X\le P$. Suppose $T^n(X)\le P+c_n I$, where $c_n=2n\alpha\ge0$. Order preservation and linearity of $T$, followed by subunitality, give

$$
\begin{aligned}
T^{n+1}(X)
&\le T(P)+c_nT(I)\\
&\le P+2\alpha I+c_nI
=P+2(n+1)\alpha I.
\end{aligned}
\tag{6.8}
$$

This induction uses no lower bound on $X$. It proves the first inequality in (6.2).

For $U\le V$, the two matrices $\sigma$ and $V-U$ are positive semidefinite. Positivity of their trace pairing gives

$$
0\le\operatorname{Re}\operatorname{Tr}\bigl[\sigma(V-U)\bigr],
\qquad
\operatorname{Re}\operatorname{Tr}(\sigma U)
\le\operatorname{Re}\operatorname{Tr}(\sigma V).
\tag{6.9}
$$

Apply this to the first inequality in (6.2). Linearity of trace and $\operatorname{Tr}\sigma=1$ give

$$
\operatorname{Re}\operatorname{Tr}\bigl[\sigma(P+2n\alpha I)\bigr]
=\operatorname{Re}\operatorname{Tr}(\sigma P)+2n\alpha,
$$

which is the second inequality. $\square$

In the notation of Theorem 3.3, its spectral cutoff part $B_+$ satisfies $0\le B_+\le P$. Substitution of $X=B_+$ in (6.2) supplies the scalar comparison used in (3.18):

$$
\operatorname{Re}\operatorname{Tr}\bigl[\sigma T^n(B_+)\bigr]
\le\operatorname{Tr}(\sigma P)+2n\alpha.
\tag{6.10}
$$

The trace on the right is real by positivity of the trace pairing. To obtain the coefficient in (3.7), the frame projection must additionally connect the residual estimates (3.10) to the actual corner estimate

$$
\sqrt{\|(I-P)T(P)(I-P)\|_\infty}
\le D^{3/2}\delta=\frac{p}{8n}.
\tag{6.11}
$$

The short-word expansions must supply the coefficient bound $C=(D/\delta)^{D-r}$ and the observation estimate $\operatorname{Tr}(\sigma P)\le DC^2\epsilon/t$ of (3.13). The cutoff must supply $B=B_++B_-$ with $0\le B_+\le P$ and $0\le B_-\le tI$, using $t=p\lambda_r(B)/4$ in the positive-eigenvalue branch. These are separate frame-to-corner, coefficient and cutoff requirements: (6.2) alone gives neither the eigenvalue estimate of Theorem 3.3 nor its rank-horizon and reset-stability consequences. The norm estimate (6.6) is used only for $Z=T(Y)$ with $0\le Y\le P$; the conclusion for the general input $X\le P$ is the order and trace comparison (6.2).

The coherent-compression and density-observation synthesis is the repository-derived result `coherent_compression_trace_transfer`. Its positive square root, $C^*$-norm identities, positive-order norm monotonicity, self-adjoint norm-to-order bound and positive-semidefinite trace pairing are classical finite-dimensional $C^*$-algebra and matrix tools. The operator-norm and CP conventions agree with Lemma 3.2.

## 追加锚（本行以下为增补区）
