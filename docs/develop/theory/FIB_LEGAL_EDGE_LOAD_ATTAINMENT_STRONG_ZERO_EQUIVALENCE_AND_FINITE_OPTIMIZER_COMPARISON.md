# FIB harmonic-edge load: attainment, strong-zero equivalence and finite-optimizer comparison

Actual attainment together with explicit one-sided square-root erasure summability forces the original-law loss cocycle to vanish on every legal finite modification, on one saturated conull set. Combined with the guarded-replacement converse, this gives a conditional equivalence with attainment and makes the existing finite-hidden rank budget necessary for an attainer satisfying the summability premise. The proof compares the actual law directly with each finite optimizer. Its spatial sums are test functions, and its concentration step is a proved uniform-integrability estimate.

The original question remains whether any finite exact-real hidden producer attains the growth constant, or every finite hidden dimension has a strict gap. Neither root summability for every hypothetical attainer nor the required rank-discrepancy growth is proved here. All statements below are ordinary handwritten mathematics relative to the explicitly cited mathematical premises.

## 1. Original objective, entire parameter domain and same-law definitions

**Definition 1.1 (Complete open-path objective).** For $n\ge1$, let

$$
B_n=\{w\in\{0,1\}^n:w_iw_{i+1}=0\ (1\le i<n)\},\qquad
\mathsf X=\{x\in\{0,1\}^{\mathbb Z}:x_ix_{i+1}=0\ (i\in\mathbb Z)\}.
$$

The graph $\Gamma_n$ has every vertex of $B_n$ and every legal Hamming-one edge. Endpoint insertions use $w_0=w_{n+1}=0$; the endpoints are not joined. On the entire probability simplex define

$$
\begin{aligned}
h(s,t)&=\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}\\
\Phi_n(\mu)&=\sum_{\{u,v\}\in E(\Gamma_n)}h(\mu_u,\mu_v),\qquad
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu),\qquad
c_\star=\lim_{n\to\infty}\kappa_n/n.
\end{aligned}
\tag{1.1}
$$

Zero masses retain their vertices and edges. The all-zero word, endpoint ones when legal, forced singleton fibers and all internal seams belong to this same objective.

**Definition 1.2 (Whole original finite-hidden domain).** For each integer $N\ge1$, retain exactly [Universal, Definition 4.1][U]'s parameter set

$$
\Theta_N=\left\{(\lambda,M_0,M_1):
\begin{array}{l}
\lambda\ge0,\quad\lambda\mathbf1=1,\quad M_0,M_1\ge0,\\
A=M_0+M_1,\quad A\mathbf1=\mathbf1,\quad\lambda A=\lambda,\\
\lambda M_1^2\mathbf1=0
\end{array}\right\}.
\tag{1.2}
$$

Here $\lambda$ is a row and $M_0,M_1$ are $N\times N$ exact-real matrices. Structural zeros, zero stationary hidden masses, reducibility, periodicity and nonminimal presentations are permitted. The last equation is scalar stationary no11 legality; entrywise $M_1^2=0$ is not imposed. No hidden-state trimming is used.

For a fixed $\theta\in\Theta_N$, [Universal, Proposition 4.2][U] supplies the single actual stationary joint law

$$
\begin{aligned}
&J_\theta(H_a=h_a,\ldots,H_{b+1}=h_{b+1},X_a=x_a,\ldots,X_b=x_b)\\
&\hspace{25mm}=\lambda_{h_a}\prod_{i=a}^bM_{x_i}(h_i,h_{i+1}),\qquad
P_\theta([w]_a)=\lambda M_w\mathbf1.
\end{aligned}
\tag{1.3}
$$

The product $M_w=M_{w_1}\cdots M_{w_n}$ is ordered, with empty product $I$, and $[w]_a$ specifies the consecutive coordinates beginning at $a$. The visible law $P_\theta$ is supported on $\mathsf X$. Every seam $uv$ uses $\lambda M_uM_v\mathbf1$, without factorizing its mass. Coordinates count original emitted bits.

**Definition 1.3 (Actual predictors, risk and erasures).** Initially let $P$ be any stationary Borel probability on $\mathsf X$; in the finite-hidden conclusions it is the actual $P_\theta$ above. Set $(Tx)_i=x_{i+1}$ and

$$
\mathcal E_i=\sigma(X_j:j\ne i),\qquad
F_i=\{X_{i-1}=X_{i+1}=0\}.
$$

Choose a $[0,1]$ Borel exterior version of $q_0=\mathbb E_P[X_0\mid\mathcal E_0]$, set $q_i=q_0\circ T^i$, and define

$$
\ell_i(x)=(x_i-q_i(x))^2.
\tag{1.4}
$$

For integer $r\ge1$, let

$$
q_{r,i}=\mathbb E_P[X_i\mid\sigma(X_{i-r},\ldots,X_{i-1},X_{i+1},\ldots,X_{i+r})],
\qquad D_r(P)=\mathbb E_P(X_0-q_{r,0})^2.
$$

The supplied actual-risk formula [Universal, (1.5)][U] is

$$
D_r(P)\downarrow d(P)=\mathbb E_P\ell_0
=\lim_{n\to\infty}\Phi_n(P_n)/n\le c_\star,
\tag{1.5}
$$

where $P_n$ is the actual $[1,n]$ marginal. Null finite fibers have arbitrary conditional versions and zero weighted contribution. Retaining a neighbor one forces the center posterior to zero; erasing that neighbor supplies no such conclusion.

Use precisely the one-sided fields of [Root-tail, Definition 1.3][R]. For $j\ge0$, put

$$
\begin{aligned}
\mathcal L_j&=\sigma(X_{-j},\ldots,X_{-1},X_1,X_2,\ldots),\\
\mathcal R_j&=\sigma(\ldots,X_{-2},X_{-1},X_1,\ldots,X_j),\\
p_j^L&=\mathbb E_P[X_0\mid\mathcal L_j],\qquad
p_j^R=\mathbb E_P[X_0\mid\mathcal R_j],\\
e_L(j)&=\mathbb E_P(q_0-p_j^L)^2,\qquad
e_R(j)=\mathbb E_P(q_0-p_j^R)^2,\\
A_P&=\sum_{j\ge0}\bigl(\sqrt{e_L(j)}+\sqrt{e_R(j)}\bigr).
\end{aligned}
\tag{1.6}
$$

Each field retains the entire opposite half-line, including at $j=0$. Both zero-offset defects remain. Every expectation, norm, projection and response in the direct proof is under this same $P$. In particular, $q_i$ and $\ell_i$ evaluated at modified configurations are still the original $P$ functions.

**Definition 1.4 (Band, cocycle and strong zero).** The band property is

$$
\mathsf B(P):\qquad q_i=0\text{ on }F_i^c,\qquad
\tfrac14\le q_i\le\tfrac12\text{ on }F_i,
\quad P\text{-almost surely for every }i\in\mathbb Z.
\tag{1.7}
$$

For a nonempty finite integer interval $C=[a,b]$, write $L=b-a+1$,

$$
\mathcal H_C=\sigma(X_j:j\notin C),\quad Y=X_{C^c},\quad
\mu_C=\operatorname{law}_P(Y),\quad p_C(w;y)=P(X_C=w\mid Y=y),\quad
Z_Cx=0^Lx_{C^c}.
\tag{1.8}
$$

A word $w\in B_L$ is compatible with $y$ exactly when $y_{a-1}w_1=w_Ly_{b+1}=0$. Denote its completion by $wy$. On a suitable conull domain the actual loss cocycle is

$$
\Delta_P(x,z)=\sum_{i\in\mathbb Z}(\ell_i(x)-\ell_i(z)),
\tag{1.9}
$$

for legal configurations differing at finitely many sites. Write $\mathsf Z_\Delta(P)$ if there is one shift-invariant Borel $P$-conull set $\Omega_0$, saturated under every legal finite modification, on which every such series converges absolutely and equals zero. Saturation means that whenever $x\in\Omega_0$ and $z\in\mathsf X$ differs from $x$ finitely, then $z\in\Omega_0$.

**Theorem 1.5 (Direct conditional bridge, with exact quantifiers).** For every stationary legal law $P$,

$$
d(P)=c_\star\quad\text{and}\quad A_P<\infty
\quad\Longrightarrow\quad\mathsf Z_\Delta(P).
\tag{1.10}
$$

Consequently, on the entire original finite-hidden domain,

$$
\forall N\ge1\ \forall\theta\in\Theta_N:\quad
\bigl[d(P_\theta)=c_\star\ \text{and}\ A_{P_\theta}<\infty\bigr]
\Longrightarrow\mathsf Z_\Delta(P_\theta).
\tag{1.11}
$$

The band used in the proof follows from attainment. The root sum is a separate additional premise; it is not inferred from the band, finite hidden dimension or attainment. Constants may depend on this law and on a fixed block and test. No parameter-uniform rate is asserted. The proof occupies §§3–8; §2 states the reused premises.

## 2. Reused finite optimization and legal-surgery premises

**Convention 2.1 (Finite optimizer and attained band).** [Universal, Convention 1.3 and Lemma 2.1][U] supplies, for each $n$, a positive optimizer $\pi_n$ on all of $B_n$. Its single-site predictor $a_{n,i}$ is

$$
a_{n,i}(u_{-i})=\frac{\pi_n(v)}{\pi_n(u)+\pi_n(v)}
\quad\text{on a legal insertion edge }u\to v,
\tag{2.1}
$$

and is zero on a forced singleton. If $p_{\nu,n,i}$ is the analogous predictor for any $\nu\in\mathcal P(B_n)$, the supplied exact identity is

$$
\kappa_n-\Phi_n(\nu)
=\sum_{i=1}^n\mathbb E_\nu(p_{\nu,n,i}-a_{n,i})^2.
\tag{2.2}
$$

Zero-total fibers have zero weight. The identity covers the whole simplex, all endpoint edges and $n=1$. The same source supplies

$$
\tfrac13\pi_n(u)\le\pi_n(v)\le\pi_n(u),\qquad
nc_\star\le\kappa_n\le(n+1)c_\star.
\tag{2.3}
$$

These optimizers and their identity retain their original ownership. They are chosen separately for each $n$; no consistency of their marginals is assumed.

[Universal, Theorem 3.1][U] supplies $d(P)=c_\star\Rightarrow\mathsf B(P)$ and, for every legal word $w\in B_n$ and every location $a$,

$$
P([w]_a)\ge2^{-(n+2)}3^{-k(w)}>0,
\qquad k(w)=\sum_iw_i.
\tag{2.4}
$$

Thus full visible support is a derived attained-law fact. It is not an imposed restriction on $\Theta_N$.

**Convention 2.2 (Absolute cocycle and nonsingular replacements).** Under $\mathsf B(P)$ and $A_P<\infty$, [Exterior, Theorem 3.1][E] supplies the cocycle (1.9), with its general stationary-law scope stated explicitly in [Guarded, Lemma 2.2][G]. For every finite interval $C$, almost every exterior has

$$
\begin{aligned}
p_C(0^L;y)&\ge2^{-L},\\
3^{-k(w)}p_C(0^L;y)&\le p_C(w;y)\le p_C(0^L;y)
&&\text{for each compatible }w.
\end{aligned}
\tag{2.5}
$$

Incompatible words have mass zero. Zero replacement satisfies

$$
(Z_C)_*P\le2^LP,
\tag{2.6}
$$

and every fixed total legal replacement $R_{C,w}$ is nonsingular: it replaces $C$ by $w$ on compatible exteriors and is the identity on incompatible ones. Here nonsingularity means that the inverse image of every $P$-null set is $P$-null.

There is a shift-invariant Borel conull set $\Omega$, saturated under all finite legal modifications, on which (1.9) converges absolutely and is antisymmetric and additive. The supplied integrable majorant is

$$
V_C(x)=\sum_{i\in\mathbb Z}|\ell_i(x)-\ell_i(Z_Cx)|,
\qquad
\mathbb E_PV_C\le L+2(1+2^{L/2})A_P<\infty.
\tag{2.7}
$$

It includes the zero-offset erasure terms at both seams. Any two fixed collections of original-law posterior versions agree on a common saturated conull domain. This is not a null set uniform over all conceivable version choices.

Set $D_C(x)=\Delta_P(x,Z_Cx)$ on $\Omega$, extending it by zero on its null complement, and choose an exterior-measurable version of its conditional mean. The centered score notation of [Second-order, Convention 2.1 and Theorem 3.1][S] is

$$
m_C=\mathbb E_P[D_C\mid\mathcal H_C],\qquad a_C=D_C-m_C.
\tag{2.8}
$$

The localization in §8 uses only the integrability in (2.7). The stronger $L^2$ estimate, centered-score interpretation and square-contrast framework of [Second-order, Theorem 3.1][S] keep their source attribution; no second-moment estimate for $D_C$ is needed for the direct bridge.

## 3. A pointwise optimizer score and the attainment discrepancy budget

**Lemma 3.1 (Exact finite score under an arbitrary actual law).** For every $n\ge1$ and every $w\in B_n$,

$$
\sum_{i=1}^n(w_i-a_{n,i}(w_{-i}))^2=\kappa_n.
\tag{3.1}
$$

For the fixed stationary $P$, evaluate $a_{n,i}$ at $X_{[1,n]\setminus\{i\}}$ and put

$$
v_{n,i}=a_{n,i}-q_i,\qquad \Xi_n=\sum_{i=1}^nv_{n,i}^2.
\tag{3.2}
$$

Then, pointwise with the chosen versions,

$$
\sum_{i=1}^n\ell_i-\kappa_n
=2\sum_{i=1}^n(X_i-q_i)v_{n,i}-\Xi_n,
\tag{3.3}
$$

and

$$
0\le\Xi_n\le n,\qquad \mathbb E_P\Xi_n=\kappa_n-nd(P).
\tag{3.4}
$$

In particular, actual attainment gives the uniform budget

$$
\mathbb E_P\Xi_n=\kappa_n-nc_\star\le c_\star.
\tag{3.5}
$$

**Proof.** Apply the supplied identity (2.2) to the point mass $\delta_w$. Its edge objective is zero. On each fiber seen by this measure its posterior is $w_i$, including a forced zero singleton. Thus (2.2) becomes (3.1). This is a direct use of the original finite optimizer identity, with no new optimization assertion.

For each site, write $X_i-a_{n,i}=(X_i-q_i)-v_{n,i}$. Expanding its square, subtracting from $\ell_i$, and summing (3.1) gives (3.3). Both $a_{n,i}$ and $q_i$ are $\mathcal E_i$-measurable, while

$$
\mathbb E_P[X_i-q_i\mid\mathcal E_i]=0.
$$

Consequently $\mathbb E_P[(X_i-q_i)v_{n,i}]=0$. Stationarity and (1.5) make the expectation of the loss sum $nd(P)$, proving (3.4). The pointwise bound uses $|v_{n,i}|\le1$. Under attainment, (2.3) gives (3.5). $\square$

At an open endpoint a neighbor outside $[1,n]$ can force $q_i=0$ although the optimizer's fiber remains free. That discrepancy is included in $\Xi_n$. Every expectation in (3.3)–(3.5) is under $P$, not under an optimizer law or a limiting law of optimizers.

## 4. One-sided erasures control complete conditional block distributions

**Definition 4.1 (Boundary-conditioned discrepancy).** For $L\ge1$ and $\alpha,\beta\in\{0,1\}$ let

$$
K_L^{\alpha,\beta}=\{w\in B_L:\alpha w_1=w_L\beta=0\}.
$$

Give this set every legal Hamming-one edge. For a probability $p$ and a positive probability $r$ on this set, the conditional Brier discrepancy of [Guarded, Definition 3.1][G] is

$$
\begin{aligned}
\mathcal D_K(p\Vert r)
&=\sum_{i=1}^L\mathbb E_p(p_i(W_{-i})-r_i(W_{-i}))^2\\
&=\sum_{u\to v\text{ in }K}(p_u+p_v)
\left(\frac{p_v}{p_u+p_v}-\frac{r_v}{r_u+r_v}\right)^2.
\end{aligned}
\tag{4.1}
$$

A zero-total $p$ edge contributes zero; forced singleton posteriors are zero. A probability is band-compatible when $p_u/3\le p_v\le p_u$ on every insertion edge.

**Lemma 4.2 (Recalled finite coercivity, with its ratio proof).** The band floor and inverse estimate of [Guarded, Lemmas 3.3 and 8.1][G] give, for band-compatible $p,r$ on the same $K=K_L^{\alpha,\beta}$,

$$
p_w,r_w\ge6^{-L}\quad(w\in K),\qquad
\|p-r\|_1^2\le H_L\mathcal D_K(p\Vert r),\qquad H_L=2L6^{4L}.
\tag{4.2}
$$

**Proof of the recalled estimate.** Deleting ones reaches $0^L$ and shows every mass is at most the zero-word mass, which is therefore at least $|K|^{-1}$. Reinserting ones gives $p_w\ge3^{-k(w)}|K|^{-1}\ge6^{-L}$, and likewise for $r$.

Set $t_w=r_w/p_w$ and $\alpha_L=6^{-L}$. Each edge term in (4.1) equals

$$
\frac{(p_up_v)^2(t_u-t_v)^2}{(p_u+p_v)(r_u+r_v)^2}
\ge\alpha_L^4(t_u-t_v)^2,
\tag{4.3}
$$

since the pair sums are at most one. Any two vertices are connected by deleting and inserting ones through zero in at most $2L$ steps; removing repetitions gives a simple path. Cauchy–Schwarz on a path between the largest and smallest ratios gives

$$
(\max_wt_w-\min_wt_w)^2\le2L\alpha_L^{-4}\mathcal D_K(p\Vert r).
$$

Because $\sum_wp_wt_w=1$, the number one lies between these extreme ratios, so
$\|p-r\|_1=\sum_wp_w|1-t_w|\le\max t-\min t$. This proves (4.2). If $K$ is a singleton, its two probabilities coincide and the estimate is immediate. $\square$

**Proposition 4.3 (Actual one-sided conditional-block estimate).** Assume $\mathsf B(P)$ and fix $C=[a,b]$. With $p_C(\cdot;Y)$ from (1.8), define

$$
\begin{aligned}
\mathcal V_t^R&=\sigma(X_j:j<a\text{ or }b<j\le t),&
s_t^R&=P(X_C=\cdot\mid\mathcal V_t^R),&&t\ge b+1,\\
\mathcal V_t^L&=\sigma(X_j:t\le j<a\text{ or }j>b),&
s_t^L&=P(X_C=\cdot\mid\mathcal V_t^L),&&t\le a-1.
\end{aligned}
\tag{4.4}
$$

Both adjacent bits $X_{a-1},X_{b+1}$ are retained in either field. Then

$$
\begin{aligned}
\mathbb E_P\|p_C-s_t^R\|_1^2&\le H_L\sum_{i=a}^b e_R(t-i),&&t\ge b+1,\\
\mathbb E_P\|p_C-s_t^L\|_1^2&\le H_L\sum_{i=a}^b e_L(i-t),&&t\le a-1.
\end{aligned}
\tag{4.5}
$$

**Proof.** On a full exterior fiber, condition the band on the other block coordinates. For each legal insertion $u\to v$, its free posterior lies in $[1/4,1/2]$, which is equivalent to
$p_C(u;Y)/3\le p_C(v;Y)\le p_C(u;Y)$. More formally, integrate the band against arbitrary exterior events and the specified other block coordinates; conditional integration gives these mass inequalities almost surely. They hold for all the finitely many edges simultaneously. Thus $p_C$ is band-compatible on

$$
K=K_L^{X_{a-1},X_{b+1}}.
$$

The graph $K$ is measurable in each field in (4.4), since both boundary bits are retained. Moreover $s_t^R=\mathbb E_P[p_C\mid\mathcal V_t^R]$ coordinate by coordinate. The same inequalities pass through this conditional expectation, and incompatible words keep mass zero. Therefore $s_t^R$ and $p_C$ are band-compatible on the same actual $K$, with the floor (4.2); the left-side argument is identical.

Apply (4.2) in the order $p=p_C$, $r=s_t^R$. For a site $i\in C$, the single-site posterior of $p_C$, evaluated at the actual other block bits, is $q_i$. The corresponding posterior of $s_t^R$ conditions on

$$
\mathcal V_t^R\vee\sigma(X_j:j\in C,\ j\ne i)
=\sigma(X_j:j\le t,\ j\ne i).
\tag{4.6}
$$

To verify the identification, multiply the candidate finite conditional ratio by the conditional probability of the other block bits; its defining numerator is exactly the conditional probability with $X_i=1$. Testing against the retained field and summing the finitely many other-bit choices gives the conditional-expectation identity. Positive compatible masses justify division on every actual compatible fiber; null exterior records are immaterial.

The field in (4.6) is the translated original right-erasure field with offset $t-i$: it keeps the entire left half-line and $t-i$ future bits. Disintegrating the $p_C$-weighted discrepancy in (4.1) and using stationarity gives exactly

$$
\mathbb E_P\mathcal D_K(p_C\Vert s_t^R)
=\sum_{i=a}^b\mathbb E_P\left(q_i-\mathbb E_P[X_i\mid\sigma(X_j:j\le t,j\ne i)]\right)^2
=\sum_{i=a}^b e_R(t-i).
\tag{4.7}
$$

This proves the first inequality in (4.5). For the other direction the joined field is

$$
\mathcal V_t^L\vee\sigma(X_j:j\in C,j\ne i)
=\sigma(X_j:j\ge t,j\ne i),
\tag{4.8}
$$

the translated left-erasure field with offset $i-t$. The same disintegration gives the second inequality. Singleton completion graphs contribute zero. Countably many intervals, cuts and sites permit simultaneous conditional versions. No two-sided finite-window rate, conditional independence or hidden filtering stability is used. $\square$

## 5. Exterior-centered cylinder tests and two summable norm series

**Proposition 5.1 (Projection and full-residual summability).** Assume $\mathsf B(P)$ and $A_P<\infty$. Fix $C=[a,b]$ and any bounded cylinder function $h$, whose finite coordinate support need not lie in $C$. Let

$$
g=h-\mathbb E_P[h\mid\mathcal H_C],\qquad
\mathcal F_k=\sigma(X_j:j\le k),\qquad
f_k=\mathbb E_P[g\mid\mathcal F_k]-\mathbb E_P[g\mid\mathcal F_{k-1}].
\tag{5.1}
$$

Then

$$
g=\sum_{k\ge a}f_k\text{ in }L^2(P),\qquad
A(g):=\sum_{k\ge a}\|f_k\|_2<\infty.
\tag{5.2}
$$

For the original full-posterior residual, set

$$
c_i(g)=\mathbb E_P[(X_i-q_i)g\mid\mathcal E_i].
$$

It also satisfies

$$
W(g):=\sum_{i\in\mathbb Z}\|c_i(g)\|_2<\infty.
\tag{5.3}
$$

**Proof.** Let $H=\|h\|_\infty$ and choose a finite interval containing $C$ and every coordinate used by $h$. For $t$ beyond its right end and with $t\ge b+1$, put

$$
g_t^R=h-\mathbb E_P[h\mid\mathcal V_t^R].
$$

It is $\mathcal F_t$-measurable. All exterior coordinates used by $h$ are retained in $\mathcal V_t^R$. Thus for each block word $w$, the value of $h$ at that completion is a bounded $\mathcal V_t^R$-measurable function $h_w$, and

$$
\mathbb E_P[h\mid\mathcal H_C]=\sum_wh_wp_C(w;Y),\qquad
\mathbb E_P[h\mid\mathcal V_t^R]=\sum_wh_ws_t^R(w).
$$

Set $h_w=0$ on incompatible retained exteriors. Proposition 4.3 gives

$$
\|g-g_t^R\|_2\le H\bigl(\mathbb E_P\|p_C-s_t^R\|_1^2\bigr)^{1/2}
\le H\left(H_L\sum_{i=a}^be_R(t-i)\right)^{1/2}=:b_R(t).
\tag{5.4}
$$

For $t$ before the left end of the chosen interval and with $t\le a-1$, the corresponding function

$$
g_t^L=h-\mathbb E_P[h\mid\mathcal V_t^L]
$$

is measurable in $\sigma(X_j:j\ge t)$ and satisfies

$$
\|g-g_t^L\|_2\le H\left(H_L\sum_{i=a}^be_L(i-t)\right)^{1/2}=:b_L(t).
\tag{5.5}
$$

These two bounds are summable over their respective distant cuts. Indeed
$\sqrt{\sum_i u_i}\le\sum_i\sqrt{u_i}$ for nonnegative numbers, and a fixed finite $C$ turns either sum over cuts into at most $L$ shifted subseries of the corresponding root sum in (1.6).

Since $\mathcal F_{a-1}\subseteq\mathcal H_C$ and $\mathbb E_P[g\mid\mathcal H_C]=0$, the initial projection onto $\mathcal F_{a-1}$ is zero. The increasing fields $\mathcal F_k$ generate the full configuration field. Their $L^2$ projections of $g$ therefore converge to $g$: one can first approximate $g$ in $L^2$ by finite-coordinate simple functions, each measurable in some $\mathcal F_k$, and use projection contraction. Telescoping the projections proves the decomposition in (5.2).

For sufficiently large $k$, $g_{k-1}^R$ is $\mathcal F_{k-1}$-measurable. The operator $\Pi_{\mathcal F_k}-\Pi_{\mathcal F_{k-1}}$ is an orthogonal projection, of norm at most one, and annihilates this function. Hence

$$
\|f_k\|_2\le\|g-g_{k-1}^R\|_2\le b_R(k-1).
\tag{5.6}
$$

The omitted initial terms are finite in number, proving $A(g)<\infty$.

For a sufficiently far-right site $i$, $g_{i-1}^R$ is $\mathcal E_i$-measurable. Using the conditional mean-zero residual, conditional contraction and $|X_i-q_i|\le1$ gives

$$
\begin{aligned}
\|c_i(g)\|_2
&=\left\|\mathbb E_P[(X_i-q_i)(g-g_{i-1}^R)\mid\mathcal E_i]\right\|_2\\
&\le\|g-g_{i-1}^R\|_2\le b_R(i-1).
\end{aligned}
\tag{5.7}
$$

At sufficiently far-left sites, $g_{i+1}^L$ is $\mathcal E_i$-measurable and gives the bound $b_L(i+1)$. Every remaining site costs at most $\|g\|_\infty$, and there are only finitely many. This proves (5.3). The finitely many seam sites have not been assigned zero defects. Neither mixing nor ergodicity enters the argument. $\square$

## 6. Uniform integrability of spatial tests and pairing with a bounded budget

**Lemma 6.1 (Spatial uniform integrability).** Let $g$ be a bounded function with the decomposition (5.2) in the stationary filtration $\mathcal F_k$. Define

$$
G_n=\sum_{j=1}^ng\circ T^j.
\tag{6.1}
$$

Then $\|G_n/\sqrt n\|_2\le A(g)$ for every $n$, and the family
$\{G_n^2/n:n\ge1\}$ is uniformly integrable. If, on this same probability space,

$$
0\le Z_n\le n,\qquad \sup_n\mathbb E_PZ_n\le K<\infty,
\tag{6.2}
$$

then

$$
\frac1n\mathbb E_P[|G_n|Z_n]\longrightarrow0.
\tag{6.3}
$$

No independence between $G_n$ and $Z_n$ is required.

**Proof.** For each fixed $k$, stationarity makes $f_k\circ T^j$ a martingale difference at time $k+j$: it is $\mathcal F_{k+j}$-measurable and has zero conditional mean given $\mathcal F_{k+j-1}$. Distinct such times are orthogonal. Therefore

$$
\left\|\sum_{j=1}^nf_k\circ T^j\right\|_2=\sqrt n\,\|f_k\|_2.
$$

For an integer $m\ge a$ define

$$
G_n^{(m)}=\sum_{k=a}^m\sum_{j=1}^nf_k\circ T^j,
\qquad \eta_m=\sum_{k>m}\|f_k\|_2.
$$

Minkowski's inequality and (5.2) give

$$
\left\|\frac{G_n}{\sqrt n}\right\|_2\le A(g),\qquad
\sup_n\left\|\frac{G_n-G_n^{(m)}}{\sqrt n}\right\|_2\le\eta_m\longrightarrow0.
\tag{6.4}
$$

For fixed $n,m$, group the finite sum by $t=k+j$:

$$
d_t=\sum_{\substack{a\le k\le m\\1\le t-k\le n}}f_k\circ T^{t-k},
\qquad G_n^{(m)}=\sum_{t=a+1}^{m+n}d_t.
$$

Each $d_t$ is a martingale difference for $\mathcal F_t$. There are
$J=n+m-a$ terms and

$$
|d_t|\le M_m:=2\|g\|_\infty(m-a+1),
\tag{6.5}
$$

because each conditional expectation of $g$ is bounded by $\|g\|_\infty$.

We prove the fourth-moment estimate needed for this finite truncation. For any $J$ successive martingale differences bounded by $M$, let $S_j$ be their partial sums. Orthogonality gives $\mathbb E_PS_{j-1}^2\le(j-1)M^2$. In the expansion

$$
(S_{j-1}+d_j)^4-S_{j-1}^4
=4S_{j-1}^3d_j+6S_{j-1}^2d_j^2+4S_{j-1}d_j^3+d_j^4,
$$

the first expectation is zero. The other three are bounded above by
$6M^2\mathbb E_PS_{j-1}^2$, $4M^3\mathbb E_P|S_{j-1}|$ and $M^4$. Cauchy–Schwarz consequently yields

$$
\mathbb E_PS_J^4
\le M^4\sum_{j=1}^J\bigl(6(j-1)+4\sqrt{j-1}+1\bigr)
\le8M^4J^2.
\tag{6.6}
$$

For the last inequality use $\sqrt{j-1}\le j-1$ for integral $j\ge1$; the resulting sum is $5J^2-4J\le8J^2$. Applying (6.6) to (6.5) shows, for each fixed $m$,

$$
C_m:=\sup_{n\ge1}\mathbb E_P\left(\frac{G_n^{(m)}}{\sqrt n}\right)^4
\le8M_m^4(m-a+1)^2<\infty.
\tag{6.7}
$$

Write $Y_n=G_n/\sqrt n$, $Y_n^{(m)}=G_n^{(m)}/\sqrt n$ and
$E_{n,R}=\{|Y_n|>R\}$. By (6.4), Markov's inequality gives
$P(E_{n,R})\le A(g)^2/R^2$. Thus

$$
\begin{aligned}
\mathbb E_P[Y_n^2\mathbf1_{E_{n,R}}]
&\le2\mathbb E_P(Y_n-Y_n^{(m)})^2
 +2\mathbb E_P[(Y_n^{(m)})^2\mathbf1_{E_{n,R}}]\\
&\le2\eta_m^2+2C_m^{1/2}A(g)/R.
\end{aligned}
\tag{6.8}
$$

Take the supremum over $n$, then let $R\to\infty$ with $m$ fixed, and finally $m\to\infty$. This proves uniform integrability of $Y_n^2$. The bound on its expectation alone would not prove this conclusion.

Finally fix $\varepsilon>0$. Split according to $|G_n|\le\varepsilon n$ and its complement, and use both bounds in (6.2):

$$
\begin{aligned}
\frac1n\mathbb E_P[|G_n|Z_n]
&\le\varepsilon K+\mathbb E_P[|G_n|\mathbf1_{\{|G_n|>\varepsilon n\}}]\\
&\le\varepsilon K+\frac1\varepsilon
\mathbb E_P\left[\frac{G_n^2}{n}
\mathbf1_{\{|G_n|/\sqrt n>\varepsilon\sqrt n\}}\right].
\end{aligned}
\tag{6.9}
$$

For fixed $\varepsilon$ the last term tends to zero by the uniform integrability just proved. First let $n\to\infty$ and then $\varepsilon\downarrow0$, proving (6.3). $\square$

## 7. Attainment forces exact zero response for all the centered tests

**Theorem 7.1 (Exterior-centered response).** Assume $d(P)=c_\star$ and $A_P<\infty$. For every finite interval $C$ and every bounded cylinder $h$, let
$g=h-\mathbb E_P[h\mid\mathcal H_C]$. Then

$$
\sum_{i\in\mathbb Z}|\mathbb E_P[g\ell_i]|<\infty,
\qquad S_P(g):=\sum_{i\in\mathbb Z}\mathbb E_P[g\ell_i]=0.
\tag{7.1}
$$

In particular the tests need not be intrinsic-null functions of the block word alone.

**Proof.** Attainment supplies the band, so Conventions 2.2 and Proposition 5.1 apply. For every individual $i$, the function $\ell_i\circ Z_C$ is $\mathcal H_C$-measurable. Exterior centering therefore gives

$$
\mathbb E_P[g\ell_i]
=\mathbb E_P[g(\ell_i-\ell_i\circ Z_C)].
$$

Subtracting this term before any infinite summation, (2.7) proves

$$
\sum_i|\mathbb E_P[g\ell_i]|\le\|g\|_\infty\mathbb E_PV_C<\infty.
\tag{7.2}
$$

Let $r_k=\mathbb E_P[g\ell_k]$. This scalar sequence is absolutely summable.

Form the spatial test $G_n$ of (6.1). Multiply the finite identity (3.3) by $G_n$ and integrate. Its mean is zero because $\mathbb E_Pg=0$, so the constant $\kappa_n$ drops out. Conditioning each residual on $\mathcal E_i$ gives

$$
\mathbb E_P\left[G_n\sum_{i=1}^n\ell_i\right]
=2\sum_{i=1}^n\mathbb E_P[v_{n,i}c_i(G_n)]-\mathbb E_P[G_n\Xi_n].
\tag{7.3}
$$

Translation of conditional expectation under stationary $P$ and the fixed translated posterior versions yields

$$
c_i(g\circ T^j)=c_{i-j}(g)\circ T^j
\quad\text{as }L^2(P)\text{ classes}.
$$

This follows by testing against a translated $\mathcal E_i$ event and changing variables by the invertible measure-preserving shift. Linearity and (5.3) imply

$$
\|c_i(G_n)\|_2
\le\sum_{j=1}^n\|c_{i-j}(g)\|_2\le W(g).
\tag{7.4}
$$

Cauchy–Schwarz over the sites and the probability space, followed by (3.5), gives

$$
\left|2\sum_{i=1}^n\mathbb E_P[v_{n,i}c_i(G_n)]\right|
\le2(\mathbb E_P\Xi_n)^{1/2}
\left(\sum_{i=1}^n\|c_i(G_n)\|_2^2\right)^{1/2}
\le2W(g)\sqrt{nc_\star}.
\tag{7.5}
$$

After division by $n$ this tends to zero. Equations (3.4)–(3.5) supply exactly (6.2) with $Z_n=\Xi_n$ and $K=c_\star$. Hence Lemma 6.1 also gives

$$
\frac1n|\mathbb E_P[G_n\Xi_n]|
\le\frac1n\mathbb E_P[|G_n|\Xi_n]\longrightarrow0.
\tag{7.6}
$$

On the other hand, stationarity and a finite rearrangement show

$$
\frac1n\mathbb E_P\left[G_n\sum_{i=1}^n\ell_i\right]
=\frac1n\sum_{j=1}^n\sum_{i=1}^nr_{i-j}
=\sum_{|k|<n}\left(1-\frac{|k|}{n}\right)r_k.
\tag{7.7}
$$

Absolute summability in (7.2) permits dominated convergence of this scalar series. Its limit is $S_P(g)$. Equations (7.3), (7.5) and (7.6) make that limit zero, proving (7.1). $\square$

The discrepancy paid in (7.6) belongs to the actual law through the pointwise optimizer score. No posterior limit of $\pi_n$ is taken, and $G_n$ is not a density or a modification kernel. The argument does not assign the fixed-$P$ loss to the Bayes risk of another law.

## 8. Cylinder separation, the exterior constant and one saturated domain

**Proof of Theorem 1.5.** Fix $C$ and use $D_C,m_C,a_C$ from (2.8). They are integrable, and $m_C$ is a Borel function of the exterior coordinates alone. For any bounded cylinder $h$ set $g=h-\mathbb E_P[h\mid\mathcal H_C]$. The subtraction and absolute majorant in (7.2) permit summation under the integral and give

$$
0=S_P(g)=\mathbb E_P[gD_C]
=\mathbb E_P[h(D_C-m_C)]=\mathbb E_P[ha_C].
\tag{8.1}
$$

For the penultimate equality, condition the term
$\mathbb E_P[(\mathbb E_P[h\mid\mathcal H_C])D_C]$ on $\mathcal H_C$ and use $m_C$'s measurability. Bounded $h$ and integrable $D_C$ justify these operations.

The finite signed measure $\nu_C(B)=\int_Ba_C\,dP$ vanishes by (8.1) on every finite-coordinate cylinder indicator. These cylinders, together with the empty set, form a countable intersection-stable generating family containing the whole space. To spell out the uniqueness step, $\nu_C(\mathsf X)=0$ and the family of Borel sets on which $\nu_C$ vanishes is a Dynkin class: it is closed under complements and countable disjoint unions by finite signed-measure additivity. The generating-family theorem therefore makes $\nu_C$ zero on the full Borel field. Apply this to the positive and negative sets of $a_C$ to conclude

$$
a_C=0\quad P\text{-almost surely}.
\tag{8.2}
$$

This still allows the exterior constant $m_C$, which must be removed. Domination (2.6) transports (8.2) to the zero replacement: $a_C(Z_CX)=0$ almost surely. On the saturated cocycle domain,

$$
D_C(Z_CX)=\Delta_P(Z_CX,Z_CZ_CX)=0,
\qquad m_C(Z_CX)=m_C(X).
$$

The second identity is pointwise for the exterior version, and the first uses idempotence of $Z_C$. Hence
$0=a_C(Z_CX)=-m_C(X)$ almost surely. Together with (8.2) this proves

$$
D_C=0\quad P\text{-almost surely for every finite interval }C.
\tag{8.3}
$$

Choose a Borel conull $B\subseteq\Omega$ where (8.3) holds simultaneously for every finite integer interval. This is a countable intersection. Let $\mathcal G$ be the countable monoid generated by the identity, $T,T^{-1}$ and all fixed total legal interval replacements $R_{C,w}$ of Convention 2.2. Each member is nonsingular, by stationarity for shifts and by (2.5)–(2.6)'s supplied surgery mechanism for replacements. Define

$$
\Omega_0=\bigcap_{G\in\mathcal G}G^{-1}B.
\tag{8.4}
$$

It is Borel and conull. If $x\in\Omega_0$ and $H\in\mathcal G$, then for every $G\in\mathcal G$ the composition $G\circ H$ is in $\mathcal G$, so $Hx\in\Omega_0$. Both shifts are included, making $T\Omega_0=\Omega_0$. If $z$ is any legal finite modification of $x$, choose a containing interval $C$; then $z=R_{C,z_C}x$, proving saturation for every such modification, including configuration-dependent choices.

For any legal finitely differing $x,z\in\Omega_0$, choose a containing interval $C$. Their zero replacements coincide. Absolute convergence and additivity inherited from $\Omega$ give

$$
\Delta_P(x,z)
=\Delta_P(x,Z_Cx)-\Delta_P(z,Z_Cz)
=D_C(x)-D_C(z)=0.
\tag{8.5}
$$

This proves the full pathwise statement, not merely an averaged balance or a statement on intrinsic word directions. For any two fixed original posterior-version collections, intersect with their supplied common saturated agreement set before (8.4); the conclusion then agrees for both. The proof used no hidden matrices, so it proves (1.10), and substitution of each actual $P_\theta$ proves (1.11). $\square$

All limiting steps have a fixed-law order. First fix $P,C,h$; use the actual one-sided root sums to obtain (5.2)–(5.3). In uniform integrability, fix the martingale truncation, send its tail threshold to infinity, and then remove the truncation. For (6.9), fix $\varepsilon$, send the spatial length to infinity, and then send $\varepsilon$ to zero. Equation (7.7) uses one absolutely summable scalar series. Signed-measure separation follows only after every cylinder test is proved; countable saturation is last. There is no simultaneous density, volume and conditioning limit.

## 9. Conditional equivalence and the inherited finite-hidden consumer

**Corollary 9.1 (Same-law conditional equivalence).** For every stationary legal $P$ satisfying $\mathsf B(P)$ and $A_P<\infty$,

$$
d(P)=c_\star\quad\Longleftrightarrow\quad\mathsf Z_\Delta(P).
\tag{9.1}
$$

**Proof.** The forward implication is Theorem 1.5. The reverse implication is [Guarded, Theorem 5.1][G]. Its exact consumption is as follows. Independently draw $W\sim\pi_n$ and $X\sim P$, and replace the block $[0,n+1]$ by $0W0$, obtaining $Z$. Guarded's Theorem 4.2 supplies an integrable difference of the same original losses and the identity

$$
\mathbb E\Delta_P(X,Z)
=(n+2)d(P)-\kappa_n-\mathcal B_n-G_n^{\rm guard}-E_n^{\rm ext}-O_n^{\rm ext},
\tag{9.2}
$$

Here $C=[0,n+1]$, $Q=\operatorname{law}(Z)$, and $\mathcal B_n$ is the mean conditional discrepancy (9.5). The other penalties, in the notation of the supplied identity, are

$$
\begin{aligned}
b_i^C&=\mathbb E_P[X_i\mid\sigma(X_j:j\notin C,\ j\ne i)],&&i\notin C,\\
G_n^{\rm guard}&=\mathbb E_Q(q_0^2+q_{n+1}^2),\\
E_n^{\rm ext}&=\sum_{i\notin C}\mathbb E_P(q_i-b_i^C)^2,\qquad
O_n^{\rm ext}=\sum_{i\notin C}\mathbb E_Q(q_i-b_i^C)^2.
\end{aligned}
$$

All four penalties are finite and nonnegative by that theorem, with every predictor still from $P$. Strong zero makes the left side of (9.2) zero, since the finite replacement remains inside its saturated conull set. Thus $(n+2)d(P)\ge\kappa_n$ for every $n$. Letting $n\to\infty$ and using (1.5), (2.3) proves equality. Only scalar inequalities are passed to the limit. The auxiliary finite replacement in this reused converse is not asserted stationary and its scored predictors remain those of $P$. $\square$

**Definition 9.2 (The existing rank discrepancy).** For a probability $r$ on $B_n$, extend it by zero to every binary word and let its cut at $1\le k<n$ be

$$
\mathsf F_k(r)(s,t)=r(st),\qquad
s\in\{0,1\}^k,\quad t\in\{0,1\}^{n-k}.
$$

Nonnegative rank is the least number of nonnegative rank-one matrix summands. Let $\mathscr F_{N,n}^{0,0}$ be the band-compatible probabilities on $B_n=K_n^{0,0}$ whose every internal cut has nonnegative rank at most $N$. With the positive optimizer $\pi_n$, use [Guarded, Definition 6.3][G]'s unchanged quantity

$$
\mathcal R_{N,n}=\min_{r\in\mathscr F_{N,n}^{0,0}}
\mathcal D_{B_n}(\pi_n\Vert r),\qquad \min\varnothing=+\infty.
\tag{9.3}
$$

For $n=1$ there are no internal cuts. All illegal seams remain zero entries of the flattenings. The minimizing family is the existing compact relaxation, not a family asserted to share a stationary realization or common matrices across lengths.

**Corollary 9.3 (Inherited necessary budget for an attainer with a root sum).** For every finite $N$ and every $\theta\in\Theta_N$, if its actual law satisfies $d(P_\theta)=c_\star$ and $A_{P_\theta}<\infty$, then, for all $n\ge1$,

$$
\mathcal R_{N,n}
\le(n+2)c_\star-\kappa_n-\tfrac1{24}
\le2c_\star-\tfrac1{24}
\le2(3-2\sqrt2)-\tfrac1{24}.
\tag{9.4}
$$

**Proof and consumer attribution.** The band follows from [Universal, Theorem 3.1][U], and Theorem 1.5 supplies strong zero. Thus [Guarded, Corollary 6.4][G] applies with exactly its original hypotheses. To exhibit the quantities it compares, take $C=[0,n+1]$, $Y=X_{C^c}$ and define the actual guarded conditional

$$
g_C(y)=P(X_0=X_{n+1}=0\mid Y=y),\qquad
r_n^y(w)=\frac{p_C(0w0;y)}{g_C(y)},\qquad
\mathcal B_n=\mathbb E_{\mu_C}\mathcal D_{B_n}(\pi_n\Vert r_n^Y).
\tag{9.5}
$$

The band supplies $g_C\ge2^{-(n+2)}$. Guarded's Theorem 6.2, using the original $N$-term nonnegative matrix factorization and the full-exterior conditional limit, gives $r_n^y\in\mathscr F_{N,n}^{0,0}$ almost surely. Therefore $\mathcal R_{N,n}\le\mathcal B_n$. Its Lemma 5.2 and Corollary 5.3 give

$$
G_n^{\rm guard}\ge\tfrac1{24},\qquad
\mathcal B_n+G_n^{\rm guard}+E_n^{\rm ext}+O_n^{\rm ext}
=(n+2)c_\star-\kappa_n.
$$

Dropping the other nonnegative penalties yields the first inequality in (9.4). The remaining inequalities use $\kappa_n\ge nc_\star$ and the supplied ceiling $c_\star\le3-2\sqrt2$ [Guarded, Definition 1.1][G]. This reuses the budget; it supplies no lower bound growing with $n$. $\square$

A proved violation of (9.4) for a specified $N,n$ would exclude an attainer of dimension $N$ satisfying the root-sum premise. The disjoint-block and determinant consumers of [Guarded, §§7–9][G] still require their actual conditional-discrepancy lower bounds under one and the same finite optimizer. A single nonzero minor, positivity, or finite rank alone does not supply that growth. Conditionals of $\pi_n$ cannot be replaced by standalone smaller optimizers or by a stationary bulk limit without a further theorem.

**Corollary 9.4 (The attained-law square contrasts vanish).** Under Theorem 1.5's hypotheses, for every $C$ and almost every exterior $y$,

$$
d_C(w;y):=\Delta_P(wy,0^Ly)=0
\quad\text{for every compatible }w.
\tag{9.6}
$$

Consequently the square contrast and normalized cocycle tilt of [Second-order, Theorems 3.2 and 6.1][S] satisfy

$$
\begin{aligned}
R_{C,f}(y)&:=\sum_wp_C(w;y)f(w)d_C(w;y)^2=0,\\
\pi_C^t(w;y)&:=\frac{p_C(w;y)e^{td_C(w;y)}}{\sum_vp_C(v;y)e^{td_C(v;y)}}
=p_C(w;y)\quad(t\in\mathbb R).
\end{aligned}
\tag{9.7}
$$

In the square-contrast notation $f$ may in particular be any intrinsic-null block direction, meaning $\mathbb E_P[f(X_C)\mid\mathcal H_C]=0$.

**Proof.** Finite disintegration of the conull $\Omega_0$ gives
$\sum_wp_C(w;y)\mathbf1_{\{wy\notin\Omega_0\}}=0$ for almost every $y$. Every compatible mass is positive by (2.5), so every compatible completion, including zero, lies in $\Omega_0$. Equation (8.5) proves (9.6) simultaneously over those finitely many words. Substitution proves both formulas in (9.7); the denominator of the tilt is one. Countably many intervals allow a simultaneous choice of exterior conull sets. $\square$

This conclusion uses actual attainment. It does not prove square cancellation or strong zero from only $\mathsf B(P)$, $A_P<\infty$ and the weaker first-order property $\mathsf Z(P)$, which requires zero response only for intrinsic-null block-word directions. The arbitrary exterior-centered cylinder tests in Theorem 7.1 are the additional separation supplied by the finite-optimizer comparison.

## 10. Mathematical attribution, literature boundary and remaining original gaps

The direct argument combines the actual-law square budget (3.5), the one-sided conditional-block estimate (4.5), the two summable test series (5.2)–(5.3), the proved uniform integrability in §6 and the exact response comparison in §7. Cylinder separation and nonsingular zero replacement then give the full pathwise conclusion. This is a synthesis relative to the following canonical results; the finite optimization identity, legal cocycle, converse and rank consumer retain their supplier ownership.

| Canonical source | Exact use and boundary |
| --- | --- |
| [Universal posterior defect and finite-hidden separation][U], Convention 1.3, Lemma 2.1, Theorem 3.1, Definition 4.1, Proposition 4.2 and Theorem 6.2 | Original finite optimizers and square identity, growth and actual-risk formulas, attainment-implied band and support, whole $\Theta_N$ and actual joint law, and the fixed-dimension separation equivalence. No consistent optimizer marginals are supplied or required. |
| [Exterior localization and actual loss-cocycle balance][E], Theorem 3.1 | Compatible-fiber positivity, nonsingular replacements, the integrable absolute cocycle and version/saturation mechanism. These make the fixed original losses legitimate after zero replacement. |
| [Second-order loss localization and local tilt averaging obstruction][S], Convention 2.1 and Theorems 3.1, 3.2, 6.1, 7.1 | Centered-score notation and integrability, square-contrast and tilt interpretations. The single fixed local-tilt averaging result remains unchanged; the direct proof constructs no stationary continuation. |
| [Guarded replacement, attainment and conditional-rank obstruction][G], Lemma 2.2, Lemmas 3.3 and 8.1, Theorems 4.2 and 5.1, Corollary 6.4 | General stationary-law scope of surgery, finite band floor and coercivity, the guarded converse, and the inherited rank budget. The present implication supplies its strong-zero premise under attainment plus the root sum. |
| [One-sided erasure summability and output-filter boundaries][R], Definition 1.3 | Only the actual-law one-sided fields, defects and root-sum definition. No sufficient-filter, rectangle-word, flag-block or example statement is a premise of this volume. |

Conditional expectation as an $L^2$ projection, martingale orthogonality, Cauchy–Schwarz, Minkowski, dominated convergence and uniqueness of finite signed measures are classical tools. The particular fourth-moment and pairing estimates needed here are proved in §6. No mixing or ergodic theorem is needed for the direct bridge.

The bounded literature comparison is inherited through [Exterior][E], [Second-order][S] and [Guarded][G]. Dawid–Lauritzen–Parry's *Proper Local Scoring Rules on Discrete Sample Spaces*, §4.2, describes conditional Brier scoring and squared conditional discrepancy. Its everywhere-positive full-product strict-propriety argument does not by itself cover hard no11; the constrained-graph coercivity used here is the explicitly credited finite ratio argument. Chandgotia–Meyerovitch's finite-modification cocycle language does not supply finite-boundary dependence or an identity with conditional log-probability ratios for the loss cocycle. Neither a Gibbs specification nor a finite visible Markov order is inferred. The forward–backward matrix comparison discussed by Balle–Panangaden–Precup provides no stationary positive realization merely from a rank bound. These comparisons import no additional theorem into the proof and establish no priority claim or absence of another solution.

**Open Problem 10.1 (Unchanged original finite-attainment alternative).** On the entire parameter domain (1.2), set

$$
C_N=\sup_{\theta\in\Theta_N}d(P_\theta),\qquad
U_{N,r}=\max_{\theta\in\Theta_N}D_r(P_\theta),\qquad r\ge1.
\tag{10.1}
$$

[Universal, Theorem 6.2][U] supplies attainment of $C_N$ and
$C_N=\inf_{r\ge1}U_{N,r}\le c_\star$. The original alternatives are still

$$
\exists N\ge1\ \exists\theta\in\Theta_N:\ d(P_\theta)=c_\star,
\qquad\text{or}\qquad
\forall N\ge1:\ C_N<c_\star.
\tag{10.2}
$$

The second alternative is equivalently

$$
\forall N\ge1\ \exists r,m\ge1:\quad
U_{N,r}<\frac{\kappa_m}{m+1}.
\tag{10.3}
$$

Zero-mass states remain allowed, so a presentation with fewer than $N$ states can be padded by zero stationary masses as in the supplied theorem. The parameter domain is never replaced by a positive, irreducible, aperiodic or finite-visible-memory subclass.

Theorem 1.5 settles the conditional implication under actual attainment and $A_P<\infty$. The following obligations remain distinct and unresolved here:

- Root summability for every law in the original finite-hidden domain, for every band-qualified law, or even for every hypothetical finite-hidden attainer. The convergence of individual erasure defects to zero gives no root-sum conclusion.
- A rank-discrepancy or common-transfer lower bound strong enough to violate the inherited budget for every intended finite dimension. No actual rank growth or determinant magnitude is supplied.
- Strong zero or square cancellation under only the band, root sum and intrinsic-null first-order balance, without actual attainment.
- An actual finite-hidden attainer or a strict finite separation pair for every $N$. The conditional equivalence alone constructs neither.

No sparse stationary continuation, jointly realized positive-density modification process, common family of optimizer marginals or finite-hidden competitor is constructed. Such a route would need its own existence and risk arguments. The direct bridge does not require it. The cocycle remains a measurable object on a saturated conull finite-modification relation; no continuous extension to every legal configuration, locality, Gibbs property, uniform parameter-family bound or empirical learning consequence follows from this proof.

[U]: FIB_LEGAL_EDGE_LOAD_UNIVERSAL_POSTERIOR_DEFECT_AND_FINITE_HIDDEN_SEPARATION.md
[E]: FIB_LEGAL_EDGE_LOAD_EXTERIOR_LOCALIZATION_AND_ACTUAL_LOSS_COCYCLE_BALANCE.md
[S]: FIB_LEGAL_EDGE_LOAD_SECOND_ORDER_LOSS_LOCALIZATION_AND_LOCAL_TILT_AVERAGING_OBSTRUCTION.md
[G]: FIB_LEGAL_EDGE_LOAD_GUARDED_REPLACEMENT_ATTAINMENT_AND_CONDITIONAL_RANK_OBSTRUCTION.md
[R]: FIB_LEGAL_EDGE_LOAD_ONE_SIDED_ERASURE_SUMMABILITY_AND_OUTPUT_FILTER_BOUNDARIES.md

## 追加锚（本行以下为增补区）
