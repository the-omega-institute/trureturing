# FIB harmonic-edge load: fixed-state tail nonuniformity and an erasure-risk jump

This volume gives ordinary handwritten probability proofs. One stationary four-state family on the original emitted-bit clock has finite erasure-defect tails at every parameter, but unbounded tail suprema at every fixed radius. Its finite marginals are continuous while its actual full-exterior Brier risk is zero off the fair parameter and $1/8$ at that parameter. These are boundaries for the existing conditional-stability and compact-separation interfaces; the arbitrary-finite attainment problem remains open.

**Reference status.** This is ordinary mathematical reference input, not Lean-kernel evidence. Numbered claims and the terminal append anchor follow the theory-volume convention. The existing supplier results retain their stated hypotheses and ownership; no scientific conclusion below is a claim of source admission.

## 1. Original domain, actual law and conditioning fields

**Convention 1.1 (Complete legal domain and supplied risk interface).** Retain

$$
\mathcal X=\{x\in\{0,1\}^{\mathbb Z}:x_ix_{i+1}=0\ (i\in\mathbb Z)\},\qquad
B_n=\{w\in\{0,1\}^n:w_iw_{i+1}=0\ (1\le i<n)\}.
$$

The graph $\Gamma_n$ contains all $B_n$ vertices and all legal Hamming-one edges. Endpoint insertion uses $w_0=w_{n+1}=0$, with no first-to-last constraint. With

$$
h(s,t)=\begin{cases}st/(s+t)&s+t>0,\\0&s=t=0,\end{cases}\qquad
\Phi_n(\mu)=\sum_{\{w,z\}\in E(\Gamma_n)}h(\mu_w,\mu_z),\qquad
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu),
$$

use the supplied constant $c_\star=\lim_n\kappa_n/n$. All-zero words, endpoint ones, every legal seam, forced singletons and zero-total fibers remain in this domain. Assigning a word zero probability does not delete its vertex or edges.

Write $X_i$ for the coordinate variable, $[w]_a$ for a word cylinder beginning at $a$, and $P_n$ for the actual marginal on $[1,n]$. For a normalized two-sided stationary legal law $P$, set

$$
\mathcal E_i=\sigma(X_j:j\ne i)\ (i\in\mathbb Z),\quad
\mathcal F_r=\sigma(X_{-r},\ldots,X_{-1},X_1,\ldots,X_r),\quad
q_P=\mathbb E_P[X_0\mid\mathcal E_0],\quad q_{r,P}=\mathbb E_P[X_0\mid\mathcal F_r],
$$

$$
D_r(P)=\mathbb E_P(X_0-q_{r,P})^2,\qquad
d(P)=\lim_n\Phi_n(P_n)/n=\mathbb E_P(X_0-q_P)^2
=\inf_{r\ge0}D_r(P)\le c_\star.
\tag{1.1}
$$

This is [Universal, §1][U]'s supplied harmonic/Brier identity. “Full-exterior erasure risk” means predicting one erased site from all other coordinates. It is not ordinary one-sided predictive risk or erasure of the entire record. Radius zero has the trivial field. An observed neighbor equal to one forces the center and its posterior to zero; zero-total fibers have zero weighted contribution, with no division required.

**Convention 1.2 (Complete edge-emitting producer domain).** For every finite $N\ge1$, retain [Universal, Definition 4.1 and Proposition 4.2][U]'s

$$
\Theta_N=\{(\lambda,M_0,M_1):\lambda\ge0,\ \lambda\mathbf1=1,\ M_0,M_1\ge0,
\ A=M_0+M_1,\ A\mathbf1=\mathbf1,\ \lambda A=\lambda,\ \lambda M_1^2\mathbf1=0\}.
\tag{1.2}
$$

Here $\lambda$ is a row, the matrices are $N\times N$ with exact real entries, and $M_w=M_{w_1}\cdots M_{w_n}$; the empty product is the identity. Structural zeros, zero stationary masses, reducibility, periodicity and noncontractive boundaries are allowed. Entrywise $M_1^2=0$ is not required of every untrimmed presentation.

Every quantity for $\theta\in\Theta_N$ belongs to the same stationary joint law and its visible marginal:

$$
J_\theta(H_a=h_a,\ldots,H_{b+1}=h_{b+1},X_a=x_a,\ldots,X_b=x_b)
=\lambda_{h_a}\prod_{i=a}^bM_{x_i}(h_i,h_{i+1}),\qquad
P_\theta([w]_a)=\lambda M_w\mathbf1.
\tag{1.3}
$$

The supplied construction has left and right consistency by $\lambda A=\lambda$ and $A\mathbf1=\mathbf1$. Seams use the joint ordered product $\lambda M_uM_v\mathbf1$, not independently joined marginals. [Renewal, Lemma 8.2][R] permits deletion of zero-mass hidden states while preserving the same visible law; that reduction introduces no positivity or minimality assumption here.

On a positive radius-$r$ exterior atom $u,v$, the actual finite predictor is [Conditional Response, §4][C]'s

$$
q_{r,P_\theta}=\frac{\lambda M_uM_1M_v\mathbf1}{\lambda M_uAM_v\mathbf1}.
$$

Zero denominators have zero weighted contribution and may be assigned predictor zero. An observed neighbor one makes the numerator zero. Empty $u,v$ handle $r=0$.

**Definition 1.3 (Exact one-sided erasure defects).** For $r,R\in\mathbb N_0$, use precisely [Conditional Response, §2][C]'s fields

$$
\mathcal G^L_r=\sigma(X_{-r},\ldots,X_{-1},X_j:j\ge1),\qquad
\mathcal G^R_r=\sigma(X_j:j\le-1,X_1,\ldots,X_r),
$$

$$
p^L_{r,P}=\mathbb E_P[X_0\mid\mathcal G^L_r],\quad
p^R_{r,P}=\mathbb E_P[X_0\mid\mathcal G^R_r],\quad
e_{L,P}(r)=\|q_P-p^L_{r,P}\|_{L^2(P)}^2,\quad
e_{R,P}(r)=\|q_P-p^R_{r,P}\|_{L^2(P)}^2,
$$

$$
\tau_P(R)=\sum_{r=R}^\infty(e_{L,P}(r)+e_{R,P}(r))\in[0,+\infty].
\tag{1.4}
$$

The entire opposite half-line remains in each field, including at $r=0$. All posteriors are $[0,1]$ versions interpreted under their own law. No general summability hypothesis is included in this definition.

## 2. A lawful four-state family on the original clock

**Proposition 2.1 (Stationary realization, including endpoints).** For $0\le p\le1$, order the states $(a_0,a_1,b_0,b_1)$ and put $\pi_0=1-p$, $\pi_1=p$,

$$
\lambda_p=\tfrac12(1-p,p,1-p,p),\qquad
M_0(p)=\begin{pmatrix}
0&0&1-p&0\\0&0&0&p\\1&0&0&0\\0&1&0&0
\end{pmatrix},\qquad
M_1(p)=\begin{pmatrix}
0&0&0&p\\0&0&1-p&0\\0&0&0&0\\0&0&0&0
\end{pmatrix}.
\tag{2.1}
$$

Then $\theta_p=(\lambda_p,M_0(p),M_1(p))\in\Theta_4$. Write $J_p=J_{\theta_p}$ and $P_p=P_{\theta_p}$. For $0<p<1$ the hidden chain is irreducible of period two and all four stationary masses are positive. At $p=0,1$ its visible law is $\delta_{0^{\mathbb Z}}$. Every finite visible marginal is continuous in $p$, and $P_p=P_{1-p}$.

Proof. From $a_s$, choose $b_t$ with probability $\pi_t$ and emit $s\mathbin\oplus t$; from $b_t$, move to $a_t$ deterministically and emit zero. Every row of $A=M_0+M_1$ sums to one. Incoming mass at $b_t$ is $\sum_s(\pi_s/2)\pi_t=\pi_t/2$, and copying gives incoming mass $\pi_t/2$ at $a_t$. Thus $\lambda_pA=\lambda_p$. Every one-edge enters a $b$-state, whose $M_1$ row is zero, so $M_1^2=0$. Interior irreducibility follows from $a_s\to b_t\to a_t$ for either $t$; all transitions alternate the two state classes and a two-step return is possible, giving period two.

For an explicit two-sided realization, let $\varphi\in\{0,1\}$ be uniform and independent of iid Bernoulli$(p)$ spins $(S_k)_{k\in\mathbb Z}$. On the original integer coordinates define

$$
\begin{aligned}
H_{2k+\varphi}&=a_{S_k},& H_{2k+\varphi+1}&=b_{S_{k+1}},\\
X_{2k+\varphi}&=Y_k:=S_k\mathbin\oplus S_{k+1},& X_{2k+\varphi+1}&=0.
\end{aligned}
\tag{2.2}
$$

These hidden paths have exactly the initial masses and transition/emission factors (1.3). In particular the phase mixture is one stationary integer-clock law, with no time rescaling. All emitted ones occupy its active parity; zeros separate consecutive active sites, including across every interval seam. At either endpoint all spins are constant and every emission is zero. Complementing all spins exchanges $p$ and $1-p$ without changing the visible record. Finally each cylinder $\lambda_pM_w(p)\mathbf1$ is a polynomial in $p$. Marginalizing these cylinders proves finite-marginal continuity, including zero masses and endpoint laws. $\square$

**Lemma 2.2 (Observable phase on complete half-lines).** Under every $0<p<1$, either complete visible half-line determines the active parity almost surely. The same is true of the exterior of any fixed finite block.

Proof. Disjoint spin pairs give independent active trials for $Y_k=1$, each with probability $2p(1-p)>0$. The probability of no successes after any fixed starting trial is zero, since the probability over $n$ trials is $(1-2p(1-p))^n\to0$. A countable union over starting trials shows infinitely many ones on both half-lines. All their indices have the active parity. Removing finitely many sites leaves this observation intact. This proof includes $p=1/2$ and makes no claim of phase observability at $p=0,1$. $\square$

## 3. Exact biased defects and the fair exception

**Lemma 3.1 (Complement-pair variance).** In the spin representation let

$$
v_m(p)=\mathbb E_p\operatorname{Var}(S_0\mid Y_{-m},\ldots,Y_{-1}),\qquad m\ge0,
\quad \beta(p)=2\sqrt{p(1-p)}.
$$

Then $v_0(p)=p(1-p)$, each $v_m$ is continuous on $[0,1]$ and symmetric about $1/2$, and

$$
0\le v_m(p)\le\tfrac14\beta(p)^{m+1},\qquad
v_m(1/2)=1/4,\qquad v_m(0)=v_m(1)=0.
\tag{3.1}
$$

Proof. A record of $m$ consecutive XORs determines its $m+1$ spins up to simultaneous complementation. An unordered complementary pair $(s,\bar s)$ with masses $a,b$ is exactly one parity atom. Its endpoint spin takes the two opposite values, so its weighted conditional variance is $ab/(a+b)=h(a,b)$, with value zero when $a+b=0$. Thus $v_m$ is the sum of $h(a,b)$ over the $2^m$ pairs. This finite identity is continuous through all zero-mass cases and invariant under $p\leftrightarrow1-p$.

For each pair, $ab=[p(1-p)]^{m+1}$ and $h(a,b)\le\sqrt{ab}/2$. Summing gives (3.1). At fairness each spin word has mass $2^{-(m+1)}$, so each pair contributes $2^{-(m+2)}$ and the sum is $1/4$. At endpoints the spin is deterministic. $\square$

**Theorem 3.2 (Biased actual posteriors and tails).** For $0<p<1$, $p\ne1/2$, and every $r\ge0$, the actual full posterior satisfies $q_{P_p}=X_0$ almost surely and

$$
e_{L,P_p}(r)=e_{R,P_p}(r)=\tfrac12v_{\lfloor r/2\rfloor}(p).
\tag{3.2}
$$

For every $R\ge0$, with $M=\lfloor R/2\rfloor$,

$$
\tau_{P_p}(0)=2\sum_{m\ge0}v_m(p)\le\frac{\beta(p)}{2(1-\beta(p))}<\infty,
\qquad
\tau_{P_p}(R)\le\frac{\beta(p)^{M+1}}{2(1-\beta(p))}.
\tag{3.3}
$$

Proof. Conditional expectation is orthogonal projection. The residual variance for recovering $S_0$ from $Y_{-m:-1}$ is $v_m(p)\to0$, since $\beta(p)<1$. Increasing these finite fields to the whole past therefore makes $S_0$ measurable from that past. The identical argument on $Y_{1: m}$ recovers $S_1$ from the whole future. At an active center the two erased-record half-lines recover both endpoints of $Y_0=S_0\oplus S_1$, while Lemma 2.2 identifies their phase. At a separator the center is zero. This proves $q_{P_p}=X_0$ under its own law.

Condition now on the active-center phase. The field $\mathcal G^L_r$ contains exactly $m=\lfloor r/2\rfloor$ negative active XORs and the entire future $Y_1,Y_2,\ldots$, which determines $S_1$. The left spin block $S_{-m:0}$ is independent of that future spin half-line $S_{1:\infty}$. If $a_m=\mathbb E_p[S_0\mid Y_{-m:-1}]$, the left predictor is $a_m$ when $S_1=0$ and $1-a_m$ when $S_1=1$. Its squared discrepancy from $X_0$ is $(S_0-a_m)^2$. Averaging gives $v_m$ on active centers and zero on separators; their stationary masses are $1/2$ each. Reflection at an active center is realized by $S'_k=S_{1-k}$, which sends $Y_k$ to $Y_{-k}$ and preserves the iid spin law. It gives the right formula with its whole past retained. Conditional projections and independence here are all under the one $J_p$.

Each $m$ occurs at offsets $r=2m,2m+1$. Hence

$$
\tau_{P_p}(2M)=2\sum_{m\ge M}v_m(p),\qquad
\tau_{P_p}(2M+1)=v_M(p)+2\sum_{m\ge M+1}v_m(p).
$$

Summing (3.1) proves (3.3), with harmless overcount for odd $R$. $\square$

**Proposition 3.3 (Fair and endpoint laws).** At $p=1/2$, write $A_i$ for the indicator that site $i$ is active. Then

$$
q_{P_{1/2}}=p^L_{r,P_{1/2}}=p^R_{r,P_{1/2}}=A_0/2\quad\text{almost surely},
\qquad e_{L,P_{1/2}}(r)=e_{R,P_{1/2}}(r)=\tau_{P_{1/2}}(R)=0.
\tag{3.4}
$$

At $p=0,1$, all these posteriors and defects are zero. Formula (3.2) is restricted to biased interior parameters: substituting $v_m(1/2)=1/4$ into it would give a false fair-law defect.

Proof. At fairness any consecutive $m$-XOR record has two equally likely spin preimages and mass $2^{-m}$. Extending any finite set to a consecutive interval and marginalizing shows the entire $Y$ process is iid fair. Given the phase, $Y_0$ is independent of all other XORs; finite-cylinder independence extends to their generated field. Lemma 2.2 makes phase measurable in each one-sided field even at $r=0$. Thus an active erased center has posterior $1/2$, and a separator has posterior zero, for the full and both one-sided fields. At endpoints the actual visible law is all-zero, so direct conditioning gives zero. $\square$

## 4. Fixed-state nonuniformity and persistent hidden memory

**Theorem 4.1 (Unbounded fixed-radius tail suprema).** For every $R\ge0$ and every $N\ge4$,

$$
\sup_{\theta\in\Theta_N}\tau_{P_\theta}(R)=+\infty.
\tag{4.1}
$$

Every member of the closed curve $(P_p)_{0\le p\le1}$ nevertheless has a finite tail. More precisely, for every fixed $r,R$,

$$
\lim_{\substack{p\to1/2\\p\ne1/2}}e_{L,P_p}(r)
=\lim_{\substack{p\to1/2\\p\ne1/2}}e_{R,P_p}(r)=1/8,\qquad
\lim_{\substack{p\to1/2\\p\ne1/2}}\tau_{P_p}(R)=+\infty,
\tag{4.2}
$$

although both defects and every tail are zero at $p=1/2$. On this curve the supremum of either side defect at every fixed $r$ is exactly $1/8$.

Proof. For $K\ge1$ choose $\varepsilon_K=1/[16(K+1)]$ and $p_K=1/2+\varepsilon_K$. Put $t=(1+2\varepsilon_K)/(1-2\varepsilon_K)$. A complementary $(m+1)$-spin pair with $k$ ones in one completion has likelihood ratio $t^{2k-(m+1)}$. Its endpoint-spin odds therefore lie between $t^{-(m+1)}$ and $t^{m+1}$. For $0\le\varepsilon\le1/4$,

$$
\frac{d}{d\varepsilon}\log\frac{1+2\varepsilon}{1-2\varepsilon}
=\frac4{1-4\varepsilon^2}\le\frac{16}3<8.
$$

Consequently $m\le K$ implies $(m+1)\log t\le1/2<\log2$. On every parity atom the endpoint posterior lies in $[1/3,2/3]$, so its variance is at least $2/9$. Thus $v_m(p_K)\ge2/9$ for $m\le K$, and (3.2) gives

$$
e_{L,P_{p_K}}(r)+e_{R,P_{p_K}}(r)\ge2/9\quad(0\le r\le2K+1),\qquad
\tau_{P_{p_K}}(R)\ge\tfrac29(2K+2-R)\quad(R\le2K+1).
\tag{4.3}
$$

Sending $K\to\infty$ proves (4.1) for $N=4$, even in any neighborhood of fairness. For $N>4$, pad $\lambda$ with zeros, $M_0$ with a deterministic-zero identity block and $M_1$ with a zero block. This is in $\Theta_N$ and preserves every actual visible quantity.

Continuity of each $v_m$ at fairness proves the fixed-$r$ limits in (4.2). For any prescribed finite lower bound and fixed $R$, choose a sufficiently long finite tail segment. Its punctured parameter limit has $1/4$ per offset, so its sum eventually exceeds that bound for every sufficiently close biased parameter. Nonnegativity of the remaining terms proves the actual tail limit, without using a divergent upper estimate as a lower bound. Finally a Bernoulli conditional variance is at most $1/4$; (3.2), its punctured limit and (3.4) give the stated side-defect supremum. $\square$

**Corollary 4.2 (Other limits and restricted uniform control).** As $p\to0$ or $p\to1$, every $\tau_{P_p}(R)\to0$, consistently with the endpoint laws. For $0<\delta<1/2$, the subset $|p-1/2|\ge\delta$ has the common vanishing allowance

$$
\tau_{P_p}(R)\le\frac{\beta_\delta^{\lfloor R/2\rfloor+1}}{2(1-\beta_\delta)},\qquad
\beta_\delta=\sqrt{1-4\delta^2}<1.
\tag{4.4}
$$

Proof. Use (3.3), $\beta(p)\to0$ at either endpoint, and $\beta(p)\le\beta_\delta$ on the stated subset; direct endpoint evaluation covers $p=0,1$. For any single biased law the radius limit is geometric, while the fair and endpoint radius limits are identically zero. No such common allowance exists near fairness by Theorem 4.1. $\square$

**Proposition 4.3 (Hidden memory and the cut-budget boundary).** In this displayed realization at fairness, with natural-log information and $W_r=X_{-r:-1}$ (the empty observation at $r=0$),

$$
C_{1/2}(r):=I_{J_{1/2}}(H_{-r};H_0\mid W_r)
=H_{J_{1/2}}(H_0\mid W_r)\ge\log2\qquad(r\ge0).
\tag{4.5}
$$

Thus a nonsummable conditional hidden-endpoint information series can coexist with zero observable erasure defects. In particular, the entropy-budget inequality $\tau_{P_p}(0)\le H_{J_p}(H_j)$ fails on this family.

Proof. Given a compatible hidden state and an observed symbol, the next hidden state is uniquely determined: an active XOR determines the new spin, and a separator copies it. Hence $H_0$ is a function of $(H_{-r},W_r)$. At fairness spin complementation preserves the law, the observation and the phase, but flips the endpoint spin. Conditional on $W_r$ and its starting phase, that spin is therefore uniform. Since the endpoint state records phase and spin, its conditional entropy is $\log2$ plus the remaining conditional phase entropy, including on all-zero phase-ambiguous words. This proves (4.5); Proposition 3.3 gives the simultaneous zero observable defects. The hidden-information statement concerns this realization and is not a minimality assertion.

At any cut $j$ the actual past $X_{i<j}$ and future $X_{i\ge j}$ are conditionally independent given the four-valued $H_j$. Data processing bounds their mutual information by $H(H_j)\le\log4$; finite exterior blocks suffice to obtain the same whole-half-line bound. But at $K=16$, $p_K=137/272$, (4.3) gives

$$
\sum_{r=0}^{33}(e_{L,P_{137/272}}(r)+e_{R,P_{137/272}}(r))\ge68/9>\log4.
$$

Larger $K$ makes this sum arbitrarily large at fixed state count. Repeated defects with whole-opposite-side conditioning cannot be telescoped into one cut entropy. This refutes that budget, not arbitrary parameter-dependent estimates or universal per-law summability. $\square$

## 5. Continuous finite laws and discontinuous actual risk

**Theorem 5.1 (Full-exterior risk and intrinsic posterior jump).** The finite-cylinder-continuous curve of Proposition 2.1 has

$$
d(P_p)=\begin{cases}1/8&p=1/2,\\0&p\in[0,1]\setminus\{1/2\}.\end{cases}
\tag{5.1}
$$

For biased interior $p$, the distribution of its own actual posterior is

$$
\operatorname{Law}_{P_p}(q_{P_p})=(1-p(1-p))\delta_0+p(1-p)\delta_1,
\qquad
\operatorname{Law}_{P_{1/2}}(q_{P_{1/2}})=\tfrac12\delta_0+\tfrac12\delta_{1/2}.
\tag{5.2}
$$

The biased posterior distributions do not converge to the fair-law posterior distribution as $p\to1/2$, although $P_p\to P_{1/2}$ weakly on the original visible space.

Proof. Under every biased law Theorem 3.2 gives zero actual squared loss. At fairness Proposition 3.3 gives loss $A_0/4$ for either realized bit, and $\mathbb E A_0=1/2$, giving $1/8$. Endpoints are all-zero. This proves (5.1) through (1.1). At a biased interior parameter $q=X_0$ and $P_p(X_0=1)=\tfrac12\mathbb P_p(S_0\ne S_1)=p(1-p)$, proving (5.2). The biased posterior-law limit is $\tfrac34\delta_0+\tfrac14\delta_1$; its second moment is $1/4$, whereas the fair second moment is $1/8$. These are version-independent statements under each law separately. Cylinder continuity implies weak convergence because continuous functions on the compact finite-alphabet product space are uniformly approximable by finite-coordinate functions. $\square$

**Proposition 5.2 (A specified posterior comparison and no finite fair anchor).** Define on all legal exterior records the Borel function $g=1/2$ when the first one in the positive half-line has even index, and $g=0$ otherwise, including when no such one occurs. It is an actual fair-law posterior version. For every biased $0<p<1$,

$$
\mathbb E_{P_p}(q_{P_p}-g)^2=1/8,\qquad
\operatorname*{ess\,sup}_{P_p}|q_{P_p}-g|=1/2.
\tag{5.3}
$$

No function of finitely many exterior coordinates equals the fair full posterior almost surely.

Proof. Under every interior member the first future one exists and identifies the active parity. Thus $g=A_0/2$ almost surely under each such law. At fairness this is the actual posterior; at biased parameters $q=X_0$, so the squared difference is $1/4$ on active centers and zero on separators. This proves (5.3). It compares with the specified Borel extension $g$: a fair-law-only almost-sure equivalence class has no intrinsic norm under a different law, and arbitrary changes on fair-null sets need not preserve this cross-law comparison.

For any finite exterior coordinate set, the all-zero atom has positive probability under both fair phases: it fixes finitely many independent active fair bits to zero, while separator bits are already zero. On its active-center part the full posterior is $1/2$, and on its separator part it is zero. A function of those finite coordinates must have one value on the atom, so cannot be the full posterior. $\square$

**Proposition 5.3 (Exact fair finite-radius risk and nonuniform approximation).** For every finite $r\ge0$, put

$$
a_r=\tfrac12\,2^{-2\lfloor r/2\rfloor},\qquad
b_r=\tfrac12\,2^{-2\lceil r/2\rceil}.
$$

Then

$$
D_r(P_{1/2})=\frac18+\frac{a_rb_r}{4(a_r+b_r)}>\frac18,
\qquad D_r(P_{1/2})\downarrow\frac18.
\tag{5.4}
$$

For each fixed $r$, $D_r(P_p)$ is continuous in $p$, but its pointwise decrease to $d(P_p)$ is not uniform, even on this compact curve. In particular, for $N\ge4$,

$$
\sup_{\theta\in\Theta_N}(D_r(P_\theta)-d(P_\theta))\ge\frac18\quad\text{for every }r,
\tag{5.5}
$$

and the two limits are

$$
\lim_{\substack{p\to1/2\\p\ne1/2}}\lim_{r\to\infty}D_r(P_p)=0,
\qquad
\lim_{r\to\infty}\lim_{\substack{p\to1/2\\p\ne1/2}}D_r(P_p)=1/8.
\tag{5.6}
$$

Proof. At fairness every finite exterior atom containing a one identifies the phase, so its finite posterior equals its full posterior. The all-zero radius-$r$ exterior atom has active-center phase mass $a_r$, with $2\lfloor r/2\rfloor$ retained active bits, and separator-center phase mass $b_r$, with $2\lceil r/2\rceil$ retained active bits. Given this atom the finite posterior is $a_r/[2(a_r+b_r)]$. Orthogonal projection therefore gives

$$
D_r(P_{1/2})-d(P_{1/2})
=a_r\left(\tfrac12-\frac{a_r}{2(a_r+b_r)}\right)^2
+b_r\left(\frac{a_r}{2(a_r+b_r)}\right)^2
=\frac{a_rb_r}{4(a_r+b_r)}.
$$

Both phase masses are positive at each finite radius and tend to zero, proving (5.4). This includes $r=0$, when $a_0=b_0=1/2$ and $D_0=3/16$.

The finite-fiber identity supplied in [Universal, (1.5)][U] writes $D_r$ as a finite sum of $h$ applied to actual center-zero/center-one cylinder masses; forced atoms contribute zero. The function $h$ is continuous even at $(0,0)$, so Proposition 2.1 proves continuity of $D_r(P_p)$ without any continuity claim for pointwise quotient versions on zero fibers. By (5.1), along biased $p\to1/2$ the approximation error tends to $D_r(P_{1/2})>1/8$. This proves (5.5) on $\Theta_4$, and padding proves it for $N>4$. Pointwise conditional-projection convergence still gives $D_r(P_p)\downarrow d(P_p)$ for every fixed $p$; (5.1) and (5.4) prove (5.6). $\square$

## 6. Exact consumer boundaries and the original open problem

**Proposition 6.1 (Every actual conditional-null response here vanishes).** For any $p\in[0,1]$, $L\ge1$, block $C=[1,L]$ and bounded $f_C=f(X_C)$ with $f:B_L\to\mathbb R$ satisfying

$$
\mathbb E_{P_p}[f_C\mid\mathcal H_C]=0,\qquad
\mathcal H_C=\sigma(X_j:j\notin C),
$$

and every $i\in\mathbb Z$, let $q_i=\mathbb E_{P_p}[X_i\mid\mathcal E_i]$ and $\ell_i=(X_i-q_i)^2$. Then

$$
\mathbb E_{P_p}[f_C\ell_i]=0,\qquad
S_{P_p}(f):=\sum_{i\in\mathbb Z}\mathbb E_{P_p}[f_C\ell_i]=0,
\tag{6.1}
$$

with absolute convergence.

Proof. Under biased and endpoint laws every actual loss is zero almost surely; stationarity and a countable intersection give this simultaneously at all sites. At fairness $\ell_i=A_i/4$. Lemma 2.2 makes the phase, and thus $A_i$, measurable in $\mathcal H_C$, even when $i\in C$. Conditioning the product on $\mathcal H_C$ proves each zero term. $\square$

**Boundary 6.2 (Conditional stability keeps its hypotheses).** [Multiword, Theorem 2.2 and (2.5)][M] requires continuous finite marginals, bounded convergent directions that are conditional-null under their own laws, a specified common finite-coordinate reference posterior and actual essential posterior convergence to it, and an independently common vanishing actual-tail allowance. This curve has finite-marginal continuity and per-law finite tails. Near fairness it has neither a common tail allowance nor the required finite-coordinate reference or actual posterior control. Proposition 6.1 nevertheless gives zero responses at every parameter. Accordingly the construction does not refute that stability theorem, exhibit response discontinuity, or establish necessity of the tail hypothesis with all the other hypotheses satisfied. Its role is to show that fixed hidden dimension, finite-marginal continuity and pointwise summability cannot automatically supply those controls.

The attained-law statements in [Conditional Response, (2.1)–(2.2) and Theorem 3.1][C] remain exactly: if $d(P)=c_\star$, then $\tau_P(0)\le c_\star$, $\tau_P(R)\downarrow0$, $D_r(P)-c_\star\le c_\star/(r+1)$, and the actual conditional-null complete response is zero. They hold without finite hiddenness. The present nonattaining family says nothing about a common vanishing allowance on an attaining sublocus. [Multiword, Theorem 3.1][M]'s expanded finite certificate retains its independently proved candidate tail and productive-response conditions; this family supplies no productive direction or new violation.

**Boundary 6.3 (Compact separation requires no stronger continuity).** [Universal, Theorem 6.2][U] and [Renewal, §1.3][R] use continuous $D_r$ and upper-semicontinuous $d=\inf_rD_r$, not continuity of $d$ or uniform convergence of $D_r-d$. The upward jump (5.1) is consistent with upper semicontinuity. On the complete compact $\Theta_N$, their conclusions remain

$$
C_N:=\max_{\theta\in\Theta_N}d(P_\theta)
=\inf_{r\ge1}U_{N,r},\qquad
U_{N,r}:=\max_{\theta\in\Theta_N}D_r(P_\theta).
\tag{6.2}
$$

The same supplied compact decreasing-window argument on the curve $p\in[0,1]$ gives $\max_pD_r(P_p)\downarrow1/8$, even though (5.5) holds. Indeed a convergent subsequence of maximizing parameters leaves every fixed $D_k$ above the limiting maxima; taking $\inf_kD_k$ bounds that limit by $\max_pd(P_p)=1/8$, and the reverse bound is immediate. Thus nonuniform approximation errors do not obstruct this compact maximum argument.

Every member already has $P_p([1001])=0$, because the two ones would have opposite parities. [Universal, Theorem 3.1][U]'s full-support necessity already excludes the entire family from attainment. The supplied bound $c_\star>1/7>1/8$ in [Renewal, §1.2][R] also separates its exact risks, and the preceding compact argument yields some finite strict-risk separation for this restricted curve. These are reuse of existing exclusions and compactness, with no new attaining-law coverage or effective radius.

**Open Problem 6.4 (Unchanged arbitrary-finite attainment and separation).** For the whole original domain, decide whether some finite $N$ and $\theta\in\Theta_N$ attain $c_\star$, or whether $C_N<c_\star$ for every finite $N$. By [Universal, Theorem 6.2 and Open Problem 7.4][U], the latter remains equivalent to

$$
\forall N\ge1\ \exists r,m\ge1:\qquad U_{N,r}<\kappa_m/(m+1).
\tag{6.3}
$$

No all-$N$ separation pairs or finite attainer are supplied here. [Renewal][R]'s effective-three-state and stated rank-one reset exclusions remain their existing restricted results. The response route still needs a productive same-law conditional-null direction, or another strict certificate, covering every remaining hypothetical finite attainer and all original boundaries. This already-excluded zero-response family does not provide that coverage.

Universal per-law finiteness of $\tau_{P_\theta}(0)$ on the complete finite-hidden domain is also unresolved here. All members of this family have finite observable tails; its unbounded supremum is not a single-law divergent tail. No hidden-minimality, uniform or efficient radius, finite-sample, global novelty, physical or empirical machine-learning improvement follows.

## 7. Sources, classical attribution and proof limits

**Attribution 7.1 (Scoped synthesis and mature mechanisms).** The XOR/spin-complement filtering mechanism is classical: [Chigansky–van Handel, Example 10][CVH] observes equality of consecutive fair iid hidden bits, equivalently the complement of their XOR, and contrasts minimal and maximal hidden filters. Proposition 2.1 inserts actual emitted zero separators and a stationary phase on the original clock; §§3–5 prove the resulting legal-law erasure defects and Brier-risk parameter boundary directly. No hidden-filter theorem is substituted for those observable calculations.

[Dawid–Lauritzen–Parry, §4.2.1, Example 4.4 and (14)][DLP] supplies classical conditional Brier/ratio-matching loss and squared posterior discrepancy. Its strictly positive full-product setup does not itself cover hard no11 or zero-mass fibers. Here those cases are handled by the supplied legal-fiber identity and the direct conditional computations. [van Enter–Verbitskiy, §1.1, Theorem 2 and Theorems 5–6][EV] supplies classical whole-exterior Shannon erasure uncertainty; its Gibbs formula has a Gibbs hypothesis. Shannon erasure entropy is not the present squared-defect series or harmonic/Brier objective. Single-site recovery here is not asserted to recover every erased finite block or to establish strong bilateral determinism.

| Source | Status and exact use |
| --- | --- |
| [Universal][U], §§1, 3–4, Theorem 6.2 and Open Problem 7.4 | Ordinary supplier: actual risk, complete $\Theta_N/J_\theta/P_\theta$, full-support necessity and compact finite separation; original target unchanged. |
| [Renewal][R], §1.3 and §8 | Ordinary supplier: upper semicontinuity, same-law zero-mass trimming and its existing restricted exclusions. |
| [Conditional Response][C], §§2–4 | Ordinary supplier: exact one-sided fields, attained-law budgets, conditional-null response and finite certificate, with attainment hypotheses retained. |
| [Multiword][M], Theorems 2.2–3.1 | Ordinary supplier: conditional stability and expanded certificate; their actual posterior and tail hypotheses are not inferred from fixed state count. |
| Chigansky and van Handel, *A complete solution to Blackwell's unique ergodicity problem for hidden Markov chains*, arXiv:0910.3603v2, Example 10, DOI 10.1214/10-AAP688 | `literature-attested`: fair equality/XOR hidden-memory mechanism; not a supplier of this legal-clock tail or risk formula. |
| Dawid, Lauritzen and Parry, *Proper Local Scoring Rules on Discrete Sample Spaces*, arXiv:1104.2224v2, §4.2.1, Example 4.4, (14) | `literature-attested`: conditional Brier loss and posterior discrepancy; no transfer of full-product positivity or estimation conclusions. |
| van Enter and Verbitskiy, *Erasure entropies and Gibbs Measures*, arXiv:1001.3122v1, §1.1, Theorems 2, 5–6 | `literature-attested`: whole-exterior Shannon erasure and its stated Gibbs boundary; no replacement of the present quantities. |
| §§2–5 and Proposition 6.1 | `repo-derived`: the exact legal fixed-state construction/application and its proved boundary consequences relative to the named suppliers, without worldwide priority. |

**Proof limits.** All new claims are ordinary handwritten arguments over the one actual law, with finite conditional identities and explicitly justified infinite-field limits. No mathematical program, numerical experiment, enumeration run, new test, ingestion or Lean compilation supplies evidence here. Bounded primary attribution does not establish exhaustive literature absence. The remaining whole-domain tail and attainment questions are precisely those in Open Problem 6.4.

[U]: FIB_LEGAL_EDGE_LOAD_UNIVERSAL_POSTERIOR_DEFECT_AND_FINITE_HIDDEN_SEPARATION.md
[R]: FIB_LEGAL_EDGE_LOAD_RENEWAL_CLOSURE_SEPARATION_AND_OBSERVABLE_DEPENDENCE.md
[C]: FIB_LEGAL_EDGE_LOAD_CONDITIONAL_NULL_RESPONSE_AND_FINITE_CERTIFICATE.md
[M]: FIB_LEGAL_EDGE_LOAD_MULTIWORD_RESPONSE_STABILITY_AND_VANISHING_TAIL_CERTIFICATE.md
[CVH]: https://arxiv.org/html/0910.3603v2
[DLP]: https://arxiv.org/html/1104.2224v2
[EV]: https://arxiv.org/html/1001.3122v1

## 追加锚（本行以下为增补区）

## 8. Measurable hidden endpoints from the original biased-law half-lines

**Lemma 8.1 (Original-law biased XOR hidden-endpoint recovery).** Give $A=\{a_0,a_1,b_0,b_1\}$ and $\{0,1\}$ their discrete sigma-algebras, and give $\Omega=A^{\mathbb Z}\times\{0,1\}^{\mathbb Z}$ its product sigma-algebra. Let $H_i$ and $X_i$ be its actual hidden and visible coordinate projections. Use exactly the row $\lambda_p$ and the two matrices $M_0(p),M_1(p)$ of (2.1), in their displayed state order, including every structural zero.

For every real $p$ with $0<p<1$ and $p\ne1/2$, there exist total measurable maps

$$
D^-_p,D^+_p:\{0,1\}^{\mathbb N}\longrightarrow A
$$

such that the following holds for every probability measure $J$ on $\Omega$. Assume that $J$ satisfies the complete joint-cylinder law (1.3) with these coefficients: for every $\ell\in\mathbb Z$, $n\in\mathbb N_0$, hidden assignment $h:\{0,\ldots,n\}\to A$ and bit assignment $x:\{0,\ldots,n-1\}\to\{0,1\}$, the joint event specifying $H_{\ell+i}=h_i$ for $0\le i\le n$ and $X_{\ell+i}=x_i$ for $0\le i<n$ has mass given by (1.3) with $a=\ell$ and $b=\ell+n-1$. At $n=0$ this means the hidden singleton mass $\lambda_p(h_0)$, with empty product one. These nonnegative real masses are interpreted by their canonical inclusion in $[0,+\infty]$ when $J$ is extended-nonnegative-real-valued. Thus every origin, every interval length and every ordered seam is included. Then, simultaneously,

$$
J\left(\left\{\omega:
H_0(\omega)=D^-_p\bigl((X_{-n-1}(\omega))_{n\ge0}\bigr)
\ \text{and}\;
H_1(\omega)=D^+_p\bigl((X_{n+1}(\omega))_{n\ge0}\bigr)
\right\}\right)=1.
$$

The maps may depend on $p$ and are chosen before $J$. Neither joint measurability in $p$ nor a decoder independent of $p$ is asserted.

Proof. First identify the actual law, rather than assume a hidden-spin representation for $J$. Proposition 2.1 constructs independent Bernoulli$(p)$ spins and an independent uniform phase, with hidden and visible coordinates (2.2). Its induced measure on $\Omega$ satisfies the required cylinders: an initial $a_s$ or $b_s$ has mass $\pi_s/2$; every active transition chooses the next spin with mass $\pi_t$ and the required XOR; every separator transition copies the spin and emits zero. Incompatible transitions have mass zero. Multiplying these factors gives (1.3) for every interval and origin, including intervals starting or ending at either phase and the hidden singleton case. This checks the joint hidden-visible law, not just its visible marginal.

The complete interval cylinders determine a probability measure on $\Omega$. Indeed any cylinder restricting finitely many hidden and visible coordinates is a finite disjoint union of complete cylinders on a containing interval, with its final hidden coordinate included. Such finite-coordinate cylinders form a generating pi-system for the product sigma-algebra. Uniqueness of probability measures on that system shows that every $J$ in the statement equals the induced measure just constructed. It is therefore sufficient to construct measurable decoders under that realization and then transfer their measurable equality event by equality of the actual joint measures.

Here is a total construction on binary half-lines. For a half-line $z=(z_n)_{n\ge0}$, let $\varphi(z)$ be the parity of $n+1$ at its first one; set $\varphi(z)=0$ if it has no one. This parity is the parity of the original coordinate on either side, since $-n-1$ and $n+1$ have the same parity. The first-one rule is measurable, being specified by countably many finite-coordinate events. Under the realization, Lemma 2.2 says that this rule equals the active phase on each complete half-line almost surely.

Set $d=2$ if $\varphi(z)=0$ and $d=1$ if $\varphi(z)=1$, and extract $y_j=z_{d+2j-1}$ for $j\ge0$. This only selects active coordinates in the original half-line; it does not change the law or the clock. Form a candidate spin sequence by $t_0=0$ and $t_{j+1}=t_j\mathbin\oplus y_j$. Define $c_p(z)=1$ when the averages of $t_0,\ldots,t_{m-1}$ converge to $1-p$ as $m\to\infty$, and define $c_p(z)=0$ otherwise. The latter case includes convergence to $p$ and all exceptional records. Each $t_j$ is a measurable function of finitely many coordinates after the measurable phase choice; convergence to the specified real number is a countable measurable condition. Thus $c_p$ is a total measurable bit-valued map. Finally put

$$
\begin{aligned}
D^-_p(z)&=\begin{cases}a_{c_p(z)}&\varphi(z)=0,\\b_{c_p(z)}&\varphi(z)=1,\end{cases}\\
D^+_p(z)&=\begin{cases}b_{c_p(z)}&\varphi(z)=0,\\a_{c_p(z)}&\varphi(z)=1.\end{cases}
\end{aligned}
$$

These maps are measurable on the entire half-line space, including records incompatible with either phase.

To check the endpoint indices, if the actual phase is zero, the negative active list is $Y_{-1},Y_{-2},\ldots$ and the positive active list is $Y_1,Y_2,\ldots$. Their adjacent spins start respectively at $S_0$ and $S_1$, and the required states are $H_0=a_{S_0}$ and $H_1=b_{S_1}$. If the actual phase is one, the lists are $Y_{-1},Y_{-2},\ldots$ and $Y_0,Y_1,\ldots$; both start at $S_0$, and the required states are $H_0=b_{S_0}$ and $H_1=a_{S_0}$. For either direction the recurrence for $t$ gives the actual adjacent spin sequence when its endpoint spin is zero, and its complement when that endpoint spin is one. The strong law for each one-sided iid spin sequence gives limiting frequency $p$ for the actual sequence and $1-p$ for its complement. Because $p\ne1/2$, the rule $c_p$ selects the endpoint spin in all four cases. The finitely many phase and directional almost-sure events can be intersected, proving both state equalities simultaneously. Equality of joint laws established above transfers this single measurable event to every admissible $J$.

This is the endpoint-recovery step used in Theorem 3.2: Lemma 3.1's complement-pair variance tending to zero supplies its conditional-projection formulation, while Lemma 2.2 supplies the phase. The strong-law selection is also the mechanism in [Conditional gain deficit, Proposition 4.1](FIB_LEGAL_EDGE_LOAD_CONDITIONAL_GAIN_DEFICIT_AND_UNWEIGHTED_BRIDGE_OBSTRUCTION.md) at $p=3/5$; the two distinct limiting frequencies apply on both biased parameter ranges here. The assertion is a `repo-derived` explicit original-domain measurable formulation of that recovery relation, with the classical strong law and measure-uniqueness argument retaining their usual attribution and no literature-priority claim.

The hypotheses are satisfiable by Proposition 2.1. No decoder, spin-image law, independence of the observed half-lines, tail summability, finite-record sufficiency or extra positivity is assumed. The period-two law requires no mixing or aperiodicity premise. The fair parameter and endpoints are excluded. This auxiliary asserts only the displayed endpoint relation; it does not assert a law-existence theorem, posterior, moment, entropy or tail conclusion, or the other conclusions of Theorem 3.2 or the cited Proposition 4.1. $\square$

## 追加锚（本行以下为增补区）

## 9. Original-law paid-read lower bound for a hidden endpoint

**Definition 9.1 (Admissible arbitrary-address protocol).** Fix $0<p<1$ with
$p\ne1/2$, $j\in\{0,1\}$, and let $(\mathsf U,\mathcal U,\nu)$ be one
arbitrary probability space independent of the complete joint law $J_p$. Fixed
public data may be included as a constant in $\mathsf U$; any random public
data are included in the same source-independent variable with its unchanged
law $\nu$. A protocol is a measurable next-event rule which, given
$u\in\mathsf U$ and each finite acquired ordered record

$$
r=((t_1,x_1),\ldots,(t_n,x_n))\in(\mathbb Z\times\{0,1\})^n,
$$

either chooses the next integer address $t_{n+1}$, returns a state
$A\in\{a_0,a_1,b_0,b_1\}$, or continues internally indefinitely without any
further read or return. Finite next events may follow internal waiting:
their occurrence, type, address or output, and finite waiting time depend
measurably only on the fixed public data, $u$ and $r$. All internal
randomness is included in $u$. If an address is chosen, the only reply is
the actual source bit $x_{n+1}=X_{t_{n+1}}$ from the same stationary source.
Every such read is charged: repetitions, separator zeros, negative, positive,
disconnected and arbitrarily distant addresses all count once.

The return time $\tau$ and the charged read count
$N\in\mathbb N_0\cup\{\infty\}$ are separate random variables. Set
$\tau=\infty$ on every nonreturning path, and let $N$ count all actual reads.
Thus $\tau=\infty$ with any finite $N$, including $N=0$, is permitted by
indefinite internal continuation after that finite record. Infinite read
paths are also permitted. On a return, $N$ is finite; the output and $\tau$
depend measurably only on the fixed public data, $u$, and the acquired
ordered address/reply record. On $\{\tau<\infty\}$, write $\mathsf R$ for that
terminal ordered record.

There is no hidden-state, half-line or tail read, source-dependent seed or
timing, reset, law switch, moving endpoint, or erased-coordinate substitution.
The rule may return before any read and may output a state from the wrong
phase. Null records and versions completed by null sets are included through
the usual measurable completion. Put

$$
\mathbb P_p=J_p\otimes\nu,
\qquad
E_k=\{\tau<\infty,\ N\le k\},
\qquad
R=\frac{\max(p,1-p)}{\min(p,1-p)}>1.
\tag{9.1}
$$

The public and auxiliary variables are independent of the original hidden
endpoint $H_j$ and of every $X_t$.

**Theorem 9.2 (Original-clock fixed-endpoint XOR acquisition bound).** For
every admissible protocol of Definition 9.1 and every $k\ge0$,

$$
\mathbb P_p\bigl(A\ne H_j,\ E_k\bigr)
\ \ge\
\frac{\mathbb P_p(E_k)}{1+R^{k+1}}.
\tag{9.2}
$$

Consequently, if a protocol has a positive-probability finite return, then
its error probability on finite returns is positive. More explicitly, the
same proof gives the random-count form

$$
\mathbb P_p\bigl(A\ne H_j,\ \tau<\infty\bigr)
\ \ge\
\mathbb E_p\!\left[
 \frac{\mathbf 1_{\{\tau<\infty\}}}{1+R^{N+1}}
\right].
\tag{9.3}
$$

No almost-sure return, deterministic bound, or finite expected value of $N$ is
assumed. The integrand in (9.3) is defined as zero on $\{\tau=\infty\}$,
whether $N$ is finite or infinite.

**Proof.** Use the realization (2.2) supplied by Proposition 2.1 only as a
description of the one fixed law $J_p$. Thus $\varphi$ is uniform and the
$S_\ell$ are iid Bernoulli$(p)$. The hidden endpoint states can be written as

$$
\begin{array}{c|cc}
 &j=0&j=1\\ \hline
\varphi=0&a_{S_0}&b_{S_1}\\
\varphi=1&b_{S_0}&a_{S_0}
\end{array}
\tag{9.4}
$$

For a fixed phase $\varphi$, the two entries obtained by replacing the
displayed spin by its complement are the two states of that phase. We compare
their masses while keeping $p$, the phase, the source, and the protocol fixed.

Fix $u$ and a finite record $r$ of length $n$. Whether the next-event
choices at its successive prefixes prescribe $r$ followed by a finite
return is determined by $u$ and $r$. If not, its terminal mass is zero under
every hidden state. If so, the source section of
$\{\mathsf R=r,\tau<\infty\}$ is exactly the finite cylinder
$\{X_{t_i}=x_i:1\le i\le n\}$, and $A$ and $\tau$ are fixed. In particular,
internal waiting or its divergence imposes no additional source condition:
the same $u$ and acquired replies give the same finite events and delays.
This applies also to adaptive addresses. Under phase $\varphi$, a read at
$t=2\ell+\varphi$ returns

$$
X_t=Y_\ell=S_\ell\mathbin\oplus S_{\ell+1},
$$

whereas a read at the other parity returns the separator zero. Discarding
the latter reads from the comparison does not discard their charges. The
active reads in $r$ therefore give a finite labelled multigraph on the spin
indices, with an edge $\{\ell,\ell+1\}$ for each active read. Repeated reads
give repeated edges. Inconsistent duplicate labels have zero probability
under both endpoint states.

For an arbitrary measurable seed space, the masses below are source-section
masses at the fixed value $u$; no regular conditional probability on
$\mathsf U$ is being assumed.

Let $q=q_{j,\varphi}$ be the spin index displayed in (9.4): $q=j$ when
$\varphi=0$ and $q=0$ when $\varphi=1$. In the graph formed by the active
reads, the component containing $q$ has at most $n+1$ vertices. Once $S_q=s$
is fixed, the labelled edges determine every spin in this component, if they
are consistent. The joint mass of that component, including the Bernoulli
factor at $q$, is a product of at most $n+1$ factors, each equal to $p$ or
$1-p$. Replacing $s$ by $1-s$ complements all those factors. Consequently,
for the two same-phase endpoint states $h_{\varphi,0}$ and
$h_{\varphi,1}$, the joint masses of $r$ satisfy

$$
R^{-(n+1)}\le
\frac{\mathbb P_p(H_j=h_{\varphi,0},\,\mathsf R=r,\,\tau<\infty\mid u)}
     {\mathbb P_p(H_j=h_{\varphi,1},\,\mathsf R=r,\,\tau<\infty\mid u)}
\le R^{n+1},
\tag{9.5}
$$

whenever the denominator is nonzero. The same argument shows that the two
masses are simultaneously zero or simultaneously positive. All components
disjoint from the component of $q$ contribute the same factor to both masses;
this is why disconnected and distant reads do not increase the exponent.
The phase factor $1/2$ is also common. This is only a reindexing of a finite
product in the original law, not a transformation of the source or a newly
permitted read.

For this fixed $u$ and $r$, write $w_h$ for the joint mass of the terminal
record and $H_j=h$, and let $h_\ast=A(u,r)$. Let $\bar h_\ast$ be the other
state with the same phase as $h_\ast$ and the complementary spin. By (9.5),

$$
w_{h_\ast}\le R^{n+1}w_{\bar h_\ast}.
$$

Every state in the opposite phase is an error whenever the output is
$h_\ast$. If $O$ denotes the total mass of those two opposite-phase states,
then, with $W=\sum_hw_h$ and $L=\sum_{h\ne h_\ast}w_h$,

$$
W=w_{h_\ast}+w_{\bar h_\ast}+O
\le (1+R^{n+1})w_{\bar h_\ast}+O
\le (1+R^{n+1})L.
\tag{9.6}
$$

Thus $L\ge W/(1+R^{n+1})$. Summing (9.6) over all terminal records of
length $n\le k$ and then integrating over $u$ gives

$$
\mathbb P_p(A\ne H_j,E_k)
\ge \frac{\mathbb P_p(E_k)}{1+R^{k+1}},
$$

because $R>1$. The same recordwise inequality with its own $n$ sums over all
finite terminal records and gives (9.3). If
$\mathbb P_p(\tau<\infty)>0$, then the finite-return event is the countable
union of the $E_k$, so some $E_k$ has positive probability and (9.2) gives a
strictly positive error probability. Paths continuing internally forever
after finitely many reads, and infinite-read nonreturning paths, belong to
none of these terminal events and contribute zero to both sides of (9.3).
Only actual reads enter the returning record length $n$. The argument uses
finite record masses, so completion choices and null fibres do not change
it. $\square$

**Attribution 9.3 (Scope of the acquisition increment).** Proposition 2.1,
Lemma 3.1, Theorem 4.1 and Lemma 8.1 supply the four-state law, its
complement-pair products, fixed original clock and measurable endpoint
description. The finite-energy/product-likelihood step in the proof is the
elementary finite specialization of those displayed products. The filtering
and synchronization results of [Chigansky--van Handel, Example 10][CVH],
[Travers--Crutchfield, *Exact Synchronization*, Definitions 5--8 and
Theorem 3](https://arxiv.org/html/1008.4182v3), and [Travers--Crutchfield,
*Asymptotic Synchronization*, §VI Theorem 1 and §VII.1 Proposition
3](https://arxiv.org/html/1011.1581v2) provide neighboring mechanisms but do
not supply (9.2) for arbitrary integer-address adaptive paid reads. Equation
(9.2) is the source-specific repo-derived quantitative bridge. It makes no
sharpness or optimal-cost claim, and it does not assert physical storage,
universal filtering, formal verification, or completion of the original
attainment problem.

## 追加锚（本行以下为增补区）

## 10. Sharp count-only endpoint error with paid phase information

**Theorem 10.1 (Paid phase-cost refinement and selective sharpness).** Retain
exactly Definition 9.1, including the fixed original $H_j$, $j\in\{0,1\}$,
the one law $J_p$, and the arbitrary unchanged independent auxiliary law
$\nu$. Put

$$
a=\max(p,1-p),\qquad b=\min(p,1-p),\qquad R=a/b,
\qquad e_0=1-a/2,\qquad e_n=\frac1{1+R^n}\quad(n\ge1).
\tag{10.1}
$$

For a fixed seed and a positive terminal cylinder of length $n$, let $W$
be its source mass and $L$ its error mass for the protocol's chosen output.
For every output state, whether or not it maximizes posterior probability,

$$
L\ge e_nW.
\tag{10.2}
$$

Consequently every admissible protocol satisfies

$$
\begin{aligned}
\mathbb P_p(A\ne H_j,\tau<\infty)&\ge\mathbb E_p[g],
&g&=\begin{cases}e_N&\tau<\infty,\\0&\tau=\infty,\end{cases}\\
\mathbb P_p(A\ne H_j,E_0)&\ge(1-a/2)\mathbb P_p(E_0),\\
\mathbb P_p(A\ne H_j,E_k)&\ge\frac{\mathbb P_p(E_k)}{1+R^k}
&& (k\ge1).
\end{aligned}
\tag{10.3}
$$

Each $e_n$ is the largest coefficient depending only on $p$ and $n$ that
works in (10.2) for all such records and protocols. The coefficients in the
two budget bounds of (10.3) are likewise best possible when selective finite
return is permitted.

Proof. Reuse Theorem 9.2's fixed-seed terminal-cylinder reduction. For each
seed $u$ and terminal ordered record $r$, the source section is the cylinder
$C=\{X_{t_i}=x_i:1\le i\le n\}$ if the prescribed choices and finite return
are consistent, and is empty otherwise. The output is fixed on that
section. Adaptive choices and internal waiting add no source constraint.
These are section masses, with no regular conditional probability assumed
on the auxiliary space.

Write $w_h=J_p(C,H_j=h)$, $W=\sum_hw_h$, and $L=W-w_h$ when the output is
$h$. At $n=0$, a nonempty terminal section is the whole source space.
Proposition 2.1 gives largest state prior $a/2$, so $L\ge(1-a/2)W$.
Now take $n\ge1$. If $w_h=0$, (10.2) is immediate. Otherwise let $\varphi$
be the phase corresponding to $h$ at this original endpoint, and let
$q=q_{j,\varphi}$ be its actual spin index from (9.4): $q=j$ for
$\varphi=0$, and $q=0$ for $\varphi=1$. Let $\bar h$ be the complementary
spin state at the same endpoint and phase.

Under this phase, use the graph of distinct active edges
$\{\ell,\ell+1\}$ read in $r$, adjoining $q$ as an isolated vertex if
necessary. Let $V$ be the component of $q$ and $v=|V|$. It is a finite path
or a singleton, so it has $v-1$ distinct edges and $v\le n+1$. Separator
reads remain charged, as do repeated edges. Positive mass excludes a one
at a separator, inconsistent repetitions and any incompatible labels.
As in Lemma 3.1 and (9.5), the two endpoint choices determine complementary
assignments $(s_\ell)_{\ell\in V}$ and $(1-s_\ell)_{\ell\in V}$. With
$\pi_0=1-p$ and $\pi_1=p$, their masses have the form

$$
w_h=K\prod_{\ell\in V}\pi_{s_\ell},\qquad
w_{\bar h}=K\prod_{\ell\in V}\pi_{1-s_\ell},\qquad K>0.
$$

The common factor includes $1/2$ for the phase and all components disjoint
from $V$. Thus if $v\le n$,
$w_h\le R^v w_{\bar h}\le R^nL$.

It remains to consider $v=n+1$. The $n$ distinct edges in $V$ then use all
$n$ calls: every call is a distinct active edge in this one component, with
no repetition, separator or other component. If any reply is one, both
spin values occur in each of the two complementary assignments. Hence
$|\#\{\ell:s_\ell=1\}-\#\{\ell:s_\ell=0\}|\le v-2=n-1$, and the same
products give $w_h\le R^{n-1}w_{\bar h}\le R^nL$.

If instead all replies are zero, every address has parity $\varphi$.
Under the opposite phase all these reads are separator zeros, imposing no
spin constraint. The same seed and replies follow the same terminal rule,
so the opposite-phase joint mass of $C$ is exactly $1/2$. All of it is
error for output $h$, whereas $w_h\le1/2$. Thus $w_h\le L\le R^nL$
also in this case. We have proved $W=w_h+L\le(1+R^n)L$ in every case.
Zero-mass cylinders contribute zero. In particular the argument covers
both endpoints and bias directions, all-zero and one-containing records,
and repeated, disconnected, negative or arbitrarily distant reads.

There are countably many finite ordered integer-address/reply records.
Sum (10.2) over terminal records and integrate over the unchanged
independent law $\nu$, as in Theorem 9.2. This gives the first bound in
(10.3). On nonreturns $g=0$, including indefinite internal continuation
after any finite $N$ and infinite-read paths. The sequence $(e_n)_{n\ge0}$
is nonincreasing: $e_1=b<e_0$, and $R>1$. Restriction to $N\le k$ therefore
gives both budget bounds. Measurable completion changes none of these
integrated masses.

For sharpness fix $n\ge1$ and either original endpoint $j$. Ignore the
auxiliary variable without changing its law. Make all $n$ predetermined
actual reads: first the $n-1$ even addresses
$2(j+i)$, $0\le i\le n-2$, then the distant even address $2(j+n)$.
Return only if every local reply is zero and the distant reply is one;
on every other complete record continue internally forever with no more
reads. Thus $N=n$ on every path. Put $\sigma=1$ for $p>1/2$ and $\sigma=0$
for $p<1/2$, and return $a_\sigma$ when $j=0$ or $b_\sigma$ when $j=1$.

The paid distant one forces phase zero. In that phase the local zero
replies say that the $n$ spins $S_j,\ldots,S_{j+n-1}$ are all equal.
The distant reply is $S_{j+n}\mathbin\oplus S_{j+n+1}$, whose spin set is
disjoint from that block and whose probability of being one is $2ab$.
The two local assignments have masses $a^n$ and $b^n$, and (9.4) identifies
their endpoint states. Independence in the same realization (2.2) gives

$$
\begin{aligned}
\mathbb P_p(\tau<\infty)&=ab(a^n+b^n)>0,\\
\mathbb P_p(A\ne H_j,\tau<\infty)&=ab\,b^n,\\
\mathbb P_p(A\ne H_j\mid\tau<\infty)&=\frac{b^n}{a^n+b^n}=e_n.
\end{aligned}
\tag{10.4}
$$

For $n=1$ the local read list is empty; its block is the single unobserved
endpoint spin $S_j$, still disjoint from the distant pair. The local event
is then unrestricted, consistently with $a+b=1$, so (10.4) holds without
an unpaid read. For $n=0$, immediate return of any state with prior $a/2$
has error $e_0$. These protocols attain (10.2) and the corresponding budget
bounds, proving maximality of their count-only coefficients. $\square$

The finite-product ambiguity used in the proof retains the attribution of
Lemma 3.1 and Theorem 9.2. [Chigansky--van Handel, arXiv:0910.3603v2,
Example 10][CVH] supplies the classical fair hidden equality/XOR ambiguity.
[Travers--Crutchfield, arXiv:1008.4182v3, Definitions 5--8 and
Theorem 3](https://arxiv.org/html/1008.4182v3) and
[arXiv:1011.1581v2, §VI Theorem 1 and §VII.1 Proposition
3](https://arxiv.org/html/1011.1581v2) concern current-state synchronization
from consecutive words. They do not supply the biased original-clock
paid-record coefficient above. The phase-cost case distinction and the
same-law selective equality are `repo-derived`, without a literature-priority
claim. Theorem 9.2 remains valid with its weaker exponent.

Sharpness here concerns selective finite-return events. For $n\ge1$ the
witness has positive nonreturn probability, even though $N=n$ always; it
does not determine optimal unconditional risk for bounded almost-surely
returning protocols, optimal expected read cost, or optima at a prescribed
return probability. The lower bounds apply to those protocols whenever
they satisfy Definition 9.1. Open Problem 6.4 is unchanged.

## 追加锚（本行以下为增补区）

## 11. All-zero paid records and a one-call guaranteed-return optimum

**Theorem 11.1 (Sharp all-zero terminal-cylinder envelope).** Retain exactly
Definition 9.1 and the coefficients $a,b,R,e_n$ of Theorem 10.1. Put

$$
c=a^2+b^2\in(0,1),\qquad
f_n(m)=\frac{b^{m+1}+c^{n-m}}
 {a^{m+1}+b^{m+1}+c^{n-m}},\qquad
z_n=\min_{0\le m\le n}f_n(m)\quad(n\ge0),
\tag{11.1}
$$

where the minimum is over integers. For each fixed seed and each positive
all-zero finite terminal source cylinder of actual record length $n$, its
mass $W$ and error mass $L$ satisfy $L\ge z_nW$ for every output. The empty
record is all-zero. Each $z_n$ is the largest coefficient for this precise
class of records, for either original endpoint, either bias direction and
any unchanged independent auxiliary law. Moreover,

$$
z_0=e_0=1-a/2,\qquad z_n>e_n\quad(n\ge1),\qquad
z_{n+1}<z_n\quad(n\ge0).
\tag{11.2}
$$

No $z_n$ bound is asserted for a record containing a one.

Proof. Use Proposition 2.1's realization (2.2) and Theorem 9.2's
fixed-seed terminal-cylinder reduction. A terminal ordered record consistent
with the rule has source section exactly its acquired-bit cylinder; adaptive
choices and finite internal waits impose no additional source restriction.
Thus fix an ordered list of $n$ addresses, all with reply zero. Let $n_0,n_1$
count its actual calls at the two parities, including repetitions, so that
$n_0+n_1=n$.

For a phase $\varphi$, let $Q_\varphi$ be the probability of this cylinder
under that phase, without its prior factor $1/2$. Distinct active queried
edges form disjoint finite paths on the spin indices. A path of $\ell$
edges forces its $\ell+1$ spins to be equal and contributes
$t_{\ell+1}=a^{\ell+1}+b^{\ell+1}$. Disjoint paths use disjoint iid spins.
The elementary convexity inequality, with weights $a,b$ summing to one,
gives

$$
t_{\ell+1}=a\,a^\ell+b\,b^\ell
\ge(a\,a+b\,b)^\ell=c^\ell\quad(\ell\ge1).
$$

If $d_\varphi$ is the number of distinct queried active edges in that
phase, then $d_\varphi\le n_\varphi$ and consequently

$$
Q_\varphi=\prod_{\text{active components}}t_{\ell+1}
\ge c^{d_\varphi}\ge c^{n_\varphi}>0.
\tag{11.3}
$$

An empty product is one. Separator calls impose no constraint in that phase
but remain in the actual counts; repeated edges likewise retain their
charges. This product description allows arbitrary negative, disconnected
and distant integer addresses.

Fix the output state $h$. At the fixed original endpoint $j$, it specifies
one phase $\varphi$ and one endpoint-spin value. That spin's index is
$q=q_{j,\varphi}$ from (9.4). Adjoin $q$ as an isolated vertex when no
queried active edge is incident to it. Its component has $m$ distinct
edges and $m+1$ vertices,
where $0\le m\le n_\varphi$. Let $D\in(0,1]$ be the product of the factors
for all other active components in that phase. The two endpoint-state
masses in phase $\varphi$ are

$$
\frac12a^{m+1}D,\qquad \frac12b^{m+1}D.
$$

The opposite-phase mass is $Q_{1-\varphi}/2$ and is entirely error for
output $h$. The larger of the two displayed masses is an upper bound on
the success mass for that output. Writing $T=Q_{1-\varphi}/D$ gives

$$
\frac LW\ge
\frac{b^{m+1}+T}{a^{m+1}+b^{m+1}+T},\qquad
T\ge c^{n_{1-\varphi}}\ge c^{n-m}.
\tag{11.4}
$$

The fraction increases with $T$, so it is at least $f_n(m)\ge z_n$.
This comparison also covers output of the less likely spin state. Both
phases have positive mass on every finite zero cylinder; no phase has been
read for free.

At $n=0$, (11.1) gives $(b+1)/2=1-a/2$. If $n\ge1$ and $m<n$, then

$$
f_n(m)>\frac{b^{m+1}}{a^{m+1}+b^{m+1}}
=\frac1{1+R^{m+1}}\ge e_n.
$$

If $m=n$, its numerator $b^{n+1}+1$ exceeds $a^{n+1}$, so
$f_n(n)>1/2>e_n$. The minimum over the finite set is therefore strictly
larger than $e_n$. For strict decrease choose a minimizer $m$ for $z_n$.
Keeping this same $m$ in $f_{n+1}$ multiplies its positive $c^{n-m}$ term
by $c<1$ and strictly decreases the fraction. Hence
$z_{n+1}\le f_{n+1}(m)<f_n(m)=z_n$.

For attainment, fix any $0\le m\le n$, put $d=n-m$, and choose a public
phase label $\psi\in\{0,1\}$; this label is a choice of query pattern, not
knowledge of the actual phase. Let $q=q_{j,\psi}$, $L_*=j+m+2$, and make
all $n$ predetermined actual calls at

$$
2(q+i)+\psi\quad(0\le i<m),\qquad
2(L_*+2i)+(1-\psi)\quad(0\le i<d),
\tag{11.5}
$$

in the displayed order. Ignore the auxiliary variable without changing its
law. Return only when all $n$ replies are zero; otherwise continue
internally forever after the last call, without further reads. Let
$\sigma=1$ if $p>1/2$ and $\sigma=0$ if $p<1/2$. Write
$h_{j,\eta,s}$ for the endpoint state specified in (9.4) by phase $\eta$
and endpoint-spin value $s$. Return $h_{j,\psi,\sigma}$.

In phase $\psi$ the first list is the $m$-edge path starting at $q$ and
the second list consists of separators. In phase $1-\psi$ the first list
consists of separators and the second list gives $d$ disjoint active
spin pairs, all disjoint from that phase's endpoint spin. Indeed both
endpoint indices are at most $j\le1$, whereas these pairs start at
$L_*\ge j+2$. Let $C$ be the all-zero cylinder of these calls. Independence
within each phase of the one law gives the complete endpoint masses

$$
\begin{aligned}
J_p(C,H_j=h_{j,\psi,\sigma})&=\tfrac12a^{m+1},&
J_p(C,H_j=h_{j,\psi,1-\sigma})&=\tfrac12b^{m+1},\\
J_p(C,H_j=h_{j,1-\psi,\sigma})&=\tfrac12a c^d,&
J_p(C,H_j=h_{j,1-\psi,1-\sigma})&=\tfrac12b c^d.
\end{aligned}
\tag{11.6}
$$

These formulas include $m=0$ and $d=0$. In particular, with
$r_{n,m}=\mathbb P_p(\tau<\infty)$,

$$
\begin{aligned}
r_{n,m}&=\tfrac12(a^{m+1}+b^{m+1}+c^{n-m}),\\
\mathbb P_p(A\ne H_j,\tau<\infty)
&=\tfrac12(b^{m+1}+c^{n-m}),\\
\mathbb P_p(A\ne H_j\mid\tau<\infty)&=f_n(m),\qquad
N=n\ \text{on every path},\qquad \mathbb E_pN=n.
\end{aligned}
\tag{11.7}
$$

Choosing a minimizer attains $z_n$, proving maximality for the stated
class. For $n=0$ this is immediate return. For $n\ge1$,
$0<r_{n,m}<1$: if $m\ge1$, then $a^{m+1}+b^{m+1}<1$; if $m=0$, then
$c^{n-m}<1$. All rejected paths still pay $n$ calls, contributing
$n(1-r_{n,m})$ to the unconditional mean. The construction works with
either $\psi$, either $j$, and either direction of bias. $\square$

**Theorem 11.2 (Integrated bound separated by record type).** Under the
same contract let $Z$ be the event of finite return with all replies zero,
including a return with no calls. Define the random variable $G$ by cases,

$$
G=\begin{cases}
z_N&\text{on }Z,\\
e_N&\text{on }\{\tau<\infty\}\setminus Z,\\
0&\text{on }\{\tau=\infty\}.
\end{cases}
\qquad
\mathbb P_p(A\ne H_j,\tau<\infty)\ge\mathbb E_pG.
\tag{11.8}
$$

The definition makes no evaluation of $z_\infty$ or $e_\infty$.

Proof. For each fixed seed, sum Theorem 11.1's inequality over the all-zero
terminal records and Theorem 10.1's inequality over the other terminal
records. There are countably many finite ordered integer-address/reply
records. Their terminal sections are disjoint, including the empty record,
so integration over the arbitrary independent law $\nu$ and Tonelli's
theorem give (11.8). All masses used before integration are source-section
masses, with no conditioning on a singleton seed or assumed regular
conditional law on the seed space. Finite internal waits supply no extra
observations. Every nonreturn, whether internal divergence after finitely
many calls or an infinite-read path, contributes zero to $G$; its actual
reads remain part of $N$. Measurable completion changes none of these
integrated masses. $\square$

**Theorem 11.3 (Zero-record mass forced by a return budget).** For an
integer $k\ge1$ put

$$
E_k=\{\tau<\infty,N\le k\},\qquad
\rho_k=\mathbb P_p(E_k),\qquad Z_k=E_k\cap Z,\qquad
\beta_k=\frac{c^{\lfloor k/2\rfloor}+c^{\lceil k/2\rceil}}2.
\tag{11.9}
$$

For every protocol of Definition 9.1, without any restriction on reads
outside $E_k$,

$$
\begin{aligned}
\mathbb P_p(Z_k)&\ge(\rho_k+\beta_k-1)_+,\\
\mathbb P_p(A\ne H_j,E_k)
&\ge e_k\rho_k+(z_k-e_k)(\rho_k+\beta_k-1)_+,
\end{aligned}
\tag{11.10}
$$

where $x_+=\max(x,0)$. In particular, almost-sure finite return within $k$
actual calls has unconditional error at least

$$
e_k+(z_k-e_k)\beta_k>e_k.
\tag{11.11}
$$

Proof. For a fixed seed $u$, follow the next-event rules with every reply
specified to be zero, stopping this construction at the $k$th call, a
finite return, or indefinite internal continuation, whichever comes first.
Let $\ell\le k$ be the number of calls collected and let $B(u)$ be the
source cylinder requiring zero at these $\ell$ addresses. At the $k$th
call impose no condition on subsequent actions. The construction is an
analysis of one branch of the rule; it gives the protocol no extra source
access. Let $n_0(u),n_1(u)$ be its actual call counts by parity, so that
$n_0(u)+n_1(u)=\ell$. By (11.3),

$$
J_p(B(u))\ge\tfrac12(c^{n_0(u)}+c^{n_1(u)})\ge\beta_k.
\tag{11.12}
$$

For the last inequality, adding missing units to reach total $k$ can only
decrease the sum. At a fixed total, transferring a unit from a count at
least two larger than the other count decreases the sum, since $0<c<1$.
Thus the integer minimum occurs at the two balanced counts in (11.9).
Repetitions and separator calls are included throughout this argument.

The subset $B$ of the source/seed product with sections $B(u)$ is
measurable: only finitely many next-event choices, each measurable, and
countably many finite address lists are involved. Integrating (11.12)
gives $\mathbb P_p(B)\ge\beta_k$. On $B$, the actual protocol follows the
specified zero branch for all the collected calls. If $\ell<k$, that
branch has already returned or continues internally forever; in the latter
case it cannot lie in $E_k$. If $\ell=k$, a return with at most $k$ calls
has no additional replies. Consequently

$$
B\cap E_k\subseteq Z_k,\qquad
\mathbb P_p(Z_k)\ge\mathbb P_p(B)+\rho_k-1
\ge\beta_k+\rho_k-1.
$$

Nonnegativity proves the first bound in (11.10). Restrict the recordwise
sum in Theorem 11.2 to $E_k$. The two coefficient sequences are
nonincreasing, including their index-zero terms, and therefore

$$
\mathbb P_p(A\ne H_j,E_k)
\ge z_k\mathbb P_p(Z_k)+e_k\mathbb P_p(E_k\setminus Z_k)
=e_k\rho_k+(z_k-e_k)\mathbb P_p(Z_k).
$$

Since $z_k-e_k>0$, the first bound yields the second. With $\rho_k=1$ it
gives (11.11), whose strict inequality uses $\beta_k>0$. Paths outside
$E_k$ can make any finite or infinite number of reads, or diverge
internally; no bound on them entered the construction. $\square$

**Theorem 11.4 (Exact guaranteed-return one-call risk).** For each original
endpoint $j\in\{0,1\}$, among protocols of Definition 9.1 with almost-sure
finite return and at most one actual call, the minimum unconditional state
error is exactly

$$
b+\frac{ac}{2}=1-\frac a2-a^2b.
\tag{11.13}
$$

Proof. The two candidates for $z_1$ have the common denominator $1+c$;
their success numerators are respectively $a$ and $a^2$. Since $a>a^2$,

$$
z_1=\frac{b+c}{1+c},\qquad \beta_1=\frac{1+c}{2},\qquad e_1=b.
$$

Theorem 11.3, including protocols which return without a call on some
seeds, bounds the error below by

$$
b+\left(\frac{b+c}{1+c}-b\right)\frac{1+c}{2}
=b+\frac{ac}{2}.
$$

For equality, ignore the auxiliary variable without changing its law and
read the actual bit at the fixed even address $t=2(j+2)$. Return
$h_{j,0,\sigma}$ on reply one and $h_{j,1,\sigma}$ on reply zero, with
$\sigma$ and the states as in Theorem 11.1. Equivalently the outputs are
$a_\sigma,b_\sigma$ for replies one, zero when $j=0$, and
$b_\sigma,a_\sigma$ for replies one, zero when $j=1$.

In phase zero this bit is $S_{j+2}\mathbin\oplus S_{j+3}$, independent
of the endpoint spin $S_j$; in phase one it is a separator zero. Thus a
one identifies phase zero, while a zero leaves positive mass in both
phases. The zero branch's output has joint success mass $a/2$ from phase
one, without observing that phase. The one branch has joint success mass
$a^2b$. More explicitly the actual joint reply and error masses are

$$
\begin{array}{c|cc}
x&\mathbb P_p(X_t=x)&\mathbb P_p(X_t=x,A\ne H_j)\\ \hline
0&(1+c)/2&(b+c)/2\\
1&ab&ab^2
\end{array}
\tag{11.14}
$$

The rule returns after its one paid call on every path. The total error
is $1-a/2-a^2b$, equal to $b+ac/2$ because $c=1-2ab$. It is legal for
both original endpoints and both directions of bias under the unchanged
stationary law and auxiliary law. $\square$

For $k\ge2$, (11.10)--(11.11) are lower bounds without a general sharpness
assertion. The exact zero-record envelope and its selective witnesses do
not provide a protocol jointly attaining all the recordwise bounds and
the forced zero-record mass at an arbitrary prescribed return probability.
The full joint risk/return-probability/expected-read-cost frontier remains
unresolved. Its total cost is the extended expectation $\mathbb E_pN$
over returning and nonreturning paths, including all repetitions and
separators; replacing it by a mean restricted to returns would discard
the $n(1-r_{n,m})$ charges in (11.7). Internal nonreturn after finitely many
reads and infinite-read nonreturn are distinct allowed cost cases.
Open Problem 6.4's whole-domain attainment and separation question remains
unchanged.

The supplier law, complementary-spin products and terminal-cylinder
reduction are Proposition 2.1, Lemma 3.1 and Theorems 9.2--10.1. The
convexity and finite-product Bayesian comparisons above are elementary;
the source-specific zero-record coefficient, its same-law equality and
the return-budget consequences are `repo-derived`. Classical attribution
remains [Chigansky--van Handel, arXiv:0910.3603v2, Example 10][CVH] for the
fair equality/XOR ambiguity, and [Travers--Crutchfield,
arXiv:1008.4182v3, Definitions 5--8 and Theorem
3](https://arxiv.org/html/1008.4182v3) and
[arXiv:1011.1581v2, §VI Theorem 1 and §VII.1 Proposition
3](https://arxiv.org/html/1011.1581v2) for consecutive-word current-state
synchronization. Their current-state/consecutive-observation statements
do not supply the arbitrary-address, fixed-original-endpoint zero-record
envelope under Definition 9.1. These attributions make no worldwide
priority claim.

## 追加锚（本行以下为增补区）

## 12. Finite representatives for a hard total paid-read budget

**Definition 12.1 (Hard budget and the preserved law).** Retain exactly
Definition 9.1, with the one original $J_p$, fixed public
$0<p<1$, $p\ne1/2$, fixed original endpoint $j\in\{0,1\}$, and the given
independent probability space $(\mathsf U,\mathcal U,\nu)$ with its
unchanged law. Fix $k\in\mathbb N_0$. A pathwise hard total budget means
$N\le k$ on every execution, including nonreturns and exceptional
source/seed paths. An almost-sure hard total budget means
$\mathbb P_p(N\le k)=1$. Neither condition merely bounds the count on
returning paths or on $E_k$.

Set $\mathcal A=\{a_0,a_1,b_0,b_1\}$ and introduce a symbol
$\bot\notin\mathcal A$. The statistics to be preserved are

$$
D=\mathbf1_{\{\tau<\infty\}},\qquad
O=\begin{cases}A&D=1,\\\bot&D=0,\end{cases}
\qquad Z=(H_j,O,D,N).
\tag{12.1}
$$

Under a pathwise cap $Z$ takes values in the following finite alphabet;
under an almost-sure cap it does so almost surely:

$$
\mathcal Z_k=
\{(h,o,d,n):h\in\mathcal A,\ o\in\mathcal A\cup\{\bot\},
 d=\mathbf1_{\{o\ne\bot\}},\ 0\le n\le k\}.
\tag{12.2}
$$

We preserve the joint law of $(u,Z)$ on
$\mathsf U\times\mathcal Z_k$, so the dependence on the given seed is
part of the assertion. Finite numerical return times and the numerical
names of acquired addresses are not coordinates of this law. Equality
of this law is not equality of outputs or counts on each original source
sample. A nonreturn with $N=n$ keeps its $n$ paid calls and means
indefinite internal continuation after those calls; it is not a finite
return with an omitted output.

**Theorem 12.2 (Finite legal deterministic family).** For every $k$ and
either $j$, there is a nonempty finite family
$\mathcal D_{k,j}=\{\Pi_1,\ldots,\Pi_m\}$ of deterministic protocols of
Definition 9.1, each ignoring the auxiliary variable, with the following
properties. Every representative obeys the total cap $k$ on every formal
binary reply branch, including branches of source probability zero, and
all its addresses belong to one finite set $F_{k,j}\subset\mathbb Z$.
For every deterministic protocol with a pathwise hard total budget $k$,
one representative has exactly the same law of $Z$. A deterministic
protocol with only an almost-sure hard total budget has the same law as
a pathwise-capped representative as well. The family and $F_{k,j}$ may
be chosen independently of $p$ throughout the stated parameter range.
The equality holds under the original $J_p$, with neither a phase read
nor a change of target or source.

Proof. First discard the numerical values of finite internal delays,
retaining their distinction from indefinite internal continuation.
Keep the original next-event types, addresses and outputs; replace only
their finite delays by fixed finite delays.
Whenever the next event at a record of length $k$ would be another read,
replace that event by indefinite internal continuation without that read.
This gives a rule capped on every formal branch. On every execution
already having $N\le k$, the boundary replacement changes no event;
erasing finite delays changes only finite timing values. Thus this
normalization preserves $Z$ on all such executions, and preserves its
law under either hard-budget hypothesis.

Unfold the normalized deterministic rule into its binary reply tree.
A node at depth $n$ carries the acquired record of length $n$. It is
either a read node, with two children indexed by the next reply, or a
terminal labelled by one of the four return states or by $\bot$.
A $\bot$ terminal means internal nonreturn with no further call.
The tree has height at most $k$ and at most $2^k-1$ read nodes. Terminal
depth is the actual paid count even at a $\bot$ terminal. Unreachable
formal reply branches may be retained. This ordinary finite-horizon
policy-tree unfolding is classical; it does not yet make the unbounded
integer address labels finite.

Here is the additional source-specific information needed for those
labels. Fix a tree shape, its terminal labels, and the distinct node
positions $v$ in that tree. Write $t_v\in\mathbb Z$ for the address at a
read node, and $\epsilon_v\in\{0,1\}$ for its parity. For each phase
$\phi\in\{0,1\}$ form a finite set of formal spin slots

$$
\mathcal I_\phi=\{*\}\ \cup
\{(v,-),(v,+): v\text{ is a read node and }\epsilon_v=\phi\}.
\tag{12.3}
$$

The distinguished slot $*$ represents the original target spin, whose
index is $q_{j,0}=j$ and $q_{j,1}=0$, exactly as in (9.4). Assign integer
indices to the other slots by

$$
\iota_\phi(*)=q_{j,\phi},\qquad
\iota_\phi(v,-)=\frac{t_v-\phi}{2},\qquad
\iota_\phi(v,+)=\frac{t_v-\phi}{2}+1.
\tag{12.4}
$$

Record the equivalence relation on $\mathcal I_\phi$ given by equality
of these indices. The signature consists of the tree shape and terminal
labels, all node parities, and these two equivalence relations, with the
distinguished slots retained. It refers to all read nodes in the whole
tree at once, including nodes on incompatible reply branches.

Conditional on phase $\phi$, the original iid realization assigns one
independent Bernoulli$(p)$ spin to each equivalence class of
$\mathcal I_\phi$. At an active node the potential reply $X_{t_v}$ is
the XOR of its two class spins; at an inactive node it is zero. The
target is $h_{j,\phi,s}$, the entry in (9.4) with phase $\phi$ and
displayed spin $s$, where $s$ is the class spin of $*$.
Consequently the signature determines the joint conditional law of

$$
\left(H_j,(X_{t_v})_{v\text{ a read node}}\right)
\quad\text{given }\varphi=\phi.
\tag{12.5}
$$

This uses only the original finite iid-spin products of Proposition 2.1.
It includes every overlap and repetition: slots with the same actual
spin index are identified, and all remaining class spins are independent.
Disconnected and distant edges create no extra relation. Negative
addresses obey the same integer formulas (12.4). For inactive nodes no
spin is read or inferred from their compulsory zero. The two
phase-conditional distributions are combined with their original masses
$1/2,1/2$; no joint coupling between two different phase alternatives is
needed. In particular this step does not splice independently optimized
phase laws.

The tree's execution is a deterministic function of its complete
potential-reply array: start at the root, use the reply at each visited
read node, and stop at its terminal. Its terminal label and depth give
$(O,D,N)$. It follows from (12.5) that any two address assignments with
the same signature have the same joint law of $Z$. Recording the
whole array before applying this deterministic function ensures that
adaptively chosen nodes retain their joint relations with the target.

There are finitely many tree shapes and terminal labellings at the fixed
height. For each there are finitely many parity assignments and finitely
many equivalence relations on the finite slot sets. Some signatures
cannot come from integer addresses with the distinguished target at its
fixed original index; discard them. For each signature that is realized,
choose one actual integer-address assignment realizing the entire
signature in both phases simultaneously. Keep that labelled tree as a
representative. This is a finite selection from realized signatures,
not an assertion that arbitrary pairs of abstract incidence relations
are geometrically realizable.

Each selected tree is a legal protocol: make its specified actual reads,
return its terminal state after finite internal waiting, or continue
internally forever at its $\bot$ terminal. It makes at most $k$ calls
on every formal branch. Its finite-event delays can, for example, all be
one unit. Taking the union of the addresses in this finite collection
gives the finite set $F_{k,j}$. The construction of signatures and the
choice of an integer realization involve $k,j$ and integer geometry,
not $p$; the same class-spin argument applies for every allowed $p$.
The normalized input tree has one of these realized signatures, proving
the assertions. When $k=0$ the trees are simply the four immediate
returns and the immediate internal nonreturn, and $F_{0,j}$ may be empty.
$\square$

**Theorem 12.3 (Measurable same-seed representation and converse).** Fix
$k,j,p$ and the original given $(\mathsf U,\mathcal U,\nu)$. Let
$v_i(z)=J_p(Z^{\Pi_i}=z)$ be the finite law vector of representative
$\Pi_i$. For every protocol with a pathwise hard total budget $k$, there
is a measurable function $f:\mathsf U\to\{1,\ldots,m\}$ such that,
for every $B\in\mathcal U$ and $z\in\mathcal Z_k$,

$$
\mathbb P_p(u\in B,Z=z)
=\sum_{i=1}^m\nu(B\cap\{f=i\})v_i(z).
\tag{12.6}
$$

The same assertion holds for an almost-sure hard total budget; its
representing protocol has the pathwise cap. Conversely every measurable
$f$ in (12.6) is attained by a legal pathwise-capped protocol on that
same probability space with its unchanged law $\nu$. Thus the two
budget conventions have exactly the same attainable joint laws of
$(u,Z)$, though they remain different requirements on individual rules.

Proof. Apply the boundary replacement and delay normalization in the
proof of Theorem 12.2 with $u$ fixed. At each seed this leaves a finite
deterministic tree with integer labels. The space of all such trees is
countable: there are finitely many shapes and terminal label patterns,
and a finite tuple of integers for each shape. Give this space its
discrete sigma-algebra.

The tree depends measurably on $u$. To see this without a conditional
probability on singleton seeds, build its nodes successively. The record
at each node takes values in the countable set of finite acquired
integer-address/reply records. Evaluating a measurable next-event rule
at that record is measurable: the preimage of an event is a countable
union over the possible records of the intersection of the event
specifying that record with the corresponding next-event condition.
There are only finitely many node positions through depth $k$.
Induction therefore proves measurability of the tree map. Finite versus
indefinite waiting is part of the measurable event type; its finite
numerical value has been discarded. The finite signature of this
countably valued tree is measurable, so its selected representative
index $f(u)$ is measurable as well.

For each fixed seed, Theorem 12.2's signature argument identifies the
source-section law of the normalized tree with $v_{f(u)}$. For a
pathwise-capped input normalization preserves the source-section law
of $Z$ at every seed, apart from any allowed completion-version choice.
For an almost-sure-capped input the boundary replacement changes $Z$
only on the product-null event $\{N>k\}$; equivalently, by Tonelli it
preserves the source-section law for $\nu$-almost every seed. Integrate
these finite-alphabet section identities over $B$ to obtain (12.6).
No regular conditional distribution on an arbitrary auxiliary space is
being assumed. Allowed measurable completions give the same identities;
with countably many records, measurable versions can be chosen together
and the exceptional null choices do not affect (12.6).

For the converse, at seed $u$ choose the existing representative
$\Pi_{f(u)}$, and follow its tree using only the actual replies of the
same $J_p$ source. This is a measurable next-event rule: the selection
has finitely many measurable seed cells, and each representative has a
fixed finite labelled tree. On records incompatible with the selected
tree, set the next event to internal nonreturn, making the rule total.
Its actions are functions only of $u$ and its acquired record. No source
observation enters the initial selection, and no extra random coin is
introduced. All branches have the pathwise cap, including every internal
nonreturn. Independence of
the original source and the unchanged seed law gives (12.6) for this
protocol. Since pathwise-capped protocols are almost-sure-capped, both
attainable-law sets are therefore identical. $\square$

The representation preserves the joint original target, output or
$\bot$, finite-return indicator, and exact paid-count distribution,
including their correlation with every measurable seed event. In
particular it preserves state-classification error, return probability,
and unconditional paid cost jointly. Repeated reads and separator reads
are still visits to paid nodes; charges are not removed when their
likelihood constraints are redundant. Every nonreturn of a representative
is internal divergence after its terminal number of actual calls.
The representation need not agree with the original rule on a source
sample, and it preserves neither finite return-time values nor literal
address names. It is an existence result for measurable rules; deciding
which arbitrary seed belongs to which cell, or whether a given internal
computation eventually has a next event, receives no effective procedure.

## 13. The exact image of the given seed's measurable partitions

**Definition 13.1 (Partition weights and finite law region).** For the
family in Theorem 12.2 put

$$
\begin{aligned}
W_m(\nu)&=\{(\nu(B_1),\ldots,\nu(B_m)):\\
&\qquad B_1,\ldots,B_m\in\mathcal U\text{ form a measurable partition of }
\mathsf U\},\\
\mathcal V_{k,j,p,\nu}
&=\left\{\sum_{i=1}^m w_i v_i:w\in W_m(\nu)\right\}.
\end{aligned}
\tag{13.1}
$$

Empty cells are permitted, and completed measurable partitions may be
replaced by versions without changing their measures. The region
$\mathcal V_{k,j,p,\nu}$ records the law of $Z$ after forgetting the
seed coordinate. Its full seed-dependent counterpart is precisely the
set of measures specified on rectangles by

$$
\mu(B\times\{z\})
=\sum_{i=1}^m\nu(B\cap B_i)v_i(z),
\qquad B\in\mathcal U,\quad z\in\mathcal Z_k,
\tag{13.2}
$$

as the same measurable partitions vary. Formula (13.2), rather than
just the weights in (13.1), retains the seed dependence.

**Theorem 13.2 (Exact finite region, compactness, and its atomless
specialization).** The attainable laws of $Z$ under either hard-budget
convention are exactly $\mathcal V_{k,j,p,\nu}$, and their joint laws
with the given seed are exactly (13.2). The finite-dimensional set
$\mathcal V_{k,j,p,\nu}$ is compact for every given probability space,
including atomic spaces. If $\nu$ is atomless, then

$$
W_m(\nu)=\Delta_m
:=\{w\in[0,1]^m:\textstyle\sum_iw_i=1\},\qquad
\mathcal V_{k,j,p,\nu}=\operatorname{conv}\{v_1,\ldots,v_m\}.
\tag{13.3}
$$

For a general given seed, (13.1) is the exact region; replacing
$W_m(\nu)$ by $\Delta_m$ requires proof of the needed partition
availability and is not part of the representation theorem.

Proof. Theorems 12.2--12.3 give both inclusions, first with the seed
retained and then by taking $B=\mathsf U$ in (13.2). For compactness use
the classical decomposition-range result of Dvoretzky, Wald and
Wolfowitz, *Relations among certain ranges of vector measures*, Pacific
Journal of Mathematics **1**, 59--74, Section 1 and Section 3,
Remark (c), p. 68 [DWW]. In their notation take the underlying measurable
space to be $(\mathsf U,\mathcal U)$, take the single measure
$\mu_1=\nu$, and take their number of decisions to be $n=m$. A pure
probability $m$-vector is exactly
$(\mathbf1_{B_1},\ldots,\mathbf1_{B_m})$ for a measurable partition.
Its decomposition-range vector is
$(\int\mathbf1_{B_i}\,d\nu)_{i=1}^m=w$; hence their decomposition range
is precisely $W_m(\nu)$. The measure is finite and nonnegative with
$\nu(\mathsf U)=1$. Remark (c) keeps compactness without atomlessness,
while explicitly withdrawing general convexity. The finite linear map
$w\mapsto\sum_iw_iv_i$ is continuous, so its image is compact.

When $\nu$ is atomless, their Section 3, Lemma 2 gives a partition with
any prescribed nonnegative weights summing to one, by taking again the
one finite measure $\mu_1=\nu$. Equivalently, Theorem 4 identifies its
pure range with the full probability-vector range, which in this
one-measure case is $\Delta_m$: constant probability vectors already
realize every point of that simplex. This proves (13.3). This is a
classical partition corollary, not a new purification theorem or a
change to the given seed. No compactness assertion about a space of
seed-dependent measures in an unspecified topology is used. $\square$

**Boundary 13.3 (Atoms cannot be split by the selector).** The classical
atomic/atomless decomposition makes the restriction explicit. Let
$(C_\ell)$ be disjoint measurable atoms of positive masses
$\alpha_\ell$, exhausting the atomic part modulo null sets, and let
$r=1-\sum_\ell\alpha_\ell$ be the mass of the atomless remainder.
There are at most countably many such atoms; they need not be singleton
points. With $e_i$ the coordinate unit vectors,

$$
W_m(\nu)=
\left\{r w+\sum_\ell\alpha_\ell e_{i_\ell}:
 w\in\Delta_m,\ i_\ell\in\{1,\ldots,m\}\right\}.
\tag{13.4}
$$

Each atom lies, up to null sets, wholly in one partition cell. Conversely
allocate those whole atoms to the selected cells, and partition the
atomless remainder with the proportions $w$, using DWW Lemma 2 for the
restricted finite measure. This gives (13.4), including $r=0$, when
the $w$ term vanishes. This is the usual one-measure decomposition
underlying DWW Remark (c).

For example, take $k=0$ and a one-atom probability space. The only
possible return probabilities are zero and one: before any read the
seed-measurable return indicator is constant almost surely. Immediate
return of $a_0$ and immediate internal nonreturn are both legal, but
their half-and-half mixture of $Z$ laws has return probability $1/2$
and is unattainable on this space. Thus even the finite law region
need not be convex. The obstruction already occurs without any address
geometry. At larger budgets a deterministic tree can also obtain
random replies from the original source; those replies are already
included in its $v_i$, and do not authorize replacing the seed-partition
restriction by an independent coin.

**Corollary 13.4 (Hard-budget risk, return, and paid-cost attainment).**
For $v\in\mathcal V_{k,j,p,\nu}$ define

$$
\begin{aligned}
Q(v)&=\sum_{(h,o,d,n)\in\mathcal Z_k}d\,v(h,o,d,n),\\
\Lambda(v)&=\sum_{(h,o,d,n)\in\mathcal Z_k}
 d\,\mathbf1_{\{o\ne h\}}v(h,o,d,n),\\
C(v)&=\sum_{(h,o,d,n)\in\mathcal Z_k}n\,v(h,o,d,n).
\end{aligned}
\tag{13.5}
$$

Their exact jointly attainable region is

$$
\{(Q(v),\Lambda(v),C(v)):v\in\mathcal V_{k,j,p,\nu}\}
=\left\{\sum_{i=1}^m w_i(Q(v_i),\Lambda(v_i),C(v_i)):
 w\in W_m(\nu)\right\}.
\tag{13.6}
$$

For every attainable prescribed return probability $q$, the minimum
of $\Lambda(v)$ subject to $Q(v)=q$ is attained. More generally, the
same is true on any nonempty closed subset of the finite law region,
including one imposing also $C(v)\le c_0$ for a prescribed real $c_0$.
The cost $C(v)=\mathbb E_pN$ includes every nonreturning path; its
nonreturn contribution is exactly

$$
\sum_{h\in\mathcal A}\sum_{n=0}^k n\,v(h,\bot,0,n).
\tag{13.7}
$$

Proof. All three functions in (13.5) are finite linear functions of the
law coordinates, and Theorem 13.2 and its converse give (13.6). The
slice $Q(v)=q$ is a nonempty closed subset of the compact finite law
region. The extra weak cost inequality is also closed. Any nonempty
closed subset is compact, and the continuous function $\Lambda$
attains its minimum there. The representing measurable partition and
Theorem 12.3 realize each minimizing vector with the same seed law.
The sum in (13.7) is the part of $C$ with $D=0$, not a return-conditioned
mean. This proof asserts attainment under a fixed finite hard cap;
it does not evaluate the minimum. $\square$

## 14. Projection to the paid-return frontier without a hard cap

**Theorem 14.1 (Exact budgeted-return projection).** Use the same
$p,j,\nu$ as in
[Paid-return, Definitions 1.3 and 6.1][PR], and let
$\mathcal R_{k,\nu}$ denote that source's attainable region of pairs
$(q_k,L_k)$ over all protocols of Definition 9.1, with arbitrary behavior
outside $E_k$. Then

$$
\mathcal R_{k,\nu}
=\{(Q(v),\Lambda(v)):v\in\mathcal V_{k,j,p,\nu}\}.
\tag{14.1}
$$

Consequently $\mathcal R_{k,\nu}$ is compact for every given seed law,
and its infimum $\mathcal L_{k,\nu}(q)$ at each attainable mass is a
minimum realized by a pathwise hard-total-budget-$k$ protocol with the
same seed. For an atomless seed, (14.1) is the convex hull of the finite
points $(Q(v_i),\Lambda(v_i))$; for an arbitrary seed the exact formula
uses $w\in W_m(\nu)$.

Proof. The supplier's Assumption 1.1 is the same realization (2.2),
its target table (1.2) is (9.4), and its Definition 1.2 is precisely
Definition 9.1. Its $q_k,L_k$ in Definition 1.3 are, respectively, the
mass and joint error on $E_k=\{\tau<\infty,N\le k\}$; they impose no
constraint on later-return or nonreturning paths. Thus the only extra
restriction used in $\mathcal V_{k,j,p,\nu}$ is the hard total cap.

Given any unrestricted protocol $\Pi$, define $\Pi^{[k]}$ by following
its original next-event rule, except that at a record of length $k$ a
next read is replaced by indefinite internal continuation with no
further read. A next return at that record is kept, including its
finite internal waiting, as is internal nonreturn. At shorter records
all events are kept. The decision being replaced is a measurable
function only of the seed and that acquired record, so this rule is
legal and nonanticipating; it does not need to know the source's future
or the outcome of an additional read.

On the same source/seed sample the two rules agree until a replaced
request. Hence, with the convention $\min(\infty,k)=k$,

$$
\begin{aligned}
\{\tau^{[k]}<\infty\}&=E_k^\Pi,\\
O^{[k]}&=\begin{cases}A^\Pi&E_k^\Pi,\\\bot&\text{otherwise},\end{cases}\\
N^{[k]}&=\min(N^\Pi,k).
\end{aligned}
\tag{14.2}
$$

The count identity includes a nonreturn after fewer than $k$ calls,
a nonreturn after more than $k$ calls, an infinite-read path, and a
return originally after more than $k$ calls. When $k=0$, a zero-read
finite return is kept and every first read is suppressed. The rule has
a hard cap on every branch. It preserves $q_k,L_k$, including their
joint dependence on the endpoint and seed on the retained return
sections. Therefore every unrestricted pair belongs to the right side
of (14.1), by Theorem 12.3. Conversely every hard-capped protocol is an
unrestricted admissible protocol, and on it $E_k=\{D=1\}$, so the pair
is $(Q(v),\Lambda(v))$. This proves (14.1).

The continuous projection of the compact finite law region is compact.
Its nonempty fixed-$q$ slice has a minimum second coordinate, or
Corollary 13.4 may be applied directly. The same-seed converse supplies
a legal hard-capped minimizer. The atomless and general partition
formulas follow from Theorem 13.2. $\square$

The projection argument does not preserve an unrestricted protocol's
whole law or its whole paid cost. In (14.2), finite returns requiring
more than $k$ calls become nonreturns and paid counts above $k$ become $k$.
In particular

$$
\mathbb E_pN^{[k]}=\mathbb E_p\min(N^\Pi,k)\le\mathbb E_pN^\Pi,
\tag{14.3}
$$

with all costs on newly nonreturning paths retained at their truncated
counts. The full-law equality in Theorem 12.3 applies to hard-capped
inputs; (14.1) for unrestricted inputs is only the stated two-coordinate
projection. It gives no equality of attainable regions if an
unrestricted total-cost coordinate or a constraint on later returns is
also imposed without a separate proof.

**Corollary 14.2 (An absent one-read equality gate gives a strict gap).**
Let $f(q)$ be the universal one-read lower curve in
[Paid-return, Theorem 4.1, (4.1)--(4.2)][PR]. At an attainable
$q\in[0,1]$, let $g(q)$ be the required seed-event mass in its (4.3),
using its lower formula at $q=\eta$. Then

$$
\mathcal L_{1,\nu}(q)=f(q)
\quad\Longleftrightarrow\quad
\exists G\in\mathcal U:\nu(G)=g(q).
\tag{14.4}
$$

If that event is absent and $q$ is attainable, then
$\mathcal L_{1,\nu}(q)>f(q)$. No value or uniform positive lower bound
for this gap is asserted.

Proof. The quoted theorem already proves the universal inequality
and the exact necessary and sufficient event condition for equality
by any protocol, under this same law, target, seed and return-event
convention. Theorem 14.1 adds that the infimum on every nonempty
fixed-$q$ slice is attained. Thus equality of the minimum with $f(q)$
requires, and the quoted equality construction supplies, precisely
that gate. If it is unavailable, the attained minimum cannot equal
the lower bound, and must be strictly greater. This does not repeat
the numerical envelope proof or compute an optimum above it. $\square$

## 15. Sources and boundaries of the finite-budget representation

The original-law suppliers are Proposition 2.1 and (2.2), the fixed
endpoint table (9.4), and the finite-record semantics of Theorems
9.2--11.4. Their likelihood inequalities, sharp selective witnesses,
zero-record coefficients and one-read guaranteed-return optimum are
retained as existing results. The finite whole-tree spin-slot signature
in Theorem 12.2 supplies the additional arbitrary-address reduction;
Theorem 12.3 supplies its measurable same-given-seed and joint-law
form. These are repo-derived ordinary mathematical consequences of
the original XOR realization, without a worldwide originality claim.

Kaelbling, Littman and Cassandra, *Planning and Acting in Partially
Observable Stochastic Domains*, Artificial Intelligence **101**,
99--134, Sections 2.1 and 4.1, pp. 101--102 and 108--110 [KLC], provide
the classical finite-horizon policy-tree background. Their finite
state/action model and scalar value-function representation alone do
not reduce this contract's unbounded integer addresses, give its full
joint target/output/return/count law, or discharge its fixed-seed
partition requirement. The finite tree unfolding is reused as ordinary
background; the simultaneous two-phase integer-realizable signature
and original-target relation are established in Section 12.

Dvoretzky, Wald and Wolfowitz [DWW], Section 1 and Section 3, Theorem 4,
Lemma 2 and Remark (c), supply exactly the classical partition-range
facts used in Section 13. Their single finite measure here is the given
seed law, not the source law or a newly introduced randomizer. The
finite family is selected before applying those facts. Compactness
for atomic seeds and unrestricted simplex weights for atomless seeds
are different conclusions with different hypotheses. The partition
image, compact projections and continuous minima are applications of
these classical results, not new general vector-measure theorems.

The consumer [Paid-return, Definitions 1.3 and 6.1 and Theorem 4.1][PR]
already owns its return-mass coordinates, one-read lower curve and exact
equality gate. The additional link is (14.1), which justifies minimum
attainment for that region under every given seed, and the strict
qualitative gap in Corollary 14.2 when a gate is absent. A finite
representative family is not a closed-form numerical frontier. No
general larger-budget optimum, optimal adaptive rule, minimal dictionary,
sharp address radius or algorithm for arbitrary seed laws is supplied.

All statements fix a finite total hard budget when preserving the full
law. They assert neither an effective compiler nor bounded memory,
finite precision, bounded internal work, a physical implementation, or
an online quotient valid for unbounded histories. No compactness
uniform in $k$, exchange of an unbounded-budget limit with optimization,
or unbounded expected-paid-cost optimum follows. Internal nonreturn
costs stay in (13.7); the restricted cost change in (14.3) is explicit.
The fixed public bias, original stationary law, both original endpoints,
all paid calls and unchanged independent seed remain as in Definition
9.1. Neither the fair parameter nor the parameter endpoints are added
to that contract. Renewal constructions, native and quantum control
models, and Green-function sources concern different operations and
supply no transfer to the original XOR acquisition problem here.
Open Problem 6.4 remains unchanged.

[DWW]: https://msp.org/pjm/1951/1-1/pjm-v1-n1-p06-s.pdf
[KLC]: https://people.csail.mit.edu/lpk/papers/aij98-pomdp.pdf
[PR]: FIB_PAID_READ_RETURN_MASS_AND_ENDPOINT_RISK_FRONTIER.md

## 追加锚（本行以下为增补区）
