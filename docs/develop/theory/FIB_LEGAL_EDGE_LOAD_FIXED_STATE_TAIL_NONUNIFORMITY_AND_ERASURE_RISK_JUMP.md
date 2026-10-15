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
