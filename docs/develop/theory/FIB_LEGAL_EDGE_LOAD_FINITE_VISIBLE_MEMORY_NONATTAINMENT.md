# Fibonacci harmonic-edge load: finite visible-memory nonattainment

## 1. Original domains and the nonattainment theorem

**Definition 1.1 (Complete open-word graphs).** For every integer $n\ge1$, let

$$
B_n=\{b\in\{0,1\}^n:b_jb_{j+1}=0\text{ for }1\le j<n\}.
$$

The graph $\Gamma_n$ has vertex set $B_n$ and all Hamming-one edges between its vertices. There is no constraint between the last and first bits. Thus $0^n$ and every legal word beginning or ending with $1$ are included. Write $b_0=b_{n+1}=0$ for the purpose of testing an upward flip. Each edge is uniquely $\{b,b+e_i\}$ with $b_{i-1}=b_i=b_{i+1}=0$.

**Definition 1.2 (Harmonic objective).** On the entire probability simplex $\mathcal P(B_n)$, define

$$
h(s,t)=\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}
\qquad
\Phi_n(\mu)=\sum_{\{b,c\}\in E(\Gamma_n)}h(\mu(b),\mu(c)).
\tag{1.1}
$$

**Convention 1.3 (Owned growth and duality).** The results [Growth], Theorems 3.2 and 5.2, give

$$
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu),\qquad
c_\star=\lim_{n\to\infty}\frac{\kappa_n}{n}.
\tag{1.2}
$$

Here $\kappa_n$ is exactly the original squared-share minimax on $\Gamma_n$. These identities, including their complete domains, are reused; no numerical value of $c_\star$ is needed.

**Definition 1.4 (Permitted visible laws).** Let

$$
\mathcal X=\{x\in\{0,1\}^{\mathbb Z}:x_ix_{i+1}=0\text{ for every }i\in\mathbb Z\},
\qquad (Tx)_j=x_{j+1}.
$$

A permitted law is a normalized, two-sided, stationary probability law $P$ on $\mathcal X$ with positive probability for every legal finite cylinder. It has visible order at most $k\ge1$ if there is a kernel $K_P(a\mid u)$, $u\in B_k$, such that the conditional distribution of the next bit given its entire visible past depends only on its last $k$ bits and equals this kernel. Each row sums to one over the legal extensions $ua\in B_{k+1}$, and each such extension has positive probability. In particular a row whose last bit is $1$ has its sole legal extension $0$ with probability one. Let $P_n$ denote the actual $n$-bit marginal of this one law, at any translated interval. Whenever the limit exists, put

$$
d(P)=\lim_{n\to\infty}\frac{\Phi_n(P_n)}n.
\tag{1.3}
$$

**Theorem 1.5 (Universal pointwise nonattainment).** For every integer $m\ge1$ and every permitted law $Q$ of visible order at most $m$, the limit $d(Q)$ exists. There are $\varepsilon_Q>0$ and one family of permitted laws $(Q_t)_{0\le t<\varepsilon_Q}$ on the same visible bits, with $Q_0=Q$ and visible order at most $2m$, such that for every $0<t<\varepsilon_Q$,

$$
d(Q)<d(Q_t)\le c_\star.
\tag{1.4}
$$

Consequently $d(Q)<c_\star$ for every permitted finite visible-order law. Every $Q_t$ is stationary, normalized and positive on all legal finite cylinders and all legal next extensions; its marginals at all lengths belong to that same law. The proof is given in §6 after the local obstruction and compatible perturbation have been established.

## 2. Actual cylinders, binary risk and boundary contributions

**Lemma 2.1 (Coordinate fibers, including zero masses).** For $1\le i\le n$, let

$$
\Phi_{n,i}(\mu)=
\sum_{\substack{b\in B_n\\b_{i-1}=b_i=b_{i+1}=0}}
h(\mu(b),\mu(b+e_i)).
$$

Then $\Phi_n(\mu)=\sum_{i=1}^n\Phi_{n,i}(\mu)$ and

$$
0\le\Phi_{n,i}(\mu)\le\frac14.
\tag{2.1}
$$

Moreover $\Phi_{n,i}(\mu)$ is the conditional Bayes squared-error risk for the bit at $i$, given every other bit in this finite word.

**Proof.** Fix the other $n-1$ bits. A nonempty legal fiber has either two words, with center bits $0,1$, or the single word with center $0$ forced by a neighboring $1$. For a two-word fiber with masses $s,t$ and $s+t>0$, its center posterior is $p=t/(s+t)$ and

$$
s p^2+t(1-p)^2=\frac{st}{s+t}=h(s,t).
\tag{2.2}
$$

This also holds when exactly one mass is zero. If $s=t=0$, the fiber has zero probability, its conditional action may be chosen arbitrarily, and both its weighted risk and $h(0,0)$ are zero. A singleton has posterior zero and risk zero. Thus no division by a zero-total fiber is used. Each two-word fiber is precisely one original coordinate edge, proving the risk identity and the sum decomposition. Coordinate edges form a matching, and

$$
h(s,t)\le\frac{s+t}{4}
$$

follows from $(s-t)^2\ge0$, also at $(0,0)$. The total mass of the endpoints in a matching is at most one, proving (2.1). This includes the unique coordinate at $n=1$ and every open endpoint. $\square$

**Proposition 2.2 (Full-word cancellation and the exterior posterior).** Let $P$ be permitted of visible order at most $k$, and put $\pi_P(u)=P_k(u)$. For $n\ge k$,

$$
P_n(b)=\pi_P(b_1\cdots b_k)
\prod_{j=k+1}^nK_P(b_j\mid b_{j-k}\cdots b_{j-1}).
\tag{2.3}
$$

For shorter words use the marginals of $\pi_P$. For an original upward edge $c=b+e_i$ with $n\ge k$, define

$$
J_{n,i}=[k+1,n]\cap[i,i+k]\cap\mathbb Z.
$$

Then its actual full-word ratio is

$$
\frac{P_n(c)}{P_n(b)}=
\frac{\pi_P(c_1\cdots c_k)}{\pi_P(b_1\cdots b_k)}
\prod_{j\in J_{n,i}}
\frac{K_P(c_j\mid c_{j-k}\cdots c_{j-1})}
{K_P(b_j\mid b_{j-k}\cdots b_{j-1})}.
\tag{2.4}
$$

In particular the initial factor cancels for $k+1\le i\le n-k$, and the ratio depends only on the radius-$k$ window about $i$.

To describe this common ratio, set $\varphi_P(ua)=\log K_P(a\mid u)$ on $B_{k+1}$. If $x_{-1}=x_1=0$, let $x^{(a)}$ replace the center of $x$ by $a$ and put

$$
H_P(x)=\sum_{j=-k}^{0}
\left[\varphi_P(x^{(1)}_{[j,j+k]})
-\varphi_P(x^{(0)}_{[j,j+k]})\right],\qquad
p_P(x)=\frac{e^{H_P(x)}}{1+e^{H_P(x)}}.
\tag{2.5}
$$

If a neighboring bit is $1$, put $p_P(x)=0$. The function $p_P$ is independent of $x_0$, depends only on the radius-$k$ exterior, and is a version of $P(X_0=1\mid X_j,\ j\ne0)$. On each exterior allowing both center choices it belongs to $(0,1)$.

**Proof.** The chain rule and the visible-order hypothesis give (2.3). All legal initial marginals and transition factors are positive. Division of its two full-word products gives (2.4): a transition factor can change only when its block contains $i$, and no other factor is discarded. For an interior coordinate these changed blocks are exactly the $k+1$ translates in (2.5).

For a conditioning window $[-N,N]$ with $N\ge k$, conditioning on all its bits except the center gives precisely this insertion ratio by (2.4); the left initial $k$-block does not include the center. Full cylinder support makes every legal conditioning context positive. A neighbor equal to $1$ forces the center to zero. The conditional probabilities therefore equal $p_P$ in every such window. Bounded conditional-expectation convergence for the increasing exterior sigma-algebras gives the same version for the entire exterior. Equivalently, the conditional identity against every exterior cylinder event extends to their generated sigma-algebra. No logarithm of an illegal transition or zero legal probability is taken. $\square$

**Remark 2.3 (Endpoints and cuts).** Formula (2.4) retains the initial marginal when it changes, the truncated list of transition factors near the last endpoint, and empty products. In particular

$$
P_n(0^n)=\pi_P(0^k)K_P(0\mid0^k)^{n-k}>0\qquad(n\ge k).
$$

Every shorter all-zero cylinder and every legal endpoint-one cylinder is also positive. A cut at any other coordinate retains the same joint factorization; there is no new independence assumption or edge restriction at a cut or seam.

**Lemma 2.4 (Density from one coherent law).** Define the local function

$$
\ell_P(x)=(x_0-p_P(x))^2,\qquad
D_P=\mathbb E_P\ell_P=\mathbb E_P[p_P(1-p_P)].
\tag{2.6}
$$

For $n\ge2k+1$,

$$
\Phi_n(P_n)=(n-2k)D_P+E_n,\qquad 0\le E_n\le k/2,
\tag{2.7}
$$

where $E_n$ is exactly the sum of the original coordinate contributions at $1,\ldots,k,n-k+1,\ldots,n$. For every $n\ge1$,

$$
\left|\Phi_n(P_n)-nD_P\right|\le k/2.
\tag{2.8}
$$

Thus $d(P)=D_P$ exists, $0\le d(P)\le1/4$, and $d(P)\le c_\star$.

**Proof.** Conditional expectation using Proposition 2.2 gives (2.6). At an interior coordinate, the actual finite-word posterior is $p_P$ on its local exterior. Lemma 2.1 and stationarity therefore give $\Phi_{n,i}(P_n)=D_P$. In terms of paired outside completions, their masses $(s_\omega,t_\omega)$ obey $t_\omega=R s_\omega$ with the same positive $R$ for each fixed interior context. Hence the grouping used here is the exact joint identity

$$
\sum_\omega h(s_\omega,t_\omega)
=h\left(\sum_\omega s_\omega,\sum_\omega t_\omega\right).
\tag{2.9}
$$

Both sums are cylinders of that same law. This is the extension of the full-word grouping in [TwoStep], Proposition 2.4 and Theorem 3.1, to an arbitrary finite visible order.

Lemma 2.1 bounds each of the retained $2k$ boundary contributions by $1/4$, proving (2.7). Taking an interior coordinate at length $2k+1$ also bounds $D_P$ by $1/4$. For $n\ge2k+1$, both $E_n$ and $2kD_P$ lie in $[0,k/2]$, giving (2.8). For $n\le2k$, both $\Phi_n(P_n)$ and $nD_P$ lie in $[0,n/4]$, giving the same bound. Divide by $n$ and use (1.2) with $\Phi_n(P_n)\le\kappa_n$. $\square$

**Lemma 2.5 (Exact conditional square discrepancy).** If $P,Q$ are two permitted finite visible-order laws, then

$$
\mathbb E_P\ell_Q
=d(P)+\mathbb E_P[(p_P-p_Q)^2].
\tag{2.10}
$$

**Proof.** The functions $p_P,p_Q$ are defined on every legal exterior, so the second is meaningful under $P$ as well. Expand

$$
(X_0-p_Q)^2=(X_0-p_P)^2
+2(X_0-p_P)(p_P-p_Q)+(p_P-p_Q)^2.
$$

The cross term has zero conditional expectation given the exterior under $P$, by Proposition 2.2. Lemma 2.4 identifies the first expectation with $d(P)$. In a forced-zero exterior both posteriors are zero. This is the scalar binary squared-loss identity, with its exact conditional hypotheses, rather than a log-loss or entropy formula. $\square$

## 3. A nonzero interaction at the least visible order

**Lemma 3.1 (Endpoint interaction).** Let $r\ge1$ be the least visible order of a permitted finite-order law $Q$. Put $K=K_Q$ at that order and $\varphi(ua)=\log K(a\mid u)$ on $B_{r+1}$. If $r\ge2$, there is $w\in B_{r-1}$ beginning and ending in $0$ such that

$$
J(w)=\varphi(1w1)-\varphi(1w0)-\varphi(0w1)+\varphi(0w0)\ne0.
\tag{3.1}
$$

**Proof.** A full-support order-zero law would be iid with positive one-bit probability for $1$, contradicting the prohibition of $11$. Thus the least order is positive. Suppose $r\ge2$ and all differences (3.1) vanish. For every legal suffix $w$ of length $r-1$, compare $K(\cdot\mid0w)$ and $K(\cdot\mid1w)$ whenever both histories are legal.

If $w$ begins with $1$, only history $0w$ is legal. If $w$ ends with $1$, the next bit is forced to $0$, so all available rows agree. In the remaining case $w$ begins and ends with $0$, both center choices in each row are positive, and $J(w)=0$ says

$$
\frac{K(1\mid1w)}{K(0\mid1w)}
=\frac{K(1\mid0w)}{K(0\mid0w)}.
$$

Row normalization forces these two binary distributions to coincide. In all cases $K(a\mid bw)=K(a\mid0w)$ on every legal history $bw$. The normalized kernel $K'(a\mid w)=K(a\mid0w)$ therefore represents the conditional next-bit distribution of the same law given its entire past. It has order at most $r-1$, contradicting minimality. $\square$

## 4. Unequal periodic averages of the local loss

**Proposition 4.1 (Finite endpoint obstruction).** For $Q$ and $r$ as in Lemma 3.1, set $L=4r+3$ and

$$
F(z)=\sum_{j=0}^{L-1}\ell_Q(T^jz)
$$

for every legal $L$-periodic configuration $z$. These totals are not all equal. In particular there is such a $z$ with

$$
\beta=F(z)/L\ne d(Q).
\tag{4.1}
$$

**Proof.** The loss $\ell_Q$ depends only on a radius-$r$ window. For bits $a,b$ at positions $-r,r$ and fixed other bits, write the mixed endpoint difference as

$$
\Delta F=F_{11}-F_{10}-F_{01}+F_{00}.
$$

Since $L>4r$, the only radius-$r$ window on this period that can contain both endpoints is the window centered at $0$. Indeed the direct distance between them is $2r$, while the other circular distance is $L-2r>2r$. A window containing both along the shorter arc must have center $0$. Every other local term depends on at most one endpoint and cancels in $\Delta F$.

If $r=1$, the insertion posterior at zero neighbors is the constant

$$
p=\frac{R}{1+R}\in(0,1),\qquad
R=\frac{K(1\mid0)}{K(0\mid0)^2},
$$

because $K(0\mid1)=1$. Take the four periodic configurations with center $0$, endpoints $a,b$ at $-1,1$, and all other sites zero. All four are legal. At the center their losses are $p^2$ for $(a,b)=(0,0)$ and zero otherwise, since an endpoint $1$ forces the center to zero. Thus $\Delta F=p^2>0$, proving unequal totals.

Now let $r\ge2$ and choose $w$ with $J=J(w)\ne0$ from Lemma 3.1. In the positions $[-r,r]$ place

$$
a\,w\,c\,w\,b,
\qquad a,b,c\in\{0,1\},
\tag{4.2}
$$

and set all other positions in a period to zero. All eight configurations are legal: $w$ begins and ends in zero, and the exterior zeros separate the period seam and the endpoints. For each fixed $c$, taking $\Delta F$ isolates the center loss as above.

In (2.5), only the block $[-r,0]$ includes the left endpoint and only $[0,r]$ includes the right endpoint. The left endpoint's change in the center log odds is

$$
[\varphi(1w1)-\varphi(1w0)]
-[\varphi(0w1)-\varphi(0w0)]=J,
$$

and the right endpoint's change is

$$
[\varphi(1w1)-\varphi(0w1)]
-[\varphi(1w0)-\varphi(0w0)]=J.
$$

There is no block containing the center and both endpoints. The same oriented word $w$ was used on each side; no reflection symmetry of $Q$ is assumed. For some real $u$, the center posterior is therefore

$$
p_{ab}=\sigma(u+(a+b)J),\qquad
\sigma(v)=\frac{e^v}{1+e^v},
\tag{4.3}
$$

independently of the current center label $c$.

If all eight totals were equal, their mixed differences would vanish both for $c=0$ and for $c=1$. With $p_0=\sigma(u)$, $p_1=\sigma(u+J)$ and $p_2=\sigma(u+2J)$ this would give

$$
p_2^2-2p_1^2+p_0^2=0,\qquad
(1-p_2)^2-2(1-p_1)^2+(1-p_0)^2=0.
\tag{4.4}
$$

Subtracting yields $p_2-2p_1+p_0=0$. Substitution in the first equality gives $2(p_1-p_0)^2=0$, contradicting strict monotonicity of $\sigma$ and $J\ne0$. Thus the totals cannot all be equal. At least one differs from $Ld(Q)$, proving (4.1). $\square$

**Remark 4.2 (Role of periodic configurations).** These configurations supply auxiliary stationary orbit measures and a test of a finite local function. They do not impose periodic boundary conditions on $B_n$, remove edges from $\Gamma_n$, or replace the law $Q$. Their orbit measures may have zero cylinder masses; those measures will only provide a perturbation direction, not the permitted improving law.

## 5. Positive stationary cylinder-flow perturbations

**Proposition 5.1 (One actual visible-order law from a positive flow).** Let $M\ge1$. Regard a legal word $e\in B_{M+1}$ as an edge from its first $M$ bits to its last $M$ bits. Suppose a vector $f(e)>0$ has total one and satisfies, for every $u\in B_M$,

$$
\sum_{a:ua\in B_{M+1}}f(ua)
=\sum_{b:bu\in B_{M+1}}f(bu).
\tag{5.1}
$$

There is a permitted stationary visible-order-at-most-$M$ law $P^f$ whose $(M+1)$-word marginal is exactly $f$.

**Proof.** Set

$$
\pi_f(u)=\sum_{a:ua\text{ legal}}f(ua)>0,\qquad
K_f(a\mid u)=\frac{f(ua)}{\pi_f(u)}.
\tag{5.2}
$$

The kernel is normalized and positive on precisely the legal extensions. The state transition is $u=u_1\cdots u_M\longmapsto u_2\cdots u_Ma$. Conservation (5.1) gives its stationarity explicitly:

$$
\sum_{b:bu\text{ legal}}\pi_f(bu_1\cdots u_{M-1})
K_f(u_M\mid bu_1\cdots u_{M-1})
=\sum_{b:bu\text{ legal}}f(bu)=\pi_f(u).
$$

The stationary two-sided state chain, supported on these overlap edges, thus defines a bit process. More explicitly its probabilities are, for $n\ge M$,

$$
P^f_n(b)=\pi_f(b_1\cdots b_M)
\prod_{j=M+1}^nK_f(b_j\mid b_{j-M}\cdots b_{j-1}),
\tag{5.3}
$$

with shorter cylinders the corresponding marginals of $\pi_f$. Summing a final bit uses a row sum equal to one; summing an initial bit uses the incoming conservation identity. These give both endpoint consistency and translation-invariant cylinder distributions, hence one normalized stationary law on $\mathbb Z$. Its state is exactly the last $M$ visible bits, so its visible next-bit dependence is at most $M$. Each legal cylinder has positive mass in (5.3), including shorter cylinders by marginalization. At length $M+1$, (5.3) equals $f(ua)$. $\square$

**Lemma 5.2 (A signed positive flow through the original law).** Fix a permitted $Q$ of least order $r$, let $M=2r$, and choose $z,\beta$ from Proposition 4.1. Define, for $e\in B_{M+1}$,

$$
q(e)=Q_{M+1}(e),\qquad
v(e)=\frac1L\sum_{j=0}^{L-1}\mathbf1\{z_{[j,j+M]}=e\},
$$

and put

$$
\delta=|\beta-d(Q)|>0,\qquad
s=\operatorname{sign}(\beta-d(Q)),\qquad
\alpha=\min_{e\in B_{M+1}}q(e)>0,
\qquad f_t=q+s t(v-q).
\tag{5.4}
$$

For $|t|\le\alpha/4$, $f_t$ is a positive normalized stationary flow. The law $Q_t=P^{f_t}$ from Proposition 5.1 has visible order at most $M$, satisfies $Q_0=Q$, and obeys

$$
\mathbb E_{Q_t}\ell_Q=d(Q)+\delta t.
\tag{5.5}
$$

**Proof.** Stationarity of $Q$ gives conservation for $q$. The vector $v$ is the genuine $(M+1)$-cylinder distribution of the uniform orbit law of $z$; incoming and outgoing $M$-word frequencies coincide by cyclic reindexing. Both vectors have total one and obey (5.1), so the same is true for $f_t$. Since $|v(e)-q(e)|\le1$,

$$
f_t(e)\ge q(e)-|t|\ge3\alpha/4>0.
$$

This verifies positivity even for the sign $s=-1$, when the direction is an extrapolation rather than a convex combination. Proposition 5.1 now supplies the claimed law. At $t=0$, its initial $M$-block distribution is $Q_M$ and its transition kernel is $Q_{M+1}(ua)/Q_M(u)$. The visible-order property of $Q$, with $r\le M$, identifies this with the original next-bit kernel on the last $r$ bits. Thus every cylinder in (5.3) agrees with $Q$, proving $Q_0=Q$.

The function $\ell_Q$ depends on a centered block of length $2r+1=M+1$. Let $\ell_Q(e)$ denote its value with the center at bit $r+1$ of $e$. Stationarity gives

$$
\begin{aligned}
\mathbb E_{Q_t}\ell_Q
&=\sum_e f_t(e)\ell_Q(e)\\
&=d(Q)+s t\left[\sum_e v(e)\ell_Q(e)-d(Q)\right]\\
&=d(Q)+s t[\beta-d(Q)]=d(Q)+\delta t.
\end{aligned}
$$

The orbit average in the penultimate line is $\beta$ because shifting the center by $r$ just permutes the $L$ terms. This establishes (5.5) for one actual compatible cylinder law. $\square$

## 6. Strict density improvement and the global comparison

**Lemma 6.1 (Quadratic posterior remainder).** For the family of Lemma 5.2 there is a finite constant $C\ge1$, depending on $Q$ and the chosen direction, such that for $|t|\le\alpha/4$ and every legal exterior,

$$
|p_{Q_t}(x)-p_Q(x)|\le C|t|.
\tag{6.1}
$$

Consequently

$$
d(Q_t)\ge d(Q)+\delta t-C^2t^2.
\tag{6.2}
$$

**Proof.** The kernel in (5.2) is a rational function of $t$ whose denominators $\pi_{f_t}(u)$ are positive throughout this compact interval. Formula (5.3) makes every legal $(2M+1)$-word probability a positive rational function of $t$. For each radius-$M$ exterior permitting both center choices, the posterior is the probability of the center-one word divided by the sum of its two word probabilities. Its denominator is positive, so this posterior and its derivative are continuous on the interval. There are finitely many such exterior contexts. In a forced-zero context the posterior is identically zero.

At $t=0$ these posteriors equal $p_Q$ in every legal radius-$M$ context: Proposition 2.2 applied to $Q$ shows that conditioning on a larger exterior window leaves its radius-$r$ posterior unchanged. Choose $C$ to be at least one and at least the maximum absolute derivative over the finite contexts and the compact interval. The mean-value theorem gives (6.1). This is a uniform bound over contexts for this fixed law, not a bound over different kernels.

Lemma 2.5, applied with $P=Q_t$, and (5.5) give the exact equality

$$
d(Q_t)=d(Q)+\delta t
-\mathbb E_{Q_t}[(p_{Q_t}-p_Q)^2].
\tag{6.3}
$$

Using (6.1) proves (6.2), including all forced-zero contexts. $\square$

**Proof of Theorem 1.5.** Fix arbitrary $m\ge1$ and a permitted $Q$ of visible order at most $m$. Its least order $r$ lies in $[1,m]$. Lemma 2.4 gives existence of $d(Q)$, and Proposition 4.1 supplies a direction with $\delta>0$. Lemma 5.2 produces the same-domain stationary family with visible order $M=2r\le2m$. Set

$$
\varepsilon_Q=\min\left\{\frac\alpha4,\frac{\delta}{2C^2}\right\}>0.
$$

For every $0<t<\varepsilon_Q$, Lemma 6.1 gives

$$
d(Q_t)\ge d(Q)+\delta t-C^2t^2
>d(Q)+\frac{\delta t}{2}>d(Q).
\tag{6.4}
$$

For each one of these fixed laws, every actual marginal $(Q_t)_n$ belongs to the entire original simplex $\mathcal P(B_n)$. Thus [Growth], Theorem 3.2, gives

$$
\Phi_n((Q_t)_n)\le\kappa_n\qquad(n\ge1).
$$

Lemma 2.4 applied at order bound $M$ supplies its density limit, and [Growth], Theorem 5.2, supplies the right-hand limit. Dividing by $n$ and taking $n\to\infty$ yields $d(Q_t)\le c_\star$, which proves (1.4) and $d(Q)<c_\star$.

The family, its parameter and its visible order are fixed before any length limit. Only finite cylinder probabilities and conditional tables were differentiated in bounding (6.1); there is no interchange of a derivative with a thermodynamic limit. Both density limits also hold along the original subsequence $n=3N$. $\square$

## 7. Consequence for the supplied pair law and applicability boundaries

**Corollary 7.1 (Strict inequality beyond the pair witness).** Let $Q^{\mathrm{pair}}$ be the stationary law in [TwoStep], Definition 2.1 and Proposition 2.2. With its supplied density

$$
d_{\mathrm{pair}}=\frac1{38}
\left(\frac{1372}{543}+\frac{588}{247}+\frac{63}{113}\right),
$$

there is a permitted stationary visible-order-at-most-four law $P$ with

$$
d_{\mathrm{pair}}<d(P)\le c_\star.
$$

**Proof.** The supplied law is normalized, stationary, positive on every legal pair state and every legal extension, and hence on every legal finite cylinder. Its next-bit kernel has visible order at most two. Its cylinder density is $d_{\mathrm{pair}}$ by the owned [TwoStep], Theorem 3.1. Apply Theorem 1.5 with $m=2$. $\square$

**Boundary 7.2 (Pointwise quantifiers).** The positive parameter interval and improvement depend on the given law. Theorem 1.5 does not assert a gap uniform over all kernels of any fixed order. Nor does it compare the suprema at orders $m$ and $2m$: strict improvement of each individual member is different from a strict inequality between two suprema. It does not determine the exact $c_\star$, classify non-full-support laws, or prove approximation completeness or a rate as visible order grows. Corollary 7.1 does not decide whether the pair law is optimal among laws of order at most two.

**Boundary 7.3 (Visible dependence and costs).** The constructed transition table is finite, with states $B_{2r}$ that are actual visible suffixes. Its finite description, the existence of the chosen direction and parameter, and the costs of acquiring or evaluating them are distinct from the density statement. No efficient construction or training guarantee follows. Arbitrary finite hidden producers are outside the theorem unless their output law separately satisfies the actual finite visible-order hypothesis. No physical, quantum, or machine-learning performance claim follows from this graph-density result.

## 8. Source ownership and primary hypotheses

**Convention 8.1 (Mathematical suppliers).** The only project suppliers are [Growth] at pin `409f27ebed169a35fa000f22ed56a2f154cb9c93` and [TwoStep] at pin `348bfc85a973f021d8e3e79df589b335b5407ee7`. Growth owns the original graph objective, harmonic duality and growth limit. TwoStep owns its coherent pair law, actual full-word grouping, endpoint bound and strict one-activity separation. Its pair separation is not a premise for the universal obstruction. None of Growth's code-dependent numerical certificates is used.

**Citation scope 8.2 (Established machinery and the uncovered conclusion).** Conditional squared loss, local proper scores, finite visible-block chains and stationary edge-flow parametrization are established tools or elementary probability identities. The extension in Lemma 2.4 credits the supplied grouping argument. The substantive theorem here is the universal endpoint obstruction in Proposition 4.1 combined with a compatible positive-flow direction and the exact quadratic remainder, proving strict improvement for every permitted finite visible-order law. This conclusion is not supplied by either project text. It is an ordinary mathematical derivation, with no kernel-verification or worldwide priority claim.

| Source | Exact hypotheses and scope |
| --- | --- |
| [Dawid, Lauritzen and Parry][DLP], §§1–2, §§4.2.1–4.2.2, Example 4.4, equation (14) | `literature-attested`: scalar conditional Brier loss and its squared conditional-probability discrepancy are existing ratio-matching machinery. The paper's product-space discussion assumes everywhere-positive distributions on the product space. The forbidden-$11$ domain is not such a full product. Lemmas 2.1 and 2.5 therefore establish the needed identities directly on each legal two-point fiber and each forced singleton, including zero-total finite fibers. No estimator consistency or scoring-rule classification theorem is imported. |
| [van Enter and Verbitskiy][EV], §1.1 and §§3.1–3.2, Theorems 5–6 | `literature-attested`: erasure uncertainty conditions a finite-alphabet stationary process or translation-invariant random field on its exterior. Theorem 6's affine formula concerns logarithmic erasure entropy on Gibbs measures sharing a fixed specification. It does not imply that harmonic density is affine as a transition kernel varies; (6.3) keeps the squared discrepancy. The local free-energy discussion also includes an energy term. No Shannon extremality theorem or finite-norm interaction theorem is transferred through the hard constraint. |
| [Chandgotia, Han, Marcus, Meyerovitch and Pavlov][CHMMP], §2, Proposition 2.1 and Theorem 4.1 | `literature-attested`: the Markov/MRF equivalence is stated for stationary finite-valued one-dimensional processes, with higher orders handled by visible-block recoding and conditioning events of positive probability. This supplies context for the exterior viewpoint, not finite visible dependence of arbitrary hidden-state outputs. Propositions 2.2 and 5.1 prove the conditional localization and the actual visible-order construction used here directly. The converse MRF theorem is not a proof dependency. |
| §§3–6 of this source | `repo-derived`: the least-order endpoint interaction, the two-center-label contradiction, and the stationary-flow strict-improvement proof. The cited primary results do not themselves state Theorem 1.5 for the original Fibonacci harmonic objective. |

The inspected primary sources concern local scoring, erasure uncertainty and one-dimensional specifications. Their overlap identifies reusable mechanisms and their hypothesis boundaries; it does not establish worldwide novelty or absence of other proofs of this exact theorem.

[Growth]: https://github.com/the-omega-institute/trureturing/blob/409f27ebed169a35fa000f22ed56a2f154cb9c93/docs/develop/theory/FIB_LEGAL_EDGE_LOAD_GROWTH_CONSTANT.md
[TwoStep]: https://github.com/the-omega-institute/trureturing/blob/348bfc85a973f021d8e3e79df589b335b5407ee7/docs/develop/theory/FIB_LEGAL_EDGE_LOAD_TWO_STEP_BULK_SEPARATION.md
[DLP]: https://arxiv.org/html/1104.2224v2
[EV]: https://arxiv.org/html/1001.3122v1
[CHMMP]: https://arxiv.org/html/1112.4240v1

## 追加锚（本行以下为增补区）
