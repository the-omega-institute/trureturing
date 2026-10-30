# FIB harmonic-edge load: global and local rank compatibility and the reset-variance obstruction

## 1. The original domain and the inherited discrepancy

**Definition 1.1 (Open words and the original objective).** For $n\ge1$ let

$$
B_n=\{w\in\{0,1\}^n:w_iw_{i+1}=0\ (1\le i<n)\},\qquad
\mathsf X=\{x\in\{0,1\}^{\mathbb Z}:x_ix_{i+1}=0\ (i\in\mathbb Z)\}.
$$

$B_0$ consists of the empty word. The graph $\Gamma_n$ contains all words in $B_n$ and all legal Hamming-one edges. Endpoint insertion uses $w_0=w_{n+1}=0$, without identifying the endpoints. On the entire probability simplex define

$$
h(s,t)=
\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}
\qquad
\Phi_n(p)=\sum_{\{u,v\}\in E(\Gamma_n)}h(p_u,p_v),\qquad
\kappa_n=\max_p\Phi_n(p).
\tag{1.1}
$$

Zero masses do not delete vertices or edges. Write $\pi_n$ for the supplied positive finite optimizer. [Universal, Convention 1.3, Lemma 2.1 and Proposition 7.1][U] supplies its insertion inequalities and the bounds

$$
\frac13\pi_n(u)\le\pi_n(v)\le\pi_n(u)\quad(u\to v\text{ inserts a one}),\qquad
nc_\star\le\kappa_n\le(n+1)c_\star,\qquad
\frac{\kappa_n}{n}\longrightarrow c_\star,\qquad
c_\star\ge\frac{1800}{12559}>\frac17.
\tag{1.2}
$$

The ceiling $c_\star\le\bar c:=3-2\sqrt2$ is the supplied bound in [Guarded, Definition 1.1]. No stationary marginal is substituted for $\pi_n$.

**Definition 1.2 (One exact-real producer and its actual law).** For each finite $N\ge1$ retain the entire domain

$$
\Theta_N=\left\{(\lambda,M_0,M_1):
\begin{array}{l}
\lambda\ge0,\ \lambda\mathbf1=1,\ M_0,M_1\ge0,\\
A=M_0+M_1,\ A\mathbf1=\mathbf1,\ \lambda A=\lambda,\
\lambda M_1^2\mathbf1=0
\end{array}\right\}.
\tag{1.3}
$$

The row $\lambda$ and the $N\times N$ matrices have arbitrary exact-real entries. Structural zeros, zero stationary masses, reducibility and periodicity are allowed. The last condition is scalar; entrywise $M_1^2=0$ is not imposed. With $M_w=M_{w_1}\cdots M_{w_n}$ and $M_\varepsilon=I$, [Universal, Proposition 4.2][U] supplies one actual stationary joint law

$$
J_\theta(H_a=h_a,\ldots,H_{b+1}=h_{b+1},X_a=x_a,\ldots,X_b=x_b)
=\lambda_{h_a}\prod_{i=a}^bM_{x_i}(h_i,h_{i+1}).
\tag{1.4}
$$

Write $X_i(x)=x_i$ and $[w]_a=\{x:X_a\cdots X_{a+|w|-1}=w\}$. The visible marginal $P_\theta$ is supported on $\mathsf X$ and has cylinders $P_\theta([w]_a)=\lambda M_w\mathbf1$. Every seam uses this ordered product. The clock counts original emitted bits. For any stationary legal $P$, [Universal, (1.5)][U] supplies

$$
d(P)=\lim_{n\to\infty}\frac{\Phi_n(P_{[1,n]})}{n}
=\mathbb E_P\bigl(X_0-\mathbb E_P[X_0\mid\sigma(X_j:j\ne0)]\bigr)^2
\le c_\star.
\tag{1.5}
$$

**Definition 1.3 (The guarded finite families).** For $a,b\in\{0,1\}$ and $m\ge1$ let

$$
K_m^{a,b}=\{w\in B_m:aw_1=w_mb=0\}.
$$

A probability $p$ on $K=K_m^{a,b}$ is band-compatible if $p_u/3\le p_v\le p_u$ on each legal insertion edge $u\to v$. [Guarded, Lemma 3.3] supplies positivity and the bound $p_w\ge3^{-k(w)}/|K|$, where $k(w)=\sum_iw_i$.

For a probability $p$ on $K$, write $p_i(w_{-i})=p(W_i=1\mid W_{-i}=w_{-i})$, always conditioning on all other bits of this finite word. A forced singleton fiber has posterior zero; on a zero-total fiber any version has zero weighted contribution. For positive $r$ on $K$ put

$$
\mathcal D_K(p\Vert r)
=\sum_{i=1}^m\mathbb E_p(p_i(W_{-i})-r_i(W_{-i}))^2
=\sum_{u\to v}(p_u+p_v)
\left(\frac{p_v}{p_u+p_v}-\frac{r_v}{r_u+r_v}\right)^2.
\tag{1.6}
$$

Zero-total terms are defined as zero without division. Let $\Phi_K$ denote the corresponding edge sum of $h$. Extend $r$ by zero to the entire binary cube and define its cut matrix by

$$
\mathsf F_k(r)(s,t)=r(st),\qquad
s\in\{0,1\}^k,\quad t\in\{0,1\}^{m-k},\quad 1\le k<m.
\tag{1.7}
$$

Illegal words and seams remain zero entries. Nonnegative rank is the least number of nonnegative rank-one summands. Use exactly [Guarded, Definition 6.3]'s family $\mathscr F_{N,m}^{a,b}$ of band-compatible probabilities with $\operatorname{rank}_+\mathsf F_k(r)\le N$ at every internal cut, and put

$$
\delta_{N,m}^{a,b}(p)=\min_{r\in\mathscr F_{N,m}^{a,b}}\mathcal D_{K_m^{a,b}}(p\Vert r),
\qquad
\mathscr R_{N,n}(p)=\delta_{N,n}^{0,0}(p),\qquad
\mathcal R_{N,n}=\mathscr R_{N,n}(\pi_n).
\tag{1.8}
$$

The empty-family minimum is $+\infty$. At $m=1$ there are no cut conditions. A singleton completion set has its unique probability and zero discrepancy.

**Premise 1.4 (Credited score and rank interfaces).** [Guarded, Lemmas 3.2–3.3 and Definition 6.3] supplies compactness of the nonempty families in (1.8), continuity of their discrepancy, and

$$
\mathbb E_p\sum_i(W_i-r_i(W_{-i}))^2=\Phi_K(p)+\mathcal D_K(p\Vert r).
\tag{1.9}
$$

For positive $p,r$ on the connected legal completion graph, $\mathcal D_K(p\Vert r)=0$ exactly when $p=r$. Concavity of $\Phi_K$ follows from the supplied concavity of $h$. In particular, $\mathcal D_K(\,\cdot\,\Vert r)$ is convex.

For disjoint nonempty intervals $C_j\subseteq[1,n]$, let $\eta=W_{[1,n]\setminus C_j}$ be the entire complement, let $a_j,b_j$ be its adjacent bits, with zero at an open endpoint, and let $p_j^\eta=p(W_{C_j}=\cdot\mid\eta)$. The conditional-slicing argument of [Guarded, Theorem 7.1] gives, for any band-compatible $p$,

$$
\mathscr R_{N,n}(p)\ge
\sum_j\mathbb E_p\delta_{N,|C_j|}^{a_j,b_j}(p_j^\eta).
\tag{1.10}
$$

This use of its argument requires only positivity and the insertion inequalities, not the optimizer equation. Each candidate conditional on its left is a slice of one global $r$; the minima on its right can choose candidates separately. Restricting rows and columns of a cut matrix and dividing by a positive complement mass preserves its rank bound. Only extendible complements enter; all others contribute zero without division. No independence of adjacent or separated blocks is asserted.

For an $(N+1)\times(N+1)$ minor $A_p$ of a cut matrix, [Guarded, Theorem 8.2] supplies

$$
\delta_{N,m}^{a,b}(p)\ge
\frac{6^{-4m}}{2m(N!)^2}|\det A_p|^2.
\tag{1.11}
$$

These inherited interfaces are necessary relaxations. They do not assert that all members of $\mathscr F$ have one common nonnegative matrix representation or a stationary extension.

## 2. Rank two forces a reset and an actual-optimizer variance bound

**Lemma 2.1 (Reset at every visible one).** Let $r$ be positive on $B_n$ and suppose every internal cut matrix has ordinary rank at most two. For each $1\le k\le n$, conditional on $W_k=1$, the two strings $W_{[1,k-1]}$ and $W_{[k+1,n]}$ are independent under this same $r$.

Proof. At a cut $k<n$, every row whose last bit is one vanishes on every column whose first bit is one. Such a legal row is nonzero, since its entry at the all-zero suffix is positive. A legal row ending in zero has a positive entry at the column $10^{n-k-1}$. It is therefore outside the span of the rows ending in one. If the latter span had dimension at least two, the whole cut matrix would have rank at least three. Its dimension is consequently exactly one.

All nonzero rows ending in one are positive multiples of a fixed such row: their coordinates at the all-zero suffix determine a positive proportionality factor. Normalizing each row by its sum shows that the conditional suffix law is the same for every legal prefix ending in one. This is the asserted independence. When $k=1$ the left string is empty; when $k=n$ the right string is empty. Those assertions are tautological, including $n=1$. The proof retains every forbidden seam as a zero. $\square$

**Lemma 2.2 (Two resets fix the middle posterior).** Under Lemma 2.1's hypotheses, for $n\ge5$ and $3\le i\le n-2$ put

$$
E_i=\{W_{i-2}=W_{i+2}=1\}.
\tag{2.1}
$$

There is a number $c_i(r)$ such that $r_i(W_{-i})=c_i(r)$ on every legal complement in $E_i$.

Proof. Legality forces $W_{i-1}=W_{i+1}=0$. Write a completion as $\ell\,10x01\,t$, where $x\in\{0,1\}$ and the outer strings are compatible with the two displayed ones. Both choices of $x$ are legal for exactly the same outer strings and have positive masses.

Apply the row proportionality from Lemma 2.1 at $i-2$: changing $\ell$ multiplies the masses of every suffix after that one by a factor $A(\ell)>0$, independent of $x,t$. Apply it at $i+2$: the normalized suffix law after the second one is independent of the prefix, hence contributes a common factor $B(t)>0$, independent of $\ell,x$. Fixing one legal outer string on each side thus gives positive constants $H_0,H_1$ with

$$
r(\ell\,10x01\,t)=A(\ell)H_xB(t).
\tag{2.2}
$$

If a reset is an endpoint, its empty outer string has factor one. Consequently the posterior is $H_1/(H_0+H_1)$, independently of the entire distant complement. This uses two cuts of one $r$, not independently specified block kernels. $\square$

**Theorem 2.3 (Reset-variance lower bound).** For any band-compatible $p$ on $B_n$, define

$$
V_2(p;n)=\sum_{i=3}^{n-2}p(E_i)\operatorname{Var}_p\bigl(p_i(W_{-i})\mid E_i\bigr),
\qquad V_2(p;n)=0\quad(n<5).
\tag{2.3}
$$

Then

$$
\mathscr R_{2,n}(p)\ge V_2(p;n).
\tag{2.4}
$$

In particular, with the actual full-complement optimizer posterior

$$
a_{n,i}=\pi_n(W_i=1\mid W_{[1,n]\setminus\{i\}}),\qquad
V_2(n)=\sum_{i=3}^{n-2}\pi_n(E_i)\operatorname{Var}_{\pi_n}(a_{n,i}\mid E_i),
$$

one has $\mathcal R_{2,n}\ge V_2(n)$.

Proof. A member $r$ of $\mathscr F_{2,n}^{0,0}$ is positive, and its ordinary ranks are at most its nonnegative ranks, hence at most two. Lemma 2.2 applies. Retain from (1.6) only site $i$ and the event $E_i$. The least-squares identity for a constant gives

$$
\begin{aligned}
\mathbb E_p\mathbf1_{E_i}(p_i-r_i)^2
&=p(E_i)\left[
\operatorname{Var}_p(p_i\mid E_i)
+\bigl(\mathbb E_p[p_i\mid E_i]-c_i(r)\bigr)^2\right]\\
&\ge p(E_i)\operatorname{Var}_p(p_i\mid E_i).
\end{aligned}
\tag{2.5}
$$

Each retained term belongs to a different site, so overlap between the events $E_i$ creates no double counting. Sum and minimize over the single global $r$. An empty family satisfies the inequality in the extended order. For $n<5$ it is nonnegativity. Positivity makes $p(E_i)>0$ whenever that event is used. The final specialization uses only $p=\pi_n$ in every conditional, variance and weight. $\square$

**Corollary 2.4 (A separate sufficient test on $\pi_n$).** Put

$$
\tau=2(3-2\sqrt2)-\frac1{24}.
\tag{2.6}
$$

If some $n$ satisfies $V_2(n)>\tau$, no $\theta\in\Theta_2$ can satisfy simultaneously the band, $A_{P_\theta}<\infty$ and strong zero as defined in §6.

Proof. [Guarded, Corollary 6.4] gives $\mathcal R_{2,n}\le\tau$ under those three premises; Theorem 2.3 contradicts it. This is a sufficient conditional test. It supplies no value of $V_2(n)$ and no implication from attainment to strong zero. $\square$

## 3. One stationary common-matrix comparison law

**Definition 3.1 (Persistent finite mixture).** Fix $N\ge2$ and $K=N+1$. Choose

$$
\frac13\le a_1<\cdots<a_K\le\frac38,\qquad
w_\ell>0,\qquad\sum_{\ell=1}^Kw_\ell=1.
\tag{3.1}
$$

For example, $a_\ell=1/3+(\ell-1)/(24N)$ gives distinct admissible parameters. Let

$$
A_\ell=\begin{pmatrix}1-a_\ell&a_\ell\\1&0\end{pmatrix},\qquad
\lambda_\ell=\left(\frac1{1+a_\ell},\frac{a_\ell}{1+a_\ell}\right),\qquad
D_0=\operatorname{diag}(1,0),\quad D_1=\operatorname{diag}(0,1).
\tag{3.2}
$$

The stationary binary Markov law with these parameters is denoted by $R^{a_\ell}$. Its two-state mechanism is the one in [Universal, Proposition 7.1][U]. Define once and for all

$$
M_x=\bigoplus_{\ell=1}^K D_xA_\ell,\qquad
\lambda=(w_1\lambda_1,\ldots,w_K\lambda_K),\qquad
P=\sum_{\ell=1}^Kw_\ell R^{a_\ell},\qquad
\mu_n=P_{[1,n]}.
\tag{3.3}
$$

Write $J$ for the joint law (1.4) of (3.3). Its label $L=\ell$ records the closed block of the hidden state and is constant along the whole trajectory. Label probabilities and expectations below are taken under this $J$. Their visible-coordinate marginals are $P$ and $\mu_n$; in a length-$n$ calculation write $W=X_{[1,n]}$.

**Proposition 3.2 (Exact representation and every-length band).** The parameters (3.3) belong to $\Theta_{2(N+1)}$ and yield this one stationary $P$ at all lengths. Every $\mu_n$ is positive and band-compatible on all of $B_n$. Every actual component conditional on a finite block, given its entire finite complement, belongs to the corresponding $\mathscr F_{2,m}^{a,b}$.

Proof. Each $A_\ell$ is stochastic and $\lambda_\ell A_\ell=\lambda_\ell$. Also $(D_1A_\ell)^2=0$. Block sums give all conditions of (1.3); summing the hidden states gives exactly (3.3). This particular representation has $2(N+1)$ states. No claim of a representation with $N$ states or of minimal hidden dimension is made.

All allowed transitions and both stationary probabilities in each component are positive, so every legal word has positive mass. Its insertion ratio in a component is, respectively,

$$
a_\ell\quad(n=1),\qquad
\frac{a_\ell}{1-a_\ell}\quad\text{at an open endpoint when }n\ge2,\qquad
z_\ell:=\frac{a_\ell}{(1-a_\ell)^2}\quad\text{at an interior free site}.
\tag{3.4}
$$

For every component set $Q_\ell=z_\ell/(1+z_\ell)$; these constants are distinct from the full-exterior predictor functions $q_i$ used in §6.

For the first endpoint the stationary factor changes as well as the first transition; their ratio is $a_\ell/(1-a_\ell)$. At the last endpoint only the last transition changes. At an interior site the two transition factors change from $(1-a_\ell)^2$ to $a_\ell$. Thus the three ranges are $[1/3,3/8]$, $[1/2,3/5]$ and $[3/4,24/25]$, all contained in $[1/3,1]$. The linear insertion inequalities survive the same positive mixture.

In each component, any whole-word cut factors through its two hidden states. Fixing the full complement of an interval selects rows and columns at each internal cut, and positive normalization gives the component conditional matrix. Hence its nonnegative rank is at most two. Insertion ratios are inherited by division by a common complement mass, including boundary-forced fibers and blocks touching open endpoints. At length one the rank requirement is vacuous. $\square$

**Proposition 3.3 (Actual conditional mixture and its interior formula).** Let $C=[u,v]\subseteq[1,n]$ have length $m$, and let $\eta$ be any extendible word on its entire complement. Write

$$
\theta_\ell(\eta)=J(L=\ell\mid W_{[1,n]\setminus C}=\eta),\qquad
r_{\ell,C}^{\eta}=R^{a_\ell}(W_C=\cdot\mid W_{[1,n]\setminus C}=\eta).
$$

Then all $\theta_\ell(\eta)$ are positive and

$$
p_C^\eta:=\mu_n(W_C=\cdot\mid W_{[1,n]\setminus C}=\eta)
=\sum_{\ell=1}^K\theta_\ell(\eta)r_{\ell,C}^\eta.
\tag{3.5}
$$

For an interior interval, $1<u\le v<n$, let $a=\eta_{u-1}$ and $b=\eta_{v+1}$. Then

$$
r_{\ell,C}^{\eta}(w)=\frac{z_\ell^{k(w)}}{Z_{\ell,m}^{a,b}},\qquad
Z_{\ell,m}^{a,b}=\sum_{w\in K_m^{a,b}}z_\ell^{k(w)}>0.
\tag{3.6}
$$

Proof. An extendible complement has at least one legal completion, positive under every component by Proposition 3.2. Bayes' formula therefore gives positive posterior weights and (3.5), with no null denominator. In a fixed component the exterior transition factors cancel in the conditional. For the path from $a$ through $w$ to $b$, there are $k(w)+b$ transitions $0\to1$, $k(w)+a$ transitions $1\to0$, and $m+1-a-b-2k(w)$ transitions $0\to0$. Its transition product is

$$
a_\ell^b(1-a_\ell)^{m+1-a-b}z_\ell^{k(w)}.
\tag{3.7}
$$

The prefactor is independent of $w$, proving (3.6). This formula is used only when both adjacent exterior bits are actually present. Formula (3.5) and Proposition 3.2 cover open-endpoint blocks and the whole interval without imposing fictitious exterior observations. Nonextendible complements have zero weight throughout. $\square$

## 4. Nonzero finite minors with vanishing fixed-block accumulation

**Lemma 4.1 (Explicit minor at every interior complement).** For the law (3.3), set $m_0=4N+2$. Every interior length-$m_0$ conditional in Proposition 3.3 has a nonzero $(N+1)\times(N+1)$ minor and therefore has $\delta_{N,m_0}^{a,b}(p_C^\eta)>0$.

Proof. Cut the block after $2N+1$ bits. For $0\le j\le N$ choose the rows and columns

$$
s_j=t_j=0(10)^j0^{2(N-j)}.
\tag{4.1}
$$

Each has length $2N+1$, begins and ends in zero, and contains $j$ ones. All selected concatenations are legal for either value of each exterior bit. By (3.5)–(3.6), their matrix $H$ has entries

$$
H_{ij}=\sum_{\ell=1}^{N+1}c_\ell z_\ell^{i+j},\qquad
c_\ell=\frac{\theta_\ell(\eta)}{Z_{\ell,m_0}^{a,b}}>0.
$$

Thus $H=V\operatorname{diag}(c_\ell)V^{\mathsf T}$ with $V_{i\ell}=z_\ell^i$. The parameters $z_\ell$ are strictly increasing, since $a/(1-a)^2$ is strictly increasing on $(0,1)$. The Vandermonde identity gives

$$
\det H=\left(\prod_{\ell=1}^{N+1}c_\ell\right)
\prod_{\ell<k}(z_k-z_\ell)^2>0.
\tag{4.2}
$$

For completeness, the Vandermonde determinant is an alternating polynomial in its nodes, hence divisible by every node difference; their product has the same total degree. Comparing the coefficient obtained by taking exponents $0,1,\ldots,N$ in column order makes the remaining constant one. This proves the identity used here. Ordinary rank exceeds $N$, and ordinary rank never exceeds nonnegative rank. The minimizing family is nonempty by Proposition 3.2 and $N\ge2$. Compactness and strict equality in Premise 1.4, or (1.11), give the asserted positive discrepancy. $\square$

**Lemma 4.2 (A conditional upper bound).** For every length-$m$ block, including an endpoint block, its actual conditional (3.5) satisfies

$$
\delta_{N,m}^{a,b}(p_C^\eta)\le
m\bigl(1-\max_\ell\theta_\ell(\eta)\bigr).
\tag{4.3}
$$

Proof. Each $r_{\ell,C}^\eta$ lies in $\mathscr F_{2,m}^{a,b}\subseteq\mathscr F_{N,m}^{a,b}$. For a fixed index $k$, the score identity (1.9) and concavity of $\Phi_K$ give

$$
\mathcal D_K\left(\sum_\ell\theta_\ell r_\ell\middle\Vert r_k\right)
\le\sum_\ell\theta_\ell\mathcal D_K(r_\ell\Vert r_k)
\le m(1-\theta_k).
\tag{4.4}
$$

The last inequality uses zero discrepancy for $\ell=k$ and the bound one for each squared single-site posterior difference. Choose an index of largest posterior weight. This choice is allowed separately for each complement in the local minimum. It is not asserted to be a conditional slice of any one global rank-$N$ candidate. Singleton completion sets have zero discrepancy and satisfy the same inequality. $\square$

**Lemma 4.3 (Component-identification bound).** Put

$$
\rho_\ell=\frac{a_\ell}{1+a_\ell},\qquad
\Delta=\min_{\ell\ne k}|\rho_\ell-\rho_k|>0.
\tag{4.5}
$$

For any length-$s$ contiguous segment of the stationary process, classify its label by the nearest $\rho_\ell$ to its empirical mean, with any fixed tie rule. If $s\Delta\ge4$, its error probability under any component, and under their actual mixture, is at most

$$
2\exp(-s\Delta^2/32).
\tag{4.6}
$$

Proof. Under one component with parameter $a$ and mean $\rho=a/(1+a)$, put $Y_j=X_j-\rho$ and

$$
Z_j=Y_j+aY_{j-1}=X_j-a(1-X_{j-1}),\qquad 1\le j\le s.
$$

The Markov transition rule gives $\mathbb E[Z_j\mid X_0,\ldots,X_{j-1}]=0$, and $|Z_j|\le1$. For any conditional mean-zero $Z\in[-1,1]$, convexity of the exponential gives

$$
\mathbb E[e^{tZ}\mid\mathcal H]\le\frac{e^t+e^{-t}}2
=\cosh t\le e^{t^2/2}.
\tag{4.7}
$$

The last bound follows termwise from $(2k)!\ge2^kk!$ in the power series. Iterating (4.7) gives $\mathbb E\exp(t\sum_{j=1}^sZ_j)\le\exp(st^2/2)$. Exponential Markov inequality, with $t=u/s$ and then with its negative, yields

$$
\Pr\left(\left|\sum_{j=1}^sZ_j\right|\ge u\right)
\le2\exp(-u^2/(2s)).
\tag{4.8}
$$

Moreover,

$$
\sum_{j=1}^sZ_j=(1+a)\sum_{j=1}^sY_j+a(Y_0-Y_s),\qquad
|a(Y_0-Y_s)|\le1.
\tag{4.9}
$$

An empirical-mean deviation of at least $\Delta/2$ therefore forces $|\sum Z_j|\ge s\Delta/2-1\ge s\Delta/4$ when $s\Delta\ge4$. Substitution into (4.8) gives (4.6). Misclassification implies such a deviation, since distinct component means are separated by at least $\Delta$. The preceding bit $X_0$ is used only in this proof, not by the classifier. Stationarity gives the same bound for any translated segment, including one in the past. Averaging over the one actual label preserves the bound. This is the elementary bounded-martingale exponential method; see the mathematical citation [Azuma] below. $\square$

**Theorem 4.4 (Vanishing fixed-block defects for one stationary law).** Fix the single stationary law (3.3). For any fixed $m\ge1$, any $n>m$ with $(n-m)\Delta\ge8$, and any deterministic family of $B$ disjoint length-$m$ intervals in $[1,n]$,

$$
\sum_{j=1}^B\mathbb E_{\mu_n}
\delta_{N,m}^{a_j,b_j}\bigl(\mu_n(W_{C_j}=\cdot\mid W_{[1,n]\setminus C_j})\bigr)
\le2mB\exp(-(n-m)\Delta^2/64)
\le2n\exp(-(n-m)\Delta^2/64).
\tag{4.10}
$$

Hence the sum tends to zero as $n\to\infty$ for every fixed $m$, uniformly over these families. At $m=m_0$, every interior-block term is nevertheless strictly positive for each supported finite complement.

Proof. The complement of any length-$m$ interval contains a contiguous segment of length $s\ge(n-m)/2$. Classifying from its empirical mean uses only the observed complement. Lemma 4.3 bounds its error by $2\exp(-(n-m)\Delta^2/64)$. Given that complement, the minimum conditional error among label guesses is $1-\max_\ell\theta_\ell$: guessing $k$ is correct with probability $\theta_k$. Its expectation, the Bayes error using the full complement, is no greater than the error of the segment classifier. Taking expectations in (4.3) proves the first bound after summing. Disjointness gives $mB\le n$, proving the second. The exponential bound tends to zero for fixed $m,\Delta>0$. The positivity assertion is Lemma 4.1.

For lengths not satisfying the displayed size condition, (4.3) still gives the finite bound $mB$. The construction and its band have not excluded $n=1$, forced fibers, open endpoints or whole-interval blocks; only the concentration estimate needs a sufficiently long observed segment. All $\mu_n$ here are marginals of the same matrices and the same stationary $P$, not distributions selected independently with $n$. $\square$

**Corollary 4.5 (Nonzero minors need not have positive density).** For $B$ disjoint interior length-$m_0$ blocks, let $H_j^\eta$ be the minors (4.2). Then

$$
\sum_j\mathbb E_{\mu_n}|\det H_j^\eta|^2
\le8(N!)^2B\exp(-(n-m_0)\Delta^2/64)\longrightarrow0
\tag{4.11}
$$

under the size condition of Theorem 4.4, even though each determinant is positive on every supported complement.

Proof. At that complement choose a largest-weight component $r_k$. Its cut rank is at most two, hence at most $N$, so the corresponding determinant vanishes. For matrices whose entries lie in $[0,1]$, telescoping the permutation products bounds the determinant difference by $N!$ times the sum of the entry differences; each entry appears in $N!$ products. Distinct selected entries represent distinct words. Thus

$$
|\det H_j^\eta|\le N!\|p_C^\eta-r_k\|_1
\le2N!(1-\theta_k).
$$

Square and use $(1-\theta_k)^2\le1-\theta_k$. The Bayes error estimate from Theorem 4.4 gives (4.11). Since $B\le n/m_0$, its right side tends to zero. This is the determinant continuity estimate of [Guarded, (8.5)] applied to the actual posterior mixture. $\square$

## 5. Linear global discrepancy for that same law at rank two

**Theorem 5.1 (Positive stationary variance and global versus local separation).** Take Definition 3.1 with $N=2$, so the fixed representation has six hidden states and three positive component weights. Define

$$
Q_\ell=\frac{z_\ell}{1+z_\ell},\qquad
e_\ell=\frac{a_\ell^2((1-a_\ell)^2+a_\ell)}{1+a_\ell},\qquad
S=\sum_{\ell=1}^3w_\ell e_\ell,
$$

$$
v=S\operatorname{Var}_J(Q_L\mid X_{-2}=X_2=1)
=\frac1S\sum_{\ell<k}w_\ell e_\ell w_ke_k(Q_\ell-Q_k)^2>0.
\tag{5.1}
$$

The variance in (5.1) is under the joint law (1.4) of this mixture. For every $n\ge5$ with $(n-1)\Delta\ge8$,

$$
\mathscr R_{2,n}(\mu_n)\ge
(n-4)\left[v-2\exp(-(n-1)\Delta^2/64)\right].
\tag{5.2}
$$

In particular,

$$
\liminf_{n\to\infty}\frac{\mathscr R_{2,n}(\mu_n)}n\ge v>0,
\qquad
\lim_{n\to\infty}\sum_j
\mathbb E_{\mu_n}\delta_{2,m}^{a_j,b_j}(p_j^\eta)=0
\tag{5.3}
$$

for every fixed $m$ and every sequence of disjoint length-$m$ block families. Both limits concern the same $P$, with $\mu_n=P_{[1,n]}$; neither concerns $\pi_n$.

Proof. Under component $\ell$, the event $E_i=\{X_{i-2}=X_{i+2}=1\}$ consists of the two five-bit words $10001$ and $10101$. Their probabilities are respectively

$$
\frac{a_\ell^2(1-a_\ell)^2}{1+a_\ell},
\qquad
\frac{a_\ell^3}{1+a_\ell}.
\tag{5.4}
$$

Their sum is $e_\ell>0$. Conditional on $E_i$ the label weights under $J$ are $w_\ell e_\ell/S$. The pairwise formula for weighted variance gives (5.1); every weight is positive and the $Q_\ell$ are distinct. Stationarity makes $S$ and $v$ independent of $i$.

Let $\mathcal G_{n,i}=\sigma(W_j:1\le j\le n,\ j\ne i)$ and $p_{n,i}=\mathbb E_J[X_i\mid\mathcal G_{n,i}]$, which is exactly the $\mu_n$ full-complement posterior. For $3\le i\le n-2$, $E_i\in\mathcal G_{n,i}$. The two neighbors of $i$ are zero on $E_i$. Given $L=\ell$ and this entire complement, the Markov transition ratio at $i$ is $z_\ell$, so its posterior is $Q_\ell$. Consequently,

$$
p_{n,i}=\mathbb E_J[Q_L\mid\mathcal G_{n,i}]\quad\text{on }E_i.
\tag{5.5}
$$

Conditional variance decomposition within the same joint probability space now gives

$$
\mu_n(E_i)\operatorname{Var}_{\mu_n}(p_{n,i}\mid E_i)
=v-\mathbb E_J\!\left[\mathbf1_{E_i}
\operatorname{Var}_J(Q_L\mid\mathcal G_{n,i})\right].
\tag{5.6}
$$

Indeed, expand $Q_L$ around its conditional mean given $\mathcal G_{n,i}$; the cross term vanishes even after multiplying by $\mathbf1_{E_i}$, since this event belongs to that field. This proves (5.6) without mixing variances from different laws.

At a given complement choose a most probable label $k$. Since every $Q_\ell\in[0,1]$, comparison with the constant $Q_k$ gives

$$
\operatorname{Var}_J(Q_L\mid\mathcal G_{n,i})
\le1-\max_\ell J(L=\ell\mid\mathcal G_{n,i}).
\tag{5.7}
$$

The complement of the one missing site contains a segment of length at least $(n-1)/2$. The same classifier and Bayes comparison as in Theorem 4.4 bound the expectation of (5.7) by $2\exp(-(n-1)\Delta^2/64)$. Dropping $\mathbf1_{E_i}$ only enlarges this nonnegative bound. Apply Theorem 2.3 to the band-compatible law $p=\mu_n$, sum over its $n-4$ indicated sites, and obtain (5.2). Division by $n$ gives the first limit in (5.3); Theorem 4.4 gives the second. $\square$

**Corollary 5.2 (The compatibility absent from independent minima).** In Theorem 5.1, no choice of one global $r_n\in\mathscr F_{2,n}^{0,0}$ can achieve the vanishing total discrepancy of the independently chosen conditional fits.

Proof. The discrepancy of every such $r_n$ is bounded below by (5.2), which grows linearly with positive asymptotic coefficient. The independently minimized fixed-block sum tends to zero by (5.3). The reset law (2.2) is a necessary constraint on every global candidate, whereas the choice in (4.4) may depend on a component learned from the full complement. Those conditional choices are not thereby the conditionals of a common global candidate. $\square$

## 6. Endpoint premises and the comparison law's strict nonattainment

**Definition 6.1 (Band, summability and strong zero).** For a stationary legal $P$, let $(Tx)_i=x_{i+1}$. Choose a Borel exterior version of $q_0$ and put $q_i=q_0\circ T^i$, so that

$$
\mathcal E_i=\sigma(X_j:j\ne i),\qquad
F_i=\{X_{i-1}=X_{i+1}=0\},\qquad
q_i=\mathbb E_P[X_i\mid\mathcal E_i],\qquad
\ell_i=(X_i-q_i)^2.
$$

The band $\mathsf B(P)$ means $q_i=0$ on $F_i^c$ and $1/4\le q_i\le1/2$ on $F_i$, almost surely. Define

$$
\begin{aligned}
p_j^L&=\mathbb E_P[X_0\mid X_{-j},\ldots,X_{-1},X_1,X_2,\ldots],&
e_L(j)&=\mathbb E_P(q_0-p_j^L)^2,\\
p_j^R&=\mathbb E_P[X_0\mid\ldots,X_{-2},X_{-1},X_1,\ldots,X_j],&
e_R(j)&=\mathbb E_P(q_0-p_j^R)^2,\\
A_P&=\sum_{j\ge0}\bigl(\sqrt{e_L(j)}+\sqrt{e_R(j)}\bigr).
\end{aligned}
\tag{6.1}
$$

At $j=0$ the whole opposite half-line is retained. Under the band and $A_P<\infty$, [Guarded, Lemma 2.2] supplies a saturated conull set where

$$
\Delta_P(x,z)=\sum_{i\in\mathbb Z}(\ell_i(x)-\ell_i(z))
\tag{6.2}
$$

is absolutely convergent for every legal finite modification. All losses use the original $P$ predictors. Strong zero, denoted $\mathsf Z_\Delta(P)$, asserts that this cocycle vanishes on every such pair in a saturated conull set. It is an additional pathwise premise.

**Premise 6.2 (Guarded sufficient endpoint and budget).** [Guarded, Theorem 5.1 and Corollary 6.4] supplies

$$
\mathsf B(P),\ A_P<\infty,\ \mathsf Z_\Delta(P)\quad\Longrightarrow\quad d(P)=c_\star,
\tag{6.3}
$$

and, for a single $\theta\in\Theta_N$ satisfying those premises,

$$
\mathcal R_{N,n}\le(n+2)c_\star-\kappa_n-\frac1{24}\le\tau
\quad\text{for every }n.
\tag{6.4}
$$

Its conditional-rank input is [Guarded, Theorem 6.2]: the guarded kernels from disintegrating that same $J_\theta/P_\theta$ satisfy all cut bounds. This is not an implication from cut ranks back to a producer. No implication from attainment or first-order balance to strong zero, and no generic assertion of $A_P<\infty$ on $\Theta_N$, is included in these premises.

**Proposition 6.3 (The comparison law satisfies the band and summability, but not attainment or strong zero).** For every mixture (3.3), either visible infinite half-line determines $L$ under $J$ almost surely, and

$$
q_0=Q_L\mathbf1_{F_0},\qquad
A_P\le2,\qquad
d(P)\le\frac17<c_\star,\qquad
\neg\mathsf Z_\Delta(P).
\tag{6.5}
$$

Proof. Classify $L$ from $X_1,\ldots,X_s$ as in Lemma 4.3. For sufficiently large $s$ the error probabilities are bounded by a summable geometric sequence. The probability of any error after index $t$ is bounded by its tail sum, which tends to zero. Thus the guesses are eventually equal to $L$ almost surely, and their limit is future-half-line measurable. By stationarity the same argument for $X_{-s},\ldots,X_{-1}$ makes $L$ past-half-line measurable. This elementary tail argument needs no independence of the guesses.

Within each component, the full exterior posterior at a free site is $Q_\ell=z_\ell/(1+z_\ell)$ by the two transition products in (3.4), and it is zero on a forced site. This identity for finite windows containing both neighbors extends to all exterior events: those finite events generate $\mathcal E_0$, and their conditional integral identities extend by uniqueness of finite measures. Combining the component identities with the exterior-measurable label gives $q_0=Q_L\mathbf1_{F_0}$ under $J$, where $q_0$ is pulled back from the visible law $P$. Here $3/7\le Q_\ell\le24/49$, so the band holds.

For $j\ge1$, each field defining $p_j^L$ or $p_j^R$ contains both neighbors and a whole opposite half-line. It therefore determines $L$ and $F_0$, so $q_0$ is measurable in it. The tower property gives $p_j^L=p_j^R=q_0$, whence $e_L(j)=e_R(j)=0$. At $j=0$ both squared errors are at most one, proving $A_P\le2$. This is a property of the explicit mixture only.

Under component $\ell$, $J(F_0\mid L=\ell)=((1-a_\ell)^2+a_\ell)/(1+a_\ell)$. Using (1.5) and the actual posterior gives

$$
d(P)=\sum_\ell w_\ell
\frac{a_\ell(1-a_\ell)^2}{(1+a_\ell)((1-a_\ell)^2+a_\ell)}.
\tag{6.6}
$$

For $1/3\le a\le3/8$, the denominator minus seven times the numerator is

$$
(1+a)((1-a)^2+a)-7a(1-a)^2
=(3a-1)(-2a^2+4a-1)\ge0,
\tag{6.7}
$$

because $3a-1\ge0$ and $-2a^2+4a-1=1-2(1-a)^2\ge1/9$. Each component value in (6.6) is consequently at most $1/7$, and the weights sum to one. The strict comparison with $c_\star$ is (1.2). Since this same $P$ satisfies the other two premises of (6.3), strong zero would contradict its strict nonattainment. $\square$

## 7. Open mathematical questions on the original domain

**Open Question 7.1 (Quantitative information for the actual optimizer).** Does some $n$ satisfy $V_2(n)>\tau$? More generally, do the full-complement conditionals of the actual $\pi_n$ provide a lower bound for $\mathcal R_{N,n}$ or for the common-transfer refinement of [Guarded, Proposition 6.5] that exceeds $\tau$ for an intended $N$?

Theorem 2.3 is a test on $\pi_n$ with no value supplied for its variance. Theorems 4.4 and 5.1 concern $\mu_n$ from (3.3). They imply neither posterior concentration for $\pi_n$ nor a lower bound on its variance or minors. Positive finite minors alone do not provide positive-density mean squared minors; (4.11) exhibits the obstruction. Failure of one localized bound to grow does not show that the global rank relaxation fails on $\pi_n$.

**Open Question 7.2 (Attainment and the additional endpoint premises).** If a finite hidden law attains $c_\star$, must it satisfy $A_P<\infty$ and strong zero, or is there another complete route from attainment to a finite exclusion? The necessary band supplied by [Universal, Theorem 3.1][U] does not answer these questions. First-order conditional balances are not the pathwise property in Definition 6.1. The explicit summability in Proposition 6.3 cannot be applied to arbitrary scalar-no11 presentations with structural zeros, zero stationary masses, reducibility or periodicity.

**Open Question 7.3 (Unchanged whole-domain finite attainment).** On precisely (1.3), put

$$
C_N=\sup_{\theta\in\Theta_N}d(P_\theta),\qquad
D_r(P)=\mathbb E_P\left(X_0-
\mathbb E_P[X_0\mid X_{-r},\ldots,X_{-1},X_1,\ldots,X_r]\right)^2,\qquad
U_{N,r}=\max_{\theta\in\Theta_N}D_r(P_\theta).
$$

Does some finite $N$ admit $d(P_\theta)=c_\star$, or is $C_N<c_\star$ for every finite $N$? [Universal, Theorem 6.2][U] supplies attainment of each $C_N$, the identity $C_N=\inf_rU_{N,r}$, and the equivalence of the second alternative with

$$
\forall N\ge1\ \exists r,m\ge1:\qquad
U_{N,r}<\frac{\kappa_m}{m+1}.
\tag{7.1}
$$

Neither alternative follows from the comparison law, which has the exhibited dimension $2(N+1)$ and is strictly nonattaining. For $N=1$, scalar legality forces $M_1=0$ and the all-zero visible law; it fails the free-site band. This boundary does not settle arbitrary finite $N$.

An attainment construction must use one actual stationary common-matrix law across all lengths. At the rank-relaxation level, all candidate block kernels must be slices of a single global candidate. At the producer level they must additionally arise from the same $J_\theta/P_\theta$ and the same matrices. Ordinary marginals of that law are projective; guarded kernels at different lengths condition on different events and are not required to be projective. Ordinary rank at most two supplied the reset obstruction, but no converse to it or to any nonnegative-rank necessary condition is asserted.

## 8. Mathematical citations

[Universal][U], *FIB 合法边调和负载：普适后验缺陷与有限隐藏维数分离*: Convention 1.3 and Lemma 2.1 supply the original optimizer and growth interfaces; Definition 4.1 and Proposition 4.2 supply the entire exact-real domain and its joint law; (1.5) supplies the density/posterior identity; Theorem 3.1 supplies the necessary attained-law band; Theorem 6.2 supplies the compact separation alternative; Proposition 7.1 supplies the elementary two-state family and the strict lower comparison for $c_\star$.

**[Guarded]** *FIB harmonic-edge load: guarded replacement, attainment and conditional-rank obstruction*: Definition 1.1 supplies the ceiling for $c_\star$; Definitions 2.1 and 2.3 and Lemma 2.2 supply the additional endpoint premises; Lemmas 3.2–3.3, Definition 6.3 and Theorems 7.1 and 8.2 supply the conditional score, compact rank families, slicing and minor bounds; Theorem 5.1 and Corollary 6.4 supply the sufficient endpoint and its finite budget. The guarded replacement identity and its rank machinery retain this source's attribution.

**[Azuma]** Kazuoki Azuma, *Weighted sums of certain dependent random variables*, Tohoku Mathematical Journal, Second Series, 19(3), 357–367, [doi:10.2748/tmj/1178243286](https://doi.org/10.2748/tmj/1178243286). The bounded-martingale exponential method is classical; Lemma 4.3 contains the full estimate needed here. Conditional least squares, the law of total variance, elementary Markov conditioning, rank-one row factorization and the Vandermonde identity are the other classical ingredients in the displayed proofs.

[U]: FIB_LEGAL_EDGE_LOAD_UNIVERSAL_POSTERIOR_DEFECT_AND_FINITE_HIDDEN_SEPARATION.md

## 追加锚（本行以下为增补区）

## 9. Shared complete contexts and a spectral discrepancy bound

**Definition 9.1 (Unnormalized context weights and spectral tails).** Retain exactly $B_n$, $K_m^{a,b}$, $\mathcal D_K$, $\mathscr F_{N,n}^{0,0}$ and $\mathscr R_{N,n}$ from Definitions 1.1–1.3. Let $p$ be band-compatible on $B_n$, and let $C=[c,d]$ be an interior interval, so $1<c\le d<n$ and $m=d-c+1$. A complete complement is $\eta=(u,v)$ with $u=W_{[1,c-1]}$ and $v=W_{[d+1,n]}$. For each extendible $\eta$ write

$$
p_\eta=p(W_{C^c}=\eta)>0,\qquad
p_C^\eta(w)=p(W_C=w\mid W_{C^c}=\eta),\qquad
a=u_{c-1},\quad b=v_1.
\tag{9.1}
$$

Here and below $C^c$ in a finite-word conditional means $[1,n]\setminus C$. Let $S_C^{a,b}(p)$ have one row for every extendible complete complement with these adjacent bits, one column for every $w\in K_m^{a,b}$, and entries

$$
S_C^{a,b}(p)(\eta,w)=\sqrt{p_\eta}\,p_C^\eta(w).
\tag{9.2}
$$

The mass $p_\eta$ is not divided by $p(W_{c-1}=a,W_{d+1}=b)$. In particular, the four matrices retain their original relative weights. A type without rows gives the zero matrix. For a finite real matrix $S$ and integer $q\ge0$ put

$$
\operatorname{tail}_q(S)=\sum_{j>q}\sigma_j(S)^2,\qquad
c_m=\frac{6^{-4m}}{2m},
\tag{9.3}
$$

where singular values are decreasing and continued by zeros.

**Theorem 9.2 (Weighted shared-context lower bound).** For every $N\ge1$, every band-compatible $p$ on $B_n$, and every deterministic family of disjoint nonempty interior intervals $C_j$,

$$
\mathscr R_{N,n}(p)\ge
\sum_j c_{|C_j|}\sum_{a,b\in\{0,1\}}
\operatorname{tail}_{N^2}\bigl(S_{C_j}^{a,b}(p)\bigr).
\tag{9.4}
$$

Every comparison in the minimum on the left is one global $r\in\mathscr F_{N,n}^{0,0}$. All conditionals and weights on the right belong to the same $p$.

Proof. Fix such an $r$ and one interval $C=[c,d]$. Extend its word probabilities by zero to the whole binary cube, as in (1.7). The ordinary ranks at the cuts $c-1$ and $d$ are at most $N$, since ordinary rank is at most nonnegative rank. At the first cut choose $h\le N$ prefix rows indexed by $u_\alpha$ spanning all prefix rows. There are real coefficients $A_\alpha(u)$, independent of $w,v$, such that

$$
r(uwv)=\sum_{\alpha=1}^h A_\alpha(u)r(u_\alpha wv).
\tag{9.5}
$$

At the second cut choose a basis $D_\beta(v)$, $1\le\beta\le e\le N$, for the row space of the prefix/suffix matrix. For each $\alpha,w$ there are coefficients $H_{\alpha\beta}(w)$ with

$$
r(u_\alpha wv)=\sum_{\beta=1}^e H_{\alpha\beta}(w)D_\beta(v),\qquad
r(uwv)=\sum_{\alpha,\beta}A_\alpha(u)D_\beta(v)H_{\alpha\beta}(w).
\tag{9.6}
$$

Thus the matrix with rows $(u,v)$, columns $w$ and entries $r(uwv)$ has ordinary rank at most $he\le N^2$. These equalities hold on the full binary cube, including every illegal entry. The auxiliary real coefficients need not be nonnegative. This is the two-cut linear-factorization mechanism also underlying the context rank in [Intrinsic, §2][SC-I]; it is used only as a necessary condition on the given global $r$.

Both $p$ and $r$ are positive on $B_n$ by Definition 1.3. Hence every extendible complement has $r_\eta=r(W_{C^c}=\eta)>0$. For a fixed adjacent-bit type define

$$
T_C^{a,b}(\eta,w)=\sqrt{p_\eta}\,r_C^\eta(w),\qquad
r_C^\eta(w)=\frac{r(uwv)}{r_\eta}.
\tag{9.7}
$$

Restricting the matrix in (9.6) to those rows and to $K_m^{a,b}$, then scaling row $\eta$ by $\sqrt{p_\eta}/r_\eta$, gives $T_C^{a,b}$. Consequently its ordinary rank is at most $N^2$. For every such row, $p_C^\eta$ and $r_C^\eta$ are band-compatible on exactly the same $K_m^{a,b}$: each insertion inequality is an original inequality divided by the corresponding fixed positive complement mass.

The global single-site predictors at sites in $C$, after the entire complement is fixed, are exactly the single-site predictors of these conditional block laws. Disintegration, [Guarded, Lemma 8.1][SC-G] and $\|x\|_1\ge\|x\|_2$ give

$$
\begin{aligned}
\sum_{i\in C}\mathbb E_p(p_i(W_{-i})-r_i(W_{-i}))^2
&=\sum_\eta p_\eta\mathcal D_{K_m^{a,b}}(p_C^\eta\Vert r_C^\eta)\\
&\ge c_m\sum_\eta p_\eta\|p_C^\eta-r_C^\eta\|_1^2\\
&\ge c_m\sum_{a,b}\|S_C^{a,b}(p)-T_C^{a,b}\|_F^2.
\end{aligned}
\tag{9.8}
$$

In the first two sums $a,b$ are the adjacent bits of that $\eta$. Forced fibers have zero single-site discrepancy; singleton completion sets satisfy the same inequality. Nonextendible complements contribute zero and require no denominator.

The needed low-rank approximation inequality is the classical orthogonal-projection bound [Eckart–Young][SC-EY], also used in [Whitebox, Theorem 43.5][SC-W]. Explicitly, if $T$ has rank at most $q$ and $Q$ is the orthogonal projection onto its column space, then

$$
\|S-T\|_F^2\ge\|(I-Q)S\|_F^2
=\operatorname{tr}(SS^{\mathsf T})-\operatorname{tr}(QSS^{\mathsf T})
\ge\sum_{j>q}\sigma_j(S)^2.
\tag{9.9}
$$

To obtain the last inequality, diagonalize $SS^{\mathsf T}$. The diagonal entries of $Q$ in that basis lie in $[0,1]$ and sum to at most $q$, so their pairing with the decreasing nonnegative eigenvalues is at most the sum of the first $q$. Apply (9.9) to each term of (9.8) with $q=N^2$. The site sums for disjoint $C_j$ are distinct summands of $\mathcal D_{B_n}(p\Vert r)$, even if their complements or adjacent bits overlap. They can therefore be added without independence. Minimize over this single global $r$. If the family is empty its value is $+\infty$, so (9.4) still holds. $\square$

## 10. All finite comparison ranks admit a global/local separation

**Theorem 10.1 (One common stationary law at every comparison rank).** For every integer $N\ge2$, set

$$
k=N^2+1,\qquad m=2N^2=2(k-1),\qquad
 a_\ell=\frac13+\frac{\ell-1}{24N^2},\qquad w_\ell=\frac1k,
\quad 1\le\ell\le k.
\tag{10.1}
$$

Use the two-state $A_\ell,\lambda_\ell,D_x$ of (3.2) with these parameters, and define

$$
M_x^{(N)}=\bigoplus_{\ell=1}^kD_xA_\ell,\qquad
\lambda^{(N)}=(w_1\lambda_1,\ldots,w_k\lambda_k).
\tag{10.2}
$$

This is one element of the original $\Theta_{2k}$. Its actual stationary law is

$$
P^{(N)}=\sum_{\ell=1}^kw_\ell R^{a_\ell},\qquad
\mu_n=P^{(N)}_{[1,n]},\qquad
\mu_n(w)=\lambda^{(N)}M_{w_1}^{(N)}\cdots M_{w_n}^{(N)}\mathbf1
\quad\text{for every }n.
\tag{10.3}
$$

All legal words have positive mass and every $\mu_n$ is band-compatible. Define

$$
\begin{aligned}
z_\ell&=\frac{a_\ell}{(1-a_\ell)^2},&
\rho_\ell&=\frac{a_\ell}{1+a_\ell},&
\Delta&=\min_{\ell\ne h}|\rho_\ell-\rho_h|>0,\\
Z_\ell&=\sum_{w\in B_m}z_\ell^{k(w)},&
v_\ell(w)&=\frac{z_\ell^{k(w)}}{Z_\ell},&
b_\ell&=\lambda_{\ell,0}(A_\ell^{m+1})_{00}>0,\\
G&=\sum_{\ell=1}^kw_\ell b_\ell v_\ell v_\ell^{\mathsf T},&
\gamma&=\lambda_k(G)>0.
\end{aligned}
\tag{10.4}
$$

The $v_\ell$ are column probability vectors on $B_m$; $\lambda_{\ell,0}=1/(1+a_\ell)$, and eigenvalues are decreasing. For every $n>m$ with $(n-m)\Delta\ge8$,

$$
\mathscr R_{N,n}(\mu_n)\ge
c_m\left\lfloor\frac{n-2}{m}\right\rfloor
\left[\gamma-4\exp\left(-\frac{(n-m)\Delta^2}{64}\right)\right]_+,
\qquad [x]_+=\max(x,0).
\tag{10.5}
$$

In particular,

$$
\liminf_{n\to\infty}\frac{\mathscr R_{N,n}(\mu_n)}n
\ge\frac{c_m\gamma}{m}>0.
\tag{10.6}
$$

In contrast, for every fixed $t\ge1$, every $n>t$ with $(n-t)\Delta\ge8$, and every deterministic family of disjoint length-$t$ intervals $C_j\subseteq[1,n]$,

$$
\sum_j\mathbb E_{\mu_n}\delta_{N,t}^{a_j,b_j}
\bigl(\mu_n(W_{C_j}=\cdot\mid W_{C_j^c})\bigr)
\le2n\exp\left(-\frac{(n-t)\Delta^2}{64}\right)\longrightarrow0.
\tag{10.7}
$$

The adjacent bits in (10.7) are the actual observed adjacent bits, with zero at an open endpoint as in (1.10).

Proof. The parameters in (10.1) lie in $[1/3,3/8]$ and are distinct. The persistent-mixture construction of Propositions 3.2–3.3 applies to any finite number of positive-weight components: their proofs use only the displayed parameter range, positive weights and block-diagonal matrices. Equivalently, apply those propositions with their component-count parameter equal to $k-1$, then compare against the rank $N$ used here. Each $A_\ell$ is stochastic, $\lambda_\ell A_\ell=\lambda_\ell$ and $(D_1A_\ell)^2=0$. Thus (10.2) directly satisfies every condition in (1.3). The joint law (1.4) has a persistent label $L\in\{1,\ldots,k\}$, and conditional on $L=\ell$ its visible law is $R^{a_\ell}$. All expectations involving $L$ below are under this one joint law, denoted $J^{(N)}$.

The component insertion ratios, including $n=1$ and open endpoints, are exactly (3.4), and their linear inequalities survive the mixture. Each component whole-word marginal and each actual component block conditional has all nonnegative cut ranks at most two. Thus $\mathscr F_{N,n}^{0,0}$ is nonempty for $N\ge2$, and the component conditional is feasible in $\mathscr F_{N,t}^{a,b}$, including endpoint blocks and singleton completion sets. No conversion from real rank to a stationary realization is being made; (10.2) already supplies the actual nonnegative realization and all seams.

The $z_\ell$ are distinct because $a/(1-a)^2$ is strictly increasing on $(0,1)$. For $0\le j\le k-1$ the legal word

$$
w_j=(10)^j0^{m-2j}\in B_m
\tag{10.8}
$$

has $j$ ones, also at $j=k-1$ when the final zero string is empty. The matrix with rows $j$ and columns $\ell$ given by $v_\ell(w_j)=z_\ell^j/Z_\ell$ has determinant

$$
\left(\prod_{\ell=1}^kZ_\ell^{-1}\right)
\prod_{\ell<h}(z_h-z_\ell)\ne0.
\tag{10.9}
$$

Hence the vectors $v_\ell$ are linearly independent. The coefficient $b_\ell$ is the stationary probability, under component $\ell$, that the two endpoints of a segment of $m+1$ transitions are both zero. It is positive, for example because the all-zero path has positive probability. Therefore $G$ has rank $k$ and $\gamma=\lambda_k(G)>0$.

Fix any interior length-$m$ interval $C=[c,d]$ and put

$$
\mathcal H=\sigma(W_{C^c}),\qquad
\theta_\ell=J^{(N)}(L=\ell\mid\mathcal H),\qquad
E=\{W_{c-1}=W_{d+1}=0\}\in\mathcal H.
\tag{10.10}
$$

These are the posterior weights given the entire finite complement, not just its adjacent bits. On $E$, Proposition 3.3 gives the exact identity

$$
\mu_n(W_C=\cdot\mid\mathcal H)=\sum_{\ell=1}^k\theta_\ell v_\ell
=\mathbb E_{J^{(N)}}[v_L\mid\mathcal H].
\tag{10.11}
$$

Stationarity and the actual component transition law give

$$
J^{(N)}(L=\ell,E)=w_\ell b_\ell.
\tag{10.12}
$$

In particular these weights are not replaced by the prior $w_\ell$ or normalized by $J^{(N)}(E)$.

The complement contains a contiguous observed segment of length $s\ge(n-m)/2$. Lemma 4.3 applies under every component because $s\Delta\ge4$, including equality. Its nearest-mean classifier uses only that segment and has error at most

$$
\varepsilon_n=2\exp\left(-\frac{(n-m)\Delta^2}{64}\right).
\tag{10.13}
$$

Given $\mathcal H$, the least conditional error of a label guess is $1-\max_\ell\theta_\ell$. A guess using the whole complement can use this segment classifier, so

$$
\mathbb E_{J^{(N)}}(1-\max_\ell\theta_\ell)\le\varepsilon_n.
\tag{10.14}
$$

The bound is uniform in the position of $C$ for this fixed law. The constants depend on its separated means; there is no parameter-uniform rate.

Let $V=v_L$ as a random column vector, and put

$$
G_{n,C}=\bigl(S_C^{0,0}(\mu_n)\bigr)^{\mathsf T}S_C^{0,0}(\mu_n).
$$

Equations (9.2), (10.11) and (10.12), with the original complement masses in (9.2), yield

$$
\begin{aligned}
G&=\mathbb E_{J^{(N)}}[\mathbf1_EVV^{\mathsf T}],\\
G_{n,C}&=\mathbb E_{J^{(N)}}\left[\mathbf1_E
\mathbb E[V\mid\mathcal H]\mathbb E[V\mid\mathcal H]^{\mathsf T}\right],\\
G-G_{n,C}&=\mathbb E_{J^{(N)}}[\mathbf1_E\operatorname{Cov}(V\mid\mathcal H)]\succeq0.
\end{aligned}
\tag{10.15}
$$

At a given complement choose an index $h$ of largest $\theta_h$. Conditional means minimize squared Euclidean error. Since probability vectors have squared Euclidean distance at most two,

$$
\begin{aligned}
\operatorname{tr}\operatorname{Cov}(V\mid\mathcal H)
&\le\sum_\ell\theta_\ell\|v_\ell-v_h\|_2^2
\le2(1-\theta_h),\\
\|G-G_{n,C}\|_{\mathrm{op}}
&\le\operatorname{tr}(G-G_{n,C})
\le2\varepsilon_n.
\end{aligned}
\tag{10.16}
$$

For the second line, positivity in (10.15) bounds the operator norm by the trace, and dropping $\mathbf1_E$ enlarges a nonnegative expectation. The eigenvalue variational principle gives

$$
\lambda_k(G_{n,C})\ge\gamma-2\varepsilon_n,\qquad
\operatorname{tail}_{N^2}(S_C^{0,0}(\mu_n))
\ge[\gamma-2\varepsilon_n]_+,
\tag{10.17}
$$

because $k=N^2+1$. Choose $\lfloor(n-2)/m\rfloor$ consecutive disjoint length-$m$ intervals in $[2,n-1]$. Apply Theorem 9.2, retaining only their $00$ types. Equations (10.13) and (10.17) prove (10.5), and division by $n$ gives (10.6). The contexts of neighboring chosen blocks may overlap; Theorem 9.2 requires only disjoint site sets.

For (10.7), fix $t$ and a block $C_j$ of that length. Under the same $J^{(N)}$ define $\theta_{\ell,j}=J^{(N)}(L=\ell\mid W_{C_j^c})$. Its actual conditional is the mixture of its actual component conditionals with these weights, as in (3.5). Lemma 4.2, with comparison rank $N\ge2$, gives

$$
\delta_{N,t}^{a_j,b_j}\bigl(\mu_n(W_{C_j}=\cdot\mid W_{C_j^c})\bigr)
\le t(1-\max_\ell\theta_{\ell,j}).
\tag{10.18}
$$

Indeed, its proof compares with a largest-weight feasible rank-two component, using convexity in the first argument of $\mathcal D_K$ and the bound $t$ on that discrepancy. It does not require an interior block. A complement segment has length at least $(n-t)/2$, so the same application of Lemma 4.3 and Bayes comparison gives

$$
\mathbb E_{J^{(N)}}(1-\max_\ell\theta_{\ell,j})
\le2\exp\left(-\frac{(n-t)\Delta^2}{64}\right).
\tag{10.19}
$$

There are at most $n/t$ disjoint blocks, proving (10.7). At an endpoint the component law in (10.18) is its true conditional; (3.6) is not used there. Thus the statement retains open endpoints, all original legal words, the same common matrices at every length and the entire complement in every predictor. $\square$

## 11. The actual-optimizer consumer and its spectral premise

**Corollary 11.1 (Shared-context sufficient inequality on the original optimizer).** For fixed $N\ge1$, $n\ge1$ and disjoint nonempty interior intervals $C_j$, define

$$
\Lambda_{N,n}(\pi_n;\{C_j\})=
\sum_jc_{|C_j|}\sum_{a,b\in\{0,1\}}
\operatorname{tail}_{N^2}\bigl(S_{C_j}^{a,b}(\pi_n)\bigr).
\tag{11.1}
$$

If

$$
\Lambda_{N,n}(\pi_n;\{C_j\})>
\tau=2(3-2\sqrt2)-\frac1{24},
\tag{11.2}
$$

then $C_N<c_\star$ on the entire original $\Theta_N$ of (1.3).

Proof. The fixed-producer geometric entropy-tail bound of [Stripping, Theorems 3.1, 5.1 and 6.5][SC-S], together with the same-law whole-half-line comparison of [Entropy erasure, Theorem 3.1][SC-H], supplies $A_{P_\theta}<\infty$ for every fixed finite $\theta\in\Theta_N$. Specifically, the comparison bounds each $e_L(j),e_R(j)$ by half the geometrically decreasing $R_j$ of Stripping; their square roots are summable. The zero-tail case has the same conclusion. This reuse needs no band, identifiability, irreducibility, aperiodicity or uniformity over $\Theta_N$.

Suppose a single $\theta\in\Theta_N$ attained $d(P_\theta)=c_\star$. Its band follows from [Universal, Theorem 3.1][U]. The just cited root sum and [Attainment, Theorem 1.5 and Corollary 9.1][SC-A] give strong zero for that same actual law and its original full-exterior predictors. [Guarded, Corollary 6.4][SC-G] therefore applies to that $J_\theta/P_\theta$ and gives

$$
\mathcal R_{N,n}\le(n+2)c_\star-\kappa_n-\frac1{24}\le\tau.
\tag{11.3}
$$

Its guarded kernels are the actual conditional laws supplied by [Guarded, Theorem 6.2][SC-G], not laws inferred from a rank converse. Theorem 9.2 with $p=\pi_n$ gives $\mathcal R_{N,n}\ge\Lambda_{N,n}(\pi_n;\{C_j\})$, contradicting (11.2). Thus no $\theta\in\Theta_N$ attains $c_\star$. The fixed-dimension maximum theorem [Universal, Theorem 6.2][U] then makes the gap strict: $C_N=\max_{\theta\in\Theta_N}d(P_\theta)<c_\star$. All implications apply to the entire original domain, including stationary mixtures, structural zeros, zero stationary masses, reducibility, periodicity and redundant presentations. $\square$

**Proposition 11.2 (Scope of the compatibility separation).** For every $N\ge2$, Theorem 10.1 disproves the implication from vanishing sums of independently minimized fixed-block discrepancies, for every fixed block length, to $\mathscr R_{N,n}(\mu_n)=o(n)$, even among marginals of one actual stationary finite producer with the band at every length. The law in that theorem satisfies

$$
A_{P^{(N)}}\le2,\qquad d(P^{(N)})\le\frac17<c_\star,
\qquad\neg\mathsf Z_\Delta(P^{(N)}).
\tag{11.4}
$$

It supplies no instance of (11.2). A sufficient unresolved optimizer inequality for each intended $N$ is precisely

$$
\exists n,\ \exists\{C_j\}\text{ disjoint interior intervals}:\quad
\sum_j\frac{6^{-4|C_j|}}{2|C_j|}
\sum_{a,b}\operatorname{tail}_{N^2}\bigl(S_{C_j}^{a,b}(\pi_n)\bigr)>\tau.
\tag{11.5}
$$

Proof. The two limits (10.6)–(10.7) contradict that implication for the same law $P^{(N)}$. Proposition 6.3 applies to its finite persistent mixture, proving (11.4) with the original entire-exterior density. Its exhibited hidden dimension is $2(N^2+1)$, whereas the comparison rank is $N$; it is not an $N$-state attainer. Every matrix in (11.5) instead uses the conditionals and weights of the actual full optimizer $\pi_n$. Theorems 9.2 and 10.1 establish neither a positive lower bound for those tails nor a coupling that transfers (10.17) to them. The implication from (11.5) is Corollary 11.1, whose strict spectral premise remains additional. In particular, no all-$N$ strict-gap conclusion or finite attainer follows from this comparison construction. $\square$

## 12. Mathematical citations for the shared-context criterion

[Guarded][SC-G], *FIB harmonic-edge load: guarded replacement, attainment and conditional-rank obstruction*, Lemma 8.1 supplies the constant $c_m$ on the hard legal completion graph, including singleton and forcing cases. Definition 6.3 supplies the all-cut nonnegative-rank family; Theorem 6.2 and Corollary 6.4 supply the actual-law guarded conditional and its budget. Propositions 3.2–3.3 and Lemmas 4.2–4.3 of the present volume supply the stationary mixture, actual conditional weights, independent-fit bound and classifier; Theorem 5.1 is its rank-two global/local separation. These remain the suppliers for Theorems 9.2 and 10.1.

[Intrinsic][SC-I], *FIB harmonic-edge load: intrinsic-null kernels, dual residuals and presentation obstruction*, §2 supplies the finite-realization context-rank mechanism. [Whitebox][SC-W], *FIB atom machine-learning whitebox*, Theorem 43.5 supplies the weighted projection/spectral-tail mechanism in a different readout problem. [Product-upper and phase-cut rank][SC-P], §23 concerns upper Schmidt-tail bounds for coherent square-root probability amplitudes. Those matrices and upper bounds are different from the weighted conditional probability tables and lower Brier-discrepancy bound in (9.2)–(9.4).

[Dawid–Lauritzen–Parry][SC-DLP], *Proper local scoring rules on discrete sample spaces*, §4.2, Example 4.4 and (14), gives the conditional Brier/ratio-matching background. Its everywhere-positive product-space hypotheses are not a substitute for the hard no11 graph coercivity cited above. [Balle–Panangaden–Precup][SC-BPP], *A Canonical Form for Weighted Automata and Applications to Approximate Minimization*, §2.2, treats real weighted realizations and Hankel rank factorization. No positive stationary realization converse is used here. [Eckart–Young][SC-EY], *The Approximation of One Matrix by Another of Lower Rank*, is the classical matrix approximation reference; the full lower-bound argument needed here is (9.9). The discrepancy application and its common-law comparison in §§9–11 are a synthesis of these tools, without a literature-priority assertion.

[Stripping][SC-S], *Equivalent-mass stripping and exponential terminal information*, Theorems 3.1, 5.1 and 6.5, gives fixed-producer geometric entropy tails on the original full domain. [Entropy erasure][SC-H], *Entropy gaps and actual erased-center influence*, Theorem 3.1, compares those tails with both actual complete-half-line erasure defects. [Attainment][SC-A], *Attainment, strong-zero equivalence and finite-optimizer comparison*, Theorem 1.5 and Corollary 9.1, supplies the attainment-to-strong-zero bridge under the resulting root sum. The constants remain law-dependent, and the common-law spectral premise (11.5) is separate from every one of these suppliers.

[SC-G]: FIB_LEGAL_EDGE_LOAD_GUARDED_REPLACEMENT_ATTAINMENT_AND_CONDITIONAL_RANK_OBSTRUCTION.md
[SC-I]: FIB_LEGAL_EDGE_LOAD_INTRINSIC_NULL_KERNEL_DUAL_RESIDUAL_AND_PRESENTATION_OBSTRUCTION.md
[SC-W]: FIB_ATOM_MACHINE_LEARNING_WHITEBOX.md
[SC-P]: FIB_LEGAL_EDGE_LOAD_PRODUCT_UPPER_EDGE_FIELD_STABILITY_AND_PHASE_CUT_RANK.md
[SC-S]: FIB_LEGAL_EDGE_LOAD_EQUIVALENT_MASS_STRIPPING_EXPONENTIAL_TERMINAL_INFORMATION.md
[SC-H]: FIB_LEGAL_EDGE_LOAD_ENTROPY_ERASURE_INFLUENCE_WEIGHTED_MOMENT.md
[SC-A]: FIB_LEGAL_EDGE_LOAD_ATTAINMENT_STRONG_ZERO_EQUIVALENCE_AND_FINITE_OPTIMIZER_COMPARISON.md
[SC-DLP]: https://arxiv.org/html/1104.2224v2
[SC-BPP]: https://arxiv.org/html/1501.06841v3
[SC-EY]: https://doi.org/10.1007/BF02288367

## 追加锚（本行以下为增补区）
