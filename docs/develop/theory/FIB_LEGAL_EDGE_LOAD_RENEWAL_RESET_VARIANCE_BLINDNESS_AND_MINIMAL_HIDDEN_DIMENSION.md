# FIB harmonic-edge load: renewal reset-variance blindness and minimal hidden dimension

One stationary three-state renewal law has zero two-anchor reset variance at every finite length, yet its discrepancy from every single global rank-two candidate grows linearly. A six-bit conditional bridge supplies the positive determinant, the discrepancy constant and the proof that three hidden states are necessary. The same law satisfies the posterior band and square-root erasure summability, and its actual radius-one risk proves strict nonattainment. These conclusions concern its stationary marginals, not the finite optimizers of the original harmonic-edge objective.

## 1. Complete objective, producer domain and original-law interfaces

**Definition 1.1 (Open words and all legal edges).** For $n\ge1$ put

$$
B_n=\{w\in\{0,1\}^n:w_iw_{i+1}=0\ (1\le i<n)\},\qquad
\mathsf X=\{x\in\{0,1\}^{\mathbb Z}:x_ix_{i+1}=0\ (i\in\mathbb Z)\}.
\tag{1.1}
$$

$B_0$ contains the empty word $\varepsilon$. The graph $\Gamma_n$ has every vertex in $B_n$ and every legal Hamming-one edge. An insertion at an endpoint uses the convention $w_0=w_{n+1}=0$, without identifying the endpoints or observing additional random bits. On the whole simplex $\mathcal P(B_n)$ define

$$
h(s,t)=\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}\quad
\Phi_n(\nu)=\sum_{\{u,v\}\in E(\Gamma_n)}h(\nu_u,\nu_v),\quad
\kappa_n=\max_{\nu\in\mathcal P(B_n)}\Phi_n(\nu).
\tag{1.2}
$$

Zero masses remove no words, edges or forbidden seams. The all-zero word, legal words beginning or ending in one, and both open endpoints remain part of this objective. Write $k(w)=\sum_iw_i$.

**Premise 1.2 (Credited optimizer and growth facts).** [Universal, Convention 1.3, Lemma 2.1 and Proposition 7.1][U] supplies the positive finite optimizer $\pi_n$, its insertion band, and

$$
\begin{gathered}
\Phi_n(\pi_n)=\kappa_n,\qquad
\tfrac13\pi_n(u)\le\pi_n(v)\le\pi_n(u)\quad(u\to v\text{ inserts one}),\\
c_\star=\lim_{n\to\infty}\frac{\kappa_n}{n},\qquad
nc_\star\le\kappa_n\le(n+1)c_\star,\qquad
\frac{\kappa_n}{n+1}\longrightarrow c_\star,\qquad
c_0:=\frac{1800}{12559}\le c_\star.
\end{gathered}
\tag{1.3}
$$

The ceiling $c_\star\le\bar c:=3-2\sqrt2$ is the interface in [Guarded, Definition 1.1]. If $a_{n,i}$ is the $\pi_n$ posterior given all other $n-1$ bits, and $p_{\nu,n,i}$ is the corresponding posterior under $\nu$, the supplied finite identity is

$$
\kappa_n-\Phi_n(\nu)=\sum_{i=1}^n
\mathbb E_\nu(p_{\nu,n,i}-a_{n,i})^2.
\tag{1.4}
$$

Forced singleton fibers have posterior zero. A null fiber has zero weight and requires no conditional division. These conventions include $n=1$. The symbol $\pi_n$ always denotes this actual optimizer; it will never denote the comparison marginal constructed below.

**Definition 1.3 (Entire exact-real domain).** For every finite $N\ge1$ retain

$$
\Theta_N=\left\{(\lambda,M_0,M_1):
\begin{array}{l}
\lambda\ge0,\quad\lambda\mathbf1=1,\quad M_0,M_1\ge0,\\
A=M_0+M_1,\quad A\mathbf1=\mathbf1,\quad\lambda A=\lambda,\quad
\lambda M_1^2\mathbf1=0
\end{array}\right\}.
\tag{1.5}
$$

$\lambda$ is a row, $M_0,M_1$ are $N\times N$ matrices with arbitrary exact-real entries, and $\mathbf1$ is the all-one column. Structural zeros, zero stationary masses, reducibility, periodicity and noncontractive presentations are allowed. The legality condition is scalar; entrywise $M_1^2=0$ is not required of this domain. Set $M_w=M_{w_1}\cdots M_{w_n}$ and $M_\varepsilon=I$.

For a word $w$, $[w]_a$ specifies $X_a,\ldots,X_{a+|w|-1}=w$, and $[w]=[w]_1$. The common-matrix convention is the single actual joint law

$$
J_\theta(H_a=h_a,\ldots,H_{b+1}=h_{b+1},X_a=x_a,\ldots,X_b=x_b)
=\lambda_{h_a}\prod_{i=a}^bM_{x_i}(h_i,h_{i+1}),\qquad
P_\theta([w]_a)=\lambda M_w\mathbf1.
\tag{1.6}
$$

Here $P_\theta$ is the visible marginal. Right consistency follows from $A\mathbf1=\mathbf1$, left consistency from $\lambda A=\lambda$, and normalization from $\lambda\mathbf1=1$. The consistent finite distributions therefore extend to a stationary probability on the two-sided finite-alphabet space, as in [Universal, Proposition 4.2][U]. Scalar legality makes each adjacent $11$ event null; their countable union is null. Every seam is evaluated by the ordered product in (1.6), with the clock counting original emitted bits.

**Definition 1.4 (Actual exterior predictors and risk).** For any stationary legal $P$, $i\in\mathbb Z$ and integer $r\ge1$, let

$$
\begin{gathered}
\mathcal E_i=\sigma(X_j:j\ne i),\qquad F_i=\{X_{i-1}=X_{i+1}=0\},\qquad
q_i=\mathbb E_P[X_i\mid\mathcal E_i],\\
\mathcal F_r=\sigma(X_{-r},\ldots,X_{-1},X_1,\ldots,X_r),\qquad
q_{r,0}=\mathbb E_P[X_0\mid\mathcal F_r],\qquad
D_r(P)=\mathbb E_P(X_0-q_{r,0})^2.
\end{gathered}
\tag{1.7}
$$

Take $[0,1]$ exterior-measurable versions, with $q_i=q_0\circ T^i$ for $(Tx)_j=x_{j+1}$. [Universal, (1.5)][U] supplies, on the entire stationary legal class,

$$
D_r(P)\downarrow d(P)=\mathbb E_P(X_0-q_0)^2
=\lim_{n\to\infty}\frac{\Phi_n(P_{[1,n]})}{n}\le c_\star.
\tag{1.8}
$$

The band $\mathsf B(P)$ means that, almost surely for every $i$, $q_i=0$ on $F_i^c$ and $1/4\le q_i\le1/2$ on $F_i$. [Universal, Theorem 3.1][U] makes it necessary for attainment. It is not an additional restriction in (1.5).

## 2. Conditional discrepancy, rank families and the reset detector

**Definition 2.1 (Completion sets and the original score).** For boundary bits $\xi,\zeta\in\{0,1\}$ set

$$
K_m^{\xi,\zeta}=\{w\in B_m:\xi w_1=w_m\zeta=0\},\qquad m\ge1.
\tag{2.1}
$$

Keep every legal Hamming-one edge of this set. A probability $\nu$ on it is band-compatible when $\nu_u/3\le\nu_v\le\nu_u$ on every insertion edge $u\to v$. For $W\sim\nu$, let $\nu_i(w_{-i})=\nu(W_i=1\mid W_{-i}=w_{-i})$, conditioning on all the other bits. Given a positive probability $r$ on the same set, use these full finite-complement posteriors to define

$$
\begin{aligned}
\mathcal D_K(\nu\Vert r)
&=\sum_{i=1}^m\mathbb E_\nu\bigl(\nu_i(W_{-i})-r_i(W_{-i})\bigr)^2\\
&=\sum_{u\to v}(\nu_u+\nu_v)
\left(\frac{\nu_v}{\nu_u+\nu_v}-\frac{r_v}{r_u+r_v}\right)^2.
\end{aligned}
\tag{2.2}
$$

A zero-total $\nu$ edge contributes zero without division. Forced singleton fibers have zero posterior under both laws. Write $\Phi_K$ for the edge sum of $h$ on this graph. These are [Guarded, Definition 3.1]'s interfaces.

**Lemma 2.2 (Score identity and positive compact band).** The graph on $K=K_m^{\xi,\zeta}$ is connected. Every band-compatible probability is positive and satisfies

$$
\nu_{0^m}\ge |K|^{-1},\qquad
\nu_w\ge3^{-k(w)}\nu_{0^m}\ge\alpha_m:=6^{-m}.
\tag{2.3}
$$

Moreover

$$
\mathbb E_\nu\sum_i(W_i-r_i(W_{-i}))^2
=\Phi_K(\nu)+\mathcal D_K(\nu\Vert r).
\tag{2.4}
$$

For positive $\nu,r$, $\mathcal D_K(\nu\Vert r)=0$ if and only if $\nu=r$.

Proof. Delete ones to reach $0^m$, and insert the desired nonadjacent ones to reach any other compatible word. The insertion inequalities make every mass at most $\nu_{0^m}$, so normalization gives the first inequality in (2.3). Inserting back gives the second, and $|K|\le2^m$, $k(w)\le m$ give the displayed floor. For (2.4), condition on $W_{-i}$ and expand the square around its conditional mean under $\nu$. The cross term vanishes. The weighted variance on a two-point fiber is $h(\nu_u,\nu_v)$, and a forced fiber contributes zero. Summing proves the identity. Zero discrepancy under positivity equates the posterior odds on every edge, making $r_w/\nu_w$ constant on the connected graph; normalization makes that constant one. For a singleton graph there is only one probability and the same conclusion holds. These are the constrained-graph arguments of [Guarded, Lemmas 3.2–3.3]. $\square$

**Definition 2.3 (All-cut families and global minima).** Extend a probability on $K_m^{\xi,\zeta}$ by zero to the full binary cube. Its cut matrix is

$$
\mathsf F_j(r)(u,v)=r(uv),\qquad
u\in\{0,1\}^j,\quad v\in\{0,1\}^{m-j},\quad1\le j<m.
\tag{2.5}
$$

Every forbidden internal or boundary seam stays a zero entry. Nonnegative rank is the least number of nonnegative rank-one summands. Let $\mathscr F_{N,m}^{\xi,\zeta}$ consist of the band-compatible probabilities with nonnegative rank at most $N$ at every internal cut. For a band-compatible reference probability $\nu$ on the indicated completion set, use [Guarded, Definition 6.3] and [Global-local, Definition 1.3]'s quantities

$$
\delta_{N,m}^{\xi,\zeta}(\nu)
=\min_{r\in\mathscr F_{N,m}^{\xi,\zeta}}\mathcal D_{K_m^{\xi,\zeta}}(\nu\Vert r),\qquad
\mathscr R_{N,n}(\nu)=\delta_{N,n}^{0,0}(\nu),\qquad
\mathcal R_{N,n}=\mathscr R_{N,n}(\pi_n).
\tag{2.6}
$$

The empty minimum is $+\infty$. At length one there are no cut conditions. A singleton completion set has discrepancy zero. The families are relaxations; membership does not assert a stationary extension or a common hidden producer.

For later use, a nonempty family is compact and its minimum is attained. Indeed, the band is closed and (2.3) gives a common positive floor. For each fixed cut, probability matrices of nonnegative rank at most $N$ are the image of the compact set

$$
R=\sum_{h=1}^Nt_h a_hb_h^{\mathsf T},\qquad
t_h\ge0,\quad\sum_ht_h=1,
\quad a_h,b_h\text{ probability vectors}.
\tag{2.7}
$$

To obtain this representation, normalize each nonzero nonnegative factor by its coordinate sum and put the product of the two sums into $t_h$; zero terms can use arbitrary probability factors. The entries of $R$ sum to one. The continuous image is compact, hence closed. Intersect the finitely many cut conditions and the band. All compatible-edge denominators in (2.2) are bounded away from zero there, so the discrepancy is continuous. This is the compactness argument of [Guarded, Theorem 6.2 and Definition 6.3].

**Definition 2.4 (Two-anchor reset variance).** For a positive band-compatible $\nu$ on $B_n$, let $p_{\nu,n,i}$ condition on all the other coordinates in $[1,n]$. For $n\ge5$ put

$$
E_i=\{W_{i-2}=W_{i+2}=1\},\qquad
V_2(\nu;n)=\sum_{i=3}^{n-2}\nu(E_i)
\operatorname{Var}_\nu(p_{\nu,n,i}\mid E_i).
\tag{2.8}
$$

Set $V_2(\nu;n)=0$ when $n<5$. This is [Global-local, Theorem 2.3]'s detector, with interface

$$
\mathscr R_{2,n}(\nu)\ge V_2(\nu;n).
\tag{2.9}
$$

To recall why this is only a lower bound, fix one positive all-cut rank-two candidate $r$. At a cut after $j<n$ bits, rows ending in one vanish on columns beginning in one. Every legal row ending in one is nonzero, since its all-zero-suffix entry is positive. A legal row ending in zero has a positive entry in column $10^{n-j-1}$. Therefore the legal rows ending in one span exactly one dimension: a two-dimensional span there would force total rank at least three. Illegal-prefix rows remain zero and do not affect the span. Normalizing the nonzero proportional rows shows that their suffix laws agree. At a visible one, the left and right strings are thus conditionally independent. Apply this at both anchors in $E_i$: the masses of $\ell\,10x01\,t$ factor as $A(\ell)H_xB(t)$, so $r_i$ is constant on that event. Empty outer strings are allowed. Least squares against this constant bounds the site's discrepancy below by the corresponding term of (2.8). Sum over distinct sites, then minimize over this one global $r$, to obtain (2.9); the empty-family case is immediate. The forthcoming law shows that equality to zero in this particular detector does not imply a zero or sublinear global discrepancy.

## 3. A fixed nonempty symbolic parameter family

**Definition 3.1 (Parameters and finite rational conditions).** Choose exact reals

$$
\frac13<a<b<\frac38,\qquad0<p<1,
\quad c=1-p,\quad s=1-a,\quad t=1-b,
\tag{3.1}
$$

and write

$$
\begin{gathered}
k=pa+cb,\qquad k_1=pa s+cb t,\qquad k_2=pa s^2+cb t^2,\qquad
Z=1+\frac pa+\frac cb,\\
L(p)=\frac{p^2a^2}{ks^2},\qquad
U(p)=\frac{k^2}{pa s^2},\qquad
H(p)=\frac{ps^2}{a}+\frac{ct^2}{b},\qquad
\mathsf D_1(p)=\frac{H(p)}{Z(H(p)+1)}.
\end{gathered}
\tag{3.2}
$$

The subfamily $\mathcal S$ is specified by (3.1) and the three strict inequalities

$$
L(p)>\frac13,\qquad U(p)<1,\qquad \mathsf D_1(p)<c_0.
\tag{3.3}
$$

The symbol $k$ in (3.2) is a scalar; $k(w)$ still counts ones in a word. The function $\mathsf D_1$ will be proved to be the actual radius-one risk of the law, not a surrogate density.

**Lemma 3.2 (Symbolic nonemptiness).** For every fixed $1/3<a<b<3/8$, all $p<1$ sufficiently close to one belong to $\mathcal S$.

Proof. The finite rational functions in (3.2) have positive denominators at $p=1$ and extend continuously there. At that point

$$
L(1)=U(1)=\frac{a}{(1-a)^2},\qquad
\frac34<\frac{a}{(1-a)^2}<\frac{24}{25}<1.
\tag{3.4}
$$

The middle inequalities follow directly from $1/3<a<3/8$ and $5/8<1-a<2/3$. In particular both required inequalities involving $L,U$ are strict at one. Also

$$
\mathsf D_1(1)=
\frac{a(1-a)^2}{(1+a)((1-a)^2+a)}.
\tag{3.5}
$$

The denominator of (3.5) minus seven times its numerator is

$$
(1+a)((1-a)^2+a)-7a(1-a)^2
=(3a-1)(-2a^2+4a-1)>0.
\tag{3.6}
$$

Indeed $3a-1>0$, and the second factor is $1-2(1-a)^2>1/9$. Thus $\mathsf D_1(1)<1/7<c_0$, the latter strict inequality being exactly $12559<12600$. Continuity of these three finite rational functions gives an $\varepsilon(a,b)>0$, decreased to at most one, for which (3.3) holds whenever $1-\varepsilon<p<1$. The interval for $a,b$ is nonempty, so $\mathcal S$ is nonempty. No continuity assertion about an infinite-exterior posterior or about $d(P)$ is involved. $\square$

From now on fix one member $(a,b,p)\in\mathcal S$, once and independently of every word length, block location, exterior observation and comparison candidate. The auxiliary endpoint $p=1$ used in the existence proof is not a member of this chosen family.

## 4. One stationary renewal law and its exact finite words

**Definition 4.1 (Three-state producer).** In the state order $(R,U,V)$ set

$$
M_0=\begin{pmatrix}0&p&c\\0&s&0\\0&0&t\end{pmatrix},\qquad
M_1=\begin{pmatrix}0&0&0\\a&0&0\\b&0&0\end{pmatrix},\qquad
\lambda=\frac1Z\left(1,\frac pa,\frac cb\right).
\tag{4.1}
$$

Let $e=(1,0,0)$ be a row and $v=(0,a,b)^{\mathsf T}$ a column; thus $M_1=ve$. Let $J$ be (1.6) for these matrices, $P$ its visible marginal, and

$$
\mu_n=P_{[1,n]}.
\tag{4.2}
$$

All probabilities and conditional expectations for the reference law below use this $J/P$, or an actual marginal (4.2).

**Proposition 4.2 (Stationarity and renewal gaps).** The parameters (4.1) belong to $\Theta_3$. Given an observed one, successive distances to subsequent ones are independent with common law

$$
f(g)=pa s^{g-2}+cb t^{g-2},\qquad g\ge2.
\tag{4.3}
$$

Proof. Every row of $A=M_0+M_1$ sums to one, and $\lambda$ is a positive probability row. Its three stationary coordinates satisfy

$$
(\lambda A)_R=\frac{p+c}{Z}=\frac1Z,\quad
(\lambda A)_U=\frac{p+(p/a)s}{Z}=\frac{p}{aZ},\quad
(\lambda A)_V=\frac{c+(c/b)t}{Z}=\frac{c}{bZ}.
\tag{4.4}
$$

Since $ev=0$, $M_1^2=v(ev)e=0$, which implies the required scalar legality. The common law therefore exists by (1.6). This particular hidden chain is irreducible: $R$ reaches $U,V$ and each returns to $R$ with positive probability. Its positive $U,V$ self-loops also make it aperiodic. These are properties of the example, not conditions imposed on $\Theta_N$.

An emission of one leaves the next hidden state exactly $R$. The next bit is a forced zero, followed by a choice of $U$ with probability $p$ or $V$ with probability $c$. In $U$, further zeros have factor $s$ until a one with factor $a$; in $V$ use $t,b$. Consequently the probability that the next one is at distance $g$ is

$$
eM_0^{g-1}v=f(g),\qquad
\sum_{g\ge2}f(g)=\frac{pa}{1-s}+\frac{cb}{1-t}=p+c=1.
\tag{4.5}
$$

For several consecutive gaps, multiply their word matrices and factor every intervening $M_1=ve$. After conditioning on the first one, their joint probability is the product of the corresponding $f(g)$ values. This proves renewal independence within $J$; no separate renewal law has been assigned. $\square$

**Lemma 4.3 (Finite words, support and visible reversibility).** Set

$$
T_0=1,\qquad T_m=ps^{m-1}+ct^{m-1}\quad(m\ge1).
\tag{4.6}
$$

For $m\ge1$,

$$
P([0^m])=\frac{(p/a)s^{m-1}+(c/b)t^{m-1}}Z,
\qquad P(X_0=1)=\frac1Z.
\tag{4.7}
$$

A legal word with $h\ge1$ ones, initial and final zero runs of lengths $\ell,r\ge0$, and intervening one-to-one distances $g_1,\ldots,g_{h-1}\ge2$, has probability

$$
P([0^\ell1\,0^{g_1-1}1\cdots0^{g_{h-1}-1}1\,0^r])
=\frac{T_\ell T_r}{Z}\prod_{j=1}^{h-1}f(g_j).
\tag{4.8}
$$

The empty product is one. Every $\mu_n$ is positive on all of $B_n$, nearest exterior ones exist on both sides of every site almost surely, and the visible two-sided law is reversible.

Proof. Direct multiplication, or induction on $m$, gives

$$
\lambda M_0^m=
\frac1Z\bigl(0,(p/a)s^{m-1},(c/b)t^{m-1}\bigr),\qquad m\ge1.
\tag{4.9}
$$

The first multiplication uses $a+s=b+t=1$; subsequent ones multiply the last two coordinates by $s,t$. Summing coordinates gives (4.7), and $\lambda v=(p+c)/Z=1/Z$. Furthermore

$$
eM_0^m\mathbf1=T_m,\qquad \lambda M_0^mv=T_m/Z\quad(m\ge0).
\tag{4.10}
$$

For $m=0$ these follow from $e\mathbf1=1$ and $\lambda v=1/Z$; for $m\ge1$ they follow from (4.9) and $eM_0^m=(0,ps^{m-1},ct^{m-1})$. Repeated factorization by $M_1=ve$ now gives (4.8). Every factor is positive. Illegal words have zero probability by $M_1^2=0$.

Because $0<t<s<1$, (4.7) implies

$$
P([0^m])\le\frac{Z-1}{Z}s^{m-1}\longrightarrow0.
\tag{4.11}
$$

Continuity of probability on decreasing events excludes an entirely zero left or right half-line. Stationarity and a countable intersection give exterior anchors on both sides simultaneously for every site.

Reversing a word with ones exchanges $\ell,r$ and reverses the order of the gap factors in (4.8), leaving its probability unchanged. All-zero words are unchanged and illegal words remain illegal. Thus all contiguous word probabilities are reversal invariant. Marginalizing such words handles every finite set of coordinates; stationarity places the reflection at any integer site. Uniqueness of the measure determined by its cylinders proves visible reversibility. No reversibility of the hidden chain is asserted. $\square$

## 5. Infinite exterior conditioning and all finite insertion edges

**Theorem 5.1 (Actual exterior posterior).** On $F_0$, let the nearest exterior ones be at $-\ell$ and $r$. Almost surely $\ell,r\ge2$, and

$$
\frac{q_0}{1-q_0}=\frac{f(\ell)f(r)}{f(\ell+r)}.
\tag{5.1}
$$

In particular $\mathsf B(P)$ holds, with strict free-site inequalities $1/4<q_i<1/2$.

Proof. Fix $\ell,r\ge2$ and the exterior event specifying ones at $-\ell,r$ and zeros between them except at the omitted center. With center zero the intervening renewal factor is $f(\ell+r)$; with center one it is $f(\ell)f(r)$. For any additional finite collars outside these anchors, $M_1=ve$ factors out the same left and right likelihoods in both completions. On a positive collar event the ratio is therefore (5.1); a zero-likelihood collar requires no division.

More explicitly, let $Q_{\ell,r}=f(\ell)f(r)/(f(\ell+r)+f(\ell)f(r))$. On the specified anchor event the conditional integral identity for $X_0$ and the constant $Q_{\ell,r}$ holds against every finite exterior cylinder: refine the cylinder into contiguous collars containing the anchors and sum the common-factor identities. Finite exterior cylinders generate $\mathcal E_0$. Uniqueness of finite measures extends the identity to every exterior event. The countably many nearest-anchor events cover $F_0$ up to a null set by Lemma 4.3. This proves that (5.1) is the full-exterior posterior of the same $P$, not only a posterior with distant observations omitted.

For every $g\ge2$,

$$
pa s^{g-2}\le f(g)\le k s^{g-2}.
\tag{5.2}
$$

The exponents in the numerator and denominator of (5.1) consequently give

$$
L(p)=\frac{p^2a^2}{ks^2}
\le\frac{f(\ell)f(r)}{f(\ell+r)}
\le\frac{k^2}{pa s^2}=U(p).
\tag{5.3}
$$

By (3.3) these odds are strictly between $1/3$ and one. On $F_0^c$ a retained neighboring one forces $X_0=0$. Translation and a countable intersection prove the stated band at every site. $\square$

**Theorem 5.2 (Every length and both open endpoints).** For every $n\ge1$, every legal insertion edge $u\to w$ in $B_n$ satisfies

$$
\frac13\mu_n(u)\le\mu_n(w)\le\mu_n(u).
\tag{5.4}
$$

Proof. There are four distinct cases.

For $2\le i\le n-1$, both neighbors belong to
$\mathcal G_{n,i}=\sigma(X_j:1\le j\le n,\ j\ne i)\subseteq\mathcal E_i$.
The actual finite posterior is
$p_{n,i}=\mathbb E_P[q_i\mid\mathcal G_{n,i}]$.
On a free finite complement $F_i$ is measurable in this field, so Theorem 5.1 gives $1/4\le p_{n,i}\le1/2$. The corresponding insertion odds lie in $[1/3,1]$. A neighbor one instead gives a forced zero fiber. Positivity of each legal word makes these conclusions valid on every supported finite complement.

At the right endpoint for $n\ge2$, a legal insertion has a prefix ending in zero. Its normalized hidden row

$$
\alpha=\frac{\lambda M_{\text{prefix}}}{\lambda M_{\text{prefix}}\mathbf1}
\tag{5.5}
$$

has $\alpha_R=0$, because $M_0$ has zero column $R$. Thus the terminal probability of one is $a\alpha_U+b\alpha_V\in[a,b]$. The insertion ratio belongs to

$$
\left[\frac{a}{1-a},\frac{b}{1-b}\right]
\subset(1/2,3/5)\subset[1/3,1].
\tag{5.6}
$$

A prefix ending in one forces the endpoint zero.

At the left endpoint for $n\ge2$, reverse both words of the insertion edge. Their probabilities are unchanged by Lemma 4.3, and the reversed edge is exactly a right-endpoint edge. This proves the left-endpoint bound without inserting an unobserved exterior zero.

At $n=1$ the only edge is $0\to1$, and (4.7) gives its ratio

$$
\frac{\mu_1(1)}{\mu_1(0)}=\frac1{p/a+c/b}\in[a,b]\subset(1/3,3/8).
\tag{5.7}
$$

There is no neighbor in this last calculation. These cases prove (5.4). $\square$

**Corollary 5.3 (Complete finite-complement convention).** Condition any $\mu_n$ on the entire complement of an interval. Every extendible complement has positive mass. Its conditional is positive and band-compatible on the completion set with the actual neighboring complement bits, using zero only for the original open-endpoint convention when the interval touches an endpoint.

Proof. A complement with a legal completion has positive probability by Lemma 4.3. Dividing the two masses on an internal insertion edge by that same complement probability preserves (5.4). Incompatible completions remain zero. A forced fiber has its sole zero-center completion; a singleton completion graph has its unique probability. A nonextendible complement is null and contributes zero without any conditional denominator. $\square$

## 6. Identically zero two-anchor reset variance

**Theorem 6.1 (Exact finite reset posterior).** For $n\ge5$, $3\le i\le n-2$, and every supported full complement in $E_i=\{X_{i-2}=X_{i+2}=1\}$,

$$
p_{n,i}=\frac{k^2}{k^2+k_2},\qquad
\mu_n(E_i)=\frac{k^2+k_2}{Z}>0.
\tag{6.1}
$$

Consequently

$$
V_2(\mu_n;n)=0\qquad\text{for every }n\ge1.
\tag{6.2}
$$

Proof. The two completions of a supported complement in $E_i$ have the form $\ell\,10x01\,t'$ with $x=0,1$. Here $\ell,t'$ are words, not the scalar parameters used earlier. The common-matrix probability is

$$
(\lambda M_\ell v)\,[eM_0M_xM_0v]\,(eM_{t'}\mathbf1).
\tag{6.3}
$$

The outer factors are positive by the legal-word formulas, and independent of $x$. At an endpoint anchor an outer word is empty, with factor $\lambda v=1/Z$ or $e\mathbf1=1$ respectively. For $x=0$ the middle factor is $f(4)=k_2$. For $x=1$ it is $(eM_0v)^2=f(2)^2=k^2$. Their ratio gives the posterior in (6.1), independently of the entire remaining finite complement.

Marginalize the exterior: the anchor event consists of the five-bit words $10001$ and $10101$. Formula (4.8) gives their probabilities $k_2/Z$ and $k^2/Z$. This proves the event mass in (6.1). Equivalently the same rank-one cancellation persists when finite collars are enlarged to the infinite exterior, as in Theorem 5.1. Thus every conditional variance in (2.8) is exactly zero, with positive event weight. Their sum is zero for $n\ge5$; the definition covers $n<5$. $\square$

This is actual screening by a renewal reset. It does not infer that all probability cut matrices have rank two. The next bridge distinguishes those assertions.

## 7. A full-complement six-bit bridge with a rank-three certificate

**Proposition 7.1 (Bridge and actual anchor mass).** Define

$$
Z_6=eA^6v=eA^6M_1\mathbf1,\qquad
r_*(w)=\frac{eM_wv}{Z_6},\qquad w\in\{0,1\}^6,
\qquad \beta=\frac{Z_6}{Z}.
\tag{7.1}
$$

Then $r_*$ is positive and band-compatible on exactly $K_6^{1,1}$, and zero on all incompatible words. For every six-bit interval $C=[u,u+5]$, on

$$
H_C=\{X_{u-1}=X_{u+6}=1\}
\tag{7.2}
$$

its full-complement conditional under $P$ is $r_*$ almost surely. The same identity holds at every supported complete complement under any $\mu_n$ containing $C$ and both anchors. In each case the anchor-event probability is $\beta>0$.

Proof. Summing the ordered products $eM_wv$ over all binary six-bit words gives $eA^6v=Z_6$. An internal $11$ vanishes because $M_1^2=0$. A first bit one vanishes because $eM_1=0$, and a last bit one because $M_1v=v(ev)=0$. Thus all required internal and boundary zeros are retained, and the sum is precisely over $K_6^{1,1}$.

For a compatible word, insert the exterior ones and factor between consecutive ones. The numerator $eM_wv$ is a product of positive gap probabilities. In particular the all-zero numerator is

$$
eM_0^6v=f(7)=pa s^5+cb t^5>0.
\tag{7.3}
$$

Hence $Z_6>0$. Also $eA^6$ is a probability row and $v$ has entries in $[0,1]$, so $Z_6\le1$. This proves normalization and precise support.

Now fix a supported entire finite complement. Write its left part as $\ell1$ and its right part as $1t'$, with the displayed ones adjacent to $C$. The joint mass of a completion is

$$
\lambda M_\ell M_1M_wM_1M_{t'}\mathbf1
=(\lambda M_\ell v)(eM_wv)(eM_{t'}\mathbf1).
\tag{7.4}
$$

The two exterior factors are positive and the same for every $w$. Their cancellation proves (7.1) for the full finite complement, including when an anchor is an endpoint and an outer word is empty. Null complements require no division.

For the infinite complement, choose increasing finite contiguous collars containing both anchors. For each word $w$, (7.4) gives
$\mathbb E_P[\mathbf1_{\{X_C=w\}}\mid\text{collars}]=r_*(w)$ on $H_C$ at every collar size. To justify the limit without discarding distant observations, put $Y=\mathbf1_{\{X_C=w\}}$ and let $Q_m$ be these conditional expectations. For nested fields and $l\ge m$, conditional projection gives
$\|Q_l-Q_m\|_2^2=\|Q_l\|_2^2-\|Q_m\|_2^2$.
The squared norms are bounded, so the sequence converges in $L^2$. Its limit has the conditional integral identity on every finite collar event. Those events generate $\sigma(X_j:j\notin C)$, so the limit is the full-complement conditional expectation. Since $H_C$ is already a collar event and $Q_m=r_*(w)$ on it, multiplication by its indicator and $L^2$ convergence give the asserted equality there. There are finitely many words, and a countable intersection handles all translated intervals simultaneously.

The actual event mass is

$$
P(X_0=1,X_7=1)
=\lambda M_1A^6M_1\mathbf1
=(\lambda v)eA^6v=\frac{Z_6}{Z}=\beta>0.
\tag{7.5}
$$

Stationarity and marginalization give the identical value in every stated finite setting. Finally, $r_*$ is the conditional of $\mu_8$ given its first and last bits equal to one. Theorem 5.2 and Corollary 5.3 give its band by division by this same positive event mass. The first and sixth bridge coordinates are forced zeros, with singleton fibers, throughout this argument. $\square$

**Theorem 7.2 (Ordered minor and determinant).** Cut the six-bit bridge after three bits. Index selected rows by $0u$ and columns by $z0$, with both two-bit label lists in the order

$$
u,z\in(00,01,10).
\tag{7.6}
$$

Thus the selected row words are $(000,001,010)$ and the column words are $(000,010,100)$. Let $H_*$ be this minor of $\mathsf F_3(r_*)$. Then

$$
H_*=\frac{LR}{Z_6},\qquad
L=\begin{pmatrix}
0&ps^2&ct^2\\
k_1&0&0\\
0&kp&kc
\end{pmatrix},\qquad
R=\begin{pmatrix}
k_2&k^2&0\\
as^3&kas&ak_1\\
bt^3&kbt&bk_1
\end{pmatrix}.
\tag{7.7}
$$

Its strictly positive determinant is

$$
\Delta_6:=\det H_*
=\frac{pcab\,k^2k_1^2(b-a)^2(s+t)^2(pa t+cb s)}{Z_6^3}>0.
\tag{7.8}
$$

Proof. In the order (7.6), the rows of $L$ are $eM_{0u}$ and the columns of $R$ are $M_{z0}v$. To verify every column, use

$$
M_0v=(k,as,bt)^{\mathsf T},\qquad
M_0^2v=(k_1,as^2,bt^2)^{\mathsf T},\qquad M_1=ve.
\tag{7.9}
$$

These give respectively $M_0^3v$, $M_0M_1M_0v=kM_0v$, and $M_1M_0^2v=k_1v$, exactly the columns in (7.7). The row computations are $eM_0^3=(0,ps^2,ct^2)$, $eM_0^2M_1=k_1e$, and $eM_0M_1M_0=k eM_0$. Their ordered product is $eM_{0u}M_{z0}v$, so the convention in (7.7) has no transpose or reversed label order.

The row with label $u=01$ and column with label $z=10$ concatenate to the forbidden middle seam $11$. Its entry is retained as zero:

$$
(k_1,0,0)\,(0,ak_1,bk_1)^{\mathsf T}=0.
\tag{7.10}
$$

Every other selected concatenation is compatible and has positive numerator by Proposition 7.1. Thus this really is a minor of the original full probability flattening, rather than of a matrix with its illegal seam removed.

Expand $\det L$ along its second row:

$$
\det L=-pc\,k k_1(s^2-t^2)
=-pc\,k k_1(s-t)(s+t).
\tag{7.11}
$$

Factor $a,b$ out of the second and third rows of $R$, then expand along its first row to obtain

$$
\begin{aligned}
\det R
&=ab\,k k_1(s-t)\bigl[k_2-k(s^2+st+t^2)\bigr]\\
&=-ab\,k k_1(s-t)(s+t)(pa t+cb s).
\end{aligned}
\tag{7.12}
$$

For the second equality, expand $k_2=pa s^2+cb t^2$ and $k=pa+cb$; the bracket is
$-pa(st+t^2)-cb(s^2+st)=-(s+t)(pa t+cb s)$.
Multiply (7.11) and (7.12), use $s-t=b-a$, and divide by the common probability normalizer $Z_6^3$. Every displayed factor in (7.8) is strictly positive for the fixed member of $\mathcal S$. This proves the sign as well as the exact value. $\square$

## 8. A finite quantitative discrepancy and its global accumulation

**Lemma 8.1 (Feasible rank-two comparison).** The family $\mathscr F_{2,n}^{0,0}$ is nonempty for every $n$, and $\mathscr F_{2,6}^{1,1}$ is nonempty.

Proof. Use the classical two-state visible Markov chain from [Universal, Proposition 7.1][U], with the same fixed number $a$ but a separate comparison law $Q$:

$$
B=\begin{pmatrix}1-a&a\\1&0\end{pmatrix},\qquad
\rho=\left(\frac1{1+a},\frac{a}{1+a}\right),\qquad
N_x=D_xB,\quad D_0=\operatorname{diag}(1,0),\quad D_1=\operatorname{diag}(0,1).
\tag{8.1}
$$

The row is stationary, all legal transitions are positive, and its word probabilities factor through two states at every cut. Insertion ratios are

$$
a\quad(n=1),\qquad
\frac{a}{1-a}\quad(\text{either endpoint},\ n\ge2),\qquad
\frac{a}{(1-a)^2}\quad(\text{a free interior site}).
\tag{8.2}
$$

At the first endpoint the stationary factor and first transition change together, giving $\rho_1B_{10}/(\rho_0B_{00})=a/(1-a)$; at the last endpoint only the final transition changes. At a free interior site the two transition products are $a$ and $(1-a)^2$. The ranges in (3.1) put all three ratios in $[1/3,1]$. Thus $Q_{[1,n]}\in\mathscr F_{2,n}^{0,0}$. Its positive eight-bit conditional given the first and last bits equal to one gives a member of $\mathscr F_{2,6}^{1,1}$: conditioning preserves the insertion ratios, and at each internal cut the conditional matrix is a selected submatrix of the corresponding eight-bit cut, divided by a positive event mass. Such restriction and scaling cannot increase nonnegative rank.

This law is used only as a feasible competitor in a minimum. No conditional, risk or event mass belonging to the reference $P$ is taken from $Q$. $\square$

**Theorem 8.2 (Attained positive bridge minimum).** For the actual bridge define

$$
\delta_*:=\delta_{2,6}^{1,1}(r_*),\qquad
\delta_0:=\frac{6^{-24}}{48}\Delta_6^2.
\tag{8.3}
$$

Then the minimum defining $\delta_*$ is attained and

$$
0<\delta_0\le\delta_*\le6.
\tag{8.4}
$$

Proof. Lemma 8.1 supplies a competitor, and the compactness and continuity following (2.7) give attainment. Every squared site-posterior difference is at most one, so this competitor gives the upper bound six.

For the quantitative lower bound, specialize the ratio argument of [Guarded, Lemma 8.1 and Theorem 8.2], retaining the constants. Let $\nu,r$ be band-compatible on $K=K_6^{1,1}$ and set $t_w=r_w/\nu_w$, $\alpha=6^{-6}$. Both probabilities have all compatible masses at least $\alpha$. On an insertion edge $u\to w$, the exact contribution to (2.2) is

$$
\frac{(\nu_u\nu_w)^2(t_u-t_w)^2}
{(\nu_u+\nu_w)(r_u+r_w)^2}
\ge\alpha^4(t_u-t_w)^2.
\tag{8.5}
$$

The denominator factors are at most one, since each pair consists of distinct words in a probability space. Connect words attaining the extreme $t$ values by deleting ones and reinserting them through $0^6$. Remove repetitions to get a simple path of at most twelve edges. Cauchy–Schwarz on this path gives

$$
(\max_wt_w-\min_wt_w)^2
\le\frac{12}{\alpha^4}\mathcal D_K(\nu\Vert r).
\tag{8.6}
$$

Since $\sum_w\nu_wt_w=1$, one lies between those extremes, and
$\|\nu-r\|_1=\sum_w\nu_w|1-t_w|\le\max t-\min t$.
Therefore

$$
\mathcal D_K(\nu\Vert r)\ge\frac{6^{-24}}{12}\|\nu-r\|_1^2.
\tag{8.7}
$$

Now take $\nu=r_*$ and any $r\in\mathscr F_{2,6}^{1,1}$. Its matching three-by-three minor has determinant zero because ordinary rank is at most nonnegative rank. Subtract the two determinant permutation formulas. Telescoping each difference of three-factor products, with entries in $[0,1]$, bounds it by the sum of the entry differences used in that product. Each selected entry occurs in two permutations. Distinct entries correspond to distinct six-bit words, and forbidden entries are zero for both laws. Hence

$$
\Delta_6\le2\sum_{\text{selected entries}}|r_*-r|
\le2\|r_*-r\|_1.
\tag{8.8}
$$

Combine (8.7) and (8.8), then minimize over $r$, to obtain the lower bound in (8.4). Strict positivity follows from (7.8). The determinant is a sufficient obstruction; vanishing determinants alone would not characterize nonnegative rank. $\square$

**Theorem 8.3 (Linear discrepancy against one global candidate).** For every $n\ge1$,

$$
\left\lfloor\frac{n-1}{7}\right\rfloor\beta\delta_*
\le\mathscr R_{2,n}(\mu_n)\le n.
\tag{8.9}
$$

These global minima are finite and attained. In particular

$$
\liminf_{n\to\infty}\frac{\mathscr R_{2,n}(\mu_n)}n
\ge\frac{\beta\delta_*}{7}
\ge\frac{\beta\,6^{-24}\Delta_6^2}{336}>0.
\tag{8.10}
$$

Proof. Put $J_n=\lfloor(n-1)/7\rfloor$ and choose the disjoint intervals

$$
C_j=[2+7j,7+7j],\qquad0\le j<J_n.
\tag{8.11}
$$

Their adjacent exterior sites $1+7j$ and $8+7j$ lie in $[1,n]$; the last right anchor is $7J_n+1\le n$. Let
$H_j=\{X_{1+7j}=X_{8+7j}=1\}$.
Proposition 7.1 gives $\mu_n(H_j)=\beta$ exactly. On each supported entire complement $\eta$ in $H_j$, the reference conditional

$$
\nu_j^\eta=\mu_n(X_{C_j}=\cdot\mid X_{[1,n]\setminus C_j}=\eta)
\tag{8.12}
$$

equals $r_*$. This is a full-complement identity, not an identification with a stand-alone block marginal.

Fix an arbitrary single global $r\in\mathscr F_{2,n}^{0,0}$ before doing any minimization. Both $\mu_n$ and $r$ are positive on all of $B_n$, so exactly the extendible complements have positive mass under each. For such $\eta$ let $r_j^\eta$ be the conditional under this same $r$. If its actual adjacent bits are $\xi_j,\zeta_j$, the insertion inequalities persist on $K_6^{\xi_j,\zeta_j}$. At an internal cut of $C_j$, fixing the entire outside prefix selects rows of the corresponding global cut, and fixing the entire outside suffix selects columns. Dividing by the positive $r$ complement mass gives the conditional cut matrix. Restriction and positive scaling preserve nonnegative rank at most two. Thus
$r_j^\eta\in\mathscr F_{2,6}^{\xi_j,\zeta_j}$.

For a site in $C_j$, conditioning inside the block after observing $\eta$ means conditioning on all other $n-1$ bits. Disintegrating the site discrepancies therefore gives exactly

$$
\begin{aligned}
\sum_{i\in C_j}\mathbb E_{\mu_n}(p_{n,i}-r_i)^2
&=\mathbb E_{\mu_n}\mathcal D_{K_6^{\xi_j,\zeta_j}}
(\nu_j^\eta\Vert r_j^\eta)\\
&\ge\mathbb E_{\mu_n}\delta_{2,6}^{\xi_j,\zeta_j}(\nu_j^\eta)
\ge\beta\delta_*.
\end{aligned}
\tag{8.13}
$$

The last inequality retains $H_j$, where both boundary bits are one and the reference conditional is exactly $r_*$; all other contributions are nonnegative. Each expectation and event weight is under the single reference marginal $\mu_n$. All comparison conditionals in the first line are slices of the same fixed $r$.

Disjointness of the $C_j$ counts each scored site at most once. Endpoints and separator sites are still present in (2.2); their nonnegative discrepancies are simply unused in this lower bound. Sum (8.13) to get
$\mathcal D_{B_n}(\mu_n\Vert r)\ge J_n\beta\delta_*$ for every global candidate, and only now minimize over $r$. Lemma 8.1 and (2.7) ensure a nonempty compact family and attainment, and its exhibited competitor has discrepancy at most $n$. For $n<8$ there are no blocks and the lower bound is just nonnegativity; it does not claim that the actual minimum vanishes.

Finally $J_n/n\to1/7$ gives (8.10). Adjacent blocks share an anchor and their events can be dependent. The paid expected event count is exactly $J_n\beta$ by linearity of expectation. No independence, empirical-frequency theorem or simultaneous choice of independently minimized kernels is used. This is the conditional-slicing consumer from [Guarded, Theorem 7.1] and [Global-local, Premise 1.4], applied to the one stationary comparison law. $\square$

## 9. Exact minimal edge-emitting dimension

**Theorem 9.1 (Three states are necessary and sufficient).** The visible law $P$ has minimal hidden dimension three in the convention (1.5)–(1.6). Moreover

$$
\mathscr R_{3,n}(\mu_n)=0\qquad(n\ge1).
\tag{9.1}
$$

Proof. The producer (4.1) supplies three states. To exclude at most two, use the same certificate as in Theorem 7.2. In the actual eight-bit marginal cut after the fourth bit, select rows $1\,0u$ and columns $z0\,1$ in the common order (7.6). Their matrix $G$ has entries

$$
G_{u,z}=P([1\,0u\,z0\,1])
=\frac1Z eM_{0u}M_{z0}v
=\beta(H_*)_{u,z},\qquad
\det G=\beta^3\Delta_6>0.
\tag{9.2}
$$

This step multiplies the actual conditional bridge by its actual anchor mass; it introduces no new conditional model or unrelated minor.

Any representation of the same visible law with $N\le2$ states would factor the entire eight-bit cut matrix as the product of rows $\lambda' M'_u$ and columns $M'_v\mathbf1$ through $N$ coordinates. Its ordinary rank and that of every selected submatrix would be at most two, contradicting (9.2). This excludes the entire $\Theta_2$ and every smaller representation, including zero masses, reducibility, periodicity and structural zeros.

Conversely, at every cut of every $\mu_n$ the exhibited common matrices give

$$
\mu_n(uv)=\lambda M_uM_v\mathbf1
=\sum_{h=1}^3(\lambda M_u)_h(M_v\mathbf1)_h.
\tag{9.3}
$$

Thus all its nonnegative cut ranks are at most three. Theorem 5.2 gives the band, so $\mu_n\in\mathscr F_{3,n}^{0,0}$. Comparing it with itself proves (9.1). This is minimality for the specified edge-emitting convention; it makes no identification with the minimal dimension in every other HMM convention. $\square$

## 10. Actual erasure tails and finite-radius strict nonattainment

**Definition 10.1 (One-sided erasure, including both seam terms).** Use precisely the fields and errors of [Guarded, Definition 2.1]:

$$
\begin{aligned}
\mathcal H_j^L&=\sigma(X_{-j},\ldots,X_{-1},X_1,X_2,\ldots),&
p_j^L&=\mathbb E_P[X_0\mid\mathcal H_j^L],&
e_L(j)&=\mathbb E_P(q_0-p_j^L)^2,\\
\mathcal H_j^R&=\sigma(\ldots,X_{-2},X_{-1},X_1,\ldots,X_j),&
p_j^R&=\mathbb E_P[X_0\mid\mathcal H_j^R],&
e_R(j)&=\mathbb E_P(q_0-p_j^R)^2,\\
A_P&=\sum_{j\ge0}\bigl(\sqrt{e_L(j)}+\sqrt{e_R(j)}\bigr).
\end{aligned}
\tag{10.1}
$$

At $j=0$ the finite retained side is empty; the entire opposite half-line is still retained. Every field is a subfield of $\mathcal E_0$, and all predictors use the reference law $P$.

**Theorem 10.2 (Direct reset-based payment of both tails).** For $j\ge1$,

$$
e_L(j),e_R(j)\le P([0^j])
\le\frac{Z-1}{Z}s^{j-1},\qquad
A_P\le2+\frac{2\sqrt{(Z-1)/Z}}{1-\sqrt s}<\infty.
\tag{10.2}
$$

More precisely, for every integer $R\ge1$,

$$
\sum_{j\ge R}\bigl(\sqrt{e_L(j)}+\sqrt{e_R(j)}\bigr)
\le\frac{2\sqrt{(Z-1)/Z}\,s^{(R-1)/2}}{1-\sqrt s}.
\tag{10.3}
$$

Proof. Let $G_j^L$ be the event that at least one of $X_{-j},\ldots,X_{-1}$ equals one. It belongs to $\mathcal H_j^L$. On this event the reduced field retains the nearest left one, all the bits between it and the missing center, and the entire right half-line. Lemma 4.3 makes a nearest right one available almost surely. If a retained immediate neighbor is one, the posterior is zero. Otherwise Theorem 5.1 expresses it using precisely the two nearest retained anchor distances. Thus $\mathbf1_{G_j^L}q_0$ is $\mathcal H_j^L$-measurable up to a null set.

Because $\mathcal H_j^L\subseteq\mathcal E_0$, the tower property gives $p_j^L=\mathbb E_P[q_0\mid\mathcal H_j^L]$. Multiply by the measurable indicator of $G_j^L$ to conclude $p_j^L=q_0$ there. On the complement, both predictors lie in $[0,1]$. Therefore

$$
e_L(j)\le P((G_j^L)^c)=P([0^j]).
\tag{10.4}
$$

For right erasure, let $G_j^R$ be the event that some $X_1,\ldots,X_j$ equals one. The field $\mathcal H_j^R$ retains that nearest right anchor and the entire left half-line. The same explicit posterior formula and forced-neighbor rule make $\mathbf1_{G_j^R}q_0$ measurable in this field. Projection gives equality of the predictors there and hence $e_R(j)\le P([0^j])$. These are separate statements about the actual two reduced fields; neither replaces an opposite half-line by a finite collar.

Use (4.11) to obtain the geometric bounds. At $j=0$, $e_L(0),e_R(0)\le1$ by the predictor range; this pays a total of at most two after taking square roots. For $j\ge1$, sum the geometric series with ratio $\sqrt s<1$. This proves (10.2), and summing from $R$ instead proves (10.3). The proof uses an actually observed visible reset and the entire opposite half-line, without a mixing assertion for an arbitrary hidden filter or a general rectangular-support theorem. $\square$

**Theorem 10.3 (Actual finite-radius risk and strict nonattainment).** The same stationary law satisfies

$$
d(P)\le D_1(P)=\mathsf D_1(p)<\frac{1800}{12559}\le c_\star,
\qquad
c_\star-d(P)\ge c_0-\mathsf D_1(p)>0.
\tag{10.5}
$$

Proof. Formula (4.7) at length three gives

$$
P([000])=\frac{H(p)}{Z}.
\tag{10.6}
$$

Since a center one forces both neighbors zero, stationarity and (4.7) give
$P([010])=P(X_0=1)=1/Z$.
For conditioning on $X_{-1},X_1$, every neighbor pattern except $00$ forces the center zero. The $00$ fiber contributes its exact weighted conditional variance, so

$$
D_1(P)=h(P([000]),P([010]))
=\frac{H(p)}{Z(H(p)+1)}=\mathsf D_1(p).
\tag{10.7}
$$

Both predictors in this comparison belong to $P$. Let $q_{1,0}=\mathbb E_P[X_0\mid X_{-1},X_1]$. The tower property gives $q_{1,0}=\mathbb E_P[q_0\mid X_{-1},X_1]$. Conditional projection and vanishing of the cross term yield

$$
D_1(P)=\mathbb E_P(X_0-q_0)^2+
\mathbb E_P(q_0-q_{1,0})^2\ge d(P),
\tag{10.8}
$$

where the equality between full-exterior risk and density is the supplied interface (1.8). Inequality (3.3), established on a nonempty fixed subfamily using only finite rational continuity, and (1.3) prove (10.5). No continuity of $d(P)$, no limiting approximation to its posterior, and no optimization over this parameter family is used. $\square$

**Corollary 10.4 (Failure of strong zero for this law).** Use the fixed original-law losses $\ell_i(x)=(x_i-q_i(x))^2$. Under the band and $A_P<\infty$, [Guarded, Lemma 2.2] supplies a shift-invariant conull set saturated under legal finite modifications on which

$$
\Delta_P(x,z)=\sum_{i\in\mathbb Z}(\ell_i(x)-\ell_i(z))
\tag{10.9}
$$

is absolutely convergent for every finitely differing pair. Strong zero $\mathsf Z_\Delta(P)$ asserts that this cocycle is zero on every such pair in a saturated conull set. The present law does not satisfy $\mathsf Z_\Delta(P)$.

Proof. Theorems 5.1 and 10.2 pay exactly the band and summability premises for this $P$. [Guarded, Theorem 5.1] proves that these premises together with strong zero imply $d(P)=c_\star$ for that same law. Its implication follows from independent insertion of a finite optimizer between two zero guards: the exact loss identity has nonnegative exterior, guard and conditional-discrepancy penalties, so strong zero gives $(n+2)d(P)\ge\kappa_n$ for every $n$; use (1.3) and (1.8). The equality it would force contradicts (10.5). This is a contrapositive for a proved strict nonattainer, not a deduction of strong zero from attainment. $\square$

## 11. The completed conjunction and the unchanged open alternative

**Theorem 11.1 (Same-law blindness of the two-anchor variance).** Fix once any $(a,b,p)\in\mathcal S$ and the single stationary joint law (4.1)–(4.2). All its finite marginals are positive and band-compatible on the entire open-path $B_n$. With the actual bridge, mass and constants (7.1), (7.8) and (8.3), for all $n\ge1$,

$$
\begin{gathered}
V_2(\mu_n;n)=0,\qquad
\left\lfloor\frac{n-1}{7}\right\rfloor\beta\delta_*
\le\mathscr R_{2,n}(\mu_n)\le n,\qquad
0<\frac{6^{-24}\Delta_6^2}{48}\le\delta_*\le6,\\
\liminf_{n\to\infty}\frac{\mathscr R_{2,n}(\mu_n)}n
\ge\frac{\beta\delta_*}{7}>0,\qquad
\mathscr R_{3,n}(\mu_n)=0.
\end{gathered}
\tag{11.1}
$$

The finite minima in these statements are attained. All constants belong to the one fixed parameter triple; no uniform positive discrepancy over $\mathcal S$ or $\Theta_N$ is asserted. The minimal edge-emitting hidden dimension is exactly three. The same $P$ is visibly reversible, satisfies $\mathsf B(P)$ and the bounds (10.2)–(10.3), and obeys

$$
d(P)\le D_1(P)<c_0\le c_\star,\qquad \neg\mathsf Z_\Delta(P).
\tag{11.2}
$$

Proof. Lemma 3.2 provides a nonempty parameter family and the subsequent fixed choice. Proposition 4.2 constructs its actual stationary joint law; Lemma 4.3 proves support and reversibility. Theorem 5.2 covers every finite edge, including both endpoints and length one. Theorem 6.1 proves exact zero variance. Proposition 7.1 identifies the bridge under both finite and infinite full-complement conditioning and computes its actual event mass. Theorem 7.2 gives the ordered determinant with its forbidden seam retained. Theorems 8.2–8.3 give attained finite minima and quantitative accumulation against a single global candidate. Theorem 9.1 gives dimension and rank-three zero discrepancy. Theorems 10.2–10.3 and Corollary 10.4 prove the remaining claims for that same law. $\square$

The mechanism separating the two conclusions is precise. A visible one resets the renewal mechanism, so two anchors remove dependence of the center posterior on more distant observations. Inside a longer anchored gap, however, the two distinct geometric persistence rates leave the positive determinant (7.8). Distant observations beyond the anchors do not remove that determinant because the full-complement bridge is exactly (7.1). Its actual positive event mass permits repeated disjoint site contributions. No trajectory-wide mixture label is being learned from the complement: in (4.1) a fresh branch is chosen after each visible one. Thus the fixed bridge defect persists, unlike the disappearing fixed-block defects of the persistent-mixture example in [Global-local, Theorem 4.4]. This comparison uses the two explicitly defined mechanisms and does not identify their probability laws.

**Open Question 11.2 (The actual finite optimizers).** Nothing in (11.1) evaluates

$$
V_2(\pi_n;n),\qquad \mathcal R_{N,n}=\mathscr R_{N,n}(\pi_n).
\tag{11.3}
$$

In particular, no vanishing, positive-density minor, posterior concentration or threshold-crossing assertion for $\pi_n$ follows by replacing $\mu_n$ in the proofs. The original conditional budget from [Guarded, Corollary 6.4] is

$$
\mathcal R_{N,n}\le(n+2)c_\star-\kappa_n-\frac1{24}
\le\tau:=2(3-2\sqrt2)-\frac1{24}
\tag{11.4}
$$

when an actual $\theta\in\Theta_N$ satisfies $\mathsf B(P_\theta)$, $A_{P_\theta}<\infty$ and $\mathsf Z_\Delta(P_\theta)$. The reference marginals in (11.1) do not replace the optimizer in (11.4). Whether the actual optimizer supplies a sufficiently large reset variance or another rank discrepancy remains unresolved here.

**Open Question 11.3 (Universal tails and the strong-zero bridge).** The tail proof in Theorem 10.2 uses this law's retained rank-one visible reset and its actual all-zero word probabilities. It proves neither $A_P<\infty$ for all $\Theta_N$ nor that condition for every hypothetical finite hidden attainer. Likewise the implication from hypothetical attainment, or its first-order conditional balances, to strong zero remains unproved. The band is a known necessary attainment condition; the additional properties used in the guarded sufficient endpoint have not thereby become necessary. This strict nonattainer cannot rule out the class of all finite attainers.

**Open Question 11.4 (Whole-domain finite attainment versus all-dimension separation).** On exactly the full domain (1.5), define

$$
C_N=\sup_{\theta\in\Theta_N}d(P_\theta),\qquad
U_{N,r}=\max_{\theta\in\Theta_N}D_r(P_\theta),\qquad N,r\ge1.
\tag{11.5}
$$

[Universal, Theorem 6.2][U] supplies attainment of $C_N$ and

$$
C_N=\inf_{r\ge1}U_{N,r}\le c_\star.
\tag{11.6}
$$

The original alternative is still whether some finite $N$ and some $\theta\in\Theta_N$ satisfy $d(P_\theta)=c_\star$, or whether $C_N<c_\star$ for every finite $N$. The latter is equivalent, by that supplied theorem, to

$$
\forall N\ge1\ \exists r,m\ge1:\qquad
U_{N,r}<\frac{\kappa_m}{m+1}.
\tag{11.7}
$$

The example's irreducibility, positive stationary masses, entrywise $M_1^2=0$, reset structure and strict parameter inequalities are not restrictions on (11.5). A nonattaining law of minimal dimension three neither excludes other laws of that dimension nor supplies the separation pairs in (11.7). The rank-family minima in (2.6) are necessary relaxations, with no converse realization theorem. The construction gives no finite attaining producer, no arbitrary-$N$ exclusion, no common optimizer representation, and no conclusion about empirical learning performance.

## 12. Mathematical credits and scope of the contribution

The result established here is the simultaneous same-law statement in Theorem 11.1. The renewal mechanism, gap-factor representation, two-anchor cancellation and six-bit certificate are used as explicit mathematical ingredients, with full proofs of their asserted properties. They are not assigned separate novelty claims. The conditional score, rank relaxation, reset detector and original optimization problem retain the following source ownership.

| Canonical supplier | Interfaces used and retained boundaries |
| --- | --- |
| [Universal][U], *FIB 合法边调和负载：普适后验缺陷与有限隐藏维数分离* | Convention 1.3 and Lemma 2.1: the original $\pi_n$, insertion band, growth and exact finite discrepancy identity. Definition 4.1 and Proposition 4.2: the entire exact-real domain and its actual stationary joint law. Equation (1.5): density as full-exterior risk. Theorem 3.1: the necessary attained-law band. Theorem 6.2: the compact-domain alternative (11.6)–(11.7). Proposition 7.1: the two-state comparison mechanism and rational lower comparison for $c_\star$. |
| [Guarded][Gd], *FIB harmonic-edge load: guarded replacement, attainment and conditional-rank obstruction* | Definitions 2.1 and 2.3 and Lemma 2.2: exact erasure fields, summability and original-loss cocycle. Lemmas 3.2–3.3 and Definition 6.3: the constrained conditional Brier score and compact rank families. Theorem 6.2: conditional rank from the actual matrices and full-complement limit. Theorem 7.1: slicing against one global candidate. Lemma 8.1 and Theorem 8.2: ratio coercivity and determinant bounds. Theorem 5.1 and Corollary 6.4: the sufficient strong-zero endpoint and optimizer budget, with their extra premises. |
| [Global-local][Gl], *FIB harmonic-edge load: global and local rank compatibility and the reset-variance obstruction* | Definition 1.3 and Premise 1.4: the reference-law extension $\mathscr R_{N,n}(\nu)$ and its conditional-slicing use. Lemmas 2.1–2.2 and Theorem 2.3: rank-two resets and the variance detector $V_2$. Theorems 4.4 and 5.1: the separate persistent-mixture comparison between local fitting and a global candidate. No fact about that mixture is substituted for a probability under the renewal law here. |

Conditional least squares and the conditional Brier score are classical; the score connection is described by Dawid, Lauritzen and Parry, *Proper Local Scoring Rules on Discrete Sample Spaces*, §4.2, Example 4.4, as credited in Guarded. Lemma 2.2 includes the equality proof needed on the constrained no11 graph. Finite-state matrix products, renewal factorization, conditional projection, convergence on increasing fields, finite-dimensional compactness, determinant expansion and geometric summation are also classical tools. The direct proofs above specify their hypotheses and uses; they import no general hidden-model regularity theorem.

The mathematical increment is the completed conjunction: exact zero of this reset-variance test coexists with positive linear discrepancy, a persistent full-complement bridge defect, minimal hidden dimension three, paid erasure tails and strict nonattainment, all for one fixed stationary common-matrix law. The unchanged optimizer and all-dimension questions in §11 remain outside that conclusion.

[U]: FIB_LEGAL_EDGE_LOAD_UNIVERSAL_POSTERIOR_DEFECT_AND_FINITE_HIDDEN_SEPARATION.md
[Gd]: FIB_LEGAL_EDGE_LOAD_GUARDED_REPLACEMENT_ATTAINMENT_AND_CONDITIONAL_RANK_OBSTRUCTION.md
[Gl]: FIB_LEGAL_EDGE_LOAD_GLOBAL_LOCAL_RANK_COMPATIBILITY_AND_RESET_VARIANCE_OBSTRUCTION.md

## 追加锚（本行以下为增补区）
