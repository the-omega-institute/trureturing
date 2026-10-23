# Fibonacci harmonic-edge load: two-step bulk separation

## 1. Complete word domains and the hard-core comparator

**Definition 1.1 (Fibonacci cubes).** For every integer $n\ge1$, let

$$
B_n=\{b\in\{0,1\}^n:b_jb_{j+1}=0\text{ for }1\le j<n\}.
$$

The graph $\Gamma_n$ has vertex set $B_n$ and an edge between two words precisely when they differ at one coordinate. The word constraint is imposed along an open path: there is no constraint between $b_n$ and $b_1$. In particular, every all-zero word and every legal word beginning or ending with $1$ belongs to the domain. Put $b_0=b_{n+1}=0$. An upward-flippable coordinate of $b$ is an $i$ with $b_{i-1}=b_i=b_{i+1}=0$; write $b+e_i$ for the corresponding insertion of $1$. Let $k(b)$ count its ones and $u(b)$ its upward-flippable coordinates. This is the domain of [Growth], Definitions 2.4–2.5, including its subsequence $n=3N$ for positive integers $N$.

**Definition 1.2 (Harmonic objective and squared-share minimax).** Let $\mathcal P(B_n)$ be the simplex of probability vectors on the whole of $B_n$. For $s,t\ge0$, define

$$
h(s,t)=\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}
\qquad
\Phi_n(\mu)=\sum_{\{b,c\}\in E(\Gamma_n)}h(\mu(b),\mu(c)).
$$

A feasible allocation consists of shares $a_{c\leftarrow b}\in[0,1]$ on every ordered adjacent pair, satisfying $a_{c\leftarrow b}+a_{b\leftarrow c}=1$. Set

$$
\kappa_n=\min_a\max_{b\in B_n}\sum_{c\sim b}a_{c\leftarrow b}^2.
$$

**Convention 1.3 (Growth dependencies).** The harmonic duality and growth identities used here are the owned results [Growth], Theorems 3.2 and 5.2:

$$
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu),\qquad
c_\star=\lim_{n\to\infty}\frac{\kappa_n}{n}
=\inf_{n\ge1}\frac{\kappa_n}{n},\qquad
c_\star n\le\kappa_n\le c_\star(n+1).
\tag{1.1}
$$

For $r>1$, use exactly its hard-core parameterization

$$
\lambda=r(r-1),\qquad
g(r)=\frac{r-1}{(r^2-r+1)(2r-1)},\qquad
p(r)=4r^3-9r^2+6r-2.
\tag{1.2}
$$

The number $r_\star$ is the unique root of $p$ in $(1,\infty)$, and $g(r_\star)=\max_{r>1}g(r)$ by [Growth], Theorem 7.3. Only these exact identities and the exact root characterization are used.

**Definition 1.4 (One-activity family).** For every $n\ge1$ and $\lambda>0$, define

$$
Z_n(\lambda)=\sum_{b\in B_n}\lambda^{k(b)},\qquad
\nu_{n,\lambda}(b)=\frac{\lambda^{k(b)}}{Z_n(\lambda)},\qquad
H_n=\sup_{\lambda>0}\Phi_n(\nu_{n,\lambda}).
\tag{1.3}
$$

The partition function is the independent-set polynomial of an $n$-vertex path at equal positive fugacities, as in Scott–Sokal [SS], §1.1, equation (1.3), and §3.2, Example 3.2. This classical identification and [Growth], Proposition 7.1 and Lemma 7.2, supply the comparator, not the strict harmonic-prior separation below.

## 2. One consistent positive prior at every length

**Definition 2.1 (Stationary legal-pair prior).** Order the pair states as $\mathcal S=(00,01,10)$, and put

$$
P=\begin{pmatrix}
7/10&3/10&0\\
0&0&1\\
2/3&1/3&0
\end{pmatrix},\qquad
\pi=(10/19,9/38,9/38).
\tag{2.1}
$$

For $n\ge2$ and $b\in B_n$, define

$$
\mu_n(b)=\pi_{b_1b_2}
\prod_{j=1}^{n-2}P_{b_jb_{j+1},\,b_{j+1}b_{j+2}}.
\tag{2.2}
$$

The product is empty when $n=2$. At length one set

$$
\mu_1(0)=29/38,\qquad \mu_1(1)=9/38.
\tag{2.3}
$$

**Proposition 2.2 (Normalization, support and stationary windows).** For every $n\ge1$, $\mu_n$ is a probability vector with $\mu_n(b)>0$ for every $b\in B_n$. Its all-zero mass is $29/38$ for $n=1$ and

$$
\mu_n(0^n)=\frac{10}{19}\left(\frac7{10}\right)^{n-2}\quad(n\ge2).
\tag{2.4}
$$

For every $1\le m\le n$, every $1\le a\le n-m+1$ and every $w\in B_m$,

$$
\Pr_{\mu_n}\{(b_a,\ldots,b_{a+m-1})=w\}=\mu_m(w).
\tag{2.5}
$$

**Proof.** Each row of $P$ sums to one. Its positive entries are exactly the transitions $(x,y)\longrightarrow(y,z)$ with $xy=yz=0$. Every legal initial pair has positive $\pi$-mass, so every legal word has positive mass in (2.2). Also $\sum_{s\in\mathcal S}\pi_s=1$ and

$$
\pi P=\left(
\frac{10}{19}\frac7{10}+\frac9{38}\frac23,
\frac{10}{19}\frac3{10}+\frac9{38}\frac13,
\frac9{38}\right)
=\left(\frac{10}{19},\frac9{38},\frac9{38}\right)=\pi.
\tag{2.6}
$$

Summing over the last bit in (2.2) removes its last transition factor. Repeating gives total mass one for every $n\ge2$. The first-bit marginal of $\pi$ is $(29/38,9/38)$, agreeing with (2.3); its second-bit marginal is the same. Thus normalization and prefix consistency hold also at length one. Formula (2.4) follows by retaining only the transitions $00\longrightarrow00$.

For $m\ge2$, summing the suffix beyond a specified window uses row sums equal to one, and summing its prefix gives the initial pair distribution $\pi P^{a-1}=\pi$. The remaining product is exactly (2.2) for $w$. For $m=1$ use the bit marginals just computed. This proves (2.5). Every transition at every cut of the word remains present; there are no additional restrictions at such cuts. $\square$

**Definition 2.3 (Contributions of actual coordinate edges).** For every $1\le i\le n$, let

$$
\Phi_{n,i}(\mu)=
\sum_{\substack{b\in B_n\\ b_{i-1}=b_i=b_{i+1}=0}}
h(\mu(b),\mu(b+e_i)).
\tag{2.7}
$$

Each original edge has exactly one lower endpoint and exactly one coordinate. Consequently $\Phi_n(\mu)=\sum_{i=1}^n\Phi_{n,i}(\mu)$, with the same formula at both boundary coordinates.

**Proposition 2.4 (Full-word ratios, including boundaries).** For any upward edge $c=b+e_i$ and $n\ge2$, put

$$
J_{n,i}=\{j:1\le j\le n-2,\ j\le i\le j+2\}.
$$

The ratio of the probabilities of its actual full-word endpoints is

$$
\frac{\mu_n(c)}{\mu_n(b)}
=\frac{\pi_{c_1c_2}}{\pi_{b_1b_2}}
\prod_{j\in J_{n,i}}
\frac{P_{c_jc_{j+1},\,c_{j+1}c_{j+2}}}
{P_{b_jb_{j+1},\,b_{j+1}b_{j+2}}}.
\tag{2.8}
$$

At $n=1$ the unique upward ratio is $9/29$. In particular, for $n\ge5$ and $3\le i\le n-2$, the flip changes the window $x000y$ to $x010y$, and the ratio, independently of its outside completion, is

$$
R_{xy}=
\frac{P_{x0,01}P_{01,10}P_{10,0y}}
{P_{x0,00}P_{00,00}P_{00,0y}}
=\frac{200}{343}\left(\frac76\right)^{x+y}.
\tag{2.9}
$$

The four values in context order $xy=00,01,10,11$ are

$$
\frac{200}{343},\qquad
\frac{100}{147},\qquad
\frac{100}{147},\qquad
\frac{50}{63}.
\tag{2.10}
$$

**Proof.** Divide the two products in (2.2). A transition factor can change only when its triple contains position $i$. Every denominator in (2.8) is positive because the lower word is legal. This proves the formula for all boundaries and all $n\ge2$, including empty transition products. For an interior position, its initial pair is unchanged and exactly three transition factors remain; substituting (2.1) gives (2.9)–(2.10).

These ratios arise from one probability vector. In particular the shares

$$
a_{c\leftarrow b}=\frac{\mu_n(c)}{\mu_n(b)+\mu_n(c)},\qquad
a_{b\leftarrow c}=\frac{\mu_n(b)}{\mu_n(b)+\mu_n(c)}
\tag{2.11}
$$

are simultaneously feasible on every original edge. Interior insertion ratios depend on the distance-two bits $x,y$, even though every insertion changes $k$ by the same amount. $\square$

## 3. Exact extensive density and a bounded endpoint remainder

**Theorem 3.1 (Harmonic density of the pair prior).** Define the rational number

$$
d=\frac1{38}\left(\frac{1372}{543}+\frac{588}{247}+\frac{63}{113}\right).
\tag{3.1}
$$

For every $n\ge5$ there is $E_n\in[0,1]$ such that

$$
\Phi_n(\mu_n)=(n-4)d+E_n.
\tag{3.2}
$$

For every $n\ge1$,

$$
|\Phi_n(\mu_n)-nd|\le1.
\tag{3.3}
$$

In particular,

$$
\lim_{n\to\infty}\frac{\Phi_n(\mu_n)}n=d,
\qquad
\lim_{N\to\infty}\frac{\Phi_{3N}(\mu_{3N})}{3N}=d.
\tag{3.4}
$$

**Proof.** Fix $n\ge5$ and $3\le i\le n-2$. By (2.5), the probabilities of its lower and upper windows are respectively

$$
L_{xy}=\pi_{x0}P_{x0,00}P_{00,00}P_{00,0y},\qquad
U_{xy}=\pi_{x0}P_{x0,01}P_{01,10}P_{10,0y}.
\tag{3.5}
$$

Their exact values are as follows; the entries in the two middle columns have the common denominator $1900$.

| Context $xy$ | $1900L_{xy}$ | $1900U_{xy}$ | $R_{xy}$ |
| --- | ---: | ---: | ---: |
| $00$ | $343$ | $200$ | $200/343$ |
| $01$ | $147$ | $100$ | $100/147$ |
| $10$ | $147$ | $100$ | $100/147$ |
| $11$ | $63$ | $50$ | $50/63$ |

For example, $L_{00}=(10/19)(7/10)^3=343/1900$ and $U_{00}=(10/19)(3/10)(2/3)=200/1900$. The other entries follow from the same three-factor products.

For each context, retaining an outside completion and flipping only coordinate $i$ is a bijection between its lower and upper full words. Both windows have zero bits next to the changed coordinate, so the same outside completions are legal on both sides. Enumerate their actual endpoint masses as $(s_\omega,t_\omega)$. Proposition 2.4 gives $t_\omega=R_{xy}s_\omega$ for every completion, and therefore

$$
\begin{aligned}
\sum_\omega h(s_\omega,t_\omega)
&=\frac{R_{xy}}{1+R_{xy}}\sum_\omega s_\omega\\
&=h\left(\sum_\omega s_\omega,\sum_\omega t_\omega\right)
=h(L_{xy},U_{xy}).
\end{aligned}
\tag{3.6}
$$

Thus the grouping is an equality justified by common ratios of paired full-word masses. Both marginals in (3.6) belong to the same normalized law $\mu_n$.

Summing the four contexts yields

$$
\begin{aligned}
\Phi_{n,i}(\mu_n)
&=\frac1{1900}\left(
\frac{343\cdot200}{543}
+2\frac{147\cdot100}{247}
+\frac{63\cdot50}{113}\right)\\
&=\frac1{38}\left(\frac{1372}{543}+\frac{588}{247}+\frac{63}{113}\right)=d.
\end{aligned}
\tag{3.7}
$$

This exact value occurs at all $n-4$ interior coordinates, without a limiting approximation.

The edges at any one coordinate form a matching. The elementary inequality $h(s,t)\le(s+t)/4$ follows from $(s-t)^2\ge0$. Since the masses of the endpoints of a matching sum to at most one, for every probability vector on $B_n$,

$$
0\le\Phi_{n,i}(\mu)\le\frac14.
\tag{3.8}
$$

All edges at coordinates $1,2,n-1,n$ remain in the objective. Their sum is exactly

$$
E_n=\Phi_{n,1}(\mu_n)+\Phi_{n,2}(\mu_n)
+\Phi_{n,n-1}(\mu_n)+\Phi_{n,n}(\mu_n)\in[0,1],
$$

proving (3.2). Taking an interior coordinate at length five in (3.8) also gives $0\le d\le1/4$. For $n\ge5$, $\Phi_n(\mu_n)-nd=E_n-4d$ lies in $[-1,1]$. For $1\le n\le4$, both $\Phi_n(\mu_n)$ and $nd$ lie in $[0,n/4]$, again proving (3.3). Division by $n$ proves both limits. $\square$

## 4. A rational margin over the entire one-activity family

**Theorem 4.1 (Strict bulk separation).** With $d$ as in (3.1),

$$
d>\frac{23}{160}+\frac1{76000},\qquad
g(r)<\frac{23}{160}\quad(r>1).
\tag{4.1}
$$

The optimized finite-length one-activity values satisfy

$$
\lim_{n\to\infty}\frac{H_n}{n}=g(r_\star),\qquad
\lim_{n\to\infty}\frac{\Phi_n(\mu_n)-H_n}{n}
=d-g(r_\star)>\frac1{76000}.
\tag{4.2}
$$

Hence the original all-prior growth constant obeys

$$
c_\star\ge d>g(r_\star)+\frac1{76000},\qquad
\kappa_n\ge dn\quad(n\ge1).
\tag{4.3}
$$

The limits and strict gap in (4.2) also hold on $n=3N$. In particular the equality $c_\star=g(r_\star)$ in [Growth], Open Problem 9.4, is false.

**Proof.** The three positive integer differences

$$
1372\cdot1000-2526\cdot543=382,\qquad
588\cdot1000-2380\cdot247=140,\qquad
63\cdot1000-557\cdot113=59
$$

give

$$
d>\frac{2526+2380+557}{38000}
=\frac{5463}{38000}
=\frac{23}{160}+\frac1{76000}.
\tag{4.4}
$$

For $r>1$ put $D(r)=(r^2-r+1)(2r-1)>0$. Then

$$
\frac{23}{160}-g(r)
=\frac{Q(r)}{160D(r)},\qquad
Q(r)=23D(r)-160(r-1)=46r^3-69r^2-91r+137.
$$

Writing $t=r-3/2>-1/2$ gives the exact positive decomposition

$$
\begin{aligned}
Q(r)&=46t^3+138t^2+\frac{25}{2}t+\frac12\\
&=46t^2\left(t+\frac12\right)
+115\left(t+\frac5{92}\right)^2+\frac{59}{368}>0.
\end{aligned}
\tag{4.5}
$$

This proves (4.1), including the uniform comparison with every fixed activity.

For completeness, the finite-length optimization in (4.2) allows its activity to vary with $n$. Pairing insertions and deletions gives, for the actual hard-core law,

$$
\mathbb E_{\nu_{n,\lambda}}k
=\lambda\mathbb E_{\nu_{n,\lambda}}u,\qquad
\Phi_n(\nu_{n,\lambda})
=\frac{\mathbb E_{\nu_{n,\lambda}}k}{1+\lambda}
=\frac{\lambda}{1+\lambda}\mathbb E_{\nu_{n,\lambda}}u.
\tag{4.6}
$$

Indeed every upper endpoint is counted $k(b)$ times by its possible deletions, and the weight of an upper endpoint is $\lambda$ times that of its paired lower endpoint. The harmonic identity is [Growth], Proposition 7.1. Since $u\le n$ and $k\le n$, (4.6) gives bounds uniform in $n$:

$$
\frac{\Phi_n(\nu_{n,\lambda})}{n}
\le\frac{\lambda}{1+\lambda},\qquad
\frac{\Phi_n(\nu_{n,\lambda})}{n}
\le\frac1{1+\lambda}.
\tag{4.7}
$$

On a compact positive activity interval $I$, let $r=r(\lambda)=(1+\sqrt{1+4\lambda})/2$ and $\theta=(r-1)/r$. The classical path formula [Growth], Lemma 7.2; [SS], §3.2, equations (3.17)–(3.19), is

$$
Z_n(\lambda)=\frac{r^{n+2}-(1-r)^{n+2}}{2r-1}
=\frac{r^{n+2}}{2r-1}\bigl(1-(-\theta)^{n+2}\bigr).
\tag{4.8}
$$

There is $q_I<1$ with $0<\theta\le q_I$ on $I$. Differentiating this finite expression and using $r'=1/(2r-1)$ and $\theta'=r'/r^2$ shows, uniformly on $I$,

$$
\frac1n\mathbb E_{\nu_{n,\lambda}}k
=\frac{\lambda}{n}\frac{d}{d\lambda}\log Z_n(\lambda)
=\frac{\lambda}{r(2r-1)}
+O_I\left(n^{-1}+q_I^n\right).
\tag{4.9}
$$

To bound the differentiated final factor, its denominator is at least $1-q_I^{n+2}$, and the absolute derivative of its numerator is at most $(n+2)q_I^{n+1}\max_I|\theta'|$. The other two differentiated factors in (4.8) give the displayed leading term and an $O_I(n^{-1})$ term. Thus (4.9) follows directly without interchanging a derivative and an unproved limit. Equations (4.6) and (4.9) imply uniformly on $I$ that $\Phi_n(\nu_{n,\lambda})/n\to g(r(\lambda))$.

Choose $I=[\alpha,\beta]$ containing $\lambda_\star=r_\star(r_\star-1)$ with $\alpha$ small and $\beta$ large enough that both activity-tail bounds in (4.7) are strictly below $g(r_\star)>0$. On $I$, uniform convergence and the owned maximization of $g$ give $\limsup H_n/n\le g(r_\star)$; the same bound holds outside $I$ by (4.7). Evaluating the supremum at $\lambda_\star$ gives the reverse $\liminf$ bound. This proves the first limit in (4.2), including arbitrary length-dependent choices of activity. Theorem 3.1 gives its second limit; (4.1) makes that limit strictly greater than $1/76000$.

Finally $\kappa_n\ge\Phi_n(\mu_n)$ by (1.1). Taking the all-length limits gives $c_\star\ge d$. The identity $c_\star=\inf_{n\ge1}\kappa_n/n$ in (1.1) then implies $\kappa_n\ge dn$ for every positive length. This last assertion is about the optimized graph quantity; the displayed prior itself has the finite-volume formula (3.2). Restricting the already established limits to $n=3N$ completes the proof. $\square$

## 5. Remaining extremal questions and citation limits

**Open Problem 5.1 (Exact growth constant).** Determine the exact value of $c_\star$ from (1.1), or give a matching upper bound for the supremum over all full-domain priors. Theorem 4.1 excludes the hard-core equality alternative of [Growth], Open Problem 9.4. It supplies a strict lower witness, not an equality $c_\star=d$. Whether $d$ is optimal even within stationary two-step priors is also undetermined.

**Open Problem 5.2 (Optimizers and constant terms).** Determine the structure of the maximizing priors for $\Phi_n$: uniqueness, full support, dependence on $k(b)$ and possible additional word relations. Determine whether $\kappa_n-c_\star n$ converges, or converges separately along even and odd lengths. These are the optimizer and constant-term questions of [Growth], Open Problem 9.5; the bounded remainder for the specific prior in Theorem 3.1 does not determine the remainder for $\kappa_n$.

**Citation scope 5.3.** [Growth], Definitions 2.1–2.6 and Theorems 3.2, 5.2 and 7.3, own the graph objective, harmonic duality, existence and near-linear bounds for $c_\star$, and exact optimized hard-core comparator. Its Proposition 9.3 proves finite-length hard-core nonoptimality, with no strict bulk conclusion. The new comparison is Theorems 3.1 and 4.1 for the explicit law (2.2). Alexander D. Scott and Alan D. Sokal, *The repulsive lattice gas, the independent-set polynomial, and the Lovász local lemma*, arXiv:cond-mat/0309352v2 [SS], supplies the independent-set and path-partition formulas cited in Definition 1.4 and the proof of Theorem 4.1. Its repulsive-interaction hypothesis $0\le W\le1$ does not supply the distance-two factor $7/6$ in (2.9); normalization and edge ratios of this prior are proved in §2. Stationary finite-state cylinders and homogeneous harmonic grouping are elementary probability machinery. No worldwide priority assertion for the strict comparison is part of these mathematical conclusions.

[Growth]: https://github.com/the-omega-institute/trureturing/blob/409f27ebed169a35fa000f22ed56a2f154cb9c93/docs/develop/theory/FIB_LEGAL_EDGE_LOAD_GROWTH_CONSTANT.md
[SS]: https://arxiv.org/html/cond-mat/0309352v2

## 追加锚（本行以下为增补区）
