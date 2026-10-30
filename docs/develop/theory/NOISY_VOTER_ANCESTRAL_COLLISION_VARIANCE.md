# Noisy voter ancestral collisions and repetition variance

## 1. Synchronous opinions and their sources

**Assumption 1.1 (The synchronous noisy voter law).** Let $G=(V,E)$ be a connected, locally finite, undirected simple graph, finite or infinite, with

$$
1\leq \deg(v)=|N(v)|<\infty\qquad(v\in V).
$$

Fix $u\in V$, $0<\varepsilon<1$ and $q=1-\varepsilon$. On an arbitrary probability space $(\Omega,\mathcal F,\mathbb P)$, let the following entire family of measurable random variables be mutually independent:

- initial opinions $I_v\sim\operatorname{Bernoulli}(1/2)$, for $v\in V$;
- fresh opinions $F_{n,v}\sim\operatorname{Bernoulli}(1/2)$, for $n\geq1$ and $v\in V$;
- refresh controls $R_{n,v}\sim\operatorname{Bernoulli}(\varepsilon)$, for $n\geq1$ and $v\in V$;
- neighbour choices $J_{n,v}$, uniform on the actual finite set $N(v)$, for $n\geq1$ and $v\in V$.

Thus the joint law is the product of these marginal laws: prescribing finitely many distinct opinion coordinates contributes a factor $2^{-1}$ per coordinate, prescribing a control value $r\in\{0,1\}$ contributes $\varepsilon^r q^{1-r}$, and prescribing $J_{n,v}=w\in N(v)$ contributes $1/\deg(v)$. The probability of every such simultaneous prescription is the product of its factors. Different kinds of coordinates have disjoint indices, even at the same vertex and time.

Define the opinions by the actual synchronous recursion

$$
X_0(v)=I_v,\qquad
X_n(v)=
\begin{cases}
F_{n,v},&R_{n,v}=1,\\
X_{n-1}(J_{n,v}),&R_{n,v}=0
\end{cases}
\quad(n\geq1).
\tag{1.1}
$$

All vertices use the preceding time layer when copying. This is the law of Benjamini, Helman Tov and Zhukovskii [1, Section 1, p. 2], with their $\xi_n(v),Y_n(v),\eta_n(v)$ corresponding respectively to $R_{n,v},F_{n,v},J_{n,v}$. No stationary initial law is substituted for the independent initial opinions.

**Definition 1.2 (Disjoint source labels).** Define the disjoint union

$$
\mathcal L=
\bigl(\{\mathrm{initial}\}\times V\bigr)
\sqcup
\bigl(\{\mathrm{fresh}\}\times\mathbb N_{\geq1}\times V\bigr).
$$

Attach opinion coins and signs to these labels by

$$
B_{(\mathrm{initial},v)}=I_v,\quad
B_{(\mathrm{fresh},n,v)}=F_{n,v},\qquad
\sigma_\ell=2B_\ell-1\in\{-1,1\}.
$$

The birth time of an initial label is $0$, and the birth time of $(\mathrm{fresh},n,v)$ is $n$. Let

$$
\mathcal H=\sigma(R_{n,v},J_{n,v}:n\geq1,\ v\in V).
$$

The source label of the actual recursion is

$$
S_0(v)=(\mathrm{initial},v),\qquad
S_n(v)=
\begin{cases}
(\mathrm{fresh},n,v),&R_{n,v}=1,\\
S_{n-1}(J_{n,v}),&R_{n,v}=0.
\end{cases}
\tag{1.2}
$$

Equivalently, starting at $(v,n)$, follow the selected edge to the preceding time layer until the first refresh, or until time zero. The terminal fresh or initial coordinate is the label. These are the finite-time graphical histories of [1, Section 2], with their terminal opinion coordinates made explicit. If two histories reach the same space-time vertex, their subsequent backward histories agree. Conversely, equal terminal labels mean that the histories meet at that terminal vertex. Thus equality of source labels is precisely coalescence of these terminated histories; it does not mean merely that two opinion values happen to agree.

**Definition 1.3 (Observation pairs and multiplicities).** For integers $d\geq1$ and $t\geq0$, write

$$
\zeta_i=\mathbf1\{X_i(u)=X_{i+d}(u)\},\qquad
W_t=\sum_{i=1}^t\zeta_i,\qquad
a_i=S_i(u),\quad b_i=S_{i+d}(u).
\tag{1.3}
$$

The data used by $W_t$ extend through time $t+d$. Define

$$
c_i=\mathbf1\{a_i=b_i\},\qquad C_t=\sum_{i=1}^t c_i.
$$

Let $\mathcal E$ be the set of all two-element subsets of $\mathcal L$. For each unordered pair $e\in\mathcal E$, set

$$
m_e=\#\{i\in\{1,\ldots,t\}:a_i\ne b_i,\ \{a_i,b_i\}=e\}.
\tag{1.4}
$$

Each unordered pair occurs once in a sum over $\mathcal E$; its repeated appearances among the observations are recorded by $m_e$. In particular,

$$
\sum_{e\in\mathcal E}m_e=t-C_t.
\tag{1.5}
$$

Empty sums are zero, so $W_0=C_0=0$ and every $m_e=0$ when $t=0$. The statistic agrees with the unnormalised repetition sum in [1, Section 2.2, pp. 5–6].

## 2. Exact collision decomposition

**Theorem 2.1 (Finite-time variance and its nonnegative remainder).** Under Assumption 1.1, for every observation vertex $u$, every integer lag $d\geq1$, every integer $t\geq0$, and every probability-space realization of the specified joint law, the objects in Definitions 1.2–1.3 are measurable and satisfy

$$
\boxed{
\operatorname{Var}(W_t)
=\frac14\operatorname{Var}(C_t)
 +\frac14\mathbb E\!\left[\sum_{e\in\mathcal E}m_e^2\right].
}
\tag{2.1}
$$

More precisely,

$$
\begin{aligned}
\operatorname{Var}(W_t)
-\frac14\sum_{i=1}^t\mathbb P(a_i\ne b_i)
&=\frac14\operatorname{Var}(C_t)
 +\frac14\mathbb E\!\left[\sum_{e\in\mathcal E}m_e(m_e-1)\right]\\
&=\frac14\operatorname{Var}(C_t)
 +\frac12\sum_{1\leq i<j\leq t}
 \mathbb P\bigl(a_i\ne b_i,\ a_j\ne b_j,
       \{a_i,b_i\}=\{a_j,b_j\}\bigr)
\ \geq\ 0.
\end{aligned}
\tag{2.2}
$$

Consequently,

$$
\boxed{
\operatorname{Var}(W_t)
\ \geq\ \frac14\sum_{i=1}^t\mathbb P(a_i\ne b_i)
\ \geq\ \frac t4(1-q^d).
}
\tag{2.3}
$$

Equality in the **first** inequality of (2.3) holds if and only if both of the following hold: $C_t$ is almost surely constant, and almost surely $m_e\leq1$ for every $e\in\mathcal E$. This characterizes that first inequality only, not equality in the final universal bound.

The graphical histories and the treatment of four histories by their shared fair colours are inherited from [1, Sections 2 and 2.4, pp. 3–4 and 12–13]. Fair-sign character orthogonality and total variance are classical inputs; see [4, Chapter 1] for the former. The assertions proved here combine the actual finite-time source partition with its unordered-pair multiplicities, retaining both terms in (2.1) and the exact remainder in (2.2).

*Proof.* We first justify the finite-time constructions on an infinite graph. For $N\geq0$, let

$$
K_N=\{v\in V:\operatorname{dist}_G(u,v)\leq N\}.
$$

The set $K_0=\{u\}$ is finite. If $K_N$ is finite, then

$$
K_{N+1}=K_N\cup\bigcup_{v\in K_N}N(v)
$$

is a finite union of finite sets. Hence every $K_N$ is finite. Connectivity gives $V=\bigcup_{N\geq0}K_N$, so $V$ is at most countable.

Fix $t,d$ and put $N=t+d$. Every history starting at $(u,s)$ with $0\leq s\leq N$ remains inside $K_N$ and uses at most $N$ backward steps. All its possible sources belong to the deterministic finite set

$$
\mathcal L_N=
\{(\mathrm{initial},v):v\in K_N\}
\sqcup
\{(\mathrm{fresh},n,v):1\leq n\leq N,\ v\in K_N\}.
$$

It is enough to reveal the finitely many controls and choices with $1\leq n\leq N$ and $v\in K_N$, and the finitely many opinion coins in $\mathcal L_N$. The recursion only consults choices along paths that have not yet reached time zero; at the $k$th backward step their distance from $u$ is at most $k$. Thus this finite set of coordinates determines all observations in (1.3). Each choice has a finite range, so induction on time expresses each relevant source and opinion as a finite measurable case distinction. This proves their measurability, as well as that of $C_t$ and all relevant multiplicities. The same argument with any vertex as root defines every $S_n(v)$ and $X_n(v)$. All sums over $\mathcal E$ below may therefore be taken over the fixed finite set of two-element subsets of $\mathcal L_N$; all other summands vanish.

Induction in (1.1)–(1.2) gives the pathwise identities

$$
X_n(v)=B_{S_n(v)},\qquad
2X_n(v)-1=\sigma_{S_n(v)}.
\tag{2.4}
$$

Indeed, they hold initially. At a refresh both recursions choose the same fresh coordinate; at a copy both use the same selected neighbour in the preceding time layer. The birth time of $S_n(v)$ is at most $n$.

All source labels and multiplicities are $\mathcal H$-measurable. The family of opinion signs is independent of $\mathcal H$ and consists of independent fair signs: this follows from mutual independence in Assumption 1.1, first for finite cylinders and then for the generated sigma-fields. In particular, on the given probability space, for every deterministic finite $A\subset\mathcal L$ and prescribed signs $s_\ell\in\{-1,1\}$,

$$
\mathbb P(\sigma_\ell=s_\ell\text{ for all }\ell\in A\mid\mathcal H)
=2^{-|A|}\quad\text{almost surely}.
\tag{2.5}
$$

This is an identity of conditional expectations, requiring no assumption that the underlying probability space itself is a canonical product space. It implies the same fair product law for any distinct labels selected measurably from the fixed finite set $\mathcal L_N$: expand over their possible labels. It does not assert independence of the observed opinions, which share a coin whenever their labels coincide.

For an unordered pair $e=\{\ell,k\}\in\mathcal E$, define $\chi_e=\sigma_\ell\sigma_k$. This does not depend on its orientation. The classical character cancellation in (2.5) gives

$$
\mathbb E(\chi_e\mid\mathcal H)=0,\qquad
\mathbb E(\chi_e\chi_f\mid\mathcal H)
=\begin{cases}1,&e=f,\\0,&e\ne f.\end{cases}
\tag{2.6}
$$

To check the second identity explicitly, when $e=f$ each of the two signs is squared. When $e\ne f$, their symmetric difference is nonempty: the two pairs are either disjoint, or share exactly one label. Some independent fair sign then occurs to an odd power, so averaging it gives zero. This is pairwise orthogonality, not mutual independence of all pair characters.

For signs $x,y\in\{-1,1\}$, $\mathbf1\{x=y\}=(1+xy)/2$. Using (2.4) and grouping precisely the unordered pairs in (1.4), we obtain

$$
W_t=\frac t2+\frac{C_t}{2}
       +\frac12\sum_{e\in\mathcal E}m_e\chi_e.
\tag{2.7}
$$

The coalesced pairs contribute $1$ to their sign products, whereas a noncoalesced pair contributes its character. From (2.6), taking the $\mathcal H$-measurable multiplicities outside the conditional expectations,

$$
\mathbb E(W_t\mid\mathcal H)=\frac{t+C_t}{2},\qquad
\operatorname{Var}(W_t\mid\mathcal H)
=\frac14\sum_{e\in\mathcal E}m_e^2.
\tag{2.8}
$$

For example, the second formula follows by squaring the last sum in (2.7); all mixed terms with different pairs have conditional expectation zero. Since $0\leq W_t,C_t\leq t$ and $\sum_e m_e^2\leq t^2$, all variables used here have finite second moments. The law of total variance now gives (2.1).

By (1.5),

$$
\mathbb E\!\left[\sum_e m_e\right]
=t-\mathbb E C_t
=\sum_{i=1}^t\mathbb P(a_i\ne b_i).
$$

Subtract one quarter of this identity from (2.1) to get the first line of (2.2). For any fixed source realization, $m_e(m_e-1)/2$ counts the index pairs $i<j$ carrying the same noncoalesced unordered pair $e$. Summing this counting identity and taking expectations proves the second line of (2.2). Both terms of its first line are nonnegative, proving the first inequality of (2.3).

The equality criterion follows in both directions from the same remainder. If equality holds, its two nonnegative terms vanish. Variance zero is equivalent to $C_t=\mathbb E C_t$ almost surely. Also the nonnegative integer-valued sum $\sum_e m_e(m_e-1)$ must be zero almost surely. On that probability-one event, every summand is zero and hence each $m_e$ is $0$ or $1$. Conversely, if $C_t$ is almost surely constant and all the multiplicities are at most one almost surely, both remainder terms vanish. The possible nonzero multiplicities belong to a deterministic finite set, so the simultaneous assertion over all $e$ introduces no exceptional-set problem. For $t=0$, both conditions and the equality hold automatically.

It remains to prove the second inequality of (2.3). For a fixed $i\geq1$, follow the potential copy path from $(u,i+d)$ through exactly $d$ layers, whether or not a refresh is present. Define

$$
Z_0=u,\qquad
Z_{k+1}=J_{i+d-k,Z_k}\quad(0\leq k<d),
$$

and let

$$
A_i=\bigcap_{k=0}^{d-1}\{R_{i+d-k,Z_k}=0\}.
$$

Condition on all neighbour choices. The $Z_k$ are then fixed, and the $d$ inspected controls have distinct time coordinates. They are independent of those choices and independent of one another, each being zero with probability $q$. Thus

$$
\mathbb P(A_i)=q^d.
\tag{2.9}
$$

If $A_i$ fails, the first refresh encountered along this backward path is at a time strictly greater than $i$. By (1.2), $b_i$ is its fresh label and has birth time greater than $i$, whereas $a_i$ has birth time at most $i$. The disjoint source labels therefore give $a_i\ne b_i$. Equivalently, $\{a_i=b_i\}\subseteq A_i$, and hence

$$
\mathbb P(a_i=b_i)\leq q^d,\qquad
\mathbb P(a_i\ne b_i)\geq1-q^d.
\tag{2.10}
$$

Summing (2.10) proves the remaining inequality. For $t=0$ it is the empty-sum identity. All arguments take place on the original probability space and in finite time; neither stationarity nor a finite-graph replacement is used. Finally, (2.6) is conditional orthogonality of source-pair characters. The proof makes no assertion about the signs of individual unconditional temporal covariances of the $\zeta_i$. ∎

## 3. The lag-two optimal-constant bracket

**Definition 3.1 (Uniform lag-two constant).** For $0<\varepsilon<1$, let

$$
c_{\mathrm{opt}}(\varepsilon)
=\inf\left\{
\frac{\operatorname{Var}(W_t)}{t}:
\begin{array}{l}
G\text{ connected, locally finite and simple},\\
1\leq\deg(v)<\infty\text{ for every }v,\quad u\in V(G),\\
t\in\mathbb N_{\geq1},\quad d=2,\\
\text{the full joint law is that of Assumption 1.1}
\end{array}
\right\}.
\tag{3.1}
$$

Finite and infinite graphs are both included. The law of $W_t$ is independent of the chosen probability-space realization: its finite set of input coordinates has the product law prescribed in Assumption 1.1, and (1.1) is a fixed measurable function of them.

**Theorem 3.2 (A bracket of ratio less than two and linear small-noise order).** For every $0<\varepsilon<1$ and $q=1-\varepsilon$,

$$
\frac{1-q^2}{4}
\ \leq\ c_{\mathrm{opt}}(\varepsilon)
\ \leq\ \frac{1-q^4}{4}.
\tag{3.2}
$$

The ratio of the upper endpoint to the lower endpoint is exactly

$$
\frac{1-q^4}{1-q^2}=1+q^2<2.
\tag{3.3}
$$

In particular,

$$
\frac{2\varepsilon-\varepsilon^2}{4}
\ \leq\ c_{\mathrm{opt}}(\varepsilon)
\ \leq\
\frac{4\varepsilon-6\varepsilon^2+4\varepsilon^3-\varepsilon^4}{4},
\tag{3.4}
$$

so $c_{\mathrm{opt}}(\varepsilon)=\Theta(\varepsilon)$ as $\varepsilon\downarrow0$. More precisely,

$$
\frac12
\leq\liminf_{\varepsilon\downarrow0}\frac{c_{\mathrm{opt}}(\varepsilon)}{\varepsilon}
\leq\limsup_{\varepsilon\downarrow0}\frac{c_{\mathrm{opt}}(\varepsilon)}{\varepsilon}
\leq1.
\tag{3.5}
$$

*Proof.* Theorem 2.1 with $d=2$ gives the lower endpoint for every element of the infimum in (3.1).

For the upper endpoint we use the star-centre transition supplied by the proof of [1, Theorem 6.1, Section 6, pp. 28–29]. Its specialization to $K_{1,1}=K_2$ is an inherited source consequence, not an additional independent proposition. To make the correspondence explicit, let $u$ be either endpoint, $v$ its unique neighbour, and put $Z_n=X_n(u)$. Uniform choice on $N(u)=\{v\}$ and $N(v)=\{u\}$ means copying the other endpoint with probability $q$ at every synchronous step, exactly as in (1.1). The noise is $\varepsilon$, and both the initial and fresh opinions are independent fair coins, as required by that source.

For $n\geq2$, the supplied centre calculation gives, for every positive-probability centre history and $x\in\{0,1\}$,

$$
\begin{aligned}
\mathbb P(Z_n=x\mid Z_0,\ldots,Z_{n-1})
&=\frac{\varepsilon}{2}
 +q\left(\frac{\varepsilon}{2}
               +q\mathbf1\{x=Z_{n-2}\}\right)\\
&=\frac{1-q^2}{2}+q^2\mathbf1\{x=Z_{n-2}\}.
\end{aligned}
\tag{3.6}
$$

Here the inner conditional distribution is the leaf distribution in that proof, and the outer update is the centre update. The original initial law also makes $Z_0,Z_1$ independent fair bits: $Z_0=I_u$, while $Z_1$ uses only $R_{1,u},F_{1,u},I_v$, independently of $I_u$.

Let $p=(1+q^2)/2$. Formula (3.6) says that the next centre bit agrees with the centre bit two steps earlier with conditional probability $p$, independently of the values in the specified history. It also gives the full independence claim needed for the variance computation. For completeness, for any $M\geq2$, the map

$$
(z_0,\ldots,z_M)\longmapsto
\bigl(z_0,z_1,e_2,\ldots,e_M\bigr),\qquad
 e_n=\mathbf1\{z_n=z_{n-2}\},
$$

is a bijection of binary strings: reconstruct each $z_n$ from $z_{n-2}$ and $e_n$. By the chain rule and (3.6), its joint probability is

$$
\frac14\prod_{n=2}^{M}p^{e_n}(1-p)^{1-e_n}.
\tag{3.7}
$$

Thus the indicators $E_n=\mathbf1\{Z_n=Z_{n-2}\}$, $n\geq2$, are mutually independent $\operatorname{Bernoulli}(p)$ variables, independent also of $Z_0,Z_1$. In particular, the exact indicators used here are $\zeta_i=E_{i+2}$, $1\leq i\leq t$. Therefore, under the original $K_2$ law,

$$
W_t\sim\operatorname{Binomial}(t,p),\qquad
\operatorname{Var}_{K_2}(W_t)
=tp(1-p)=\frac t4(1-q^4)
\quad(t\geq0).
\tag{3.8}
$$

This verifies the finite-time formula with the original indexing, including $t=0$, using the credited transition. Since $K_2$ belongs to precisely the class in (3.1), any $t\geq1$ gives the upper endpoint in (3.2).

Because $0<q<1$, factorization $1-q^4=(1-q^2)(1+q^2)$ proves (3.3). Expanding the two endpoints gives (3.4). Dividing (3.4) by $\varepsilon>0$ and taking lower and upper limits proves (3.5). For explicit uniform order bounds, $1-q^2=\varepsilon(2-\varepsilon)\geq\varepsilon$ and $1-q^4=\varepsilon(1+q+q^2+q^3)\leq4\varepsilon$, so

$$
\frac{\varepsilon}{4}\leq c_{\mathrm{opt}}(\varepsilon)\leq\varepsilon.
$$

The bracket determines the linear small-noise order, without determining the exact infimum or the existence of its normalized limit. The upper comparison does not establish that $K_2$ minimizes (3.1), or identify any minimizing graph or time. ∎

## 4. Mathematical antecedents and domains

**Assumption 4.1 (Scope of the fair-source calculation).** The hypotheses for (2.1)–(3.5) are exactly Assumption 1.1. In particular, (2.6) uses independent fair initial and fresh coins; it supplies no corresponding cancellation for biased or dependent opinion coins or for deterministic initial configurations. A stationary replacement changes the joint law of the initial sources. Continuous-time or single-vertex update schedules change (1.1) and its time histories. Signed weights change the nonnegative integer multiplicities used in (2.2). None of these replacements is included among the hypotheses of the stated results.

The degree-dependent antecedent [5] supplies, in the same synchronous graph class, the bound

$$
\operatorname{Var}(W_t)
\geq\frac{\varepsilon^{\deg(u)+2}}{2}
       \left\lfloor\frac{t}{d+1}\right\rfloor
$$

and the consequent exclusion of sublinear variance. That conclusion is an existing input to the mathematical context; Theorem 2.1 adds the finite-time collision identity, its exact remainder and equality criterion, and a lower coefficient independent of degree or spacing. The upper bound of order $t$ and the linear/logarithmic alternative belong to [1, Section 2.2, equation (7) and Lemma 2.3]. Its asymptotic normality result is [1, Section 2.3, Theorem 2.7]. No new central limit theorem, graph-distinguishability conclusion, or graph-specific asymptotic variance coefficient is asserted here.

The remaining optimal-constant problem in the present domain is to determine the infimum (3.1) between the two endpoints of (3.2), and whether it is attained. The equality criterion in Theorem 2.1 concerns the first comparison in (2.3); it does not answer this optimization problem.

**Mathematical citations.**

[1] I. Benjamini, H. Helman Tov and M. Zhukovskii, *Global information from local observations of the noisy voter model on a graph*, [arXiv:2207.01224v2](https://arxiv.org/pdf/2207.01224v2). Section 1, p. 2, specifies the synchronous law; Section 2 defines the finite graphical histories; Section 2.2, pp. 5–6, specifies the repetition statistic and variance question; Section 2.4, pp. 12–13, uses four-history coalescence and fair colouring; the proof of Theorem 6.1, pp. 28–29, supplies the star-centre transition used in (3.6). The journal publication locator is DOI [10.1214/23-AOP1637](https://doi.org/10.1214/23-AOP1637); all mathematical locators here refer to the explicitly specified arXiv version. DOI [10.1016/j.physa.2026.131974](https://doi.org/10.1016/j.physa.2026.131974) is a related citation locator, not a theorem input to these proofs.

[2] R. Pymar and N. Rivera, *Asymptotic behaviour of the noisy voter model density process*, [arXiv:2112.01478v2](https://arxiv.org/pdf/2112.01478v2), Sections 1.2 and 2.2. Its finite-state discrete-time chain updates one uniformly selected vertex at a step using a transition matrix $P$; its density statistic $\sum_x\pi(x)\xi(x)$ is evaluated for $\xi$ sampled from its stationary law $\Gamma$. Proposition 11 gives its stationary duality. These are different update, initial-law and observable domains from (1.1)–(1.3); that stationary density theorem is not a supplier of (2.1) or (3.2).

[3] P. Caddeo and E. Lubetzky, *The noisy voter model with general initial conditions*, [arXiv:2507.16188v1](https://arxiv.org/pdf/2507.16188v1), Sections 1 and 2. Its updates are driven by independent rate-one Poisson clocks, with a uniform choice among its opinion states at a refresh. Its main mixing results treat deterministic initial configurations on families of bounded-degree finite graphs with subexponential ball growth. Proposition 2.5 gives stationary spatial eigenfunction-variance formulas. Neither this continuous-time stationary variance nor those mixing statements replace the synchronous finite-time repetition law here. The state-count notation $q$ in that paper is distinct from the copy probability $q=1-\varepsilon$ used here.

[4] R. O'Donnell, *Analysis of Boolean Functions*, Chapter 1, Fourier characters on the uniform discrete cube and their orthogonality, [arXiv:2105.10386v1](https://arxiv.org/pdf/2105.10386v1). For the degree-two characters needed here, the elementary cancellation is displayed explicitly in (2.6).

[5] *The repetition-count variance of the noisy voter model*, [mathematical antecedent](../../../Problems/benjamini-helman-tov-zhukovskii-2023-noisy-voter-repetition-variance.md), with the degree-dependent estimate supplied by [RepetitionVarianceLinear](../../../D5/S3/StatisticalMechanics/NoisyVoter/RepetitionVarianceLinear.lean), specifically its `product_explicitBound` and `model_explicitBound`. The source law correspondence and the non-sublinearity conclusion are inherited; they are not new conclusions of this volume.

## 追加锚（本行以下为增补区）
