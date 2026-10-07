---
bibkey: gayrard2025mixedmemories
authors: Véronique Gayrard
year: 2025
title: Mixed memories in Hopfield networks
doi: null
url: https://arxiv.org/abs/2504.04879v2
claim: 'Given any $n\in\mathbb N$ odd, $\xi^{(N)}(m)$ is an $n$-mixed memory of type $F$ if and only if $m\in\mathcal M_{n,F}$.'
strata_touched:
  - D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation
license: citation-only
triage: anchor
---

## Verified locator

DOI: null

Source: https://arxiv.org/abs/2504.04879v2

Section 1.2.1, Definition 1.1 (printed p. 4), equations (1.2.1.4)–(1.2.1.15)
in `Mix-ALL_v2.tex` (printed equations (1.9)–(1.15), pp. 5–6), and
Conjecture 1.4 (printed p. 6). Section 2.2, equation (2.2.2) in the TeX
(printed (2.25), p. 15), defines `sign(0)=0`.
The arXiv source contains no DOI.

# Mixed memories and the proposed complete hierarchy

Conjecture 1.4 reads:

> Given any $n\in\mathbb N$ odd, $\xi^{(N)}(m)$ is an $n$-mixed memory of type $F$ if and only if $m\in\mathcal M_{n,F}$.

The standing convention is:

> Throughout the paper, $n\in\mathbb N$ is chosen to be independent of $N$ and $M$ is chosen to be a non-decreasing function of $N$.

Definition 1.1 begins:

> Let $F$ be a smooth function whose derivative satisfies $F'(x)>0$, for all $x>0$. Given $n\in\mathbb N$ independent of $N$, $n$-mixed memories of type $F$ are configurations in $\mathcal S_N$ denoted by $\xi^{(N)}(m)=\left(\xi_i(m)\right)_{1\leq i\leq N}$ and defined as

$$
\xi_i(m)=\operatorname{sign}\!\left(\sum_{\mu=1}^{M}\xi_i^\mu F'(m_\mu)\mathbf1_{m_\mu\ne0}\right).
$$

Definition 1.1 requires:

> (i) $m$ has exactly $n$ non-zero components, i.e. there exists a subset $V\subset\{1,\dots,M\}$ of cardinality $|V|=n$ such that $m_{\mu}\neq0$ if and only if $\mu\in V$.

> Let $\{\mu_1,\dots,\mu_n\}$ be an enumeration of the elements of $V$ and, for each $1\leq\nu\leq n$, set $m_{\mu_\nu}=\hat m_{\nu}$. Then, for each $1\leq\nu\leq n$, the normalised overlap of $\xi^{(N)}(m)$ with the pattern $\xi^{\mu_\nu}$ converges to $\hat m_{\nu}$ as $N$ diverges,

The displayed probability-one limits are (1.2.1.2), followed by
"and it converges to zero else," and (1.2.1.3). The patterns are jointly
independent symmetric Bernoulli variables with values $\pm1$.

The source specifies allowable compositions:

> We call an $\ell$-composition $(n_1,\dots,n_{\ell})$ allowable if $n_k\geq 2$ is even for all $1\leq k\leq\ell-1$ and $n_{\ell}\geq1$ is odd.

Their values are

$$
\alpha^{(a)}=2^{-a+1}\binom{a-1}{\lfloor(a-1)/2\rfloor},\qquad
\gamma^{(k)}=\prod_{l=1}^k\alpha^{(n_l)}.
$$

For every positive block size $a$, the formalization reuses `D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.c`, equal to the source's $\alpha^{(a)}=2^{-a+1}\binom{a-1}{\lfloor(a-1)/2\rfloor}$.

Only compositions satisfying
$2F'(\gamma^{(k)})>\sum_{r>k}n_rF'(\gamma^{(r)})$
for every nonfinal block are used. The source describes its block vector:

> Given $\gamma_n\in\mathcal G_{n,F}$, let $m(\gamma_n)=(m_{\mu}(\gamma_n))_{1\leq\mu\leq M}$ be the vector whose components are constant and equal to $\gamma^{(k)}$ on consecutive blocks of length $n_k$, $1\leq k\leq\ell$, and are $0$ beyond,

The displayed formula (1.2.1.8) pads the first $n$ coordinates by zeros. All permutations and all sign vectors are
then included, with exponent $a=1$ when $F'$ is odd and $a=2$ otherwise.

Theorem 1.2 establishes the sufficient direction for this constructed set.
The vector $(5/8,3/8,3/8,1/8,1/8)$ with $F(x)=x^2/2$ has strictly nonzero
fields and the required five limiting overlaps. Its coordinate $5/8$
exceeds every absolute coordinate allowed by the compositions of five.
The conjectured necessary direction therefore fails. This conclusion does
not establish an energy local minimum in the sense of Section 2.
