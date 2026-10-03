---
bibkey: ostrovskii2025amplitude
authors: Dmitrii M. Ostrovskii and Pavel S. Shcherbakov
year: 2025
title: "Amplitude maximization in stable systems, Schur positivity, and some conjectures on polynomial interpolation"
doi: 10.48550/arXiv.2508.13554
url: https://arxiv.org/abs/2508.13554v2
claim: "Conjecture 6.2 asserts the shifted Schur-ratio bound for self-conjugate grids in the closed unit disk, together with a hook-Schur bound under nonnegative real parts."
strata_touched:
  - D5/S3/Analytic/Interpolation/SelfConjugateGridSchurRatioRefutation
license: citation-only
triage: anchor
---

# Self-conjugate-grid interpolation

## Verified locator

arXiv:2508.13554v2, https://arxiv.org/abs/2508.13554v2,
DOI 10.48550/arXiv.2508.13554. The source archive at
https://arxiv.org/e-print/2508.13554v2 contains `shadrin.tex`,
`partitions.tex` and `notation.tex`. Definition 6.1 and Conjecture 6.2
are on PDF page 15; the definition of Q is on page 13; the elementary
and complete homogeneous functions are equation (17), page 7; the
tableau and Kostka definitions are on page 8, equation (19).

## Source statements

Definition 6.1, page 15:

> A list $z_{1:n} \in \mathbb{C}^n$ is self-conjugate if $(i)$ for any $z \in \{z_1,\dots,z_n\}$ with $\Im(z) \ne 0$, the conjugate $\bar z$ is also contained in $\{z_1,\dots,z_n\}$; $(ii)$ $z_{1:n}$ contains even number of copies of each $z \in \mathbb{R}$.

Conjecture 6.2 (Equivalent to Conjecture 6.1), page 15:

> For all $0 \le k < n \le t$ and self-conjugate $z_{1:n} \in \mathbb{D}^n$, $|Q_{t,n,k}(z_{1:n} + 1_n)| \le 1$. Moreover, if the grid additionally satisfies $\Re(z_{1:n}) \in \mathbb{R}^n_+$, then $|s_{(t-n|n-k-1)}(z_{1:n})| \le \binom{t}{n} |e_{n-k}(z_{1:n})|$.

Page 13:

> Let us define the rational multivariate function $Q_{t,n,k}: \mathbb{C}^n \to \mathbb{C}$, symmetric in its arguments, by

$$
Q_{t,n,k}(\zeta_{1:n}) := \sum_{d=0}^{t-n} (-1)^d
\frac{\binom{t}{n+d}s_{(d|n-k-1)}(\zeta_{1:n})}
{\binom{t}{n}e_{n-k}(\zeta_{1:n})}.
$$

Page 8:

> A semi-standard Young tableau (SSYT) with shape $\lambda \in \mathrm{Par}$ is a two-dimensional array $T$ that fills the cells of the Young diagram of $\lambda$ with positive integers, such that the entries (a) srtictly increase in each column; (b) do not decrease in each row.

Equation (19) is $s_\lambda=\sum_{\mu\in\mathrm{Par}}K_{\lambda\mu}m_\mu$,
where the Kostka number counts SSYTs of the specified shape and type.
The spelling “srtictly” is in the source.

## Encoding and scope

The source's closed disk is expressed by the complex norm, and its
nonnegative orthant by nonnegative real parts. `Fin n` relabels the
source indices 1,...,n by 0,...,n-1. Elementary functions sum over
d-element subsets. Complete homogeneous functions sum over
`Sym (Fin n) d`, multisets of cardinality d, each with one sorted,
weakly increasing tuple. A hook tableau consists of a corner c, an
arm multiset of cardinality a whose entries are at least c, and a
leg set of cardinality b whose entries exceed c. Sorting these
gives the weak row and strict column. Grouping tableau monomials by
weight and then permuted weights gives the source's Kostka expansion;
the finite tableau sum is its specialization, counted once per tableau.

The refutation retains both conjectured clauses. Complex division
is totalized in Lean; the counterexample denominator is 3/5, so no
singular-value convention is used. The source's equivalence with
Conjecture 6.1 is cited, rather than formalized here. The source's
independent proved results are outside this module's conclusion.
