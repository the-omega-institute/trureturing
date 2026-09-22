---
bibkey: xu2026rational
authors: Ce Xu and Jianqiang Zhao
year: 2026
title: Rational Approximations for Reciprocals of Multiple Zeta Values and Trivariate Cauchy Numbers
doi: 10.48550/arXiv.2609.11072
url: https://arxiv.org/html/2609.11072v1
claim: "Equations (7)-(8) define the strict multiple polylogarithm and its depth-normalized reciprocal coefficients; Conjecture 1.3 asks for eventual coefficient signs and an admissible strict binomial lower bound."
strata_touched:
  - D5/S3/AnalyticClosure/Polylogarithm/CompositionDisk
  - D5/S3/AnalyticClosure/Polylogarithm/CompositionRecurrences
  - D5/S3/AnalyticClosure/Polylogarithm/CompositionZeroFree
license: citation-only
triage: anchor
---

<!-- GID: D5/L/AnalyticClosure/xu2026rational -->
# Xu and Zhao's multiple-polylogarithm coefficients

## Source locator

DOI: 10.48550/arXiv.2609.11072
Source URL: https://arxiv.org/html/2609.11072v1
Version 1, equations (7)-(8), the constant term immediately following (8),
and Conjecture 1.3. The source HTML SHA256 is
`7fb0df703ba12b20b967a7a297c2d75e8a73408fb2a43f1c134256139883055f`.

For a nonempty positive composition $k=(k_1,\ldots,k_d)$, the source uses

$$
\operatorname{Li}_k(z)=\sum_{n_1>\cdots>n_d>0}
\frac{z^{n_1}}{n_1^{k_1}\cdots n_d^{k_d}},\qquad
F_k(z)=\frac{\operatorname{Li}_k(z)}{z^d}.
$$

The quotient is extended at zero. Its positive constant term is
$\prod_{i=1}^d(d+1-i)^{-k_i}$. Equation (8) defines ordinary coefficients
$C_n^{j;k;\ell}$ of $(1-z)^{-j}F_k(z)^{-\ell}$, without a factorial.
The admissibility condition is $k_1>1$.

Conjecture 1.3 quantifies over every positive composition and every
$\ell\ge1$: $C_n^{0;k;\ell}<0$ eventually. For each fixed $j\ge1$ it asks
for $C_n^{j;k;\ell}>0$ eventually, and, when $k_1>1$, the strict bound
$C_n^{j;k;\ell}>\binom{n+j-1}{n}/\zeta(k)^\ell$ eventually.
Thresholds can depend on $k,\ell,j$. The source proves the all-one,
depth-one and depth-two cases; those cases do not constitute the general
conjecture.

## Exact formal correspondence

`head : PNat` and `tail : List PNat` encode every nonempty positive
composition; `depth tail = tail.length + 1`. `H tail N` sums the remaining
strict indices at most $N$. The normalized coefficient is
$H_{n+d-1}(\mathrm{tail})/(n+d)^{\mathrm{head}}$.
`StrictIndices` independently chooses each positive index below its
predecessor. `source_series` identifies its sum with `li`, proves the
exact zero order $d$, and identifies the constant with the recursive
minimal-tuple product `leading`.

The result `CompositionZeroFree.result` proves absolute convergence and
analyticity of the actual normalized series on $|z|<1$, its nonvanishing,
and analyticity and positive real part of the explicit extension
$Q(0)=d$, $Q(z)=z\operatorname{Li}'_k(z)/\operatorname{Li}_k(z)$ off zero.
`source_recurrences` proves both differential recurrences, including the
origin values; it never equates a nonzero removable value with total
division by zero.

This is an intermediate disk theorem, not a resolution of Conjecture 1.3.
It supplies no coefficient-sign theorem, admissible boundary convergence,
slit continuation, bank asymptotics or contour transfer. Solved-problem
credit is zero. The preregistered target is
https://github.com/the-omega-institute/trureturing/issues/9372.

## Reuse and literature boundary

The frozen `AnalyticLogarithmicContinuation.scalar_series_analytic_unit_disk`
supplies scalar-series analyticity. Pinned Mathlib supplies weighted
geometric summability, differentiation of normally convergent series,
analytic orders, compact minimization and real derivatives of complex
paths. The classical integral-preservation argument is credited to
`D5/L/AnalyticClosure/miller1978starlike` and remains local in the source
consumer. No external primitive was transplanted.

The bounded supplied search found no exact all-composition Lean supplier.
The source's stated known cases and the supplied preregistration do not
establish worldwide unresolved status or priority. Exhaustive later
literature coverage is ASSUMED-UNVERIFIED; no originality claim is made.
