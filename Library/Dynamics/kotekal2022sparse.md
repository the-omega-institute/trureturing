---
bibkey: "kotekal2022sparse"
authors: "Subhodh Kotekal"
year: 2022
title: "Statistical limits of sparse mixture detection"
doi: "10.1214/22-EJS2053"
url: "https://arxiv.org/abs/2104.02507v3"
claim: "Corollaries 1–2 express the independent sparse-mixture detection boundary through the null large-deviation rate of the normalized log-likelihood ratio, subject to a likelihood-moment condition and stated regularity assumptions."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Statistical limits of sparse mixture detection

Electronic Journal of Statistics 16(2) (2022), DOI 10.1214/22-EJS2053.
Crossref confirms the author, title, year, journal, volume, issue and DOI.
The inspected primary manuscript is the 70-page arXiv:2104.02507v3,
revised 26 May 2021; its first page and arXiv metadata agree on that version.
The primary-paper claims below refer to this pinned manuscript.

Equations (1)–(3), PDF pages 1–2, compare independent observations from
`P_n` against independent observations from `(1-n^(-beta)) P_n + n^(-beta) Q_n`.
The support count in this model is random. Assumption 1, page 5, allows a
separable metric observation space with a common dominating measure and
`Q_n << P_n`; it is not restricted to continuous observations.

Theorems 1–2 and Corollaries 1–2, page 7, assume a good large-deviation
principle at speed `log n` for the null normalized log-likelihood ratio.
Condition (6) also requires, for some fixed `gamma > 1`, a finite limsup of
`log E_P[(dQ_n/dP_n)^gamma] / log n`. Corollary 1 gives equality of the
upper and lower boundaries when its supremum condition (9) holds.
Corollary 2 supplies sufficient conditions: the rate function is right
continuous at zero and the variational integrand is nonnegative somewhere
on the nonnegative half-line. The resulting formula, equation (10), is

```math
\beta^*=\frac12+\max\left\{0,\sup_{x\ge0}
 \left[x-I(x)+\frac{1\wedge I(x)}2\right]\right\}.
```

For the parity model's independent compound-Poisson comparison coordinate,
`log E_0 L^theta = lambda g_r(theta)` with `lambda/log M -> alpha`.
The limiting cumulant is finite, smooth and steep; its Legendre transform
is a finite continuous good rate function. The moment condition holds for
every fixed `gamma > 1`. At `x = alpha phi(r)`, one has `I(x) = x > 0`,
so the sufficient nonnegativity condition also holds. Substitution in the
published variational formula yields the scalar three-branch curve used
in Chapter 17. The general formula is `literature-attested`; this scalar
specialization is not claimed as a new general detection principle.

Corollaries 1–2 do not assert the same boundary for a fixed-cardinality
positive support in a compensated kernel or for stationary Markov paths.
The actual-direction relative row-count estimates, support-uniform
covariances and growing-overlap likelihood tilt require the separate
`repo-derived` proof. No full-experiment equivalence or worldwide
originality claim follows from these scope differences.
