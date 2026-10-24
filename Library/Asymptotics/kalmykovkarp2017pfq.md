---
bibkey: kalmykovkarp2017pfq
authors: S. I. Kalmykov and D. B. Karp
year: 2017
title: Log-concavity and Turán-type inequalities for the generalized hypergeometric function
doi: 10.1007/s10476-017-0503-z
url: https://arxiv.org/abs/1611.06724
claim: "Conjecture 1 extends the conclusions of Theorem 3 to all nonnegative shifts when mu is at least one."
strata_touched:
  - D5/S3/Analytic/HypergeometricShiftTuran/Defs
  - D5/S3/Analytic/HypergeometricShiftTuran/Result
  - D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockDefs
  - D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockResult
license: citation-only
triage: anchor
---

# Shifted hypergeometric Turanian coefficients

## Verified locator

DOI: 10.1007/s10476-017-0503-z

Source: https://arxiv.org/abs/1611.06724

Pinned version: https://arxiv.org/abs/1611.06724v1, Section 3,
equations (9), (10), (13), Theorem 3 and Conjecture 1. Journal publication:
*Analysis Mathematica* 43 (2017), 567–580.

## Mathematical correspondence

Equation (10) defines

$$
f(\mu;x)=\sum_{n=0}^{\infty}
\frac{\Gamma(a+\mu+n)}{\Gamma(b+\mu+n)}\frac{x^n}{n!}.
$$

In the generalized parameter notation, the coefficient ratio is

$$
c(t)=\frac{\prod_{i=1}^{p}\Gamma(a_i+t)}
{\prod_{j=1}^{q}\Gamma(b_j+t)},
\qquad
f(\mu;x)=\sum_{n=0}^{\infty}c(\mu+n)\frac{x^n}{n!}.
$$

Equation (9) defines the shifted Turanian

$$
\Delta_f(\alpha,\beta;x)=
f(\mu+\alpha;x)f(\mu+\beta;x)
-f(\mu;x)f(\mu+\alpha+\beta;x),
$$

and its degree-$m$ coefficient is

$$
\delta_m=\sum_{k=0}^{m}
\frac{c(\mu+\alpha+k)c(\mu+\beta+m-k)
-c(\mu+k)c(\mu+\alpha+\beta+m-k)}{k!(m-k)!}.
$$

Condition (13) is the descending chain of consecutive ratios of elementary
symmetric functions of the denominator and numerator parameters:

$$
\frac{e_{q-j}(\mathbf b)}{e_{p-j}(\mathbf a)}
\le
\frac{e_{q-j-1}(\mathbf b)}{e_{p-j-1}(\mathbf a)}
\qquad(0\le j<p).
$$

Theorem 3 proves $\Delta_f(\alpha,\beta;x)\ge0$ for $x\ge0$ when
$\mu,\beta\ge0$ and $\alpha\in\mathbb N$, under $p\le q$ and (13); if
$\alpha\le\beta+1$, it also proves $\delta_m\ge0$ for every
$m\in\mathbb N_0$. Conjecture 1 states verbatim:

> All conclusions of Theorem 3 hold for all α, β ≥ 0 if µ ≥ 1.

The Lean definitions `Defs.coeff`, `Defs.turanCoeff`, `Defs.esymm` and
`Defs.cond13` encode the coefficient ratio, the finite Cauchy coefficient,
the elementary symmetric functions and condition (13). `Defs.claim` records
the coefficient conclusion in the $p\le q$ branch, while `Result.result`
refutes that coefficient clause.

The bounded literature scope and its limitations are stated in
`Problems/kalmykov-karp-pfq-conjecture-one-coefficients.md`.
