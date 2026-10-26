---
bibkey: karp2016incompletebeta
authors: D. B. Karp
year: 2016
title: "Normalized incomplete beta function: log-concavity in parameters and other properties"
doi: 10.1007/s10958-016-2958-z
url: https://arxiv.org/abs/1509.05120v1
claim: "Conjecture 1 asserts strict positivity of every coefficient in the normalized incomplete beta Turanian for positive real parameters and shifts."
strata_touched:
  - D5/S3/Analytic/IncompleteBeta/Defs
  - D5/S3/Analytic/IncompleteBeta/Moment
  - D5/S3/Analytic/IncompleteBeta/Comparison
  - D5/S3/Analytic/IncompleteBeta/Result
license: citation-only
triage: anchor
---

# Coefficient-wise Wright log-concavity of normalized incomplete beta functions

## Verified locator

DOI: 10.1007/s10958-016-2958-z

Source: https://arxiv.org/abs/1509.05120v1

Pinned source: §3, Conjecture 1; definitions (1), (3), (4).
The integer-shift case is proved via Lemma 2 and Theorem 3.
Pinned source: §3, Conjecture 2, equation (6), and Corollary 1; equation (1) supplies the coefficients.
Journal publication: *Journal of Mathematical Sciences* 217(1) (2016), 91–107.

## Mathematical correspondence

Equation (1) writes the normalized incomplete beta function as

$$x^{-a}(1-x)^{-b}I_x(a,b)=\sum_{j\ge0}c_j(a,b)x^j,
\qquad c_j(a,b)=\frac{\Gamma(a+b+j)}{\Gamma(b)\Gamma(a+j+1)}.$$

Equations (3) and (4) define the Turanian and its coefficients:

$$\varphi_{a,b,\alpha,\beta}(x)
=I_x(a,b+\alpha)I_x(a,b+\beta)-I_x(a,b)I_x(a,b+\alpha+\beta)
=x^{2a}(1-x)^{2b+\alpha+\beta}\sum_{n\ge0}\varphi_nx^n,$$

$$\varphi_n=\sum_{k=0}^n\bigl[c_k(a,b+\alpha)c_{n-k}(a,b+\beta)
-c_k(a,b)c_{n-k}(a,b+\alpha+\beta)\bigr].$$

`coeff`, `phi` and `claim` in `D5/S3/Analytic/IncompleteBeta/Defs`
encode these coefficients and their strict positivity for all positive
real $a,b,\alpha,\beta$ and all natural $n$.
The coefficients do not depend on $x$; the source's restriction
$x\in(0,1)$ imposes no further coefficient condition.

`Moment.convolution_eq_betaMean` represents the coefficient convolution
as a beta moment. `Moment.W_hasDerivAt` supplies the telescoping derivative
of its symmetric kernel. `Comparison.betaMean_strictAntiOn` compares
symmetric beta means as the shape imbalance increases.
`Result.convolution_strictAnti_imbalance` applies this comparison at fixed
shape sum, and `Result.result` proves the full coefficient claim.

The source proves the restricted case $\alpha\in\mathbb N$,
$\beta\ge\alpha-1$ and states the general positive-shift case as Conjecture 1.
The bounded literature scope and its limits are given in
`Problems/karp-2016-incomplete-beta-coefficient-log-concavity.md`.
