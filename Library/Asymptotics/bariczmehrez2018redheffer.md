---
bibkey: bariczmehrez2018redheffer
authors: Á. Baricz and K. Mehrez
year: 2018
title: Redheffer type bounds for Bessel and modified Bessel functions of the first kind
doi: 10.1007/s00010-018-0545-8
url: https://arxiv.org/abs/1701.08446
claim: "Conjecture 1 in section 3 asserts the lower bound in inequality (3.2) for the normalized Bessel ratio before its first positive zero."
strata_touched:
  - D5/S3/Analytic/BesselRedheffer/Defs
  - D5/S3/Analytic/BesselRedheffer/Result
license: citation-only
triage: anchor
---

# The normalized Bessel Redheffer lower bound

## Verified locator

DOI: 10.1007/s00010-018-0545-8

Source: https://arxiv.org/abs/1701.08446

Pinned version: https://arxiv.org/abs/1701.08446v1, §3, Conjecture 1,
inequality (3.2). Journal publication: *Aequationes Mathematicae*
92 (2018), 425–439.

## Mathematical correspondence

The normalized function is

$$\mathcal J_\nu(x)=\sum_{k\ge0}
\frac{(-x^2/4)^k}{k!(\nu+1)_k},\qquad \nu>-1.$$

Here $(\nu+1)_k$ is the ascending Pochhammer symbol and $j_{\nu,1}$
is the first positive zero. For $|x|<j_{\nu,1}$ the proposed lower bound is

$$\left(\frac{j_{\nu,1}^2}{j_{\nu,1}^2-x^2}\right)^{\vartheta_\nu}
\le\frac{\mathcal J_{\nu+1}(x)}{\mathcal J_\nu(x)},
\qquad \vartheta_\nu=\frac{j_{\nu,1}^2}{4(\nu+1)(\nu+2)}.$$

The source treats the left-hand inequality as the conjecture. The
right-hand inequality in (3.2), with exponent $\eta_\nu=1$, is a known
result. The source proves the conjectured lower bound for $\nu=-1/2$.

`Defs.nbessel` is exactly the displayed series; `Defs.firstZero` is the
infimum of its positive zeros; `Defs.claim` is the universally quantified
lower bound with the real power. `Result.result` refutes this claim.
`Result.failure_family` supplies a strict counterexample for every real
$\nu\ge30$. `Expansion.failure_of_energy_bound`, together with the
first-zero estimates, gives failure at every sufficiently small positive
argument in this range. First-zero existence and attainment are proved
here for $\nu\ge30$; no such formal result for the remaining orders is
asserted by these modules.

The bounded literature scope and its limitations are stated in
`Problems/baricz-mehrez-2018-bessel-redheffer-lower-bound.md`.
Exhaustive literature completeness and priority are ASSUMED-UNVERIFIED.
