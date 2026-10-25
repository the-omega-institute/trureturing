---
bibkey: karpvishnyakovazhang2025unimodality
authors: D. Karp, A. Vishnyakova, and Y. Zhang
year: 2025
title: Unimodality preservation by ratios of functional series and integral transforms
doi: 10.1007/s00025-025-02431-4
arxiv: 2408.01755
url: https://arxiv.org/abs/2408.01755
claim: "Conjecture 1 asserts unimodality of modified Bessel ratios and log-concavity for positive ordered orders."
strata_touched:
  - D5/S3/Analytic/BesselRatioLogConcavity/Result
license: citation-only
triage: anchor
---

# Modified Bessel ratios

## Verified locator

https://arxiv.org/abs/2408.01755

https://arxiv.org/abs/2408.01755v2

https://doi.org/10.1007/s00025-025-02431-4

The supplied text is arXiv:2408.01755v2. Conjecture 1 is on printed page 12.
Its statement, with line breaks joined, is:

> Conjecture 1. Suppose b ≥ 0, ν1 ≥ ν2 > −1 and 0 < a1 ≤ a2. Then the ratio x → Iν1(a1 x)/Iν2(a2 x) is unimodal on (0, ∞). Moreover, if ν1 ≥ ν2 > 0 it is log-concave.

The parameter $b$ does not occur in the ratio. The log-concavity clause is
encoded by concavity of the logarithm on the positive real half-line.

## Standard series and mathematical correspondence

Printed page 11 states verbatim:

> with a > 0, b ≥ 0, ν > −1, µ > 0 and Iν standing for the modified Bessel function of the first kind.

It then states:

> Using the standard power series expansion of Iν [28, p.217] we have

The displayed ratio expansion on that page uses the standard series

$$
I_\nu(z)=\sum_{k=0}^{\infty}
\frac{(z/2)^{2k+\nu}}{k!\Gamma(k+\nu+1)}.
$$

`Result.besselI` uses this real series with real powers for the positive
argument; `Result.claim` records exactly the positive-order log-concavity
clause, and `Result.result` refutes it. The order is $\nu=1/10$ at both
numerator and denominator, with scales $1,2$ and arguments $3/2,9/2,15/2$.
The series converges for every positive argument and every $\nu>-1$ in the
proof. The identity $\Gamma(\nu+1+k)=(\nu+1)_k\Gamma(\nu+1)$ reduces the
comparison to positive rational series. Sixty-term partial sums and a
geometric tail bound give a strict failure of midpoint log-concavity.
The unimodality clause is a separate question.
