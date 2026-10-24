---
bibkey: karpzhang2023pochhammer
authors: Dmitrii Karp and Yi Zhang
year: 2023
title: Log-concavity and log-convexity of series containing multiple Pochhammer symbols
doi: 10.1007/s13540-023-00238-0
url: https://arxiv.org/abs/2305.09029
claim: "Conjecture 5.2 asserts coefficient-wise log-concavity of both the reciprocal-Pochhammer series and the related gamma series for a log-concave coefficient sequence."
strata_touched:
  - D5/S3/Analytic/KarpZhangReciprocal/BirthDeath
  - D5/S3/Analytic/KarpZhangReciprocal/IntervalConvolution
  - D5/S3/Analytic/KarpZhangReciprocal/Result
  - D5/S3/Analytic/KarpZhangGamma/Series
  - D5/S3/Analytic/KarpZhangConjecture/Result
license: citation-only
triage: anchor
---

# Karp--Zhang reciprocal-Pochhammer coefficients

## Verified locator

DOI: 10.1007/s13540-023-00238-0

Source: https://arxiv.org/abs/2305.09029

Pinned source: [arXiv:2305.09029v3](https://arxiv.org/abs/2305.09029v3).
The locators below use the printed page numbers of that version.

## Conjecture 5.2, page 12

> Suppose that $\{y_k\}_{k=0}^{\infty}$ is a log-concave sequence. Then the functions $\mu\to\widetilde y(\mu;x)$ and $\mu\to\widehat y(\mu;x)$ are coefficient-wise log-concave on $\mu>0$.

Immediately before the conjecture, the source defines

$$
\widetilde y(\mu;x)=\sum_{k=0}^{\infty}y_k\frac{(2\mu)_k}{(\mu)_k k!}x^k,
\qquad
\widehat y(\mu;x)=\sum_{k=0}^{\infty}y_k\frac{\Gamma(\mu+k)}{\Gamma(2\mu+k)k!}x^k.
$$

## Definition 1.1, page 2

> Let $\{f_k\}_{k=0}^{\infty}$ be a non-negative nontrivial real sequence. We call $\{f_k\}_{k=0}^{\infty}$ log-concave (or Pólya frequency two – $PF_2$, or doubly positive) if $f_k^2\ge f_{k-1}f_{k+1}$ for each $k\in\mathbb N$, and $\{f_k\}_{k=0}^{\infty}$ is supported on an interval of integers (i.e., $f_N=0$ implies either $f_{N+i}=0$ for all $i\in\mathbb N_0$ or $f_{N-i}=0$ for $i=0,\ldots,N$).

The sequence convention includes nonnegativity, nontriviality, the adjacent
log-concavity inequalities and absence of internal zeros. A formal power
series assertion is a separate inequality in every natural degree, without
any convergence requirement.

## Mathematical correspondence

`Coeff.c` is exactly the coefficient $(2t)_n/((t)_n n!)$ of the reciprocal
series. `Coeff.lambda` is its adjacent-degree ratio before division by
$n+1$. `Coeff.eta`, `Coeff.psi` and `Coeff.chi` give the adjacent score
increment, score and negative logarithmic curvature as explicit rational
finite sums. `Coeff.coefficient_calculus` includes the degree-uniform
curvature estimate.

`BirthDeath.variance_bound` is a finite variance estimate used to control
the score variance in interval convolutions. `IntervalConvolution.shift_tail`
and finite Abel summation give `KarpZhangReciprocal.Result.reciprocal_half`.
Exponential smoothing, the one-sign-change reciprocal-gamma kernel and the
positive diagonal transformation give `KarpZhangGamma.Series.gamma_half`.
`KarpZhangConjecture.Result.claim` states the conjunction of the two
coefficient assertions using those exact finite coefficients, and
`KarpZhangConjecture.Result.result` proves it for the source's full sequence
and parameter range.
