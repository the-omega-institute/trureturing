---
bibkey: glocknerlucht2011weightedinversion
authors: Helge Glöckner and Lutz G. Lucht
year: 2011
title: Weighted inversion of general Dirichlet series
doi: null
url: https://arxiv.org/abs/1112.0749v2
claim: Absolute coefficient Dirichlet convolution forms a unital Banach algebra; the classical norm perturbation inversion principle gives the dominant-head inverse norm estimate by a Neumann series.
strata_touched:
  - D5/S3/Arith/DirichletInverseAbsBudget
license: citation-only
triage: anchor
---

# Absolute coefficient Dirichlet inversion

Glöckner and Lucht, *Weighted inversion of general Dirichlet series*,
arXiv:1112.0749v2 (29 September 2012; first submitted 4 December 2011).
Page 1 defines the absolute coefficient convolution Banach algebra and
proves its submultiplicative norm inequality. Page 3 identifies ordinary
Dirichlet series with the additive semigroup log N. Page 4, Theorem 2(a),
states the classical principle that an element within norm distance less
than one of the unit is invertible.

For a real arithmetic function b with a nonzero head c=b(1), write
b=c delta+h, with h(1)=0. If every finite absolute tail is bounded by T and
T<|c|, then h is absolutely summable with norm at most T. The Neumann
series for the inverse of delta+h/c gives the classical quantitative
consequence

$$
\|b^{-1}\|_1\le |c|^{-1}\sum_{j\ge0}(T/|c|)^j
 =\frac{1}{|c|-T}.
$$

The displayed quantitative consequence is elementary Banach algebra
inversion; it is not claimed to be a separately numbered theorem in the
paper. The Lean theorem uses an existing algebraic right inverse and
proves finite partial-sum absorption before deducing absolute summability,
so it assumes no global norm bound on that inverse. Its zero coefficient
is zero under the ArithmeticFunction convention.

The general Wiener criterion in the paper concerns the closure of the
Dirichlet-series image excluding zero, equivalently a uniform separation
from zero in its stated domain. It must not be replaced by mere pointwise
nonvanishing. No originality or Riemann-hypothesis assertion is attributed
to this norm estimate.

## Source

The 19-page arXiv v2 PDF has SHA-256
`6a5a2cd65ecd912d5e436d29a90705b67f00df3d6d3ee41e54d64e84097afe22`.
Remark 1 on page 2 traces the ordinary Dirichlet-series predecessor to
Hewitt and Williamson, *Note on absolutely convergent Dirichlet series*,
Proc. Amer. Math. Soc. 8 (1957), 863–868, DOI
10.1090/S0002-9939-1957-0090680-X. That predecessor is secondary attribution
here; its original theorem text has not been directly verified.

## Verified locator

Canonical source: https://arxiv.org/abs/1112.0749v2.
The v2 PDF, *Weighted inversion of general Dirichlet series*, defines the
absolute coefficient convolution Banach algebra and its submultiplicative
norm on page 1. Page 3 identifies ordinary Dirichlet series with the
additive semigroup log N. Theorem 2(a), page 4, gives invertibility for
norm distance from the unit less than one. The dominant-head inverse
absolute sum bound above is the elementary Neumann-series consequence
of that norm perturbation principle; no separately numbered theorem in
the paper is attributed to the displayed quantitative constant.
