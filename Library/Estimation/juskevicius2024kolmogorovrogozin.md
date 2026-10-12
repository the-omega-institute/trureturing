---
bibkey: juskevicius2024kolmogorovrogozin
authors: Tomas Juškevičius
year: 2024
title: The sharp form of the Kolmogorov–Rogozin inequality and a conjecture of Leader–Radcliffe
doi: 10.1112/blms.13132
url: https://arxiv.org/abs/2201.09861v1
claim: "Theorem 1.1 states the classical Kolmogorov–Rogozin bound for independent real sums; Theorem 1.2 gives an extremal-distribution comparison with specified individual concentration bounds."
strata_touched: []
license: citation-only
triage: anchor
---

# Concentration functions and the independence requirement

## Verified locator

DOI: <https://doi.org/10.1112/blms.13132>.
Crossref identifies the title, author and 2024 publication. The
publisher endpoint returns HTTP 403; Firecrawl is unavailable with
HTTP 402. The accessible [author preprint](https://arxiv.org/abs/2201.09861v1)
has ten PDF pages and an archive stamp of 24 January 2022.
Theorems 1.1–1.2 on PDF pp. 1–2 and the historical references were read.

The original Rogozin record is *An Estimate for Concentration
Functions*, *Theory of Probability and its Applications* 6 (1961),
94–97, DOI <https://doi.org/10.1137/1106009>. Its Crossref metadata
and MathNet's volume-6 issue-1 listing were verified; the Russian
article is listed as “On Evaluating the Concentration Functions,”
pp. 103–105, identifier `tvp4753`. The SIAM endpoint and individual
MathNet article page are access blocked. The classical mathematical
statement here is verified in the accessible Juškevičius preprint;
the original Rogozin proof has not been independently inspected.

## Classical concentration bound

The source's half-open convention is
$Q_h(X)=\sup_x\mathbb P(X\in(x,x+h])$ for $h>0$.
For independent real random variables $X_1,\ldots,X_n$ and
$S_n=\sum_iX_i$, Theorem 1.1 states

$$
Q_h(S_n)\le C\left[\sum_{i=1}^n(1-Q_h(X_i))\right]^{-1/2}
$$

with an absolute constant, when the displayed denominator is positive.
For concentration bounded above by one fixed number below one,
this gives the classical $n^{-1/2}$ order. Theorem 1.2 makes an
optimal comparison with independent mixtures of uniform arithmetic
progression laws; its assumptions still concern independent summands.

## Native conditional application boundary

In the [parity model](../../docs/develop/theory/PARITY_HIDDEN_ARROW_SPECTRAL_BOUNDARY.md),
fixing two rectangle margins makes the indicators dependent. More
importantly, the complete posterior group mean is a nonlinear
function of the varying count, with a common calibration denominator.
Neither the indicators nor that mean are an independent sum merely
because their maximum atom has inverse-square-root order.

A permitted application would need a proved independent-sum
representation or another conditional anti-concentration argument
preserving the same environment. The classical theorem and its sharp
refinement do not supply the native kernel identification, response
derivative or moving-center error budget. No unrelated conjecture
from this source is a formalization target here.
