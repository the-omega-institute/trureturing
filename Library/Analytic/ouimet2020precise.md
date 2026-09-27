---
bibkey: ouimet2020precise
authors: Frédéric Ouimet
year: 2020
title: A precise local limit theorem for the multinomial distribution and some applications
doi: 10.1016/j.jspi.2021.03.006
url: https://arxiv.org/abs/2001.08512v4
claim: Theorem 2.1 and its proof supply classical local Gaussian estimates; PDF page 5, equations (3.6)-(3.7), gives the binomial power normalizations for powers two and three.
strata_touched:
  - D5/S3/AnalyticClosure/BinomialLocalGaussian
  - D5/S3/AnalyticClosure/BinomialPowerNormalization
  - D5/S3/AnalyticClosure/BinomialUniformMaximum
  - D5/S3/AnalyticClosure/BinomialPoweredRatioMaximum
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Analytic/ouimet2020precise -->
# Classical local Gaussian estimates

The mathematical locator is arXiv:2001.08512v4, Theorem 2.1 and its proof,
specialized to the binomial distribution. The local estimate controls the
relative error on growing central windows. The repository uses the window
|k-np|<=n^(7/12) for every fixed 0<p<1. It combines scalar Stirling and a
logarithmic remainder bound in that specialization.

Equations (3.6)–(3.7) on PDF page 5 supply the complete binomial power
normalizations for l=2 and l=3. They are not cited here as a statement covering every
positive integer power. The arbitrary-power weighted complete-sum supplier
is D5/L/Analytic/abel2013binomial, Theorem 3.1 for l>=2, with l=1 handled exactly.

Rendering note: the HTML rendering of arXiv:2001.08512v4 numbers these
square/cube displays (3.12)–(3.13). In the v4 PDF, (3.12)–(3.13) on pages
6–7 concern the Bernstein tail bound and likelihood decomposition;
the power-sum PDF locators are (3.6)–(3.7) on page 5.

The all-power tail and Gaussian lattice-sum statements in
BinomialLocalGaussian and the uniform upper bound in BinomialUniformMaximum
are repository formulations of classical analytic ingredients. The exact
finite-sum formulations and their use in a truncated-ratio maximum are
not attributed as verbatim statements of this source. No new discovery is
claimed for the local Gaussian estimate.

The entropy expression used by BinomialLocalGaussian and
BinomialMaximumLocalization is the already-frozen
D5/S0/Diagonal/MarginBound.bernoulliKL, reused directly without a new
definition or alias.

## Verified locator

- https://arxiv.org/abs/2001.08512v4
- https://arxiv.org/pdf/2001.08512v4, Theorem 2.1 and proof,
  and page 5, equations (3.6)–(3.7).
- https://arxiv.org/html/2001.08512v4, square/cube displays (3.12)–(3.13).
- DOI: 10.1016/j.jspi.2021.03.006

The source-body findings are supplied by the bounded audit in #9357.
The versioned abstract was consulted on 2026-09-21 UTC to verify author,
title, DOI and version identity. The bibkey year is the original preprint
year, 2020; v4 and the journal DOI date from 2021. The preprint locators do
not assert inspection of the journal version's numbering.
