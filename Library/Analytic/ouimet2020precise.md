---
bibkey: ouimet2020precise
authors: Frédéric Ouimet
year: 2020
title: A precise local limit theorem for the multinomial distribution and some applications
doi: 10.1016/j.jspi.2021.03.006
url: https://arxiv.org/abs/2001.08512v4
claim: Theorem 2.1 and its proof supply classical local Gaussian estimates; equations (3.12)-(3.13) give the binomial power normalizations for powers two and three.
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

Equations (3.12)–(3.13) supply the complete binomial power normalizations
for l=2 and l=3. They are not cited here as a statement covering every
positive integer power. The arbitrary-power weighted complete-sum supplier
is D5/L/Analytic/abel2013binomial, with l=1 handled exactly.

The all-power tail and Gaussian lattice-sum statements in
BinomialLocalGaussian and the uniform upper bound in BinomialUniformMaximum
are repository formulations of classical analytic ingredients. The exact
finite-sum formulations and their use in a truncated-ratio maximum are
not attributed as verbatim statements of this source. No new discovery is
claimed for the local Gaussian estimate.

## Verified locator

- https://arxiv.org/abs/2001.08512v4
- https://arxiv.org/pdf/2001.08512v4, Theorem 2.1 and proof,
  equations (3.12)–(3.13).
- DOI: 10.1016/j.jspi.2021.03.006

The source-body findings are supplied by the bounded audit in #9357.
The versioned abstract was consulted on 2026-09-21 UTC to verify author,
title, DOI and version identity. The bibkey year is the original preprint
year, 2020; v4 and the journal DOI date from 2021. The preprint locators do
not assert inspection of the journal version's numbering.
