---
bibkey: vanrooyenwilliamson2014genericfeatures
authors: Brendan van Rooyen; Robert C. Williamson
year: 2014
title: "Le Cam meets LeCun: Deficiency and Generic Feature Learning"
doi: 10.48550/arXiv.1402.4884
url: https://arxiv.org/abs/1402.4884v2
claim: For a fixed finite data marginal, universal signed-loss feature quality is equivalent to one randomized reconstruction rule with at most half the normalized quality bound as average mismatch probability.
strata_touched: []
license: citation-only
triage: anchor
---

# Generic features and reconstruction

The primary source is [arXiv:1402.4884v2](https://arxiv.org/pdf/1402.4884v2),
Definition 3 and Theorem 3. Section 2 specifies the finite decision setting and
signed bounded losses. Section 7.5 uses full l1 variational distance. This note
cites the source without redistributing its text or PDF.

Fix a probability mass q on a finite data type and a stochastic encoder to a
finite feature type. Universal quality compares optimal feature and data Bayes
risks for every finite decision problem whose data marginal is q. The loss is
real and signed, and the comparison is normalized by its maximum absolute value.
Theorem 3 identifies this condition with the existence of one randomized decoder
whose q-weighted mismatch probability is at most epsilon divided by two.

The factor two is witnessed directly by the signed reconstruction loss: minus
one for a correct reconstruction and plus one for a mismatch. The data risk is
minus one and the feature risk is twice its minimum mismatch probability minus
one. The source appendix has displayed indicator and normalization inconsistencies;
the stated bound is interpreted through this signed-loss identity. No positivity
of individual masses or deterministic-decoder condition is imposed.

The formal result uses the real infimum over all finite stochastic decisions and
proves attainment by observationwise finite minimization. Hypothesis, action,
data and feature types have independent universes. The statement concerns finite
experiments and supplies no measurable infinite-space extension.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.1402.4884
- Source: https://arxiv.org/abs/1402.4884v2
