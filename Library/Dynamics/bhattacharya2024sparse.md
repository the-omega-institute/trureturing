---
bibkey: "bhattacharya2024sparse"
authors: "Bhaswar B. Bhattacharya; Rajarshi Mukherjee"
year: 2024
title: "Sparse Uniformity Testing"
doi: "10.1109/TIT.2024.3424679"
url: "https://arxiv.org/abs/2109.10481v2"
claim: "Sparse multinomial uniformity testing has sharp signal thresholds in specified sample-size regimes; the lower-bound proof uses a truncated second moment."
strata_touched: []
license: "citation-only"
triage: "anchor"
---

# Sparse Uniformity Testing

IEEE Transactions on Information Theory 70(9), 6371–6390 (2024).
The inspected author manuscript is arXiv:2109.10481v2.
Theorem 2.2, manuscript pages 4–5, assumes sparsity `s=d^(1-alpha)` with
fixed `1/2 < alpha < 1`. Its sharp large-sample signal threshold assumes
`n >> d log^3 d`; a separate impossibility statement assumes `n << d log d`.
Section 5.2.2, pages 20–23, proves the lower bound through truncated likelihood
moments, including Lemmas 5.8 and 5.9. The authors attribute the truncated
second-moment method to Ingster.

These are `literature-attested` tools and related sparse testing results.
The parity-kernel experiment chooses exactly one location, keeps it fixed
throughout the sample, and imposes compensating perturbations on every other
location in the same parity class. The paper's fixed sparsity exponent theorem
does not directly cover that constraint or the Markov direction experiment.
The exact likelihood inner products, uniform log-likelihood variance, and
common information threshold for pairs and paths are `repo-derived`
specializations; their derivation does not assert a new general truncation method.
