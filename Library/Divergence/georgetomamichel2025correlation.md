---
bibkey: georgetomamichel2025correlation
authors: Ian George and Marco Tomamichel
year: 2025
title: A Unified Approach to Quantum Contraction and Correlation Coefficients
doi: 10.48550/arXiv.2505.15281
url: https://arxiv.org/abs/2505.15281v3
claim: "Section VII asks whether a finite-dimensional quantum state can have µ_AM < 1 and µ_GM = 1."
strata_touched:
  - D5/S3/Quantum/GeorgeTomamichelMaximalCorrelation
license: citation-only
triage: anchor
---

# Quantum contraction and correlation coefficients

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2505.15281

Source: https://arxiv.org/abs/2505.15281v3

Version 3, Section VII, page 66 asks: “Does there exist a quantum state ρ_AB such that µ_AM(A : B)_ρ < 1 and µ_GM(A : B)_ρ = 1?”

Definition 24, equation (54), page 19 specifies: “where the maximization is over X ∈ Herm(A), Y ∈ Herm(B).” It maximizes the absolute joint trace over Hermitian
local matrices with zero marginal expectation and unit quadratic norm. Section II,
equation (15), supplies the arithmetic and geometric mean operators. The arithmetic
operator is (σX + Xσ)/2; the geometric operator is σ^(1/2) X σ^(1/2).

The repository theorem proves that a positive semidefinite trace-one matrix on
arbitrary finite index types has µ_AM = 1 whenever µ_GM = 1. Support compression
includes singular marginals. Empty feasible sets have supremum zero in ℝ.

The source's second question concerns the asymptotic arithmetic coefficient of
tensor powers. Its Theorem 51 relates an affirmative answer to an affirmative
answer to the first question. That implication is cited from the source; the Lean
settlement proves only the first endpoint theorem. Quantitative bounds away from
one and tensorization of the arithmetic coefficient remain outside its statement.

The numerical experiment is in the-omega-institute/trureturing-experiments,
commit ad685151, docs/reports/george-tomamichel-2025-am-gm-maximal-correlation/check.py,
SHA256 d56c3a64912a3cec02640ea8d58479f5227bdfb19f9722e7bdcfa513ee71f028.
The preregistration records exit code 0 and output SHA256
ef7da5adbd7cfe7a75a02c54ef0b08b8c98ec56cb8d54dcb10e9e4dd2b8a5452.
These are finite numerical checks, separate from the proof. Literature-search
completeness is ASSUMED-UNVERIFIED, as recorded in issue #19997.
