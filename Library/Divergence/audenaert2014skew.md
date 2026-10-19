---
bibkey: audenaert2014skew
authors: Koenraad M. R. Audenaert
year: 2014
title: Quantum Skew Divergence
doi: 10.1063/1.4901039
url: https://arxiv.org/abs/1304.5935v2
claim: "Theorem 14 bounds Holevo information by mixing entropy times the largest pairwise trace distance; the equiprobable binary case gives J₂(ρ,σ) ≤ ‖ρ−σ‖tr/2."
strata_touched:
  - D5/S3/Divergence/AudenaertBinaryHolevoBound
license: citation-only
triage: anchor
---

# Quantum Skew Divergence

## Verified locator

DOI: https://doi.org/10.1063/1.4901039

Source: https://arxiv.org/abs/1304.5935v2

Journal of Mathematical Physics 55, 112202. The arXiv metadata gives the journal
reference and DOI above. Theorem 14 states χ(E) ≤ H(p)t, where t is the largest
pairwise trace distance. Taking two equally weighted states and base-two
logarithms gives

J₂(ρ,σ) = S₂((ρ+σ)/2) − (S₂(ρ)+S₂(σ))/2 ≤ ‖ρ−σ‖tr/2.

The supporting Lean theorem proves this binary specialization in every finite
dimension, including singular states. Its analytic route uses the resolvent
representation of the matrix logarithm, the differential estimate underlying
Theorem 8, integration to the skew-divergence estimate of Theorem 9, and a
trace-preserving regularization with continuity of x log x at zero.
