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
  - D5/S3/Quantum/Divergence/UmegakiBKMPath
  - D5/S3/Quantum/Divergence/UniversalCommonCenter
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

The associated finite semidefinite supplier
`UniversalCommonCenter.exists_common_center_of_posDef_trace_inf_le` concerns
arbitrary complex A and Hermitian B on r times a, for finite r and nonempty
finite a. If every positive-definite weight Z bounds the scalar infimum of
Re Tr(Z (A-X tensor I)(A-X tensor I) adjoint) by Re Tr(Z B), then one general
complex center X makes B-(A-X tensor I)(A-X tensor I) adjoint positive
semidefinite. Empty reference carriers are included; B is not assumed positive.
The proof establishes the actual quadratic epigraph's convexity and closedness,
then uses Hermitian-matrix PSD self-duality and strict separation.

This common-center inference is derived from the supplied repository-first
assessment, not attributed to Audenaert's article. It is step 3 support for the
same Umegaki complete-versus-conditional contraction problem served by the BKM
path identity. The weighted quotient-duality bridge, amplified common scalarizer
and final coefficient comparison remain open. No originality or solution of
that original problem is asserted.
