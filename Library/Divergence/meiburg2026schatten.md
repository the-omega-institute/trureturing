---
bibkey: meiburg2026schatten
authors: Alex Meiburg
year: 2026
title: Arbitrary product Schatten Holder inequality in Physlib
doi: null
url: https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HermitianMat/Schatten.lean
claim: Product Schatten Holder for arbitrary finite square complex matrices and every positive triple of exponents satisfying the reciprocal identity.
strata_touched:
  - D5/S3/Quantum/Schatten
license: Apache-2.0
triage: anchor
---

# Product Schatten Holder supplier

The endpoint is `schattenNorm_mul_le` in Alex Meiburg's Physlib source.
Its norm is the real trace of the Gram spectral power, raised to the reciprocal
exponent. It ranges over arbitrary square complex matrices and every positive
triple r, p, q with 1/r = 1/p + 1/q, including quasi-norm exponents.
No commutation, Hermitian or positivity assumption is imposed on the factors.

The supporting proof uses `sum_rpow_singularValues_mul_le` and
`holder_step_for_singularValues` from the same revision's Majorization module.
Compound matrices, Cauchy-Binet, unitary spectral similarity and weak
log-majorization supply the matrix product estimate. The retained source
selects this live proof path and the Gram trace bridges; it omits unused
Hermitian power, Young and conjugation endpoints. Source identities and
proofs are preserved, with imports redirected to the selected local modules.
The copyright and Apache-2.0 notices are retained in each source; the full
license is `docs/reports/inoutbalance/physlib-LICENSE.txt`. The upstream root
has no NOTICE. No mathematical originality is claimed.

The source is pinned to Lean and Mathlib v4.33.0, matching this repository.
The transplant retires when the repository's pinned Mathlib supplies an
equivalent consumed declaration, which must then be applied directly.
The inequality is a supplier for the full finite-dimensional Hiai problem;
it does not prove the two required outer-power trace curvature results.

## Verified locator

https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HermitianMat/Schatten.lean
