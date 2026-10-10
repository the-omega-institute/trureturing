---
bibkey: meiburg2025svd
authors: Alex Meiburg
year: 2025
title: Finite matrix singular value decomposition in Physlib
doi: null
url: https://github.com/leanprover-community/physlib/blob/6a09b2d1761a0d4430083045a247eb121d8da260/QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean
claim: Every finite complex square matrix has two unitary factors and diagonal entries equal to the square roots of the eigenvalues of its Gram matrix.
strata_touched:
  - D5/S3/Quantum/Foundation/FiniteTraceDistance
license: citation-only
triage: anchor
---

# Finite matrix singular value decomposition

## Verified locator

Source: https://github.com/leanprover-community/physlib/blob/6a09b2d1761a0d4430083045a247eb121d8da260/QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean

The retained declaration is `exists_svd_sqrt_eigenvalues` in
`D5/S3/Quantum/Foundation/FiniteTraceDistance.lean`. Its upstream source is
Physlib at the immutable revision in the URL. The Lean owner retains the
Alex Meiburg attribution and complete Apache-2.0 license. The statement uses
the canonical Hermitian proof of the Gram matrix and allows an empty index type.
