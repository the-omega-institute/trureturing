---
bibkey: mathlib2026finiteorthonormal
authors: Mathlib contributors
year: 2026
title: Finite orthonormal Parseval and Bessel inequalities
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/InnerProductSpace/PiL2.lean
claim: For a finite real orthonormal basis the sum of squared scalar products is the squared norm; for a finite orthonormal family it is at most the squared norm.
strata_touched:
  - D5/S3/Quantum/Contextuality/EightVertexQutritBound
license: citation-only
triage: anchor
---

# Finite orthonormal identities

## Verified locator

Source: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/InnerProductSpace/PiL2.lean

`OrthonormalBasis.sum_sq_inner_left`, at lines 515–518 of the pinned source,
states that the sum of the squared real inner products against a finite
orthonormal basis equals the squared norm.

`Orthonormal.sum_inner_products_le`, at line 437 of
https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/InnerProductSpace/Orthonormal.lean
bounds the sum of squared norms of inner products over a finite
orthonormal family by the squared norm. Over the real scalars this is the
sum of the squares. The two-vector specialization imposes unit norm on
both vectors and zero real inner product between them.

The statements are cited from the Apache-2.0 Mathlib project. This note
contains citation information only.
