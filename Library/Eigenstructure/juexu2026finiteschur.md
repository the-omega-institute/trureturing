---
bibkey: juexu2026finiteschur
authors: Jue Xu and LeanPool contributors
year: 2026
title: Finite rectangular Schur operator bound
doi: null
url: https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/LowWeightPauliDynamics/SchurCore.lean
claim: Absolute row and column sums bounded by R and C bound the Euclidean operator norm by sqrt(R*C), including empty index types.
strata_touched:
  - D5/S3/Combinatorics/Apollonian/CutoffSpectralBounds
license: Apache-2.0
triage: anchor
---

# Finite rectangular Schur bound

## Verified locator

https://github.com/LeanPool/lean-pool/blob/bbc67ff1e3ac4fc6a969daf42985a0d8f988d0b8/LeanPool/LowWeightPauliDynamics/SchurCore.lean

The original project is Jue Xu's https://github.com/Jue-Xu/Lean4LPD.
The source SHA-256 is `7327b00d289548d89d1018bda0d38716152a01f2838837251e3bc419c31f426f`.
The minimal port retains the rowwise weighted Cauchy--Schwarz step, its
sum-of-squares consequence, the continuous action bound and the final L2
operator bound. Private helpers are consumed by the public norm theorem.
Unused action and equal-bound corollaries are omitted. The namespace is adapted.
The current consumer is the birth-oriented late adjacency of the actual
inner-face Apollonian stages.

The Apache-2.0 text and the applicable LeanPool NOTICE are retained in
`docs/reports/brooks-suppliers/daviskahan-LICENSE.txt` and
`docs/reports/brooks-suppliers/daviskahan-NOTICE.txt`.
The source header retains Jue Xu's copyright and authorship.
Replace the port when the pinned Mathlib supplies the same rectangular RCLike
row/column-sum operator bound with empty index types.
