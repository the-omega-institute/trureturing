---
bibkey: "mathlib2026schurcomplement"
authors: "The mathlib community"
year: 2026
title: "Schur complements of finite matrices"
doi: null
url: "https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean#L369-L373"
claim: "The block determinant factors through the Schur complement. Two Schur tests applied to the signed midpoint of a Löwner sandwich give a quantitative bound for pinching one coordinate."
strata_touched:
  - D5/S3/Quantum/Divergence/SingleCoordinateSchur
  - D5/S3/Quantum/Divergence/SingleCoordinatePinchingEntropy
license: "Apache-2.0 for mathlib source"
triage: "anchor"
---

# Schur complements for one-coordinate pinching

## Verified locator

- [Mathlib, `Matrix.det_fromBlocks₁₁`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/SchurComplement.lean#L369-L373)
- [Mathlib, `Matrix.PosDef.fromBlocks₁₁` and `Matrix.PosDef.fromBlocks₂₂`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Matrix/PosDef.lean#L637-L662)

## Formula in Fibonacci observation entropy

The research manuscript `thermal-operation-width-renewal/fibonacci-observation-entropy/proof.txt`,
SHA-256 `26f86387b9a072906e9fc0098c43cde0229029560440b2315be8d8817085e197`,
gives the shifted determinant ratio and resolvent estimate in §18, lines 1098–1117.
The range `[4/3, 7/3]` gives `d = 1/2`, `d²/u² = 9/64`, and the bound
`λc/(4(uc + s))` on the Schur term. Section 18 integrates the log determinant
deficit with the equal-trace identity. The generic coefficient is
`[u d²/(u² − d²)] λ [c/(c − λ)]` multiplying `log(c/λ)`. Section 20,
lines 1259–1275, uses the specialization `(18/55) λ log(c/λ)`
for the ladder's full-rank exclusion, with `c ≥ 3λ`.
