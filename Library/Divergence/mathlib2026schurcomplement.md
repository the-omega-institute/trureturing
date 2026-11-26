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
  - D5/S3/Quantum/Divergence/PositiveReferenceReplacement
  - D5/S3/Quantum/Divergence/FibonacciQutritBlockDomination
  - D5/S3/Quantum/Divergence/FibonacciQutritSpectralTransport
  - D5/S3/Quantum/Divergence/FibonacciQutritBenchmark
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

## Positive reference replacement

In the same manuscript, §18, lines 1122–1136 give the compression
(F' = F+aτ), (C' = cτ), where (τ=C_P/(c-λ)). The exact trace-log
loss identity retains the Klein remainder (D(F'\Vert F)-a) and the
weighted logarithm remainder (a\operatorname{Re}\operatorname{Tr}
τ[\log F-\log(uC_P)]). Their nonnegativity recovers the manuscript
bound at trace one. The spectral-ceiling strong Klein inequality gives
the additional Hilbert–Schmidt term with ceiling (t=\operatorname{Re}\operatorname{Tr}F+a).

## Strict domination in qubit-plus-ray coordinates

For the block data of §20, lines 1259–1270, the strict comparison applies
when (0<λ<1/500), (c≥11/19), and (e≥c/3). The actual relocated pair
is (F'⊕0,C'⊕e). Its divergence gain keeps the coefficient (12/55)
with the full trace ratio (c/(c-λ)) and the quadratic Klein contribution.
The Lean statement takes the small eigenvalue and block coordinates
as hypotheses.

## Smallest-eigenvalue transport

Section 20, lines 1256–1275, gives the null-loss threshold and the strict
improvement after taking the smallest reference eigendirection as the ray.
The floor exclusion uses the general logarithm increment at λ = 1/500
directly, with 1 + 500e > 64 and log 2 ≥ 2/3. The coordinate change uses
[Mathlib's matrix spectral theorem](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Matrix/Spectrum.lean#L127-L146).
The matrix logarithm and trace carry the strict block estimate back to
the original divergence.

## Classical benchmark and normalized comparison

The same manuscript uses positive-class data processing in §18 and identifies
the three-ray classical preparation in §§21 and 23. The first two positive
likelihood classes share one ray, the last positive class has its own ray, and
the null class occupies the orthogonal remaining ray. Dividing the positive
reference by the sum of its weights gives a probability law on three classes.
The canonical finite preparation channel gives the output data processing
bound after cancellation of the common trace-one logarithmic shift.

The tangent bound at \(4/3\) for \(x\log x\) bounds the merge deficit by
\(b[(5/3)\log(5/4)-1/3]\). The rational cap uses the one-term logarithm
series upper bound at \(1/9\) from
[Mathlib, `Real.log_div_le_sum_range_add`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean#L344-L349).
