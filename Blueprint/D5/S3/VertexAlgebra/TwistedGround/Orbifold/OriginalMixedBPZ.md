# BPZ Transpose of the Original Mixed Coefficients

## Abstract

BPZ Transpose of the Original Mixed Coefficients

**Definition 1.1 (Lowering by the original stress state).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMixedBPZ.twistedL1`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMixedBPZ.twistedL1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For lattice data D with unit Gram determinant witnessed by hu, L1 is the complex-linear endomorphism given by mode two of the original fixed stress state on the negative twisted sector.

**Theorem 1.2 (Lowering on the underlying tensor).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMixedBPZ.twistedL1_val`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMixedBPZ.twistedL1_val` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every negative twisted state u, the underlying tensor of L1 u is the original tensor lowering operator T applied to the underlying tensor of u.

**Theorem 1.3 (Finite mixed BPZ transpose).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMixedBPZ.original_mixed_bpz_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMixedBPZ.original_mixed_bpz_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the Gram form is positive definite and D has rank 24. Take any integer n and original negative twisted states u and v of natural L0 weights H and K, respectively. For every a in the full fixed carrier, the source pairing of originalI at mode n on u and v against a equals the sum over 0 ≤ j < H − 1 of the actual bilinear form pairing v with the original right coefficient at mode 2H − n − j − 2 on L1 to the j-th power applied to u and a. Each term is divided by j!, and the sum is multiplied by (−1) to the H-th power. The range uses natural subtraction. To compare the coefficients, expand a into its fixed grades and transpose each term of the right coefficient. Its second lowering index ell ranges over 0 ≤ ell < K − 1. With t = 2H − n − j − 2 and s = n + 1 − ell − 2H + j, the doubled exponent −2(t + ell) − 2 is 2s, and the combined phase is (−1) to the (H + s)-th power.

**Theorem 1.4 (Algebraic mixed BPZ transpose).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMixedBPZ.original_mixed_bpz`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMixedBPZ.original_mixed_bpz` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same hypotheses, the source pairing equals (−1) to the H-th power times the algebraic sum over all natural j of the same divided right-coefficient terms. The terms with j ≥ H − 1 vanish by the lower energy bound on the actual twisted tensor.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMixedBPZ.original_mixed_bpz`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMixedBPZ.original_mixed_bpz_finite`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMixedBPZ.twistedL1`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalMixedBPZ.twistedL1_val`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Orbifold/OriginalOrbifoldTranslation](OriginalOrbifoldTranslation.md)
