# Exact diagonal BKM optimum

## Abstract

The sharp full-fibre quotient with the diagonal Umegaki Hessian.

**Theorem 1.1 (The actual logarithmic derivative in the quotient).**

Lean statement: `D5/S3/Quantum/Recovery/PetzDiagonalBKMOptimum.diagonal_bkm_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/PetzDiagonalBKMOptimum.diagonal_bkm_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take a diagonal base ρ with positive entries β in the given retained and flag coordinates. The Hessian is Re Tr[Z D log(ρ)[Z]]. In the resolvent integral each entry contributes its squared modulus times the reciprocal logarithmic mean of the two diagonal entries. The coincident-value branch has coefficient 1/β.

The logarithmic means are positive and bounded by the arithmetic means. Form m as the product over the sum of the two within-flag logarithmic means. For C,f,g > 0 and the same two nonnegative margins with positive sum, the quotient with this Hessian attains 16m+(f+g)²/C on the full Hermitian zero-marginal fibre.

The unique tangent has real within-flag coherences −4Cm/(f+g) and 4Cm/(f+g), with all other entries zero.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/PetzDiagonalBKMOptimum.diagonal_bkm_maximum`
- Dependency: [D5/S3/Divergence/MeanKernels/LogarithmicMeanSandwich](../../Divergence/MeanKernels/LogarithmicMeanSandwich.md)
- Dependency: [D5/S3/Quantum/Divergence/UmegakiRareFlagBKM](../Divergence/UmegakiRareFlagBKM.md)
- Dependency: [D5/S3/Quantum/Recovery/PetzWeightedHessianOptimum](PetzWeightedHessianOptimum.md)
