# de Branges-Rovnyak Defect Kernel

## Abstract

Scalar multiplier defects form Hermitian de Branges-Rovnyak kernels whose Gram matrices are exactly finite Pick matrices.

**Definition 1.1 (Scalar defect kernel).**

Lean statement: `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.deBrangesRovnyakKernel`

*Formalization.* `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.deBrangesRovnyakKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The original kernel is multiplied by one minus the multiplier outer product.

**Theorem 1.2 (Defect Gram equals Pick matrix).**

Lean statement: `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.deBrangesRovnyakKernel_gramMatrix`

*Formalization.* `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.deBrangesRovnyakKernel_gramMatrix` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sampling the defect kernel produces exactly the generic finite Pick matrix.

**Theorem 1.3 (Positivity equals kernel contractivity).**

Lean statement: `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.isPositiveKernel_deBrangesRovnyak_iff`

*Formalization.* `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.isPositiveKernel_deBrangesRovnyak_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The multiplier is kernel-contractive exactly when its de Branges-Rovnyak defect kernel is positive.

**Theorem 1.4 (Zero multiplier preserves the kernel).**

Lean statement: `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.deBrangesRovnyakKernel_zero`

*Formalization.* `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.deBrangesRovnyakKernel_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero scalar multiplier leaves every kernel entry unchanged.

**Theorem 1.5 (Unit multiplier annihilates the defect).**

Lean statement: `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.deBrangesRovnyakKernel_one`

*Formalization.* `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.deBrangesRovnyakKernel_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The constant multiplier one makes the complete defect kernel vanish.

**Theorem 1.6 (Positive kernels remain positive at zero multiplier).**

Lean statement: `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.deBrangesRovnyakKernel_zero_positive`

*Formalization.* `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.deBrangesRovnyakKernel_zero_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero-multiplier defect inherits positivity from the original kernel.

**Theorem 1.7 (Unit-multiplier defect is positive).**

Lean statement: `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.deBrangesRovnyakKernel_one_positive`

*Formalization.* `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.deBrangesRovnyakKernel_one_positive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero defect kernel is positive semidefinite.

**Theorem 1.8 (Unit-multiplier Pick matrix vanishes).**

Lean statement: `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.finitePickMatrix_one`

*Formalization.* `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.finitePickMatrix_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite Pick matrix of the constant unit multiplier is zero.

## References

- Truth anchor: `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.deBrangesRovnyakKernel`
- Truth anchor: `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.deBrangesRovnyakKernel_gramMatrix`
- Truth anchor: `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.isPositiveKernel_deBrangesRovnyak_iff`
- Truth anchor: `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.deBrangesRovnyakKernel_zero`
- Truth anchor: `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.deBrangesRovnyakKernel_one`
- Truth anchor: `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.deBrangesRovnyakKernel_zero_positive`
- Truth anchor: `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.deBrangesRovnyakKernel_one_positive`
- Truth anchor: `D5/S3/Weil/Pick/DeBrangesRovnyakKernel.finitePickMatrix_one`
- Dependency: [D5/S3/Weil/Pick/FinitePickPositivity](FinitePickPositivity.md)
