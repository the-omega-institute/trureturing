# Finite Pick Positivity

## Abstract

Positive Hermitian kernels and contractive scalar multipliers are characterized by finite Pick matrix positivity.

**Definition 1.1 (Positive Hermitian kernel).**

Lean statement: `D5/S3/Weil/Pick/FinitePickPositivity.IsPositiveKernel`

*Formalization.* `D5/S3/Weil/Pick/FinitePickPositivity.IsPositiveKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every finite sampled Gram matrix of the Hermitian kernel is positive semidefinite.

**Definition 1.2 (Finite scalar Pick matrix).**

Lean statement: `D5/S3/Weil/Pick/FinitePickPositivity.finitePickMatrix`

*Formalization.* `D5/S3/Weil/Pick/FinitePickPositivity.finitePickMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The kernel Gram entry is multiplied by one minus the proposed multiplier outer product.

**Definition 1.3 (Kernel-contractive multiplier).**

Lean statement: `D5/S3/Weil/Pick/FinitePickPositivity.IsKernelContractiveMultiplier`

*Formalization.* `D5/S3/Weil/Pick/FinitePickPositivity.IsKernelContractiveMultiplier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every finite Pick matrix of the scalar function is positive semidefinite.

**Theorem 1.4 (Pick matrices are Hermitian).**

Lean statement: `D5/S3/Weil/Pick/FinitePickPositivity.finitePickMatrix_isHermitian`

*Formalization.* `D5/S3/Weil/Pick/FinitePickPositivity.finitePickMatrix_isHermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Conjugate symmetry of the kernel and multiplier factor makes every finite Pick matrix Hermitian.

**Theorem 1.5 (Zero multiplier recovers the Gram matrix).**

Lean statement: `D5/S3/Weil/Pick/FinitePickPositivity.finitePickMatrix_zero`

*Formalization.* `D5/S3/Weil/Pick/FinitePickPositivity.finitePickMatrix_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Pick matrix of the zero function is exactly the original sampled kernel matrix.

**Theorem 1.6 (Zero is contractive for positive kernels).**

Lean statement: `D5/S3/Weil/Pick/FinitePickPositivity.zero_isKernelContractiveMultiplier`

*Formalization.* `D5/S3/Weil/Pick/FinitePickPositivity.zero_isKernelContractiveMultiplier` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive-kernel Gram matrices certify the zero multiplier.

**Definition 1.7 (Zero Hermitian kernel).**

Lean statement: `D5/S3/Weil/Pick/FinitePickPositivity.zeroHermitianKernel`

*Formalization.* `D5/S3/Weil/Pick/FinitePickPositivity.zeroHermitianKernel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The identically zero kernel provides the additive neutral positive kernel.

**Theorem 1.8 (The zero kernel is positive).**

Lean statement: `D5/S3/Weil/Pick/FinitePickPositivity.zeroHermitianKernel_isPositive`

*Formalization.* `D5/S3/Weil/Pick/FinitePickPositivity.zeroHermitianKernel_isPositive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All finite Gram matrices of the zero kernel are zero positive-semidefinite matrices.

**Theorem 1.9 (Every multiplier contracts the zero kernel).**

Lean statement: `D5/S3/Weil/Pick/FinitePickPositivity.every_multiplier_contracts_zeroKernel`

*Formalization.* `D5/S3/Weil/Pick/FinitePickPositivity.every_multiplier_contracts_zeroKernel` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite Pick matrix over the zero kernel vanishes.

## References

- Truth anchor: `D5/S3/Weil/Pick/FinitePickPositivity.IsPositiveKernel`
- Truth anchor: `D5/S3/Weil/Pick/FinitePickPositivity.finitePickMatrix`
- Truth anchor: `D5/S3/Weil/Pick/FinitePickPositivity.IsKernelContractiveMultiplier`
- Truth anchor: `D5/S3/Weil/Pick/FinitePickPositivity.finitePickMatrix_isHermitian`
- Truth anchor: `D5/S3/Weil/Pick/FinitePickPositivity.finitePickMatrix_zero`
- Truth anchor: `D5/S3/Weil/Pick/FinitePickPositivity.zero_isKernelContractiveMultiplier`
- Truth anchor: `D5/S3/Weil/Pick/FinitePickPositivity.zeroHermitianKernel`
- Truth anchor: `D5/S3/Weil/Pick/FinitePickPositivity.zeroHermitianKernel_isPositive`
- Truth anchor: `D5/S3/Weil/Pick/FinitePickPositivity.every_multiplier_contracts_zeroKernel`
- Dependency: [D5/S3/Weil/Pick/HermitianKernelNegativeSquares](HermitianKernelNegativeSquares.md)
