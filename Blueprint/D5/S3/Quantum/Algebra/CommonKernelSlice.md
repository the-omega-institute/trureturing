# The common-kernel slice

## Abstract

A finite adjoint-symmetric matrix family has a real combination with exactly its common kernel.

For every k, a, and b in ℕ, let X : Fin k → Matrix (Fin a) (Fin b) ℂ. If (X i)ᴴ * X j = (X j)ᴴ * X i for all i,j, a real coefficient function t : Fin k → ℝ has a complex linear combination whose kernel is exactly the infimum of the kernels of all X i. The statement includes empty families and zero dimensions.

**Theorem 1.1 (A real combination realizes the common kernel).**

Lean statement: `D5/S3/Quantum/Algebra/CommonKernelSlice.common_kernel_slice`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CommonKernelSlice.common_kernel_slice` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all k a b : ℕ, every X : Fin k → Matrix (Fin a) (Fin b) ℂ, and hcomm : ∀ i j, (X i)ᴴ * X j = (X j)ᴴ * X i, there exists t : Fin k → ℝ such that ker ((∑ i, (t i : ℂ) • X i).mulVecLin) = ⨅ i, ker ((X i).mulVecLin).

**Theorem 1.2 (The zero-common-kernel consequence).**

Lean statement: `D5/S3/Quantum/Algebra/CommonKernelSlice.common_kernel_slice_injective_of_common_kernel_bot`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CommonKernelSlice.common_kernel_slice_injective_of_common_kernel_bot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For all k a b : ℕ, every X and hcomm as above, and hcommon : (⨅ i, ker ((X i).mulVecLin)) = ⊥, there exists t : Fin k → ℝ such that (∑ i, (t i : ℂ) • X i).mulVecLin is injective and b ≤ a.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/CommonKernelSlice.common_kernel_slice`
- Truth anchor: `D5/S3/Quantum/Algebra/CommonKernelSlice.common_kernel_slice_injective_of_common_kernel_bot`
- Dependency: [D5/S3/Quantum/Algebra/CommonCoefficientPlane](CommonCoefficientPlane.md)
