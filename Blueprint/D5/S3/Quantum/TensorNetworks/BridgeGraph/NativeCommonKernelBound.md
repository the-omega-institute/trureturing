# The original Gram common-kernel bound

## Abstract

A common nonzero coefficient kernel vector forces three times the right input dimension to fit in twice its output dimension.

For a,b,c,d : ℕ, X : Fin 3 → Matrix (Fin a) (Fin b) ℂ, and Y : Fin 3 → Matrix (Fin d) (Fin c) ℂ, assume a < b, (∑ r, kronecker (X r) (Y r))ᴴ * (∑ r, kronecker (X r) (Y r)) = 1, and ∑ r, (X r)ᴴ * X r = 1. If v : Fin 3 → ℂ is nonzero and every Hermitian T with compression X T = 0 satisfies T *ᵥ v = 0, then 3*c ≤ 2*d.

**Theorem 1.1 (The common-kernel dimension bound).**

Lean statement: `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeCommonKernelBound.original_gram_common_kernel_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeCommonKernelBound.original_gram_common_kernel_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact telescope is {a b c d : ℕ}, X, Y, hab : a < b, hF : (∑ r, Matrix.kronecker (X r) (Y r))ᴴ * (∑ r, Matrix.kronecker (X r) (Y r)) = 1, hXGram : ∑ r, (X r)ᴴ * X r = 1, v : Fin 3 → ℂ, hv : v ≠ 0, and hkernel : ∀ T : Matrix (Fin 3) (Fin 3) ℂ, T.IsHermitian → compression X T = 0 → T *ᵥ v = 0. The conclusion is 3 * c ≤ 2 * d.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeCommonKernelBound.original_gram_common_kernel_bound`
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeRectangularBound](NativeRectangularBound.md)
