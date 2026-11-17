# The native three-term rectangular bound

## Abstract

The complete original native width-three scalar-Gram theorem: a < b forces 3c <= 2d.

For arbitrary a,b,c,d : ℕ, M : Fin 3 → Matrix (Fin a) (Fin b) ℂ, N : Fin 3 → Matrix (Fin d) (Fin c) ℂ, lambda : ℝ, hlambda : 0 < lambda, hab : a < b, and (∑ r, kronecker (M r) (N r))ᴴ * (∑ r, kronecker (M r) (N r)) = (lambda : ℂ) • (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ), the exact conclusion is 3*c ≤ 2*d. No independence or extra dimension premise is added; dependent original factors and all zero dimensions remain included.

First set F0 = (Real.sqrt lambda)⁻¹ • F, where F is the original tensor sum; then F0ᴴ * F0 = 1. Minimal-width reduction and exact whitening preserve F0, with whitening using an inverse transpose on the right factors. Widths zero and one follow from the injective stack dimension; width two uses the residual compression bound; width three uses the common-vector or neutral-plane geometry, with the vector branch invoking the original Gram common-kernel bound and the plane branch giving 2*c ≤ d.

**Theorem 1.1 (The complete original theorem).**

Lean statement: `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeThreeRectangularBound.native_three_rectangular_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeThreeRectangularBound.native_three_rectangular_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem retains all four natural dimensions, both arbitrary width-three matrix families, positive lambda, strict a < b, and the exact scalar Gram identity, and concludes 3 * c ≤ 2 * d.

## References

- Truth anchor: `D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeThreeRectangularBound.native_three_rectangular_bound`
- Dependency: [D5/S3/Quantum/Algebra/NativeThreeKernelGeometry](../../Algebra/NativeThreeKernelGeometry.md)
- Dependency: [D5/S3/Quantum/Algebra/NativeTwoKernelBound](../../Algebra/NativeTwoKernelBound.md)
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeCommonKernelBound](NativeCommonKernelBound.md)
