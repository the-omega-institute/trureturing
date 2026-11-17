# The width-two residual Gram bound

## Abstract

A strict native width-two scalar Gram forces twice the right input dimension to fit in the output dimension.

For a,b,c,d : ℕ with a < b, let M : Fin 2 → Matrix (Fin a) (Fin b) ℂ and N : Fin 2 → Matrix (Fin d) (Fin c) ℂ. If M is complex-linearly independent, (∑ r, kronecker (M r) (N r))ᴴ * (∑ r, kronecker (M r) (N r)) = 1, and ∑ r, (M r)ᴴ * M r = 1, then 2*c ≤ d. All zero-dimensional factors remain in scope.

**Theorem 1.1 (The width-two right dimension bound).**

Lean statement: `D5/S3/Quantum/Algebra/NativeTwoKernelBound.right_dimension_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/NativeTwoKernelBound.right_dimension_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact binders are {a b c d : ℕ}, hab : a < b, M : Fin 2 → Matrix (Fin a) (Fin b) ℂ, N : Fin 2 → Matrix (Fin d) (Fin c) ℂ, hM : LinearIndependent ℂ M, hF : (∑ r, Matrix.kronecker (M r) (N r))ᴴ * (∑ r, Matrix.kronecker (M r) (N r)) = 1, and hMG : ∑ r, (M r)ᴴ * M r = 1; the conclusion is 2 * c ≤ d.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/NativeTwoKernelBound.right_dimension_bound`
- Dependency: [D5/S3/Quantum/TensorNetworks/BridgeGraph/NativeRectangularBound](../TensorNetworks/BridgeGraph/NativeRectangularBound.md)
