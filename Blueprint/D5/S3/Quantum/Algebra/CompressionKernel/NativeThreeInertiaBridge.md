# Hermitian compression inertia at width three

## Abstract

A nonzero Hermitian compression-kernel form at strict width-three threshold has one positive, one negative, and one zero eigenvalue.

Let a,b : ℕ with a < b. For X : Fin 3 → Matrix (Fin a) (Fin b) ℂ, assume LinearIndependent ℂ X and that (stack X).mulVecLin is injective. If T : Matrix (Fin 3) (Fin 3) ℂ is Hermitian, compression X T = 0, and T ≠ 0, then an equivalence e : Fin 3 ≃ Fin 3 orders its eigenvalues as 0 < eigenvalues(e 0), eigenvalues(e 1) < 0, and eigenvalues(e 2) = 0.

**Theorem 1.1 (The three eigenvalue signs).**

Lean statement: `D5/S3/Quantum/Algebra/CompressionKernel/NativeThreeInertiaBridge.spectral_signs`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/CompressionKernel/NativeThreeInertiaBridge.spectral_signs` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact conclusion is ∃ e : Fin 3 ≃ Fin 3, 0 < hT.eigenvalues (e 0) ∧ hT.eigenvalues (e 1) < 0 ∧ hT.eigenvalues (e 2) = 0, under the complete telescope hab, X, hX, hinj, T, hT, hPhi, and hne.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/CompressionKernel/NativeThreeInertiaBridge.spectral_signs`
- Dependency: [D5/S3/Quantum/Algebra/CommonCoefficientPlane](../CommonCoefficientPlane.md)
