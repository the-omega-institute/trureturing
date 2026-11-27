# Original Half-Frequency Oscillator Hermitian Form

## Abstract

Original Half-Frequency Oscillator Hermitian Form

The carrier is the original complex multivariate polynomial Oscillator(D). For each natural frequency k, r(k) is the positive real square root of (k+1/2)/(k+1). The actual algebra homomorphism R substitutes r(k) X(i,k) for each original variable. Its inverse substitutes r(k) inverse X(i,k). Polynomial induction proves both inverse laws and the derivative chain law, and r(k)^2(k+1)=k+1/2 supplies the actual half-current normalization. The form is exactly fockForm(D)(R(P),R(Q)), not a form on a different carrier. The original integer Fock suppliers retain attribution: LatticeOscillatorFockForm supplies the contraction form and both integer adjoints; LatticeOscillatorFockMetric supplies positivity for a positive-definite real original Gram and nondegeneracy under both inverse-Gram equations. No LDL decomposition or integer positivity is reproved.

**Theorem 1.1 (Actual Polynomial Chain Rule).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockHermitian.pderiv_scaling`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockHermitian.pderiv_scaling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every original coordinate and polynomial, differentiation of R(P) equals r(k) times R of the original derivative. This is proved by polynomial induction, not assumed as an interface. Its Gram-weighted sum and the scalar balance equation intertwine the actual original annihilation operators.

**Theorem 1.2 (All Original Half-Current Adjoints).**

Lean statement: `D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockHermitian.halfForm_current_adjoint`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockHermitian.halfForm_current_adjoint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integer j, current(D,i,j) is adjoint to current(D,i,-j-1). The original frequency is j+1/2. Negative j gives literal variable multiplication; nonnegative j gives (j+1/2) times the original Gram-weighted partial. The reflected index is -j-1, not -j. The form is conjugate-linear first and linear second. Its Hermitian symmetry is inherited by actual pullback. Strict positivity holds on every nonzero polynomial when gramReal(D) is positive definite. Under both inverse-Gram equations, both radicals vanish even without positive signature.

This is classical algebraic Fock and finite-group Hermitian geometry, not a claim of new physics or literature novelty. It does not establish all-state charged BPZ/PCT or unitarity, a full twisted Jacobi identity, intertwiners, fusion, orbifold gluing, the Monster, a complete string theory or AdS/CFT reconstruction. The full original objective remains open. No all-charge Lorentzian or neutral BRST positivity follows. The owning Reg sources provide explicit source bridges and four family slots; their source-binding and full admission status is separate from kernel compilation.

## References

- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockHermitian.halfForm_current_adjoint`
- Truth anchor: `D5/S3/VertexAlgebra/HalfFock/Hermitian/LatticeHalfFockHermitian.pderiv_scaling`
- Dependency: [D5/S3/VertexAlgebra/Lattice/Oscillator/LatticeOscillatorFockMetric](../../Lattice/Oscillator/LatticeOscillatorFockMetric.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockCurrentNormal](../../LatticeHalfFockCurrentNormal.md)
