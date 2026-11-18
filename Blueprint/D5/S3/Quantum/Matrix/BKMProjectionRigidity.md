# BKM projection rigidity

## Abstract

The BKM power integral sends a Hermitian projection to a positive semidefinite matrix exactly when the projection commutes with the faithful base.

**Theorem 1.1 (The integral on a commuting direction).**

Lean statement: `D5/S3/Quantum/Matrix/BKMProjectionRigidity.omega_of_commute`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/BKMProjectionRigidity.omega_of_commute` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The commutation equation eliminates matrix entries between distinct eigenspaces. On entries within an eigenspace the logarithmic mean is the eigenvalue, so the integral is multiplication by the base.

**Theorem 1.2 (Positivity detects commutation).**

Lean statement: `D5/S3/Quantum/Matrix/BKMProjectionRigidity.omega_projection_posSemidef_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/BKMProjectionRigidity.omega_projection_posSemidef_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Sandwich the BKM output by the inverse square root of the base and test its trace pairing with the complementary projection. Its trace equals the trace of the original projection. In a spectral basis the negated pairing sums squared entry magnitudes weighted by the logarithmic mean divided by the geometric mean, minus one. Each term is nonnegative, and the coefficient is positive across distinct eigenvalues. Positivity forces all such entries to vanish. In the converse direction the output is positive by compression. Every projection rank is in scope.

**Definition 1.3 (Negative spectral mass).**

Lean statement: `D5/S3/Quantum/Matrix/BKMProjectionRigidity.negTrace`

*Formalization.* `D5/S3/Quantum/Matrix/BKMProjectionRigidity.negTrace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the real trace of the negative part from continuous functional calculus.

**Theorem 1.4 (Off-diagonal leakage).**

Lean statement: `D5/S3/Quantum/Matrix/BKMProjectionRigidity.omega_projection_leakage`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/BKMProjectionRigidity.omega_projection_leakage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first two terms of the hyperbolic sine series give a quadratic bound on the logarithmic-mean coefficient. The spectral upper bound converts logarithm differences to differences of eigenvalues. The spectral lower bound controls the norm of the complementary projection after congruence. The two adjoint corners have equal squared Frobenius norm, giving the factor 12 times the squared upper bound divided by the lower bound.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/BKMProjectionRigidity.negTrace`
- Truth anchor: `D5/S3/Quantum/Matrix/BKMProjectionRigidity.omega_of_commute`
- Truth anchor: `D5/S3/Quantum/Matrix/BKMProjectionRigidity.omega_projection_leakage`
- Truth anchor: `D5/S3/Quantum/Matrix/BKMProjectionRigidity.omega_projection_posSemidef_iff`
- Dependency: [D5/S3/Quantum/Matrix/BKMLogarithmicMeanInverse](BKMLogarithmicMeanInverse.md)
