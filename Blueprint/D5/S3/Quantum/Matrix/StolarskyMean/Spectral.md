# Positive eigenvalues and conditional negativity

## Abstract

Conditional negativity and positive subspaces determine the positive inertia of real symmetric matrices.

**Definition 1.1 (Conditional negativity).**

Lean statement: `D5/S3/Quantum/Matrix/StolarskyMean/Spectral.ConditionallyNegative`

*Formalization.* `D5/S3/Quantum/Matrix/StolarskyMean/Spectral.ConditionallyNegative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The quadratic form is nonpositive for every real coefficient vector whose coordinates sum to zero. The dimension may be zero.

**Theorem 1.2 (One positive diagonal entry suffices).**

Lean statement: `D5/S3/Quantum/Matrix/StolarskyMean/Spectral.numPosEig_eq_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/StolarskyMean/Spectral.numPosEig_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A real symmetric conditionally negative matrix with at least one strictly positive diagonal entry has exactly one strictly positive eigenvalue. The sum-of-coordinates functional is injective on every positive definite subspace, so such a subspace has dimension at most one. If all eigenvalues were nonpositive, every diagonal entry would be nonpositive. These two bounds give the exact count.

**Theorem 1.3 (Class A from conditional negativity).**

Lean statement: `D5/S3/Quantum/Matrix/StolarskyMean/Spectral.inClassA_of_conditionallyNegative`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/StolarskyMean/Spectral.inClassA_of_conditionallyNegative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A real symmetric matrix of nonzero size with strictly positive entries and conditional negativity belongs to class A. A diagonal entry supplies the positive direction, and the zero-sum hyperplane excludes any second positive direction.

**Theorem 1.4 (Two positive directions force two positive eigenvalues).**

Lean statement: `D5/S3/Quantum/Matrix/StolarskyMean/Spectral.two_le_numPosEig_of_posDefOn`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/StolarskyMean/Spectral.two_le_numPosEig_of_posDefOn` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a real symmetric matrix, a subspace of dimension at least two on which the quadratic form is strictly positive away from zero forces at least two strictly positive eigenvalues. This is the positive-subspace dimension bound from Sylvester inertia theory.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/StolarskyMean/Spectral.ConditionallyNegative`
- Truth anchor: `D5/S3/Quantum/Matrix/StolarskyMean/Spectral.inClassA_of_conditionallyNegative`
- Truth anchor: `D5/S3/Quantum/Matrix/StolarskyMean/Spectral.numPosEig_eq_one`
- Truth anchor: `D5/S3/Quantum/Matrix/StolarskyMean/Spectral.two_le_numPosEig_of_posDefOn`
- Dependency: [D5/S3/Quantum/Matrix/StolarskyMean/Defs](Defs.md)
