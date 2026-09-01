# Discrete Koopman Operator

## Abstract

Pullback along a discrete update is a contravariant linear Koopman operator with multiplicative eigenfunctions.

**Definition 1.1 (Discrete Koopman pullback).**

Lean statement: `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.discreteKoopmanOperator`

*Formalization.* `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.discreteKoopmanOperator` (`✓ std3`).

**Definition 1.2 (Finite Koopman iterate).**

Lean statement: `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.koopmanIterate`

*Formalization.* `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.koopmanIterate` (`✓ std3`).

**Definition 1.3 (Koopman eigenfunction).**

Lean statement: `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.IsKoopmanEigenfunction`

*Formalization.* `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.IsKoopmanEigenfunction` (`✓ std3`).

**Theorem 1.4 (Identity update gives identity pullback).**

Lean statement: `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.discreteKoopmanOperator_id`

*Formalization.* `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.discreteKoopmanOperator_id` (`✓ std3`). ∎

**Theorem 1.5 (Pullback reverses composition).**

Lean statement: `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.discreteKoopmanOperator_comp`

*Formalization.* `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.discreteKoopmanOperator_comp` (`✓ std3`). ∎

**Theorem 1.6 (Constants are preserved).**

Lean statement: `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.discreteKoopmanOperator_one`

*Formalization.* `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.discreteKoopmanOperator_one` (`✓ std3`). ∎

**Theorem 1.7 (Observable products are preserved).**

Lean statement: `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.discreteKoopmanOperator_mul`

*Formalization.* `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.discreteKoopmanOperator_mul` (`✓ std3`). ∎

**Theorem 1.8 (Eigenfunctions multiply).**

Lean statement: `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.isKoopmanEigenfunction_mul`

*Formalization.* `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.isKoopmanEigenfunction_mul` (`✓ std3`). ∎

**Theorem 1.9 (Eigenfunction iterates are eigenvalue powers).**

Lean statement: `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.koopmanIterate_eigenfunction`

*Formalization.* `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.koopmanIterate_eigenfunction` (`✓ std3`). ∎

## References

- Truth anchor: `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.discreteKoopmanOperator`
- Truth anchor: `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.koopmanIterate`
- Truth anchor: `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.IsKoopmanEigenfunction`
- Truth anchor: `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.discreteKoopmanOperator_id`
- Truth anchor: `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.discreteKoopmanOperator_comp`
- Truth anchor: `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.discreteKoopmanOperator_one`
- Truth anchor: `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.discreteKoopmanOperator_mul`
- Truth anchor: `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.isKoopmanEigenfunction_mul`
- Truth anchor: `D5/S3/Dynamics/Koopman/DiscreteKoopmanOperator.koopmanIterate_eigenfunction`
- Dependency: [D5/S3/QuantumStates/ObservableAlgebraClosureDuality](../../QuantumStates/ObservableAlgebraClosureDuality.md)
