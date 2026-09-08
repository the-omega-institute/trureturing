# Discrete Stein Compression Stability

## Abstract

Positive diagonal discrete Stein dissipation excludes every unit-circle pole after actual principal truncation.

**Definition 1.1 (Complexified matrix).**

Lean statement: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complexMatrix`

*Formalization.* `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complexMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real matrix acts on complex states so nonreal poles are included.

**Theorem 1.2 (Complexified products).**

Lean statement: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complexMatrix_mul`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complexMatrix_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complexification preserves the actual matrix products used in iterated readouts.

**Definition 1.3 (Complex state energy).**

Lean statement: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complexEnergy`

*Formalization.* `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complexEnergy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Positive diagonal weights measure the sum of squared complex moduli.

**Theorem 1.4 (Nonnegative energy).**

Lean statement: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complexEnergy_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complexEnergy_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Nonnegative weights give nonnegative complex state energy.

**Theorem 1.5 (Definite energy).**

Lean statement: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complexEnergy_eq_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complexEnergy_eq_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Positive weights make zero energy equivalent to a zero complex state.

**Theorem 1.6 (Positive nonzero-state energy).**

Lean statement: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complexEnergy_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complexEnergy_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonzero complex eigenvector carries strictly positive energy.

**Theorem 1.7 (Complex scalar scaling).**

Lean statement: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complexEnergy_smul`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complexEnergy_smul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Complex scalar multiplication rescales energy by the squared scalar modulus.

**Theorem 1.8 (Complexified Stein inequality).**

Lean statement: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complex_observability_stein`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complex_observability_stein` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Adds the real and imaginary parts of the real Stein inequality to derive the complex-state inequality.

**Theorem 1.9 (Complexified full observation).**

Lean statement: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.observable_complexification`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.observable_complexification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Real joint readout injectivity implies complex joint injectivity by separating real and imaginary parts.

**Definition 1.10 (Zero extension).**

Lean statement: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.prefixLift`

*Formalization.* `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.prefixLift` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Zero-extends retained coordinates by a finite sum, including the empty retained space.

**Definition 1.11 (Principal projection).**

Lean statement: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.prefixProjection`

*Formalization.* `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.prefixProjection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The actual prefix projection is orthogonal for every positive diagonal metric.

**Theorem 1.12 (Retained coordinate recovery).**

Lean statement: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.prefixLift_at`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.prefixLift_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Zero extension preserves each retained coordinate exactly.

**Theorem 1.13 (Actual truncated action).**

Lean statement: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.action_prefixLift`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.action_prefixLift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Matrix action on the lifted state is exactly the action of the retained matrix columns.

**Theorem 1.14 (Retained and discarded energy).**

Lean statement: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.projection_energy_split`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.projection_energy_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Splits the exact complex state energy into retained and discarded nonnegative terms.

**Theorem 1.15 (Strict complex eigenvalue bound).**

Lean statement: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.principal_truncation_eigenvalue_lt_one`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.principal_truncation_eigenvalue_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Stein inequality puts a retained eigenvalue in the closed disk. Equality forces both discarded action and output to vanish, producing an unobservable full-system eigenvector and a contradiction. Neither a singular-value gap nor reduced minimality is assumed.

**Theorem 1.16 (Strict internal stability).**

Lean statement: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.principal_truncation_spectrum_lt_one`

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.principal_truncation_spectrum_lt_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every point of the standard complex spectrum of the actual principal block has modulus below one. This covers nonreal poles, repeated weights and zero-dimensional cuts; no custom stability predicate replaces the conclusion.

## References

- Truth anchor: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.action_prefixLift`
- Truth anchor: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complexEnergy`
- Truth anchor: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complexEnergy_eq_zero_iff`
- Truth anchor: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complexEnergy_nonneg`
- Truth anchor: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complexEnergy_pos`
- Truth anchor: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complexEnergy_smul`
- Truth anchor: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complexMatrix`
- Truth anchor: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complexMatrix_mul`
- Truth anchor: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.complex_observability_stein`
- Truth anchor: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.observable_complexification`
- Truth anchor: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.prefixLift`
- Truth anchor: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.prefixLift_at`
- Truth anchor: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.prefixProjection`
- Truth anchor: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.principal_truncation_eigenvalue_lt_one`
- Truth anchor: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.principal_truncation_spectrum_lt_one`
- Truth anchor: `D5/S3/Observer/Hankel/DiscreteSteinCompressionStability.projection_energy_split`
- Dependency: [D5/S3/Observer/Hankel/BalancedTruncationTail](BalancedTruncationTail.md)
