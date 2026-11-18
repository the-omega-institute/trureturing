# Physical qubit coefficient geometry

## Abstract

The two physical input columns are split by their output qubit label. Isometry orthogonality relates their retained and flipped vectors, controls the phase-sensitive coefficient cancellation and converts a diagonal residual into quantitative flip bounds.

**Definition 1.1 (The four physical column slices).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.column`

*Formalization.* `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.column` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The output B coordinate splits the two Stinespring columns into retained and flipped vectors in the full environment space.

**Definition 1.2 (The reduced physical action).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.reduced`

*Formalization.* `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.reduced` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjugation by the isometry followed by the actual environment partial trace defines the reduced qubit action on every complex input matrix.

**Theorem 1.3 (Retained and flipped column norms).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.retained_flip_norms`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.retained_flip_norms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each isometry input column, the squared norms of its retained and flipped output slices sum to one.

**Theorem 1.4 (Retained vectors and their phase gap).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.retained_gap`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.retained_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The squared norm of the difference between the retained vectors is at most twice the modulus of one minus their complex inner product.

**Theorem 1.5 (Phase-sensitive two-column cancellation).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.isometry_coefficient_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.isometry_coefficient_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite environment and actual two-column isometry, the reduced off-diagonal entry is the sum of four complex coefficient terms. Column orthogonality gives exact cancellation in the sum of the two diagonal-to-coherence coefficients. Their modulus is bounded by twice the square root of total flip probability times the square root of the phase-sensitive retained-column gap. No unitality is assumed.

**Theorem 1.6 (Entries of a traceless Hermitian qubit).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.traceless_qubit_entry_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.traceless_qubit_entry_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a traceless Hermitian two by two matrix, each diagonal and off-diagonal entry has modulus bounded by half the trace norm.

**Theorem 1.7 (Diagonal residual bounds the flip terms).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.diagonal_residual_controls_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.diagonal_residual_controls_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A trace-norm residual e for the diagonal Pauli direction bounds both the total flip probability and the difference of the diagonal-to-coherence coefficients by e divided by two. The exact trace norm of a traceless Hermitian qubit supplies both bounds.

**Theorem 1.8 (Hermiticity of the reduced action).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.reduced_hermitian`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.reduced_hermitian` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying an isometry on both sides and discarding the environment preserves Hermiticity.

**Theorem 1.9 (Trace of the reduced action).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.reduced_trace`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.reduced_trace` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The reduced action of an isometry preserves the matrix trace.

**Theorem 1.10 (A phase-sensitive coherence bound).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.offDiagonal_gap_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.offDiagonal_gap_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every traceless Hermitian qubit M tested against the same actual isometry, the retained-column gap times the off-diagonal modulus is bounded by half its trace-norm residual plus the coefficient-difference bound times its operator-norm bound and half the flip bound times that operator-norm bound. Complex phases and both nonunital coherence coefficients are retained.

**Theorem 1.11 (Rotate the same physical isometry).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.rotated_dilation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.rotated_dilation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A qubit unitary rotates the input and output of a physical isometry together and gives the corresponding conjugated reduced action on every complex matrix.

**Theorem 1.12 (A dilation of the actual channel).**

Lean statement: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.actual_dilation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.actual_dilation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every canonical qubit channel with finite physical output has a finite isometric dilation whose environment partial trace equals the channel on every matrix.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.actual_dilation`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.column`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.diagonal_residual_controls_coefficients`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.isometry_coefficient_geometry`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.offDiagonal_gap_bound`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.reduced`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.reduced_hermitian`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.reduced_trace`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.retained_flip_norms`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.retained_gap`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.rotated_dilation`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitCoefficientGeometry.traceless_qubit_entry_bounds`
- Dependency: [D5/S3/Quantum/Classicalization/XuImaiGuhneSimultaneousUnboundedness](../Classicalization/XuImaiGuhneSimultaneousUnboundedness.md)
- Dependency: [D5/S3/Quantum/Divergence/FaithfulConditionalGap](../Divergence/FaithfulConditionalGap.md)
- Dependency: [D5/S3/Quantum/Entanglement/FiniteSectorPhysicalConstruction](../Entanglement/FiniteSectorPhysicalConstruction.md)
- Dependency: [D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks](../Entanglement/PermutationCriteria/BellBlocks.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteDensityPurification](../Foundation/FiniteDensityPurification.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteDiamondDistance](../Foundation/FiniteDiamondDistance.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteHermitianTraceDuality](../Foundation/FiniteHermitianTraceDuality.md)
- Dependency: [D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation](../Information/ChenKatoBrandaoTraceNormCMIRefutation.md)
- Dependency: [D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity](../Information/CorrelatedGibbsEnergyIdentity.md)
- Dependency: [D5/S3/Quantum/Information/MarginalCalculus](../Information/MarginalCalculus.md)
- Dependency: [D5/S3/Quantum/Information/OrthogonalRecordEntropy](../Information/OrthogonalRecordEntropy.md)
- Dependency: [D5/S3/Quantum/Information/Pauli/PauliMatrix](../Information/Pauli/PauliMatrix.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/Matrix/UniformVarianceTraceBound](../Matrix/UniformVarianceTraceBound.md)
- Dependency: [D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance](../Measurement/AnticoherenceSpinCovariance.md)
- Dependency: [D5/S3/Quantum/Reduction/WeightedWordDefect](../Reduction/WeightedWordDefect.md)
