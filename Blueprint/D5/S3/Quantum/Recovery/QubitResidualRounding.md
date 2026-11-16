# Physical qubit residual geometry

## Abstract

Let rho be a canonical density state on A times (B times C), with B the two-dimensional coordinate type, and let T be an arbitrary canonical channel from B to B times C. Write P for the actual AB marginal and r for half the trace norm of rho minus the actual recovered reference state. Centering P at the product of its two marginals and testing all Hermitian contractions gives quantitative control that is independent of the dimensions of A and C. These statements describe correlation and dilation bounds; the universal fifth-root repair estimate requires additional estimates.

**Theorem 1.1 (A phase-sensitive coherence bound).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.offDiagonal_gap_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.offDiagonal_gap_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every traceless Hermitian qubit M tested against the same actual isometry, the retained-column gap times the off-diagonal modulus is bounded by half its trace-norm residual plus the coefficient-difference bound times its operator-norm bound and half the flip bound times that operator-norm bound. Complex phases and both nonunital coherence coefficients are retained.

**Theorem 1.2 (Complex block duality from the same diagonal geometry).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.complex_block_bound_of_diagonal_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.complex_block_bound_of_diagonal_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the centered AB matrix, suppose every Hermitian contraction slice has operator norm at most x greater than zero and actual reduced-isometry residual at most 4r. If the total flip probability and coherence-coefficient difference are each at most 2r divided by x, then for positive retained-column gap g the complex off-diagonal block has trace norm at most 16r divided by g. The modulus trace pairing first has bound 8r divided by g, and complex duality retains its factor two.

**Theorem 1.3 (An actual isometry in the attained eigenbasis).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.diagonalized_residual_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.diagonalized_residual_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any nonzero traceless Hermitian qubit K and any actual physical isometry W, diagonalize K and rotate the same input and output qubit coordinate. The resulting physical isometry V has the exact transported action on every complex matrix. If the K residual has trace norm at most e, both its total flip probability and the difference of its diagonal-to-coherence terms are at most e divided by twice the operator norm of K.

**Definition 1.4 (The four physical column slices).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.column`

*Formalization.* `D5/S3/Quantum/Recovery/QubitResidualRounding.column` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The output B coordinate splits the two Stinespring columns into retained and flipped vectors in the full environment space.

**Definition 1.5 (The reduced physical action).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.reduced`

*Formalization.* `D5/S3/Quantum/Recovery/QubitResidualRounding.reduced` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjugation by the isometry followed by the actual environment partial trace defines the reduced qubit action on every complex input matrix.

**Theorem 1.6 (Phase-sensitive two-column cancellation).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.isometry_coefficient_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.isometry_coefficient_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite environment and actual two-column isometry, the reduced off-diagonal entry is the sum of four complex coefficient terms. Column orthogonality gives exact cancellation in the sum of the two diagonal-to-coherence coefficients. Their modulus is bounded by twice the square root of total flip probability times the square root of the phase-sensitive retained-column gap. No unitality is assumed.

**Theorem 1.7 (Diagonal residual bounds the flip terms).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.diagonal_residual_controls_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.diagonal_residual_controls_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A trace-norm residual e for the diagonal Pauli direction bounds both the total flip probability and the difference of the diagonal-to-coherence coefficients by e divided by two. The exact trace norm of a traceless Hermitian qubit supplies both bounds.

**Definition 1.8 (The centered AB correlation).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.centered`

*Formalization.* `D5/S3/Quantum/Recovery/QubitResidualRounding.centered` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtract the product of the two actual marginals from the AB density matrix. Both partial traces of this centered matrix vanish.

**Definition 1.9 (Hermitian reference tests).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.sliceLinear`

*Formalization.* `D5/S3/Quantum/Recovery/QubitResidualRounding.sliceLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pair each reference block with a complex-linear test on A. For Hermitian inputs and Hermitian tests the resulting B matrix is Hermitian.

**Theorem 1.10 (An attained correlation maximum).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.attained_centered_traceNorm_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.attained_centered_traceNorm_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The maximum operator norm of the centered slice over all Hermitian A contractions is attained. Pauli reconstruction and Hermitian trace duality bound the trace norm of the centered AB matrix by six times this maximum.

**Theorem 1.11 (Every centered test is approximately fixed).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.all_centered_tests_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.all_centered_tests_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Hermitian A contraction, its centered qubit slice has residual at most 4r under the actual reduced channel obtained by discarding C after T. The AB and B residuals each have trace norm at most 2r.

**Theorem 1.12 (A product repair from small correlation).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.product_repair_of_centered_correlation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.product_repair_of_centered_correlation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an attaining reference test with slice operator norm x, the actual state a tensor T(b) on the same ABC space has ordinary conditional mutual information zero and lies within trace distance r plus 3x of rho. Here a and b are the actual marginals of P.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.all_centered_tests_residual`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.attained_centered_traceNorm_bound`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.centered`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.column`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.complex_block_bound_of_diagonal_geometry`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.diagonal_residual_controls_coefficients`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.diagonalized_residual_geometry`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.isometry_coefficient_geometry`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.offDiagonal_gap_bound`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.product_repair_of_centered_correlation`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.reduced`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.sliceLinear`
- Dependency: [D5/S3/Quantum/Classicalization/XuImaiGuhneSimultaneousUnboundedness](../Classicalization/XuImaiGuhneSimultaneousUnboundedness.md)
- Dependency: [D5/S3/Quantum/Divergence/FaithfulConditionalGap](../Divergence/FaithfulConditionalGap.md)
- Dependency: [D5/S3/Quantum/Entanglement/FiniteSectorPhysicalConstruction](../Entanglement/FiniteSectorPhysicalConstruction.md)
- Dependency: [D5/S3/Quantum/Entanglement/PermutationCriteria/BellBlocks](../Entanglement/PermutationCriteria/BellBlocks.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteDensityPurification](../Foundation/FiniteDensityPurification.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteDiamondDistance](../Foundation/FiniteDiamondDistance.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteHermitianTraceDuality](../Foundation/FiniteHermitianTraceDuality.md)
- Dependency: [D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation](../Information/ChenKatoBrandaoTraceNormCMIRefutation.md)
- Dependency: [D5/S3/Quantum/Information/MarginalCalculus](../Information/MarginalCalculus.md)
- Dependency: [D5/S3/Quantum/Information/OrthogonalRecordEntropy](../Information/OrthogonalRecordEntropy.md)
- Dependency: [D5/S3/Quantum/Information/Pauli/PauliMatrix](../Information/Pauli/PauliMatrix.md)
- Dependency: [D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors](../Information/StrongSubadditivity/MarkovConstructors.md)
- Dependency: [D5/S3/Quantum/Matrix/UniformVarianceTraceBound](../Matrix/UniformVarianceTraceBound.md)
- Dependency: [D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance](../Measurement/AnticoherenceSpinCovariance.md)
- Dependency: [D5/S3/Quantum/Reduction/WeightedWordDefect](../Reduction/WeightedWordDefect.md)
