# Coherent Fibonacci marginal extensions

## Abstract

A common-state criterion for two adjacent Fibonacci marginals with arbitrary coherences.

**Theorem 1.1 (The residual endpoint marginals).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.coherent_extendible_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.coherent_extendible_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The five legal Fibonacci words split into the middle singleton and the four occupation patterns of the two endpoints. Let b be the weight of the singleton and let L and R be the two observed endpoint blocks, obtained by restricting each edge matrix to the empty-middle subspace. Both edges supply the same middle-to-vacuum entry. Each edge supplies one additional middle-to-endpoint entry. The middle-to-double-occupation entry is free.

A common positive semidefinite trace-one state exists exactly when b is nonnegative, the two endpoint block traces both equal 1 - b, and there is a choice of the free entry for which both residual blocks are positive semidefinite and the entire coupling row vanishes if b = 0. For positive b the residuals subtract the respective endpoint marginals of the outer product of the conjugated middle row divided by b. At b = 0 the endpoint blocks themselves are the residuals.

The scalar Schur complement gives the necessity of the residual conditions. Their traces agree by trace preservation. If their trace is positive, their tensor product divided by that trace gives a joint positive residual on the endpoints. At trace zero the residual blocks are zero. Restoring the outer product contribution and the middle singleton gives the required common state.

**Theorem 1.2 (Pure extensions at a prescribed coupling).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.pure_coherent_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.pure_coherent_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix the free coupling z and suppose the middle occupation b is nonzero. A pure trace-one extension exists exactly when the left endpoint block has trace one minus b and both Schur residuals at z are zero. In that case the pure density is the only positive semidefinite extension with the specified marginals and coupling.

The middle amplitude x has squared modulus b and the middle row is x times the conjugate of the endpoint amplitudes. The endpoint block is therefore the outer product of the conjugated row divided by b. The trace condition and the left residual equation force b to be positive because for negative b the correction has nonpositive trace. Take x to be the positive square root of b and reconstruct the endpoint amplitudes from the row. Any positive extension with the same data has a positive semidefinite Schur residual with trace zero, so its endpoint block equals the same correction.

At zero middle occupation, an endpoint-only pure state can have nonzero endpoint blocks. For example, the pure vacuum has two vacuum projections as endpoint blocks. The positive-pivot formula divides by b and requires the separate zero-occupation analysis.

**Theorem 1.3 (Rational extension at a prescribed coupling).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.rational_extension_at`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.rational_extension_at` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a nonnegative middle occupation, rational observed entries, and a rational value for the unobserved coupling. Suppose the traces normalize the data, both residual marginals are positive semidefinite, and the row vanishes when the middle occupation is zero. The data admit a positive trace-one extension with rational real and imaginary parts in every entry.

Normalization makes the middle occupation rational. Take the tensor product of the two residual blocks divided by their common trace. At trace zero both blocks vanish and the product contribution is zero. Restore the correction and the middle row. Each entry uses sums, products, conjugation and reciprocals of complex numbers with rational coordinates.

**Theorem 1.4 (Rational rank at most two at a prescribed coupling).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.rational_rank_le_two_at_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.rational_rank_le_two_at_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix positive middle occupation, normalized rational edge data and a rational unobserved coupling. A rational positive extension of rank at most two exists exactly when both Schur residual marginals are positive semidefinite, their determinants agree and the common determinant is a sum of two rational squares.

The invertible Schur elimination preserves rank and leaves a one-dimensional pivot beside the joint endpoint residual. Elimination and restoration both preserve rational entries. When the common residual trace is positive, dividing by that trace reduces rank one of the joint residual to the rational two-qubit purity criterion. The determinants scale by a rational square, so the arithmetic test can use the unnormalized residuals. At trace zero both residuals vanish and restoring the pivot gives rank one.

**Theorem 1.5 (When the edge marginals determine the state).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.unique_coherent_extension_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.unique_coherent_extension_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At positive middle occupation, the two edge marginals determine a unique positive trace-one state exactly when the traces normalize the data and there is exactly one coupling z for which both Schur residuals are positive semidefinite.

Every feasible coupling gives an extension. If both residuals at a feasible coupling were positive definite, small variations in z would remain feasible. A unique feasible coupling therefore gives at least one singular residual. At trace zero the entire endpoint residual vanishes. At positive trace, the singular qubit residual has rank one. A joint positive matrix with a rank-one marginal factors, so its two marginals fix the joint residual. Restoring the correction gives the only compatible state.

At zero middle occupation the whole coupling row vanishes in every positive state. The Schur residual inequalities then have no dependence on z.

**Theorem 1.6 (Pure extensions at zero middle occupation).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.pure_coherent_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.pure_coherent_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At zero middle occupation, a pure extension exists exactly when all four couplings vanish and both endpoint matrices are positive semidefinite with trace one and equal determinants.

Arrange the four endpoint amplitudes into a two-by-two matrix M. The reductions are M times its adjoint and the transpose of the product in reverse order. These matrices have the same characteristic polynomial. Two-by-two matrices have equal characteristic polynomials exactly when they have equal traces and determinants.

For sufficiency, diagonalize both positive matrices with their common eigenvalue list. Insert the square roots of those eigenvalues between the left eigenvector unitary and the transpose of the right one. The resulting amplitude matrix has the two specified reductions.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.coherent_extendible_iff`
- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.pure_coherent_iff`
- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.pure_coherent_zero_iff`
- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.rational_extension_at`
- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.rational_rank_le_two_at_iff`
- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/FibCoherentExtension.unique_coherent_extension_iff`
- Dependency: [D5/S3/Quantum/Decoherence/LabelResetSupport](../../Decoherence/LabelResetSupport.md)
- Dependency: [D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction](../ChoiKiemKye/ConstructionReduction.md)
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/FibMarginalExtension](FibMarginalExtension.md)
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/FibRationalPureExtension](FibRationalPureExtension.md)
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/RationalQubitPurity](RationalQubitPurity.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../../Information/PartialTraceMutualInformation.md)
- Dependency: [D5/S3/Quantum/Measurements/ThreeDistinguishabilitySupportCount](../../Measurements/ThreeDistinguishabilitySupportCount.md)
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../../PureState/PureStateHandshake.md)
