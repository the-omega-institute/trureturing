# Physical qubit residual geometry

## Abstract

Let rho be a canonical density state on A times (B times C), with B the two-dimensional coordinate type, and let T be an arbitrary canonical channel from B to B times C. Write P for the actual AB marginal and r for half the trace norm of rho minus the actual recovered reference state. Centering P at the product of its two marginals and testing all Hermitian contractions gives quantitative control that is independent of the dimensions of A and C. Every such state and channel admit a density state sigma on the same ABC system with ordinary conditional mutual information zero and half trace distance from rho at most the minimum of one and six times the fifth root of r. No rank, spectral-floor, channel-closeness or repaired-marginal premise is imposed.

**Theorem 1.1 (A dimension-independent fifth-root physical repair).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.qubit_residual_fifth_root_repair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.qubit_residual_fifth_root_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary finite A and C in independent universes, a canonical state rho on A times (Fin 2 times C), and every canonical channel T from Fin 2 to Fin 2 times C, let P be the actual AB marginal of rho. Set r to the half trace distance between rho and referenceState T P. There exists sigma on the same ABC carrier with ordinary qcmi zero and distance from rho at most min(1, 6 r^(1/5)). All ranks, zero eigenvalues, singleton outer dimensions and zero conditional weights are allowed; the density-state input supplies nonemptiness. Ordinary qcmi is S(AB) plus S(BC) minus S(B) minus S(ABC), using the actual marginals of sigma. This residual theorem supplies no bound in terms of the conditional mutual information of rho without a separate recovery theorem, and makes no sharpness or novelty claim.

The maximum centered Hermitian slice is attained. A small maximum yields an A-BC product directly. Otherwise diagonalizing the attained slice transports rho, its actual marginal and T coherently, and controls the total flip probability. A small retained-column gap gives an AB-C product; small B coherence gives a classical pointer repair. For large B coherence the actual marginal equation forces a product comparison. With delta the fifth root of r, the nontrivial scale delta below one sixth gives flip probability at most 2 delta to the fourth power and all comparison bounds at most 6 delta. The distance cap handles the other scales. At r zero, the same geometry gives exactly zero flips and either a common environment vector or zero coherence in the classical repair. Undoing the local B unitary returns sigma to the original system.

**Theorem 1.2 (A common environment gives an AB-C product).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.common_environment_product_repair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.common_environment_product_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let g be the modulus of one minus the inner product of the two retained Stinespring vectors. If the total flip probability s squared is below one, normalize the first retained vector and use it for both pointer columns. This is a physical product across AB and C, with ordinary qcmi zero and half trace distance from rho at most r plus 2s plus the square root of 2g. The comparison retains every rank and the same ABC system.

**Theorem 1.3 (The actual marginal constrains the phase gap).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.marginal_coherence_gap_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.marginal_coherence_gap_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an actual B density state b with reduced-channel residual at most 2r, the phase gap times the modulus of b's off-diagonal entry is bounded by r plus s times the square root of g plus half the coefficient-difference bound and half the flip bound. The trace-one equation separates the sum and difference of the two diagonal-to-coherence coefficients, and isometry orthogonality bounds their sum.

**Theorem 1.4 (A classical repair on the same physical system).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.classical_pointer_repair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.classical_pointer_repair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let W be an actual dilation of T, and let s squared be its total flip probability in the chosen qubit basis. If s squared is below one, normalizing its two retained vectors and pinching the actual AB input produces a classical Markov state on the same ABC carrier. Its half trace distance from rho is at most r plus the trace norm z of the actual off-diagonal AB block plus 2s. A positive block weight normalizes its conditional A state; a zero block has zero positive matrix and needs no division.

**Theorem 1.5 (The cost of deleting qubit coherence).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.pointerInput_distance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.pointerInput_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Pinching an actual AB density state in the two-dimensional B basis changes it in half trace distance by at most the trace norm of its complex off-diagonal A block. The two conjugate off-diagonal terms and the half-distance convention account for the factor.

**Theorem 1.6 (A common environment comparison).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.physicalOutput_distance`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.physicalOutput_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two physical isometries applied to the same AB density state, followed by discarding their common environment, differ in half trace distance by at most the operator norm of the difference of the isometries. This comparison has no reference-dimension factor.

**Theorem 1.7 (Coherent transport of the physical recovery data).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.actual_B_unitary_transport`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.actual_B_unitary_transport` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the input unitary U, localBState conjugates rho by its inverse on B. The public conjunction identifies the actual AB marginal, its B marginal, the transported canonical channel and recovered reference state, and conjugation of every centered slice. The proof of ordinary qcmi invariance uses the actual AB, BC and B marginal entropy identities. Half trace distance is unchanged. Applying localBState with star U returns a repair and its qcmi and distance bounds to the original ABC carrier, including singular states.

**Theorem 1.8 (Actual residual geometry in the attained basis).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.actual_diagonal_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.actual_diagonal_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive attained centered slice norm x, diagonalization and coherent transport give an actual dilation of the transported channel. Every Hermitian contraction has residual at most 4r. The flip sum and coefficient difference are at most 2r divided by x; a positive phase-sensitive gap g bounds the complex off-diagonal centered block by 16r divided by g. The physical dilation is obtained by finite reindexing of the output coordinate, so arbitrary finite coordinate universes remain in scope.

**Definition 1.9 (The same state in a B coordinate).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.localBState`

*Formalization.* `D5/S3/Quantum/Recovery/QubitResidualRounding.localBState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjugate the original ABC density state by identity on A, the inverse unitary on B, and identity on C. The system and every rank are retained.

**Definition 1.10 (The coherently transported physical channel).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.localBChannel`

*Formalization.* `D5/S3/Quantum/Recovery/QubitResidualRounding.localBChannel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Precompose the canonical recovery channel by the input unitary and postcompose by its inverse on the same output B coordinate. These are canonical completely positive trace preserving channels.

**Definition 1.11 (A normalized retained-column pointer map).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.pointerIsometry`

*Formalization.* `D5/S3/Quantum/Recovery/QubitResidualRounding.pointerIsometry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two environment vectors define a qubit map whose j-th column has support only on output pointer j. Unit norms make this map an isometry.

**Theorem 1.12 (Normalize retained columns below unit flip probability).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.normalized_pointer_isometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.normalized_pointer_isometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the sum s squared of the two flip probabilities is below one, both retained columns of the actual isometry have positive norm. Normalize them and delete the flips to obtain a pointer isometry within operator norm 2s. No input block weight is inverted.

**Theorem 1.13 (A phase-sensitive coherence bound).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.offDiagonal_gap_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.offDiagonal_gap_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every traceless Hermitian qubit M tested against the same actual isometry, the retained-column gap times the off-diagonal modulus is bounded by half its trace-norm residual plus the coefficient-difference bound times its operator-norm bound and half the flip bound times that operator-norm bound. Complex phases and both nonunital coherence coefficients are retained.

**Theorem 1.14 (Complex block duality from the same diagonal geometry).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.complex_block_bound_of_diagonal_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.complex_block_bound_of_diagonal_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the centered AB matrix, suppose every Hermitian contraction slice has operator norm at most x greater than zero and actual reduced-isometry residual at most 4r. If the total flip probability and coherence-coefficient difference are each at most 2r divided by x, then for positive retained-column gap g the complex off-diagonal block has trace norm at most 16r divided by g. The modulus trace pairing first has bound 8r divided by g, and complex duality retains its factor two.

**Theorem 1.15 (An actual isometry in the attained eigenbasis).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.diagonalized_residual_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.diagonalized_residual_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any nonzero traceless Hermitian qubit K and any actual physical isometry W, diagonalize K and rotate the same input and output qubit coordinate. The resulting physical isometry V has the exact transported action on every complex matrix. If the K residual has trace norm at most e, both its total flip probability and the difference of its diagonal-to-coherence terms are at most e divided by twice the operator norm of K.

**Definition 1.16 (The four physical column slices).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.column`

*Formalization.* `D5/S3/Quantum/Recovery/QubitResidualRounding.column` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The output B coordinate splits the two Stinespring columns into retained and flipped vectors in the full environment space.

**Definition 1.17 (The reduced physical action).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.reduced`

*Formalization.* `D5/S3/Quantum/Recovery/QubitResidualRounding.reduced` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Conjugation by the isometry followed by the actual environment partial trace defines the reduced qubit action on every complex input matrix.

**Theorem 1.18 (Phase-sensitive two-column cancellation).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.isometry_coefficient_geometry`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.isometry_coefficient_geometry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite environment and actual two-column isometry, the reduced off-diagonal entry is the sum of four complex coefficient terms. Column orthogonality gives exact cancellation in the sum of the two diagonal-to-coherence coefficients. Their modulus is bounded by twice the square root of total flip probability times the square root of the phase-sensitive retained-column gap. No unitality is assumed.

**Theorem 1.19 (Diagonal residual bounds the flip terms).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.diagonal_residual_controls_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.diagonal_residual_controls_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A trace-norm residual e for the diagonal Pauli direction bounds both the total flip probability and the difference of the diagonal-to-coherence coefficients by e divided by two. The exact trace norm of a traceless Hermitian qubit supplies both bounds.

**Definition 1.20 (The centered AB correlation).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.centered`

*Formalization.* `D5/S3/Quantum/Recovery/QubitResidualRounding.centered` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subtract the product of the two actual marginals from the AB density matrix. Both partial traces of this centered matrix vanish.

**Definition 1.21 (Hermitian reference tests).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.sliceLinear`

*Formalization.* `D5/S3/Quantum/Recovery/QubitResidualRounding.sliceLinear` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pair each reference block with a complex-linear test on A. For Hermitian inputs and Hermitian tests the resulting B matrix is Hermitian.

**Theorem 1.22 (An attained correlation maximum).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.attained_centered_traceNorm_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.attained_centered_traceNorm_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The maximum operator norm of the centered slice over all Hermitian A contractions is attained. Pauli reconstruction and Hermitian trace duality bound the trace norm of the centered AB matrix by six times this maximum.

**Theorem 1.23 (Every centered test is approximately fixed).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.all_centered_tests_residual`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.all_centered_tests_residual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every Hermitian A contraction, its centered qubit slice has residual at most 4r under the actual reduced channel obtained by discarding C after T. The AB and B residuals each have trace norm at most 2r.

**Theorem 1.24 (A product repair from small correlation).**

Lean statement: `D5/S3/Quantum/Recovery/QubitResidualRounding.product_repair_of_centered_correlation`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/QubitResidualRounding.product_repair_of_centered_correlation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an attaining reference test with slice operator norm x, the actual state a tensor T(b) on the same ABC space has ordinary conditional mutual information zero and lies within trace distance r plus 3x of rho. Here a and b are the actual marginals of P.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.actual_B_unitary_transport`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.actual_diagonal_geometry`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.all_centered_tests_residual`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.attained_centered_traceNorm_bound`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.centered`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.classical_pointer_repair`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.column`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.common_environment_product_repair`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.complex_block_bound_of_diagonal_geometry`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.diagonal_residual_controls_coefficients`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.diagonalized_residual_geometry`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.isometry_coefficient_geometry`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.localBChannel`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.localBState`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.marginal_coherence_gap_bound`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.normalized_pointer_isometry`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.offDiagonal_gap_bound`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.physicalOutput_distance`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.pointerInput_distance`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.pointerIsometry`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.product_repair_of_centered_correlation`
- Truth anchor: `D5/S3/Quantum/Recovery/QubitResidualRounding.qubit_residual_fifth_root_repair`
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
- Dependency: [D5/S3/Quantum/Information/CorrelatedGibbsEnergyIdentity](../Information/CorrelatedGibbsEnergyIdentity.md)
- Dependency: [D5/S3/Quantum/Information/MarginalCalculus](../Information/MarginalCalculus.md)
- Dependency: [D5/S3/Quantum/Information/OrthogonalRecordEntropy](../Information/OrthogonalRecordEntropy.md)
- Dependency: [D5/S3/Quantum/Information/Pauli/PauliMatrix](../Information/Pauli/PauliMatrix.md)
- Dependency: [D5/S3/Quantum/Information/StrongSubadditivity/MarkovConstructors](../Information/StrongSubadditivity/MarkovConstructors.md)
- Dependency: [D5/S3/Quantum/Matrix/CartesianVariance](../Matrix/CartesianVariance.md)
- Dependency: [D5/S3/Quantum/Matrix/UniformVarianceTraceBound](../Matrix/UniformVarianceTraceBound.md)
- Dependency: [D5/S3/Quantum/Measurement/AnticoherenceSpinCovariance](../Measurement/AnticoherenceSpinCovariance.md)
- Dependency: [D5/S3/Quantum/Reduction/WeightedWordDefect](../Reduction/WeightedWordDefect.md)
