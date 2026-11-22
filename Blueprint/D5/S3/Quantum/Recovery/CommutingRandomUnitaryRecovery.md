# The dimension bound for commuting quasi-inversion

## Abstract

Optimal unitary recovery for diagonal random-unitary noise through dimension three.

**Theorem 1.1 (Li–Tam rank bound).**

Lean statement: `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.extreme_rank_sq_le`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.extreme_rank_sq_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A complex correlation matrix is positive semidefinite with unit diagonal. Factor an extreme matrix of rank r as V V* with V of full column rank. The real map H ↦ diag(V H V*) takes Hermitian r by r matrices to a real d-dimensional space. If r² > d, a nonzero kernel element gives two distinct feasible perturbations V(I ± tH)V* with the original matrix as their midpoint.

**Theorem 1.2 (Rank-one maximizer in dimensions one to three).**

Lean statement: `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.phase_gram_max`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.phase_gram_max` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The correlation matrices form a nonempty compact set. The maximizers of a linear functional form an exposed face, so an extreme point of that face is extreme in the correlation set. Li–Tam's inequality and the unit diagonal force rank one in positive dimension at most three.

**Theorem 1.3 (Channel action for arbitrary weights).**

Lean statement: `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.randomUnitaryChannel_action`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.randomUnitaryChannel_action` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The Kraus operators are the unitaries scaled by the square roots of their weights. The weights can vanish, and their sum is one.

**Theorem 1.4 (Canonical recovery score).**

Lean statement: `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.randomUnitary_score_kraus`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.randomUnitary_score_kraus` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The normalized maximally entangled input is evaluated after the decoder is composed with the noise, with identity on the reference. The canonical Kraus trace identity gives a weighted sum of squared traces of decoder-branch products.

**Theorem 1.5 (Recovery in a supplied common unitary basis).**

Lean statement: `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.unitary_optimal_of_eigenbasis`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.unitary_optimal_of_eigenbasis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Trace cyclicity transports the score to the common eigenbasis. Trace preservation bounds each diagonal entry of the decoder Gram matrix by one. Adding a positive rank-one correction on each coordinate fills its deficit and contributes a nonnegative amount to the objective. A maximizing phase Gram matrix yields a diagonal unitary, which is carried back to the original basis.

**Theorem 1.6 (Diagonal unitary optimum).**

Lean statement: `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.diagonal_unitary_optimal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.diagonal_unitary_optimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every finite diagonal random-unitary mixture in dimensions one, two and three admits a single diagonal unitary decoder attaining the score bound against all deterministic CPTP decoders.

**Theorem 1.7 (Simultaneous unitary diagonalization).**

Lean statement: `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.simultaneous_unitary_eigenbasis`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.simultaneous_unitary_eigenbasis` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Unitary inverses equal adjoints, so the real and imaginary parts of the branches form a commuting family of self-adjoint operators. Their orthogonal joint eigenspaces furnish a common unitary eigenbasis.

**Theorem 1.8 (Unitary optimum for pairwise commuting branches).**

Lean statement: `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.commuting_unitary_optimal`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.commuting_unitary_optimal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every finite probability-weighted mixture of pairwise commuting unitary conjugations on a nonzero code of dimension at most three, one unitary decoder attains the canonical entanglement fidelity against all deterministic CPTP decoders. The separate dimension-four example attains 1/4 + √3/6 by a CPTP decoder and gives a strictly smaller score for every unitary decoder.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.commuting_unitary_optimal`
- Truth anchor: `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.diagonal_unitary_optimal`
- Truth anchor: `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.extreme_rank_sq_le`
- Truth anchor: `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.phase_gram_max`
- Truth anchor: `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.randomUnitaryChannel_action`
- Truth anchor: `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.randomUnitary_score_kraus`
- Truth anchor: `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.simultaneous_unitary_eigenbasis`
- Truth anchor: `D5/S3/Quantum/Recovery/CommutingRandomUnitaryRecovery.unitary_optimal_of_eigenbasis`
- Dependency: [D5/S3/Quantum/Entanglement/BipartiteSectorDecomposition](../Entanglement/BipartiteSectorDecomposition.md)
- Dependency: [D5/S3/Quantum/Recovery/BinaryRandomUnitaryChannel](BinaryRandomUnitaryChannel.md)
