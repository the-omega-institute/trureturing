# Low-rank rational extensions of qubit marginals

## Abstract

A rational rank bound for joint positive matrices with two qubit marginals.

**Theorem 1.1 (Rational extensions of rank at most three).**

Lean statement: `D5/S3/Quantum/Entanglement/Marginals/RationalQubitMarginalRank.rational_endpoint_rank_le_three`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Marginals/RationalQubitMarginalRank.rational_endpoint_rank_le_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rational positive semidefinite joint matrix of rank at most three exists exactly for two qubit marginals that are positive semidefinite, have equal trace, and have rational real and imaginary parts in every entry. Taking a partial trace preserves positivity and trace and only sums entries.

Eliminate one scalar pivot in each marginal. The resulting decomposition has at most two terms, each a nonnegative rational weight times a rank-one trace-one matrix with rational entries. When the pivot is zero, positivity forces its off-diagonal entry to vanish. Match the two pairs of weights with a two-by-two table. Its first cell receives the smaller of the first weights from the two marginals. At least one off-diagonal cell then vanishes. Sum the corresponding products of the rank-one matrices. Their partial traces recover the prescribed weights, and at most three nonzero rank-one terms contribute to the joint matrix.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Marginals/RationalQubitMarginalRank.rational_endpoint_rank_le_three`
- Dependency: [D5/S3/Quantum/Entanglement/Marginals/FibRationalPureExtension](FibRationalPureExtension.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../../Information/PartialTraceMutualInformation.md)
