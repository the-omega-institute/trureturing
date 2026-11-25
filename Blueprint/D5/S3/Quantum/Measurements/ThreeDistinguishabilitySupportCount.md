# Rank count for three orthogonal density supports

## Abstract

Orthogonal supports in four dimensions force two of three densities to be rank one.

**Theorem 1.1 (Joint support dimension).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilitySupportCount.sum_rank_le_of_orthogonal_supports`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilitySupportCount.sum_rank_le_of_orthogonal_supports` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Hermitian matrices with pairwise zero products have mutually orthogonal nonzero eigenspaces. Collect the nonzero eigenvalue indices in a disjoint sum. Their unit eigenvectors form one orthonormal family, so the sum of the ranks is at most the dimension of the ambient space.

**Theorem 1.2 (Two rank-one states after permutation).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilitySupportCount.exists_perm_rank_one_pair`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilitySupportCount.exists_perm_rank_one_pair` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Three trace-one matrices each have positive rank. With total rank at most four, at least two ranks equal one. A permutation places these two states first.

**Theorem 1.3 (A unit representative).**

Lean statement: `D5/S3/Quantum/Measurements/ThreeDistinguishabilitySupportCount.exists_rankOneDensity_of_rank_one`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Measurements/ThreeDistinguishabilitySupportCount.exists_rankOneDensity_of_rank_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive rank-one matrix, just one spectral value is nonzero. Trace one forces it to be one, so the matrix is the outer product of its unit eigenvector.

## References

- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilitySupportCount.exists_perm_rank_one_pair`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilitySupportCount.exists_rankOneDensity_of_rank_one`
- Truth anchor: `D5/S3/Quantum/Measurements/ThreeDistinguishabilitySupportCount.sum_rank_le_of_orthogonal_supports`
- Dependency: [D5/S3/Quantum/PureState/PureStateHandshake](../PureState/PureStateHandshake.md)
