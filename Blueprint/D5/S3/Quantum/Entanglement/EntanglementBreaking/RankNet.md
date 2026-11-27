# Nets of fixed-rank coefficient matrices

## Abstract

Finite nets for complex coefficient matrices of bounded rank.

**Theorem 1.1 (Finite net on the rank-bounded unit sphere).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet.exists_rank_sphere_net`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet.exists_rank_sphere_net` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Factor each rank-at-most-k coefficient matrix with unit Frobenius norm into an isometry with k columns and a unit Frobenius factor. The product of an operator norm net and a Frobenius norm net gives the approximants. Both factor nets lie within their respective sets.

**Definition 1.2 (Rectangular op norm).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet.rectangularOpNorm`

*Formalization.* `D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet.rectangularOpNorm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take the Euclidean operator norm of the linear map given by multiplication by the rectangular complex matrix.

**Theorem 1.3 (Exists stiefel net).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet.exists_stiefel_net`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet.exists_stiefel_net` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is an internal one-eighth net for the complex isometries in the rectangular operator norm, of cardinality at most seventeen raised to the real ambient dimension.

**Theorem 1.4 (Exists frobenius sphere net).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet.exists_frobenius_sphere_net`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet.exists_frobenius_sphere_net` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is an internal one-eighth net for the complex Frobenius unit sphere, of cardinality at most seventeen raised to the real ambient dimension.

**Theorem 1.5 (Exists left stiefel factorization).**

Lean statement: `D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet.exists_left_stiefel_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet.exists_left_stiefel_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When k is at most d, a d by d coefficient matrix of rank at most k and Frobenius norm one factors as a d by k isometry times a k by d matrix of Frobenius norm one.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet.exists_frobenius_sphere_net`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet.exists_left_stiefel_factorization`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet.exists_rank_sphere_net`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet.exists_stiefel_net`
- Truth anchor: `D5/S3/Quantum/Entanglement/EntanglementBreaking/RankNet.rectangularOpNorm`
- Dependency: [D5/S3/Quantum/Entanglement/EntanglementBreaking/BallNet](BallNet.md)
- Dependency: [D5/S3/Quantum/Entanglement/EntanglementBreaking/SchmidtCompression](SchmidtCompression.md)
