# Three Omitted Uniform Bases Can Interact

## Abstract

Three omitted bases can impose dependent restrictions on the joint lifting obstruction.

**Definition 1.1 (Independent cyclic-factor replacement).**

Lean statement: `D5/S3/Combinatorics/Matroids/ThreeOmittedCircuitRefutation.claim`

*Formalization.* `D5/S3/Combinatorics/Matroids/ThreeOmittedCircuitRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For three rank-sized omissions with pairwise intersection of cardinality at most the rank minus two, the proposed decomposition removes three factors of each of the two uniform orders and adds one factor for each omission. The replacement order is the gcd of the total size and the class sizes outside that omission. The rank is at least three and the corank is at least two.

**Theorem 1.2 (Dependent restrictions in rank four).**

Lean statement: `D5/S3/Combinatorics/Matroids/ThreeOmittedCircuitRefutation.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Matroids/ThreeOmittedCircuitRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Partition six singleton classes into three pairs and omit the union of each two pairs from the rank-four bases. Each permitted basis contains exactly one complete pair. Give the three types binary coefficients u, v and u+v. The weighted boundary and signed deletion rows vanish for every choice of u and v. Two basis readouts recover the parameters, so the joint lifting obstruction has at least four elements killed by two. The proposed decomposition is cyclic of order six, with exactly two such elements.

## References

- Truth anchor: `D5/S3/Combinatorics/Matroids/ThreeOmittedCircuitRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Matroids/ThreeOmittedCircuitRefutation.result`
- Dependency: [D5/S3/Combinatorics/Matroids/RankTwoCircuitInvariantFactors](RankTwoCircuitInvariantFactors.md)
- Dependency: [D5/S3/Combinatorics/Matroids/SparsePavingCircuitCoordinates](SparsePavingCircuitCoordinates.md)
