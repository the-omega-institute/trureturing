# Expansion of the Multiple Sum into Paths

## Abstract

Repeated peak deletion expresses the multiple sum as refined path polynomials.

**Theorem 1.1 (The path expansion).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuExpansion.lhs_path_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CylindricPartition/LiUncuExpansion.lhs_path_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For nonnegative n, k at least one, and 1 at most i and i at most k, lhs(n,k,i) is the sum of refinedPathSum(k-1,k-i,2n,N) over N from zero through n.

## References

- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuExpansion.lhs_path_expansion`
- Dependency: [D5/S3/Combinatorics/CylindricPartition/LiUncuRecurrence](LiUncuRecurrence.md)
