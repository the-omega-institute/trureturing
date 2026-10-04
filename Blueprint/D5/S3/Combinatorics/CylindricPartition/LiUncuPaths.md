# Weighted Paths in a Bounded Strip

## Abstract

The sum of peak abscissae gives a polynomial weight on paths with horizontal edges only at the floor.

**Definition 1.1 (The path polynomial).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuPaths.pathPolynomial`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuPaths.pathPolynomial` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For nonnegative integers H and L and integer endpoints a and b, the polynomial sums q raised to peakWeight(0,w) over all valid words w of length L from height a to height b in the strip from zero to H. Invalid words contribute zero.

**Theorem 1.2 (The last-edge recurrence).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuPaths.path_last_edge_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CylindricPartition/LiUncuPaths.path_last_edge_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

Write P(L,a,b) for the path polynomial at height bound H. For H at least one and an integer b between zero and H, P(L+2,a,b) = P(L+1,a,b-1) when b = H. Otherwise it equals P(L+1,a,c) + P(L+1,a,b+1) + (q^(L+1) - 1) P(L,a,b), where c = 0 when b = 0 and c = b - 1 otherwise. This holds for every nonnegative L and every integer a.

## References

- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuPaths.pathPolynomial`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuPaths.path_last_edge_recurrence`
- Dependency: [D5/S3/Combinatorics/CylindricPartition/LiUncuExpansion](LiUncuExpansion.md)
