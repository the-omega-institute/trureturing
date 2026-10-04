# Gaussian Enumeration of Rectangles

## Abstract

Gaussian polynomials enumerate weakly decreasing tuples by their total size.

**Theorem 1.1 (The rectangle enumerator).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuRectangle.gauss_rectangle`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CylindricPartition/LiUncuRectangle.gauss_rectangle` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For all nonnegative integers M and m, G(M+m,m) is the sum of q raised to the sum of the entries over all weakly decreasing tuples of m entries between zero and M. Thus it enumerates partitions contained in a rectangle of width M and height m.

## References

- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuRectangle.gauss_rectangle`
- Dependency: [D5/S3/Combinatorics/CylindricPartition/LiUncuGaussian](LiUncuGaussian.md)
