# Gaussian Recurrences and Symmetry

## Abstract

Gaussian polynomials satisfy support, complementary-index, and rim identities.

**Theorem 1.1 (Vanishing above the upper index).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuGaussian.gauss_zero_of_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CylindricPartition/LiUncuGaussian.gauss_zero_of_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For nonnegative integers a and b with a less than b, G(a,b) = 0.

**Theorem 1.2 (The second Gaussian recurrence).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuGaussian.gauss_pascal_dual`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CylindricPartition/LiUncuGaussian.gauss_pascal_dual` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For all nonnegative integers a and b, G(a+1,b+1) = q^(b+1) G(a,b+1) + G(a,b).

**Theorem 1.3 (Complementary lower indices).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuGaussian.gauss_symmetry`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CylindricPartition/LiUncuGaussian.gauss_symmetry` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For nonnegative integers a and b with b at most a, G(a,b) = G(a,a-b).

**Theorem 1.4 (The rim identity).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuGaussian.gauss_hook`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CylindricPartition/LiUncuGaussian.gauss_hook` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For nonnegative integers a and b with b at most a, (1 - q^(a-b)) G(a,b) = (1 - q^a) G(a-1,b). Subtraction of natural indices is truncated at zero.

## References

- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuGaussian.gauss_hook`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuGaussian.gauss_pascal_dual`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuGaussian.gauss_symmetry`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuGaussian.gauss_zero_of_lt`
- Dependency: [D5/S3/Combinatorics/CylindricPartition/LiUncuDefs](LiUncuDefs.md)
