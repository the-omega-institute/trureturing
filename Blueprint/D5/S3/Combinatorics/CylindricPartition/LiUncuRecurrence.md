# Refined Path Polynomials and Deletion

## Abstract

Counting paths by deleted peaks yields a primed Gaussian recurrence, including negative virtual lengths.

**Definition 1.1 (All words of a fixed length).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuRecurrence.pathWords`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuRecurrence.pathWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For every nonnegative integer L, pathWords(L) is the finite set of all length-L words over the up, down, and horizontal alphabet. The length-zero set contains only the empty word.

**Definition 1.2 (The refined diagonal path sum).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuRecurrence.refinedPathSum`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuRecurrence.refinedPathSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For nonnegative H and N and integers a and L, a nonnegative L gives the sum of q raised to peakWeight(0,w) over valid length-L paths from a to a with height bound H and exactly N pairs removed by peakData. For negative L, the value is one when N = 0 and zero otherwise.

**Theorem 1.3 (The primed Gaussian deletion recurrence).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuRecurrence.path_deletion_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CylindricPartition/LiUncuRecurrence.path_deletion_recurrence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

Let H be at least one, let a be an integer between zero and H, let L be an even integer, and let N be nonnegative. Put beta = 1 when a = H and beta = 0 otherwise, and Lprime = L - 2N - 2beta. Then refinedPathSum(H,a,L,N) equals q^(N^2+beta N) times the sum, for s from zero through N, of the primed Gaussian polynomial with upper index Lprime + N - s and lower index N - s, multiplied by refinedPathSum(H-1,a-beta,Lprime,s).

**Theorem 1.4 (The height-zero value).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuRecurrence.path_zero_height`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CylindricPartition/LiUncuRecurrence.path_zero_height` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For every integer L and nonnegative integer N, refinedPathSum(0,0,L,N) is one when N = 0 and zero otherwise. For nonnegative L the sole path is the horizontal word; negative L uses the same virtual value.

## References

- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuRecurrence.pathWords`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuRecurrence.path_deletion_recurrence`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuRecurrence.path_zero_height`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuRecurrence.refinedPathSum`
- Dependency: [D5/S3/Combinatorics/CylindricPartition/LiUncuPathSums](LiUncuPathSums.md)
