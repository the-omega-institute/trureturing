# Weighted Peak-Insertion Sums

## Abstract

Insertion vectors enumerate finite sets of paths with exact Gaussian weights.

**Definition 1.1 (Mandatory insertion at a peak).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuPathSums.peakRequirement`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuPathSums.peakRequirement` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For a word q and a vertex index j counted from zero, the requirement is one precisely when the vertex lies between an up edge and the immediately following down edge. It is zero at all other indices, including indices outside the word.

**Definition 1.2 (Words with a prescribed insertion total).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuPathSums.insertionWords`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuPathSums.insertionWords` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

At the length(q) + 1 vertices of q, insert a total of N up-down pairs using nonnegative multiplicities at most N, with a positive multiplicity at every old peak. The resulting finite set contains the inserted words. When the boundary parameter is true, a down edge is added at the beginning and an up edge at the end.

**Theorem 1.3 (The weighted insertion formula).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuPathSums.peak_deletion_weighted_sum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CylindricPartition/LiUncuPathSums.peak_deletion_weighted_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

Let S be any finite set of words, let N and offset be nonnegative integers, and put beta = 1 for a true boundary parameter and beta = 0 otherwise. For each word v in S, let C(v) be the number of peaks deleted by peakData. The sum of q raised to peakWeight(offset,w) over the union of insertionWords(v,N,boundary) equals q^(N^2 + (offset+beta)N) times the sum over v in S of q^peakWeight(0,v) G(length(v)+N-C(v),N-C(v)) when C(v) is at most N, and zero otherwise.

## References

- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuPathSums.insertionWords`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuPathSums.peakRequirement`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuPathSums.peak_deletion_weighted_sum`
- Dependency: [D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion](LiUncuDeletion.md)
