# Peak Deletion and Insertion

## Abstract

Deleting up-down pairs gives a bijection between words and insertion data and lowers the height bound of paths.

**Definition 1.1 (The path alphabet).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.Step`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.Step` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

The alphabet consists of an up edge, a down edge, and a horizontal edge.

**Definition 1.2 (Deletion data).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.peakData`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.peakData` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

Scan a word from left to right and delete every adjacent up-down pair. The output consists of the remaining word, the number of deleted pairs before its first edge, and a list of multiplicities at successive vertices after that edge. Consecutive deleted pairs occupy the same insertion slot.

**Definition 1.3 (Insertion at successive vertices).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.insertPeaks`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.insertPeaks` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

Given a word, an initial multiplicity t, and a list of successive multiplicities, insert t up-down pairs before its first edge and continue recursively at later vertices. At the empty word insert only the initial pairs. For a nonempty word and an empty list, insert the initial pairs followed by its first edge.

**Definition 1.4 (Permitted insertion data).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.Insertible`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.Insertible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

The list of multiplicities must have one entry for each edge of the remaining word. Every vertex between an up edge and a following down edge must receive a positive number of inserted pairs. The initial multiplicity has no additional restriction.

**Definition 1.5 (The peak-abscissa weight).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.peakWeight`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.peakWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For a word starting at horizontal coordinate offset, the weight is the sum of horizontal coordinates of vertices between adjacent up and down edges. A deleted up-down pair contributes offset + 1, and scanning then continues two coordinates later.

**Theorem 1.6 (Deletion and insertion are inverse).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.peak_deletion_bijection`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.peak_deletion_bijection` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

There is a bijection from all words to triples consisting of a remaining word q, an initial multiplicity t, and a list ts satisfying Insertible. Its forward map is peakData and its inverse is insertPeaks. With N = t + sum(ts), the inserted word has length length(q) + 2N and peak weight N^2 plus the sum of j times the jth entry of ts, with j starting at one.

**Definition 1.7 (Paths in the bounded strip).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.ValidPath`

*Formalization.* `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.ValidPath` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

A valid path starts at integer height a, ends at integer height b, and stays between zero and the nonnegative bound H. Up and down edges change height by one. Horizontal edges occur only at height zero. The empty word is valid precisely when a = b and a lies between zero and H.

**Theorem 1.8 (Lowering the ceiling at interior endpoints).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.peak_deletion_interior`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.peak_deletion_interior` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For H at least one, if a valid path has both endpoints strictly below H, deleting all adjacent up-down pairs leaves a valid path with the same endpoints and height bound H - 1.

**Theorem 1.9 (Deletion at ceiling endpoints).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.peak_deletion_ceiling`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.peak_deletion_ceiling` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For H at least one, a nonempty valid path from H to H has deletion data (down followed by q followed by up, 0, t followed by ts followed by 0). The word q is a valid path from H - 1 to H - 1 with height bound H - 1, and its insertion data t and ts satisfy Insertible.

**Theorem 1.10 (Raising the ceiling by insertion).**

Lean statement: `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.peak_insertion_valid`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.peak_insertion_valid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Runqiao Li, Ali K. Uncu (2025). *A MacMahon Analysis View of Cylindric Partitions*. DOI: [10.48550/arXiv.2501.19272](https://doi.org/10.48550/arXiv.2501.19272). URL: <https://arxiv.org/abs/2501.19272v1>.

*Commentary.*

For H at least one, inserting peaks with data satisfying Insertible into a valid path with height bound H - 1 gives a valid path with height bound H and the same endpoints.

## References

- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.Insertible`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.Step`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.ValidPath`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.insertPeaks`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.peakData`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.peakWeight`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.peak_deletion_bijection`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.peak_deletion_ceiling`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.peak_deletion_interior`
- Truth anchor: `D5/S3/Combinatorics/CylindricPartition/LiUncuDeletion.peak_insertion_valid`
- Dependency: [D5/S3/Combinatorics/CylindricPartition/LiUncuRectangle](LiUncuRectangle.md)
