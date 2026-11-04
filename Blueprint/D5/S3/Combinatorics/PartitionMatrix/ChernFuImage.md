# Improper partition matrices and alphabet gaps

## Abstract

The fixed Claesson-Dukes-Kubitzke image of improper partition matrices is characterized by the gaps in the whole alphabet of an inversion sequence.

**Definition 1.1 (Native partition matrices).**

Lean statement: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.NativePM`

*Formalization.* `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.NativePM` (`✓ std3`).

*Citation.* Shane Chern, Shishuo Fu (2026). *Signed counting of partition matrices*. DOI: [10.48550/arXiv.2508.21318](https://doi.org/10.48550/arXiv.2508.21318). URL: <https://arxiv.org/abs/2508.21318v2>.

*Commentary.*

For arbitrary natural numbers n and k, a native matrix is a k by k matrix of finite subsets of [n]. Each label belongs to exactly one cell, every row and column is nonempty, cells below the diagonal are empty, and smaller labels have weakly smaller column indices. Lean represents native label i by the element i - 1 of Fin n, and numbers rows and columns from zero.

**Definition 1.2 (Coordinates of every label).**

Lean statement: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.Coordinates`

*Formalization.* `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.Coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shane Chern, Shishuo Fu (2026). *Signed counting of partition matrices*. DOI: [10.48550/arXiv.2508.21318](https://doi.org/10.48550/arXiv.2508.21318). URL: <https://arxiv.org/abs/2508.21318v2>.

*Commentary.*

A coordinate representation consists of a row map and a column map from Fin n to Fin k. Both maps are onto, the row of each label is at most its column, and the column map is monotone. There is no restriction involving improperness or an inversion-sequence criterion.

**Definition 1.3 (Faithful set-entry correspondence).**

Lean statement: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.nativeEquiv`

*Formalization.* `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.nativeEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shane Chern, Shishuo Fu (2026). *Signed counting of partition matrices*. DOI: [10.48550/arXiv.2508.21318](https://doi.org/10.48550/arXiv.2508.21318). URL: <https://arxiv.org/abs/2508.21318v2>.

*Commentary.*

At each n and k, native matrices and coordinate representations correspond bijectively. A matrix gives each label its unique cell. Conversely, cell (r,c) is the fiber of the coordinate pair (r,c). Both composites are identities, so all native cells, dimensions, empty cells and label positions are preserved.

**Definition 1.4 (The labels in a column).**

Lean statement: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.column`

*Formalization.* `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.column` (`✓ std3`).

*Citation.* Shane Chern, Shishuo Fu (2026). *Signed counting of partition matrices*. DOI: [10.48550/arXiv.2508.21318](https://doi.org/10.48550/arXiv.2508.21318). URL: <https://arxiv.org/abs/2508.21318v2>.

*Commentary.*

A column consists of the labels belonging to some cell in that column. Unique cell membership makes its cardinality equal to the sum of the cardinalities of its cells. Shifting between native labels and Fin n preserves cardinalities.

**Definition 1.5 (The fixed column-cardinality map).**

Lean statement: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.fixedPi`

*Formalization.* `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.fixedPi` (`✓ std3`).

*Citation.* Shane Chern, Shishuo Fu (2026). *Signed counting of partition matrices*. DOI: [10.48550/arXiv.2508.21318](https://doi.org/10.48550/arXiv.2508.21318). URL: <https://arxiv.org/abs/2508.21318v2>.

*Commentary.*

For each native label t, Pi(P) at t is the sum of the cardinalities of all columns strictly before row_P(t). The summands are column cardinalities. Row zero gives the empty sum. For an arbitrary native matrix, monotonicity makes the labels before a column an initial segment; thus this sum is the least native label of the column indexed by row_P(t), minus one.

**Definition 1.6 (The entire alphabet).**

Lean statement: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.alphabet`

*Formalization.* `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.alphabet` (`✓ std3`).

*Citation.* Anders Claesson, Mark Dukes, Martina Kubitzke (2011). *Partition and composition matrices*. DOI: [10.48550/arXiv.1006.1312](https://doi.org/10.48550/arXiv.1006.1312). URL: <https://arxiv.org/abs/1006.1312v2>.

*Commentary.*

For a function e on Fin n, A(e) is the set of all values e(t) for every t in Fin n. For a list of length n, this ranges over every list position, not a prefix.

**Definition 1.7 (The previous occurring value).**

Lean statement: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.previous`

*Formalization.* `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.previous` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shane Chern, Shishuo Fu (2026). *Signed counting of partition matrices*. DOI: [10.48550/arXiv.2508.21318](https://doi.org/10.48550/arXiv.2508.21318). URL: <https://arxiv.org/abs/2508.21318v2>.

*Commentary.*

For a natural number i, b_e(i) is the maximum of the set containing zero and all values in A(e) strictly less than i. Finset.sup includes zero even when there is no such occurring value. For an inversion sequence of positive length, zero occurs, and b_e(i) belongs to A(e) whenever i is positive.

**Definition 1.8 (The gap condition).**

Lean statement: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.Phi`

*Formalization.* `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.Phi` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Shane Chern, Shishuo Fu (2026). *Signed counting of partition matrices*. DOI: [10.48550/arXiv.2508.21318](https://doi.org/10.48550/arXiv.2508.21318). URL: <https://arxiv.org/abs/2508.21318v2>.

*Commentary.*

For every native index i with 1 <= i < n, if i does not belong to the whole alphabet A(e) and i - b_e(i) is odd, then e_i = e_(i+1). In Lean i is j.val + 1, and the two entries are at Fin indices j and j.val + 1. When n = 1 there is no adjacent index, so the condition is vacuous.

**Definition 1.9 (The least native label).**

Lean statement: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.columnLeast`

*Formalization.* `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.columnLeast` (`✓ std3`).

*Citation.* Shane Chern, Shishuo Fu (2026). *Signed counting of partition matrices*. DOI: [10.48550/arXiv.2508.21318](https://doi.org/10.48550/arXiv.2508.21318). URL: <https://arxiv.org/abs/2508.21318v2>.

*Commentary.*

The least label of a column is its least Fin n index plus one. Native nonempty-column validity makes the minimum defined. Proper parity is therefore measured against a native label, rather than against a list index.

**Definition 1.10 (Absence of proper ascents and descents).**

Lean statement: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.Improper`

*Formalization.* `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.Improper` (`✓ std3`).

*Citation.* Shane Chern, Shishuo Fu (2026). *Signed counting of partition matrices*. DOI: [10.48550/arXiv.2508.21318](https://doi.org/10.48550/arXiv.2508.21318). URL: <https://arxiv.org/abs/2508.21318v2>.

*Commentary.*

For every adjacent native pair i,i+1, neither strict row order in a common column may have i congruent modulo two to the least label of that column. The two row orders cover ascents and descents. Two labels in the same cell have equal rows and are neither an ascent nor a descent.

**Definition 1.11 (The CDK reconstruction).**

Lean statement: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.reconstruct`

*Formalization.* `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.reconstruct` (`✓ std3`).

*Citation.* Anders Claesson, Mark Dukes, Martina Kubitzke (2011). *Partition and composition matrices*. DOI: [10.48550/arXiv.1006.1312](https://doi.org/10.48550/arXiv.1006.1312). URL: <https://arxiv.org/abs/1006.1312v2>.

*Commentary.*

Let A(e) = {y_1 < ... < y_k} and append y_(k+1) = n. Row r consists of labels t with e_t = y_r, and column c consists of labels y_c < t <= y_(c+1). Equivalently, the row of t is the rank of e_t, and its column is the rank of b_e(t). The inversion bounds alone ensure upper triangularity, nonempty rows and columns, unique membership and monotone column indices. The least label of column c is y_c + 1, so the fixed Pi sends this native matrix back to e. No gap-condition assumption is used to make the matrix valid.

**Theorem 1.12 (The complete image characterization).**

$$\forall n \in \mathbb{N}, \forall e \in \operatorname{List}(\mathbb{N}), (1 \le n \land \operatorname{length}(e) = n \land \operatorname{IsInversionSeq}(e)) \Rightarrow ((\exists k \in \mathbb{N}, \exists P \in \operatorname{NativePM}(n, k), \operatorname{Improper}(P) \land \operatorname{fixedPi}(P) = \operatorname{entries}(e, n)) \Leftrightarrow \operatorname{Phi}(\operatorname{entries}(e, n)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.result` (`✓ std3`). ∎

*Resolves.* `Problems/chern-fu-improper-partition-matrix-fixed-image` (proved) by `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chern-fu-improper-partition-matrix-fixed-image","declaration_gid":"D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Shane Chern, Shishuo Fu (2026). *Signed counting of partition matrices*. DOI: [10.48550/arXiv.2508.21318](https://doi.org/10.48550/arXiv.2508.21318). URL: <https://arxiv.org/abs/2508.21318v2>.

*Commentary.*

In the formula, entries(e,n) denotes the function on Fin n sending t to e.getD t.val 0. For every natural n >= 1 and every list e of length n satisfying 0 <= e_i <= i - 1 at all native indices, e is the fixed Pi image of an improper native partition matrix, of some dimension k with no dimension restriction, if and only if Phi(e). In every native matrix, equal adjacent columns are equivalent to i not occurring in A(Pi(P)); the preceding value b_(Pi(P))(i) is the least label in that column minus one. The two row indices agree exactly when the corresponding Pi entries agree. Proper parity becomes oddness of i - b_(Pi(P))(i), so absence of both proper row orders gives precisely Phi. Conversely, the CDK reconstruction is a valid native matrix for every inversion sequence; Phi makes this matrix improper, and its fixed Pi image is e.

## References

- Truth anchor: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.Coordinates`
- Truth anchor: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.Improper`
- Truth anchor: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.NativePM`
- Truth anchor: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.Phi`
- Truth anchor: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.alphabet`
- Truth anchor: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.column`
- Truth anchor: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.columnLeast`
- Truth anchor: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.fixedPi`
- Truth anchor: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.nativeEquiv`
- Truth anchor: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.previous`
- Truth anchor: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.reconstruct`
- Truth anchor: `D5/S3/Combinatorics/PartitionMatrix/ChernFuImage.result`
- Dependency: [D5/S3/Combinatorics/InversionSeq/InversionSeqDefs](../InversionSeq/InversionSeqDefs.md)
