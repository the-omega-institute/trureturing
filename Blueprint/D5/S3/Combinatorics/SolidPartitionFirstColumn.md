# Partitions with the fewest extensions are boxes

## Abstract

In every dimension d, the d-dimensional partitions of n that extend in exactly d ways to a partition of n + 1, and the d-dimensional partitions of n + 1 that contain exactly one partition of n, are the boxes, so both are counted by the number of ordered factorizations of n, respectively n + 1, into d factors; for d = 4 these are the first columns of A098052 and A098530 on solid partitions.

**Definition 1.1 (Partitions in dimension d).**

$$\operatorname{IsSolidPartition}\left(n, I\right) \Leftrightarrow ((\forall a \in I,\; \forall b \in \mathbb{N}^{d},\; (b \le a) \Rightarrow (b \in I)) \land \left|I\right| = n)$$

*Formalization.* `D5/S3/Combinatorics/SolidPartitionFirstColumn.IsSolidPartition` (`✓ std3`).

*Citation.* Wouter Meeussen (2004). *OEIS A098052, T(n,k) counts the solid partitions of n that can be extended to a solid partition of n+1 in exactly (k+3) ways; with its twin A098530*. URL: <https://oeis.org/A098052>.

*Commentary.*

A d-dimensional partition of n is read through its Ferrers diagram: a finite set of n cells of the d-th power of the natural numbers that contains every cell below any of its cells in the coordinatewise order. For d = 4 these are the solid partitions of A000293.

**Definition 1.2 (Extensions).**

$$\operatorname{extensions}\left(n, I\right) = \left|\{J \mid \operatorname{IsSolidPartition}\left(n + 1, J\right) \land I \subseteq J\}\right|$$

*Formalization.* `D5/S3/Combinatorics/SolidPartitionFirstColumn.extensions` (`✓ std3`).

*Citation.* Wouter Meeussen (2004). *OEIS A098052, T(n,k) counts the solid partitions of n that can be extended to a solid partition of n+1 in exactly (k+3) ways; with its twin A098530*. URL: <https://oeis.org/A098052>.

*Commentary.*

The number of d-dimensional partitions of n + 1 that contain I (A098052 counts the solid partitions of n by this number).

**Definition 1.3 (Shrinkings).**

$$\operatorname{shrinkings}\left(n, J\right) = \left|\{I \mid \operatorname{IsSolidPartition}\left(n, I\right) \land I \subseteq J\}\right|$$

*Formalization.* `D5/S3/Combinatorics/SolidPartitionFirstColumn.shrinkings` (`✓ std3`).

*Citation.* Wouter Meeussen (2004). *OEIS A098052, T(n,k) counts the solid partitions of n that can be extended to a solid partition of n+1 in exactly (k+3) ways; with its twin A098530*. URL: <https://oeis.org/A098052>.

*Commentary.*

The number of d-dimensional partitions of n contained in J (A098530 counts the solid partitions of n + 1 by this number).

**Definition 1.4 (Partitions with d extensions).**

$$\operatorname{firstColumn}\left(d, n\right) = \left|\{I \mid \operatorname{IsSolidPartition}\left(n, I\right) \land \operatorname{extensions}\left(n, I\right) = d\}\right|$$

*Formalization.* `D5/S3/Combinatorics/SolidPartitionFirstColumn.firstColumn` (`✓ std3`).

*Citation.* Wouter Meeussen (2004). *OEIS A098052, T(n,k) counts the solid partitions of n that can be extended to a solid partition of n+1 in exactly (k+3) ways; with its twin A098530*. URL: <https://oeis.org/A098052>.

*Commentary.*

The number of d-dimensional partitions of n that extend in exactly d ways; for d = 4 the first column of A098052.

**Definition 1.5 (Partitions with one shrinking).**

$$\operatorname{shrinkColumn}\left(d, n\right) = \left|\{J \mid \operatorname{IsSolidPartition}\left(n + 1, J\right) \land \operatorname{shrinkings}\left(n, J\right) = 1\}\right|$$

*Formalization.* `D5/S3/Combinatorics/SolidPartitionFirstColumn.shrinkColumn` (`✓ std3`).

*Citation.* Wouter Meeussen (2004). *OEIS A098052, T(n,k) counts the solid partitions of n that can be extended to a solid partition of n+1 in exactly (k+3) ways; with its twin A098530*. URL: <https://oeis.org/A098052>.

*Commentary.*

The number of d-dimensional partitions of n + 1 that shrink in exactly one way; for d = 4 the first column of A098530.

**Definition 1.6 (Ordered factorizations into d factors).**

$$\operatorname{tau}\left(d, n\right) = \left|\{v \in \mathbb{N}^{d} \mid \prod_{i} v_{i} = n\}\right|$$

*Formalization.* `D5/S3/Combinatorics/SolidPartitionFirstColumn.tau` (`✓ std3`).

*Citation.* Wouter Meeussen (2004). *OEIS A098052, T(n,k) counts the solid partitions of n that can be extended to a solid partition of n+1 in exactly (k+3) ways; with its twin A098530*. URL: <https://oeis.org/A098052>.

*Commentary.*

The Piltz function: the number of ordered d-tuples of natural numbers whose product is n (A007426 for d = 4).

**Definition 1.7 (The first-column conjectures in every dimension).**

$$claim \Leftrightarrow (\forall d \in \mathbb{N},\; \forall n \in \mathbb{N},\; (1 \le d \land 1 \le n) \Rightarrow (\operatorname{firstColumn}\left(d, n\right) = \operatorname{tau}\left(d, n\right) \land \operatorname{shrinkColumn}\left(d, n\right) = \operatorname{tau}\left(d, n + 1\right)))$$

*Formalization.* `D5/S3/Combinatorics/SolidPartitionFirstColumn.claim` (`✓ std3`).

*Citation.* Wouter Meeussen (2004). *OEIS A098052, T(n,k) counts the solid partitions of n that can be extended to a solid partition of n+1 in exactly (k+3) ways; with its twin A098530*. URL: <https://oeis.org/A098052>.

*Commentary.*

For every d at least 1 and n at least 1, the partitions of n with exactly d extensions number tau_d(n), and the partitions of n + 1 with exactly one shrinking number tau_d(n + 1); for d = 4 these are the first-column conjectures of A098052 and A098530.

**Theorem 1.8 (Proof of the conjectures).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SolidPartitionFirstColumn.result` (`✓ std3`). ∎

*Resolves.* `Problems/meeussen-2004-solid-partition-first-column-tau4` (proved) by `D5/S3/Combinatorics/SolidPartitionFirstColumn.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"meeussen-2004-solid-partition-first-column-tau4","declaration_gid":"D5/S3/Combinatorics/SolidPartitionFirstColumn.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Wouter Meeussen (2004). *OEIS A098052, T(n,k) counts the solid partitions of n that can be extended to a solid partition of n+1 in exactly (k+3) ways; with its twin A098530*. URL: <https://oeis.org/A098052>.

*Commentary.*

For positive v the box of cells c with c_i < v_i for every i is a lower set with the product of the v_i cells, and it determines v; so boxes of n cells correspond to ordered factorizations of n into d factors. The partitions of n + 1 containing a box are exactly the box with one of the d axis cells v_i e_i added: every cell strictly below the new cell lies in the box, which forces the new cell onto an axis at distance v_i. A nonempty lower set that is not a box has a further extension: with v_i one more than its largest i-th coordinate the d axis cells can be added, and a minimal cell of the box of v outside the set can be added too. A box of n + 1 cells has exactly one partition of n inside it, obtained by removing its top cell. A lower set that is not a box has two cells with nothing of the set strictly above them, a maximal cell and a maximal cell above any cell not below that one; removing either leaves a partition of n.

## References

- Truth anchor: `D5/S3/Combinatorics/SolidPartitionFirstColumn.IsSolidPartition`
- Truth anchor: `D5/S3/Combinatorics/SolidPartitionFirstColumn.claim`
- Truth anchor: `D5/S3/Combinatorics/SolidPartitionFirstColumn.extensions`
- Truth anchor: `D5/S3/Combinatorics/SolidPartitionFirstColumn.firstColumn`
- Truth anchor: `D5/S3/Combinatorics/SolidPartitionFirstColumn.result`
- Truth anchor: `D5/S3/Combinatorics/SolidPartitionFirstColumn.shrinkColumn`
- Truth anchor: `D5/S3/Combinatorics/SolidPartitionFirstColumn.shrinkings`
- Truth anchor: `D5/S3/Combinatorics/SolidPartitionFirstColumn.tau`
