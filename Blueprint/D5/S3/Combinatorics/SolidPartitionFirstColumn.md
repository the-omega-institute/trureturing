# The first columns of A098052 and A098530 are tau_4

## Abstract

The solid partitions of n that extend in exactly four ways to a solid partition of n + 1, and the solid partitions of n + 1 that contain exactly one solid partition of n, are the boxes, so both are counted by the number of ordered factorizations of n, respectively n + 1, into four factors.

**Definition 1.1 (Solid partitions).**

$$\operatorname{IsSolidPartition}\left(n, I\right) \Leftrightarrow ((\forall a \in I,\; \forall b \in \mathbb{N}^{4},\; (b \le a) \Rightarrow (b \in I)) \land \left|I\right| = n)$$

*Formalization.* `D5/S3/Combinatorics/SolidPartitionFirstColumn.IsSolidPartition` (`✓ std3`).

*Citation.* Wouter Meeussen (2004). *OEIS A098052, T(n,k) counts the solid partitions of n that can be extended to a solid partition of n+1 in exactly (k+3) ways; with its twin A098530*. URL: <https://oeis.org/A098052>.

*Commentary.*

A solid partition of n is read through its four-dimensional Ferrers diagram: a finite set of n cells of the fourth power of the natural numbers that contains every cell below any of its cells in the coordinatewise order.

**Definition 1.2 (Extensions).**

$$\operatorname{extensions}\left(n, I\right) = \left|\{J \mid \operatorname{IsSolidPartition}\left(n + 1, J\right) \land I \subseteq J\}\right|$$

*Formalization.* `D5/S3/Combinatorics/SolidPartitionFirstColumn.extensions` (`✓ std3`).

*Citation.* Wouter Meeussen (2004). *OEIS A098052, T(n,k) counts the solid partitions of n that can be extended to a solid partition of n+1 in exactly (k+3) ways; with its twin A098530*. URL: <https://oeis.org/A098052>.

*Commentary.*

The number of solid partitions of n + 1 that contain I.

**Definition 1.3 (Shrinkings).**

$$\operatorname{shrinkings}\left(n, J\right) = \left|\{I \mid \operatorname{IsSolidPartition}\left(n, I\right) \land I \subseteq J\}\right|$$

*Formalization.* `D5/S3/Combinatorics/SolidPartitionFirstColumn.shrinkings` (`✓ std3`).

*Citation.* Wouter Meeussen (2004). *OEIS A098052, T(n,k) counts the solid partitions of n that can be extended to a solid partition of n+1 in exactly (k+3) ways; with its twin A098530*. URL: <https://oeis.org/A098052>.

*Commentary.*

The number of solid partitions of n contained in J.

**Definition 1.4 (The first column of A098052).**

$$\operatorname{a098052FirstColumn}\left(n\right) = \left|\{I \mid \operatorname{IsSolidPartition}\left(n, I\right) \land \operatorname{extensions}\left(n, I\right) = 4\}\right|$$

*Formalization.* `D5/S3/Combinatorics/SolidPartitionFirstColumn.a098052FirstColumn` (`✓ std3`).

*Citation.* Wouter Meeussen (2004). *OEIS A098052, T(n,k) counts the solid partitions of n that can be extended to a solid partition of n+1 in exactly (k+3) ways; with its twin A098530*. URL: <https://oeis.org/A098052>.

*Commentary.*

The number of solid partitions of n that extend in exactly four ways.

**Definition 1.5 (The first column of A098530).**

$$\operatorname{a098530FirstColumn}\left(n\right) = \left|\{J \mid \operatorname{IsSolidPartition}\left(n + 1, J\right) \land \operatorname{shrinkings}\left(n, J\right) = 1\}\right|$$

*Formalization.* `D5/S3/Combinatorics/SolidPartitionFirstColumn.a098530FirstColumn` (`✓ std3`).

*Citation.* Wouter Meeussen (2004). *OEIS A098052, T(n,k) counts the solid partitions of n that can be extended to a solid partition of n+1 in exactly (k+3) ways; with its twin A098530*. URL: <https://oeis.org/A098052>.

*Commentary.*

The number of solid partitions of n + 1 that shrink in exactly one way.

**Definition 1.6 (Ordered factorizations into four factors).**

$$\operatorname{tau4}\left(n\right) = \left|\{v \in \mathbb{N}^{4} \mid \prod_{i} v_{i} = n\}\right|$$

*Formalization.* `D5/S3/Combinatorics/SolidPartitionFirstColumn.tau4` (`✓ std3`).

*Citation.* Wouter Meeussen (2004). *OEIS A098052, T(n,k) counts the solid partitions of n that can be extended to a solid partition of n+1 in exactly (k+3) ways; with its twin A098530*. URL: <https://oeis.org/A098052>.

*Commentary.*

A007426: the number of ordered quadruples of natural numbers whose product is n.

**Definition 1.7 (The first-column conjectures).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; (1 \le n) \Rightarrow (\operatorname{a098052FirstColumn}\left(n\right) = \operatorname{tau4}\left(n\right) \land \operatorname{a098530FirstColumn}\left(n\right) = \operatorname{tau4}\left(n + 1\right)))$$

*Formalization.* `D5/S3/Combinatorics/SolidPartitionFirstColumn.claim` (`✓ std3`).

*Citation.* Wouter Meeussen (2004). *OEIS A098052, T(n,k) counts the solid partitions of n that can be extended to a solid partition of n+1 in exactly (k+3) ways; with its twin A098530*. URL: <https://oeis.org/A098052>.

*Commentary.*

For every n at least 1 the first column of A098052 at n is the number of ordered factorizations of n into four factors, and the first column of A098530 at n is that number for n + 1.

**Theorem 1.8 (Proof of the conjectures).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/SolidPartitionFirstColumn.result` (`✓ std3`). ∎

*Resolves.* `Problems/meeussen-2004-solid-partition-first-column-tau4` (proved) by `D5/S3/Combinatorics/SolidPartitionFirstColumn.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"meeussen-2004-solid-partition-first-column-tau4","declaration_gid":"D5/S3/Combinatorics/SolidPartitionFirstColumn.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Wouter Meeussen (2004). *OEIS A098052, T(n,k) counts the solid partitions of n that can be extended to a solid partition of n+1 in exactly (k+3) ways; with its twin A098530*. URL: <https://oeis.org/A098052>.

*Commentary.*

For positive v the box of cells c with c_i < v_i for every i is a lower set with the product of the v_i cells, and it determines v; so boxes of n cells correspond to ordered factorizations of n. The solid partitions of n + 1 containing a box are exactly the box with one of the four axis cells v_i e_i added: every cell strictly below the new cell lies in the box, which forces the new cell onto an axis at distance v_i. A nonempty lower set that is not a box has a fifth extension: with v_i one more than its largest i-th coordinate the four axis cells can be added, and the cell of least coordinate sum in the box of v outside the set can be added too. A box of n + 1 cells has exactly one solid partition of n inside it, obtained by removing its top cell. A lower set that is not a box has two cells with nothing of the set strictly above them, the cell of largest coordinate sum and, above any cell not below that one, the cell of largest coordinate sum; removing either leaves a solid partition of n.

## References

- Truth anchor: `D5/S3/Combinatorics/SolidPartitionFirstColumn.IsSolidPartition`
- Truth anchor: `D5/S3/Combinatorics/SolidPartitionFirstColumn.a098052FirstColumn`
- Truth anchor: `D5/S3/Combinatorics/SolidPartitionFirstColumn.a098530FirstColumn`
- Truth anchor: `D5/S3/Combinatorics/SolidPartitionFirstColumn.claim`
- Truth anchor: `D5/S3/Combinatorics/SolidPartitionFirstColumn.extensions`
- Truth anchor: `D5/S3/Combinatorics/SolidPartitionFirstColumn.result`
- Truth anchor: `D5/S3/Combinatorics/SolidPartitionFirstColumn.shrinkings`
- Truth anchor: `D5/S3/Combinatorics/SolidPartitionFirstColumn.tau4`
