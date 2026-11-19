# Geometric singleton columns and the root floor condition

## Abstract

The source root filter is equivalent to geometric uniqueness of a partial column in each level.

**Definition 1.1 (The geometric singleton condition).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookRootCriterion.SingletonColumns`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookRootCriterion.SingletonColumns` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each pair of column positions i and j, if both heights have nonzero remainder modulo m and their natural quotients by m agree, then i=j. A nonzero remainder means the column ends strictly inside that level; full and zero columns are excluded from partial tops. Thus every level has at most one partially filled column. This criterion concerns actual column heights, not an ordering of root labels.

**Definition 1.2 (Integer roots).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookRootCriterion.root`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookRootCriterion.root` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At zero-based position i the root is mi minus the column height. Arithmetic takes place in the integers, so negative roots are retained.

**Definition 1.3 (The original conditional floor test).**

Lean statement: `D5/S3/Combinatorics/Partitions/RookRootCriterion.RootFloorCriterion`

*Formalization.* `D5/S3/Combinatorics/Partitions/RookRootCriterion.RootFloorCriterion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At adjacent positions i,j with j=i+1, impose root(j)/m at most root(i)/m only if neither root is divisible by m. Integer Euclidean division is floor division for positive m. Multiplying those quotients by positive m gives the source m-floor version with the same inequality direction.

**Theorem 1.4 (Exact criterion for every padded Ferrers tuple).**

$$\forall m \in Nat,\; 0 < m \Rightarrow \left(\forall n \in Nat,\; \forall d \in \operatorname{Fin}\left(n\right) \to Nat,\; \operatorname{Monotone}\left(d\right) \Rightarrow \left(\operatorname{RootFloorCriterion}\left(m, \operatorname{root}\left(m, d\right)\right) \Leftrightarrow \operatorname{SingletonColumns}\left(m, d\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Partitions/RookRootCriterion.rootFloorCriterion_iff_singleton` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Kenneth Barrese, Nicholas Loehr, Jeffrey Remmel, Bruce E. Sagan (2013). *m-level rook placements*. URL: <https://arxiv.org/abs/1308.4081v1>.

*Commentary.*

For every positive m and every weakly increasing nonnegative padded tuple d, the root floor test is equivalent to SingletonColumns. This is the conditional geometric clause of Proposition 4.4 of Barrese, Loehr, Remmel and Sagan, arXiv:1308.4081v1, with the nonnegative Ferrers columns supplied explicitly. For a partial column, floor((mi-d(i))/m)=i-floor(d(i)/m)-1. The adjacent root inequality therefore forces a strict increase in the partial-top level. If two separated partial columns had the same level, monotonicity would put their intervening successor in that same level and contradict the adjacent condition. Conversely, geometric uniqueness forces every adjacent pair of partial tops into different levels. Zero padding and an empty index type need no exceptions. RookClassCandidate.rookEquivalent_iff_seedRoots identifies equality of all native rook counts with equality of the complete seed-root multisets at a common length at least one greater than each board’s area.

## References

- Truth anchor: `D5/S3/Combinatorics/Partitions/RookRootCriterion.RootFloorCriterion`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookRootCriterion.SingletonColumns`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookRootCriterion.root`
- Truth anchor: `D5/S3/Combinatorics/Partitions/RookRootCriterion.rootFloorCriterion_iff_singleton`
- Dependency: [D5/S3/Combinatorics/Partitions/RookClassNative](RookClassNative.md)
