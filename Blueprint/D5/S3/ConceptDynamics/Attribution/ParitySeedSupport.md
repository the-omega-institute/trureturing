# A marked parity support for coordinate budgets

## Abstract

Characterize simultaneous coordinate bounds by a parity support with one marked column.

**Theorem 1.1 (Coordinate budgets at odd multiplier).**

$$(\operatorname{Even}\left(n + 2\right) \land \operatorname{Odd}\left(k\right)) \Rightarrow (\operatorname{SeedCountsWithin}\left(n, k, z\right) \Leftrightarrow \operatorname{MarkedParitySupportWithin}\left(n, k, z\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/ParitySeedSupport.binary_support_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The dimension is n plus two. Its even parity gives a full row. The odd multiplier forces a column with two odd colour masses in that row. Rows are even subsets and columns are odd subsets of the coordinates. For each coordinate the budget bounds its fixed-seed count on the same uniform equivariant seed action.

Choose a binary table and a marked column of the full row. When the marked cell has binary value zero, give it base mass two. All other base masses are their binary values. Each row and column must have odd base mass at most the multiplier.

At each coordinate, count ordinary odd cells whose two profiles contain it, and count the marked column once if it contains that coordinate. Four times this count must fit the corresponding budget.

Complete the remaining margins with even masses, using the residual row and column margins. Split the full row between its two colours with odd mass only at the marked column. In the reverse direction, a given realization supplies the marked column and a binary support whose counts fit all budgets.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/ParitySeedSupport.binary_support_iff`
- Dependency: [D5/S3/Combinatorics/Transportation/OrderedMarginAllocation](../../Combinatorics/Transportation/OrderedMarginAllocation.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParityColouredTableExtraction](ParityColouredTableExtraction.md)
- Dependency: [D5/S3/ConceptDynamics/Attribution/ParityColouredTableRealization](ParityColouredTableRealization.md)
