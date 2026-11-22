# SupportedBooleanCycles

## Abstract

Tables are arbitrary Boolean functions on two independently universed finite labeled carriers. Supported means that each true cell lies in the allowed relation E. SameMargins equates every individually indexed row and column true-count. The distance is the number of cells at which the two tables disagree.

**Theorem 1.1 (One supported conformal cycle flip).**

Lean statement: `D5/S3/Combinatorics/Transportation/SupportedBooleanCycles.correcting_step`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Transportation/SupportedBooleanCycles.correcting_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For distinct supported tables M and B with equal labeled margins, correcting_step produces a supported table N and a simple alternating cycle with k at least two. Its flip preserves every row and column count, fixes all cells outside the cycle, and corrects every changed cell to its target value. The exact distance identity is distance N B plus twice k equals distance M B.

**Theorem 1.2 (A bounded finite chain to the target).**

Lean statement: `D5/S3/Combinatorics/Transportation/SupportedBooleanCycles.bounded_conformal_chain`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Transportation/SupportedBooleanCycles.bounded_conformal_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any supported endpoints A and B with equal labeled margins, bounded_conformal_chain constructs a finite Chain from A to B with at most distance A B divided by four steps. Each step corrects all its changed cells, so no cell changes twice. Strong induction on distance uses correcting_step in the unequal case; equality gives the zero-step chain, including empty carriers.

A Cycle has length k at least two and injective row and column maps from Fin k. The red matching pairs row i with column i; the blue matching pairs row i with the cyclic successor column. LegalStep allows either alternating polarity, requires both matchings inside E and opposite target bits, and sets the next table equal to the actual Boolean flip on their union. All external cells are fixed.

The two matchings are disjoint because their current bits are opposite. Their union therefore has exactly twice k distinct cells. Flipping corrects each selected disagreement. Each used row loses and gains one true cell, and the inverse cyclic permutation gives the same statement for every used column. The next table is supported and its distance plus twice k equals the old distance.

Chain is an inductive finite sequence with final node B. Its zero-step constructor starts and ends at B; its step constructor records the starting support, the complete individual margins and an actual LegalStep followed by the remaining chain. Strong induction on distance constructs a chain of n steps with n at most distance divided by four.

Every selected cell becomes equal to B and every correct cell is fixed, so a cell cannot change twice. Empty carriers and identical endpoints use the zero-step constructor. The allowed relation has no ordering, nesting, completeness, positivity, dimension or supplied decomposition assumption. The simple disagreement cycle supplies the flip, and its minimum of four cells gives the chain bound.

## References

- Truth anchor: `D5/S3/Combinatorics/Transportation/SupportedBooleanCycles.bounded_conformal_chain`
- Truth anchor: `D5/S3/Combinatorics/Transportation/SupportedBooleanCycles.correcting_step`
- Dependency: [D5/S3/Combinatorics/Transportation/FerrersIntegerRectanglePaths](FerrersIntegerRectanglePaths.md)
- Dependency: [D5/S3/Combinatorics/Transportation/SupportedCycleSupplier](SupportedCycleSupplier.md)
