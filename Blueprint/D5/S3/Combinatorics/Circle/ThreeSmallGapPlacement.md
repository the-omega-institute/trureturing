# Three-small block placement in the sixfold normalization

## Abstract

Exact placement of three same-sign SMALL gap blocks

**Theorem 1.1 (The one-block schedule).**

Lean statement: `D5/S3/Combinatorics/Circle/ThreeSmallGapPlacement.one_block`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ThreeSmallGapPlacement.one_block` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For one nonempty LARGE gap, the explicit schedule places the three distinguished positions and every consecutive pair. The pair valleys and peaks stay within the scaled strip, the total is zero, and deleting the three SMALL positions leaves the forward LARGE range.

**Theorem 1.2 (The two-block insertion schedules).**

Lean statement: `D5/S3/Combinatorics/Circle/ThreeSmallGapPlacement.two_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ThreeSmallGapPlacement.two_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For two nonempty LARGE gaps, the cut selected from the two endpoint deficits gives a complete permutation with zero total and every prefix in the scaled strip. The proof covers both orderings of the two deficits, including the corrected intermediate peak bound, and deletes exactly the three SMALL positions.

**Theorem 1.3 (The three-block insertion schedule).**

Lean statement: `D5/S3/Combinatorics/Circle/ThreeSmallGapPlacement.three_blocks`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ThreeSmallGapPlacement.three_blocks` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For three nonempty LARGE gaps, the least admissible Y cut and the aligned Z cut place the three SMALL positions between complete pair blocks. The geometric valley and peak inequalities certify every prefix, endpoint equations certify zero total, and the deleted LARGE arcs remain in forward order.

These placement lemmas are consumed by the native exactly-three same-sign SMALL completion. They retain physical labels, so repeated numerical values, nonunits and proper numerical periods remain within the stated hypotheses.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/ThreeSmallGapPlacement.one_block`
- Truth anchor: `D5/S3/Combinatorics/Circle/ThreeSmallGapPlacement.three_blocks`
- Truth anchor: `D5/S3/Combinatorics/Circle/ThreeSmallGapPlacement.two_blocks`
- Dependency: [D5/S3/Combinatorics/Circle/TwoSmallSource](TwoSmallSource.md)
