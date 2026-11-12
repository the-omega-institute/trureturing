# FixedGapGrowth

## Abstract

Stable partial matchings and the Mertens range-two probability estimate.

**Theorem 1.1 (additive_defect_bounds).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/FixedGapGrowth.additive_defect_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/FixedGapGrowth.additive_defect_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed-gap logarithmic lemma is conditional infrastructure, not the Mertens result. Mathlib Fekete supplies convergence for the original subadditive sequence and its negative plus the additive defect. Their limits differ by a sign because a constant divided by length tends to zero. Bounds hold at every natural length, including zero. GrowthTransfer applies these estimates to logarithms of the actual profile counts using the proved padded concatenation inequality.

**Theorem 1.2 (fixed_gap_log_bounds).**

Lean statement: `D5/S3/Combinatorics/Graph/Roommates/FixedGapGrowth.fixed_gap_log_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/FixedGapGrowth.fixed_gap_log_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The fixed-gap logarithmic lemma is conditional infrastructure, not the Mertens result. Mathlib Fekete supplies convergence for the original subadditive sequence and its negative plus the additive defect. Their limits differ by a sign because a constant divided by length tends to zero. Bounds hold at every natural length, including zero. GrowthTransfer applies these estimates to logarithms of the actual profile counts using the proved padded concatenation inequality.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/FixedGapGrowth.additive_defect_bounds`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/FixedGapGrowth.fixed_gap_log_bounds`
