# Finite integer rounding estimates

## Abstract

Global bounds and an exact two-candidate formula for the integer rounding gap.

Let p be a real base greater than one, λ a positive real price, and C = 1 + 1/λ. Write G for BoundaryPrimePrice.integerGap p λ, the smaller loss at the floor and ceiling of the real boundary exponent. Write u = 1/p², v = 1/p³ and w = 1/C.

**Theorem 1.1 (Two global upper bounds).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualRoundingGapEstimates.integer_gap_global_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualRoundingGapEstimates.integer_gap_global_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every such p and λ, the three simultaneous inequalities are 0 ≤ G, G ≤ λ log p and G ≤ −log(1 − u). Rounding upward costs at most one unit of price because the benefit is increasing. Rounding downward loses at most the remaining benefit beyond exponent one.

**Theorem 1.2 (Exact formula between the second and third powers).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualRoundingGapEstimates.integer_gap_chamber_identity`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualRoundingGapEstimates.integer_gap_chamber_identity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When p² < C < p³, the real exponent is strictly between one and two, so the adjacent integers are exactly one and two. The gap equals min(−log(1 − u), −log(1 − v) + λ log p) minus (−log(1 − w) + λ log(C/p²)). The minimum retains both candidates, including ties.

**Theorem 1.3 (Error of the simpler chamber profile).**

Lean statement: `D5/S3/Arith/Robin/PriceRecord/ActualRoundingGapEstimates.integer_gap_chamber_error`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/PriceRecord/ActualRoundingGapEstimates.integer_gap_chamber_error` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same strict chamber inequalities, the absolute difference between G and min(u, λ log p) is at most w/(1 − w) + λ log(C/p²) + u²/(1 − u) + v/(1 − v). The logarithmic deficit bounds control the change in each candidate and the common subtraction in the exact identity.

## References

- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualRoundingGapEstimates.integer_gap_chamber_error`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualRoundingGapEstimates.integer_gap_chamber_identity`
- Truth anchor: `D5/S3/Arith/Robin/PriceRecord/ActualRoundingGapEstimates.integer_gap_global_bounds`
- Dependency: [D5/S3/Arith/Robin/PriceRecord/BoundaryPrimePrice](BoundaryPrimePrice.md)
- Dependency: [D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel](QuantitativePrimeAbel.md)
