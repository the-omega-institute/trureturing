# Avoiding all local collisions

## Abstract

A marked edge-labeling avoiding every incident additive triple makes the cubic graph additively rigid.

**Theorem 1.1 (A finite union bound).**

Lean statement: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphUnion.arGraph_of_bad_sum_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphUnion.arGraph_of_bad_sum_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the total cardinality of the bad vertex events is smaller than the marked sample space, one labeling avoids them all.

**Theorem 1.2 (Strict factorial margin).**

Lean statement: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphUnion.sum_bad_card_lt`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphUnion.sum_bad_card_lt` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For at least twelve edges, the common marked endpoint, the two other marked endpoints, and the remaining vertices together have total bad-event bound below the sample-space factorial.

## References

- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphUnion.arGraph_of_bad_sum_lt`
- Truth anchor: `D5/S3/Combinatorics/EdgeLabeling/CubicARGraphUnion.sum_bad_card_lt`
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/CubicARGraphArithmetic](CubicARGraphArithmetic.md)
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/CubicARGraphLabeling](CubicARGraphLabeling.md)
- Dependency: [D5/S3/Combinatorics/EdgeLabeling/CubicARGraphMarkedEvents](CubicARGraphMarkedEvents.md)
