# Restriction faces of the fair-bias link

## Abstract

When nonempty facets exist, the lexicographic shelling partitions the augmented signed fair-bias complex into intervals.

**Theorem 1.1 (The restriction face identifies the new subfaces).**

Lean statement: `D5/S3/TotalVariation/FairBiasRestriction.firstAt_iff_restriction_subset`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/FairBiasRestriction.firstAt_iff_restriction_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a finite family of binary columns and a linear order of its signed labels. In a nonempty facet B, mark each vertex whose removal leaves a subset of some earlier facet. For every subset S of B, including the empty face, B is the first containing facet exactly when S contains all the marked vertices. The shelling criterion turns any earlier occurrence of S into a one-vertex omission at B.

**Theorem 1.2 (The face enumerator is the sum of the interval enumerators).**

Lean statement: `D5/S3/TotalVariation/FairBiasRestriction.faceEnumerator_eq_sum`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/FairBiasRestriction.faceEnumerator_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same ordered family, let d be the number of labels minus the rank of the columns. For every t in a commutative semiring, weight each face S by t to the power of its size, with the empty face included. When nonempty facets exist, sum over them the product of t raised to the size of the restriction face and (1 + t) raised to d minus that size. Otherwise the only face is empty and the sum is one.

## References

- Truth anchor: `D5/S3/TotalVariation/FairBiasRestriction.faceEnumerator_eq_sum`
- Truth anchor: `D5/S3/TotalVariation/FairBiasRestriction.firstAt_iff_restriction_subset`
- Dependency: [D5/S3/TotalVariation/FairBiasShelling](FairBiasShelling.md)
