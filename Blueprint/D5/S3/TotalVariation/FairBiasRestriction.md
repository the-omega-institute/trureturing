# Restriction faces of the fair-bias link

## Abstract

When nonempty facets exist, the lexicographic shelling partitions the augmented signed fair-bias complex into intervals.

**Theorem 1.1 (The restriction face identifies the new subfaces).**

Lean statement: `D5/S3/TotalVariation/FairBiasRestriction.firstAt_iff_restriction_subset`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/FairBiasRestriction.firstAt_iff_restriction_subset` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Fix a finite family of binary columns and a linear order of its signed labels. In a nonempty facet B, mark each vertex whose removal leaves a subset of some earlier facet. For every subset S of B, including the empty face, B is the first containing facet exactly when S contains all the marked vertices. The shelling criterion turns any earlier occurrence of S into a one-vertex omission at B.

**Theorem 1.2 (Every subset of a facet is an augmented face).**

Lean statement: `D5/S3/TotalVariation/FairBiasRestriction.augmented_of_subset_facet`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/FairBiasRestriction.augmented_of_subset_facet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The augmented complex contains the empty face and every nonempty subset of a facet.

**Theorem 1.3 (Each augmented face has a first containing facet).**

Lean statement: `D5/S3/TotalVariation/FairBiasRestriction.exists_first_facet`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/FairBiasRestriction.exists_first_facet` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If a nonempty facet exists, every augmented face has a containing facet that precedes all other containing facets in the given signed-label order.

**Theorem 1.4 (The first containing facet is unique).**

Lean statement: `D5/S3/TotalVariation/FairBiasRestriction.first_unique`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/FairBiasRestriction.first_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Two facets that are first for the same face in the given order coincide.

**Theorem 1.5 (The face enumerator is the sum of the interval enumerators).**

Lean statement: `D5/S3/TotalVariation/FairBiasRestriction.faceEnumerator_eq_sum`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/FairBiasRestriction.faceEnumerator_eq_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the same ordered family, let d be the number of labels minus the rank of the columns. For every t in a commutative semiring, weight each face S by t to the power of its size, with the empty face included. When nonempty facets exist, sum over them the product of t raised to the size of the restriction face and (1 + t) raised to d minus that size. Otherwise the only face is empty and the sum is one.

## References

- Truth anchor: `D5/S3/TotalVariation/FairBiasRestriction.augmented_of_subset_facet`
- Truth anchor: `D5/S3/TotalVariation/FairBiasRestriction.exists_first_facet`
- Truth anchor: `D5/S3/TotalVariation/FairBiasRestriction.faceEnumerator_eq_sum`
- Truth anchor: `D5/S3/TotalVariation/FairBiasRestriction.firstAt_iff_restriction_subset`
- Truth anchor: `D5/S3/TotalVariation/FairBiasRestriction.first_unique`
- Dependency: [D5/S3/TotalVariation/FairBiasShelling](FairBiasShelling.md)
