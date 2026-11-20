# Restriction faces of the fair-bias link

## Abstract

The lexicographic shelling partitions the augmented signed fair-bias complex into intervals.

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

For the same ordered family, assume at least one nonempty facet exists. Let d be the number of labels minus the rank of the columns. For every t in a commutative semiring, weight each face S by t to the power of its size, with the empty face included. The sum over all faces equals the sum over facets B of t to the size of the restriction face times one plus t to the power of d minus that size.

**Theorem 1.3 (The augmented enumerator is one when no nonempty facet exists).**

Lean statement: `D5/S3/TotalVariation/FairBiasRestriction.faceEnumerator_eq_one`

*Proof.* Machine-checked in Lean as `D5/S3/TotalVariation/FairBiasRestriction.faceEnumerator_eq_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the nonempty facet set is empty, no nonempty face can occur, since any such face would extend to a maximal one. The empty face contributes one for every choice of t.

## References

- Truth anchor: `D5/S3/TotalVariation/FairBiasRestriction.faceEnumerator_eq_one`
- Truth anchor: `D5/S3/TotalVariation/FairBiasRestriction.faceEnumerator_eq_sum`
- Truth anchor: `D5/S3/TotalVariation/FairBiasRestriction.firstAt_iff_restriction_subset`
- Dependency: [D5/S3/TotalVariation/FairBiasShelling](FairBiasShelling.md)
