# The four-column normal-form space

## Abstract

The normal-form carrier has exactly one element. The allowable permutation subgroup has eight elements and its permutation action on that carrier has singleton image.

**Definition 1.1 (The unique four-column matrix).**

Lean statement: `D5/S3/Geometry/Polygons/KozakiKakeiFourNormal.fourNormal`

*Formalization.* `D5/S3/Geometry/Polygons/KozakiKakeiFourNormal.fourNormal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Its rows are (0,1,1,1) and (−1,0,1,2).

**Theorem 1.2 (Four-column singleton normal form).**

Lean statement: `D5/S3/Geometry/Polygons/KozakiKakeiFourNormal.normalized_four_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/KozakiKakeiFourNormal.normalized_four_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The closing minor forces the last upper entry to be one, and the last consecutive minor forces the last lower entry to be two. The displayed matrix satisfies every nonvanishing and normalization condition.

**Theorem 1.3 (Eight allowable column permutations).**

Lean statement: `D5/S3/Geometry/Polygons/KozakiKakeiFourNormal.allowable_four_card`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Polygons/KozakiKakeiFourNormal.allowable_four_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The four rotations and four reflections correspond bijectively to a start column and a Boolean choice of orientation. Evaluation at zero determines the start and evaluation at one distinguishes the orientations. Each of the eight induces the identity on the one-point carrier.

## References

- Truth anchor: `D5/S3/Geometry/Polygons/KozakiKakeiFourNormal.allowable_four_card`
- Truth anchor: `D5/S3/Geometry/Polygons/KozakiKakeiFourNormal.fourNormal`
- Truth anchor: `D5/S3/Geometry/Polygons/KozakiKakeiFourNormal.normalized_four_iff`
- Dependency: [D5/S3/Geometry/KozakiKakeiConjecture13](../KozakiKakeiConjecture13.md)
