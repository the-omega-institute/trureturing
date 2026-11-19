# Ordered-cone joint lift preparation

## Abstract

Private arithmetic and schedule lemmas for the ordered-cone joint lift

The endpoint proof uses these private helpers to verify the floor mask, the signed heights at the three negative labels, and the zero total for the doubled source.

**Lemma 1.1 (Prefix bounds from the physical schedule).**

Lean statement: `D5/S3/Combinatorics/Circle/ThreeNegativeOrderedConeJointLift/Preparation.ordered_schedule`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ThreeNegativeOrderedConeJointLift/Preparation.ordered_schedule` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a word with three negative steps, the helper applies the equal-outer source bridge to the given permutation, nonnegative blocks, seam bounds, and zero total. Every prefix then lies in the strip of heights from zero to the specified capacity.

**Lemma 1.2 (Lower bound from the floor remainder).**

Lean statement: `D5/S3/Combinatorics/Circle/ThreeNegativeOrderedConeJointLift/Preparation.core_from_floor`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ThreeNegativeOrderedConeJointLift/Preparation.core_from_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If L minus u is B times v plus a remainder smaller than B, then B times v is at least L minus u minus B. The given lower bound on that difference yields the required nonnegative margin after adding r times (s plus one) and subtracting p times (t plus one).

**Lemma 1.3 (Zero total for the doubled source).**

Lean statement: `D5/S3/Combinatorics/Circle/ThreeNegativeOrderedConeJointLift/Preparation.doubled_source_zero_cast`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/ThreeNegativeOrderedConeJointLift/Preparation.doubled_source_zero_cast` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a length of at least three and an integer seed given as a cast of a natural seed, the equal-outer source bridge gives zero total for the centered increments over the complete cycle at twice that seed.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/ThreeNegativeOrderedConeJointLift/Preparation.core_from_floor`
- Truth anchor: `D5/S3/Combinatorics/Circle/ThreeNegativeOrderedConeJointLift/Preparation.doubled_source_zero_cast`
- Truth anchor: `D5/S3/Combinatorics/Circle/ThreeNegativeOrderedConeJointLift/Preparation.ordered_schedule`
- Dependency: [D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterJointLift](../ThreeNegativeEqualOuterJointLift.md)
