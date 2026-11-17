# Joint Multiplier Orbits Modulo 157

The multiplier-two and multiplier-three tests become substantially stronger when
treated as one group action.  Their nonzero orbit periods are 52 and 78, and
their least common multiple is 156, the size of the multiplicative group of the
field `ZMod 157`.

**Theorem 1.1 (joint nonzero orbit divisibility).**  If a finite set `S` in
`ZMod 157` is carried to itself by both `x ↦ 2x` and `x ↦ 3x`, then

\[
156\mid |S\setminus\{0\}|.
\]

*Proof.*  The free-orbit lemma gives divisibility by 52 and by 78.  Taking their
least common multiple gives 156.  The Lean proof keeps the two unit actions
explicit and uses the previously verified orders `ord(2)=52` and `ord(3)=78`.
Machine-checked as `joint_nonzero_card_dvd` (`✓ std3`). ∎

**Theorem 1.2 (joint cardinality residue).**  Under the same hypotheses,

\[
|S|\bmod 156\in\{0,1\}.
\]

The only exceptional orbit is the fixed point zero.  This is the combined
orbit obstruction, rather than a second independent single-multiplier check.
Machine-checked as `joint_invariant_cardinality_residue` (`✓ std3`).

**Theorem 1.3 (complete invariant-set classification).**  The only finite sets
invariant under both multipliers are

\[
\varnothing,\qquad \{0\},\qquad (\mathbb Z/157\mathbb Z)^\times,
\qquad \mathbb Z/157\mathbb Z.
\]

Indeed, the nonzero part has at most 156 elements and its cardinality is a
multiple of 156; if zero is present, the full cardinality is one more than
such a multiple.  Thus the joint action collapses all possible invariant
supports to four orbit-theoretic regimes.  Machine-checked as
`joint_invariant_classification` (`✓ std3`).

This module records the group-action consequence of the two verified
multiplier periods.  It does not claim the First Multiplier Theorem, the
Singer correspondence, or nonexistence of arbitrary projective planes of
order twelve.

## References

- Truth anchor: `D5/S3/ArithUnits/CyclicPlaneJointMultipliers.joint_nonzero_card_dvd`
- Truth anchor: `D5/S3/ArithUnits/CyclicPlaneJointMultipliers.joint_invariant_cardinality_residue`
- Truth anchor: `D5/S3/ArithUnits/CyclicPlaneJointMultipliers.joint_invariant_classification`
- Reused orbit theorem: `D5/S3/ArithUnits/CyclicPlaneTwelveMultiplierObstruction.orderOf_dvd_card_erase_zero_of_image_mul_eq`
- Reused order checks: `CyclicPlaneTwelveMultiplierObstruction.orderOf_two_zmod157` and `CyclicPlaneThreeMultiplierObstruction.orderOf_three_zmod157`
