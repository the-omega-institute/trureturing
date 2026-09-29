# One common cut across all levels

## Abstract

One common cut across all levels.

**Theorem 1.1 (One common cut across all levels).**

$$\operatorname{zeroExcess}\left(y\right) \iff \forall l, \operatorname{zeroExcess}\left(\operatorname{project}\left(l, y\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/InverseLimitZeroExcess.zero_excess_iff_all_levels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let adjacent alphabet maps commute with the given permutations. Applying the permutations coordinatewise defines a permutation of the actual inverse-limit thread space.

A tuple of threads is one-cut if and only if every level projection is one-cut. The sets of admissible cuts are nonempty finite decreasing sets. Their common element supplies one cut valid at every level, and coordinates separate threads.

The exact failure-count characterization consequently makes completed zero excess equivalent to zero excess at every level. Neither surjectivity nor finiteness of the alphabets is needed for this pointwise statement.

**Theorem 1.2 (Expected excess and projected laws).**

$$\operatorname{expectedExcess}\left(Q\right) = 0 \iff \forall l, \operatorname{expectedExcess}\left(\operatorname{push}\left(l, Q\right)\right) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/InverseLimitZeroExcess.expected_excess_zero_iff_all_levels` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On finite discrete Borel alphabets, the cycle excess is measurable on the space of tuples of threads. For any measure on this space, its nonnegative expected excess is zero exactly when every actual projected law has zero expected excess.

A nonnegative measurable function has zero integral exactly when it vanishes almost everywhere. The pointwise common-cut characterization and a countable intersection of full-measure events establish both directions. The measure need not be a probability, and the excess sequence is not asserted to be monotone.

## References

- Truth anchor: `D5/S3/Estimation/DataProcessing/InverseLimitZeroExcess.expected_excess_zero_iff_all_levels`
- Truth anchor: `D5/S3/Estimation/DataProcessing/InverseLimitZeroExcess.zero_excess_iff_all_levels`
- Dependency: [D5/S3/Estimation/DataProcessing/OneCutZeroExcess](OneCutZeroExcess.md)
