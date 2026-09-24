# One-cut equality in a twisted cycle

## Abstract

One-cut equality in a twisted cycle.

**Theorem 1.1 (One-cut equality in a twisted cycle).**

$$\operatorname{moving}\left(y\right) \le \operatorname{failures}\left(y\right), (\operatorname{failures}\left(y\right) = \operatorname{moving}\left(y\right) \iff \operatorname{oneCut}\left(y\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/DataProcessing/OneCutZeroExcess.failure_count_equality_iff_one_cut` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take any alphabet with a permutation and a tuple of positive finite length. Count unequal adjacent labels and add the failure of the twisted closing edge. The moving-anchor indicator is one exactly when the first label is not fixed by the permutation.

The failure count is at least the moving-anchor indicator. Equality holds exactly when there is a cut such that all coordinates up to the cut equal the anchor and every later coordinate equals its inverse image under the permutation.

With no internal failures all labels agree. With an internal failure and equality of the two counts, that failure is unique and the closing edge succeeds. The two constant segments therefore have the required values. Conversely a one-cut tuple has exactly the forced failure, including the fixed-anchor case.

## References

- Truth anchor: `D5/S3/Estimation/DataProcessing/OneCutZeroExcess.failure_count_equality_iff_one_cut`
- Dependency: [D5/S3/Estimation/DataProcessing/InverseLimitProbabilityExtension](InverseLimitProbabilityExtension.md)
