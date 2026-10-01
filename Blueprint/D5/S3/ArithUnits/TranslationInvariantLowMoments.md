# Translation-Invariant Low Moments

## Abstract

A finite translation orbit forces low power moments to vanish in positive characteristic.

**Theorem 1.1 (Low moments vanish under nonzero translation).**

Lean statement: `D5/S3/ArithUnits/TranslationInvariantLowMoments.power_sum_eq_zero_of_add_invariant`

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/TranslationInvariantLowMoments.power_sum_eq_zero_of_add_invariant` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any finite subset of a field of prime characteristic preserved by a nonzero translation, power moments of degrees k with k + 1 below the characteristic vanish. Binomial expansion makes the translation action triangular on moments; induction cancels the nonzero diagonal coefficients. The boundary degree can have a nonzero moment, and the result alone does not imply a root-polynomial factorization.

## References

- Truth anchor: `D5/S3/ArithUnits/TranslationInvariantLowMoments.power_sum_eq_zero_of_add_invariant`
