# Exact rational logistic enclosures

## Abstract

Exact rational logistic enclosures.

**Theorem 1.1 (Scaled positive exponential bounds).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/Scalar/Logistic.checked_logistic_sound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/Scalar/Logistic.checked_logistic_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a rational argument in (0,1/2], the smooth transition equals 1/(1+exp(1/t-1/(1-t))). A supplied positive scaling and Taylor depth give rational lower and upper bounds for the exponential, and the decreasing logistic map reverses the endpoints.

**Theorem 1.2 (Endpoint-safe cutoff bounds).**

Lean statement: `D5/S3/Weil/Separator/TranslationEnergy/Scalar/Logistic.checked_cutoff_logistic_sound`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/TranslationEnergy/Scalar/Logistic.checked_cutoff_logistic_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every rational argument, a successful cutoff check supplies an enclosure of the exact real smooth transition with width at most 2^-m. Arguments outside (0,1) give exact zero or one; reflection handles the upper half, and a far-tail bound handles large logistic differences.

## References

- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/Scalar/Logistic.checked_cutoff_logistic_sound`
- Truth anchor: `D5/S3/Weil/Separator/TranslationEnergy/Scalar/Logistic.checked_logistic_sound`
- Dependency: [D5/S0/Certificates/BoxCover/RationalIntervalExpression](../../../../../S0/Certificates/BoxCover/RationalIntervalExpression.md)
