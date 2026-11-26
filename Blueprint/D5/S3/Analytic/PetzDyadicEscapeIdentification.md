# Exact identification of finite Petz rate laws

## Abstract

The sharp number of positive Petz profile scales for finite rate laws with known mass and first moment.

**Theorem 1.1 (Identification from arbitrary distinct positive scales).**

Lean statement: `D5/S3/Analytic/PetzDyadicEscapeIdentification.rateProfile_identifies_weights`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzDyadicEscapeIdentification.rateProfile_identifies_weights` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m ≥ 1 and let two real weight families lie on a common strictly increasing finite grid of real rates, with at most m nonzero weights each. Assume the total masses and first rate moments agree. If the finite Petz rate profiles agree on a set of at least 2m − 2 distinct positive real scales, the weights agree at every grid point. The set of scales may be empty when m = 1.

At a positive scale, the profile difference is the difference of the two Laplace transforms divided by the scale, because the common mass and first moment cancel the affine terms. The transform difference vanishes at every sampled scale, and its value and derivative at zero vanish by the mass and first moment equalities.

If the weights differ, the transform difference is an exponential sum with decreasing exponents given by the negatives of the rates. It has at most 2m nonzero coefficients and at most 2m − 1 sign variations. The Descartes bound counts the distinct sample zeros and gives two units to the stationary zero at scale zero, requiring at least 2m sign variations and yielding a contradiction.

**Theorem 1.2 (Sharpness at one fewer scale).**

Lean statement: `D5/S3/Analytic/PetzDyadicEscapeIdentification.rateProfile_query_count_sharp`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/PetzDyadicEscapeIdentification.rateProfile_query_count_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let m ≥ 2. On any strictly increasing grid of 2m real rates and for any set of exactly 2m − 3 distinct positive real scales, there are two distinct probability laws on the grid with disjoint supports of exactly m rates each, the same first rate moment, and equal Petz profiles at every sampled scale.

The linear constraints for mass, first moment, and Laplace values at the sampled scales give 2m − 1 rows on 2m coefficients. A nonzero kernel vector gives an exponential sum with a stationary zero at zero and a zero at each sampled scale. The stationary-root Descartes bound forces 2m − 1 sign variations, so every coefficient is nonzero and adjacent signs alternate. The positive and negative parts have equal positive mass. Dividing both by that mass gives the two probability laws and preserves equality in every prescribed observation.

For example, on the grid 1, 2, 3, 4 with the single sample scale 1, put q = exp(−1). In ascending grid order, the coefficients of (1 − x)²(q − x) are q, −(1 + 2q), 2 + q, −1. The double root at x = 1 gives zero mass and zero first moment, and the root at x = q gives a zero Laplace value at scale 1. Dividing the positive and negative parts by 2 + 2q gives the two laws, supported on {1, 3} and {2, 4}.

## References

- Truth anchor: `D5/S3/Analytic/PetzDyadicEscapeIdentification.rateProfile_identifies_weights`
- Truth anchor: `D5/S3/Analytic/PetzDyadicEscapeIdentification.rateProfile_query_count_sharp`
- Dependency: [D5/S3/Analytic/ExponentialSum/DescartesRule](ExponentialSum/DescartesRule.md)
- Dependency: [D5/S3/Analytic/PetzDyadicEscapeSpectrum](PetzDyadicEscapeSpectrum.md)
