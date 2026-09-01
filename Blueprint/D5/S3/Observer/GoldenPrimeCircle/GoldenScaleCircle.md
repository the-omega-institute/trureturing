# Golden Scale Circle

## Abstract

Golden logarithmic scale turns multiplication into translation and multiplication by phi squared into one full shell step.

**Theorem 1.1 (The Golden Scale Period Is Positive).**

$$(0 < goldenScalePeriod).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/GoldenScaleCircle.golden_scale_period_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Twice the logarithm of the golden ratio is strictly positive because the golden ratio exceeds one.

This establishes the sign of the chosen orientation-preserving period; it makes no statement about a quotient coordinate.

**Theorem 1.2 (The Golden Scale Period Is Nonzero).**

$$(goldenScalePeriod \neq 0).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/GoldenScaleCircle.golden_scale_period_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Strict positivity immediately rules out a zero golden scale period.

The conclusion records only the nonvanishing needed for later divisions by the period.

**Theorem 1.3 (Positive Multiplication Becomes Coordinate Addition).**

$$\forall x: \mathbb{R} , y: \mathbb{R},\\{}(0 < x) \land (0 < y) \Rightarrow\\{}(\operatorname{goldenScaleCoordinate}\left(x \times y\right) = \operatorname{goldenScaleCoordinate}\left(x\right) + \operatorname{goldenScaleCoordinate}\left(y\right)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/GoldenScaleCircle.golden_scale_coordinate_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For positive real scales, the logarithm of a product splits into the sum of the two logarithms.

Dividing by the common golden period gives exact additivity on the unwrapped coordinate, without passing to a circle quotient.

**Theorem 1.4 (The Golden Square Has One Full Logarithmic Period).**

$$(\operatorname{log}\left({\varphi}^{2}\right) = goldenScalePeriod).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/GoldenScaleCircle.log_golden_ratio_sq_eq_period` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The logarithm of the square of the golden ratio is twice its logarithm and hence equals the defined scale period.

This is an exact normalization identity, not an approximation to the golden ratio or its logarithm.

**Theorem 1.5 (Multiplication by Phi Squared Advances One Shell).**

$$\forall x: \mathbb{R},\\{}(0 < x) \Rightarrow\\{}(\operatorname{goldenScaleCoordinate}\left({\varphi}^{2} \times x\right) = \operatorname{goldenScaleCoordinate}\left(x\right) + 1).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/GoldenScaleCircle.golden_scale_coordinate_phi_sq_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Multiplying a positive scale by the square of the golden ratio adds its one-period coordinate.

The result concerns the real-valued lift and asserts a translation by one, not equality after quotienting by integers.

**Theorem 1.6 (Even Golden Powers Advance by a Natural Number of Shells).**

$$\forall n: \mathbb{N} , x: \mathbb{R},\\{}(0 < x) \Rightarrow\\{}(\operatorname{goldenScaleCoordinate}\left({{\varphi}^{2}}^{n} \times x\right) = \operatorname{goldenScaleCoordinate}\left(x\right) + (n: \mathbb{R})).$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/GoldenPrimeCircle/GoldenScaleCircle.golden_scale_coordinate_phi_even_pow_mul` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Iterating multiplication by the orientation-preserving golden unit advances the coordinate by the natural exponent.

The positivity hypothesis on the base scale remains explicit, and the conclusion is limited to natural iterations.

## References

- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenScaleCircle.golden_scale_coordinate_mul`
- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenScaleCircle.golden_scale_coordinate_phi_even_pow_mul`
- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenScaleCircle.golden_scale_coordinate_phi_sq_mul`
- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenScaleCircle.golden_scale_period_ne_zero`
- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenScaleCircle.golden_scale_period_pos`
- Truth anchor: `D5/S3/Observer/GoldenPrimeCircle/GoldenScaleCircle.log_golden_ratio_sq_eq_period`
