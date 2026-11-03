# Three-variable coefficient indices

## Abstract

Three-variable coefficient indices

**Theorem 1.1 (signed_cleared_collision).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.signed_cleared_collision`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.signed_cleared_collision` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a genuinely lower-supported ordered channel, the all-integer Borcherds transform has finite support and equals the legally substituted native common series at every signed exponent. In the negative collision region, the positive integer binomial kernel has finite degree and all remaining terms vanish by the native numerator support.

**Definition 1.2 (slice).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.slice`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.slice` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Fix a signed spectator coefficient in a generally infinite three-variable native series, using zero extension when necessary.

**Theorem 1.3 (slice_extend).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.slice_extend`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.slice_extend` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Native slicing and signed zero extension give the same coefficient.

**Definition 1.4 (cross).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.cross`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.cross` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two finite binomial fibers expand the spectator cross factors of the three-field clearing polynomial.

**Theorem 1.5 (clearing_three).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.clearing_three`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.clearing_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Three-variable pair clearing equals the bivariate clearing of the finite spectator cross-factor expansion.

**Definition 1.6 (innerArguments).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.innerArguments`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.innerArguments` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The legal partial triangular coordinates are z0, t+z2, z2.

**Definition 1.7 (innerCollision).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.innerCollision`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.innerCollision` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Substitute the partial triangular coordinates into the generally infinite native series.

**Theorem 1.8 (innerCollision_coeff).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.innerCollision_coeff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.innerCollision_coeff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A coefficient of the partial triangular substitution is a finite antidiagonal binomial sum.

**Theorem 1.9 (innerCollision_signed).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.innerCollision_signed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.innerCollision_signed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The native inner substitution agrees with the bivariate collision on every signed spectator and collision exponent.

**Theorem 1.10 (signed_transform_clear).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.signed_transform_clear`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.signed_transform_clear` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finite signed binomial transform passes through polynomial clearing by the binomial-series composition law. Both sums use the same actual lower support cutoff.

**Definition 1.11 (index3).**

Lean statement: `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.index3`

*Formalization.* `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.index3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The native index with the three indicated nonnegative coordinates.

## References

- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.clearing_three`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.cross`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.index3`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.innerArguments`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.innerCollision`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.innerCollision_coeff`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.innerCollision_signed`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.signed_cleared_collision`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.signed_transform_clear`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.slice`
- Truth anchor: `D5/S3/VertexAlgebra/FormalSeries/SupportedThreeFieldCollision.slice_extend`
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/SupportedChannelSeries](SupportedChannelSeries.md)
- Dependency: [D5/S3/VertexAlgebra/FormalSeries/UngradedLocalWordSeries](UngradedLocalWordSeries.md)
