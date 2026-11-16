# Frequency restriction after full inverse colour transport

## Abstract

OriginalGaussianSourceRestriction

The inverse substitution is diagonal only in frequency. At each frequency its action still sums over every original colour. Expanding this action proves that full right covariance and opposite-charge mean entries restrict across nested frequency boxes. Both mixed rectangles and the external block are included. Native affine coefficient enlargement then gives full-row stabilization while retaining each external occupation in its row degree. Empty colour, frequency and external types are in scope. The original Wick contraction is also reduced to one arbitrary common box that contains the fixed external supports and the energy layer. The external analytic coefficient extraction remains separate.

**Definition 1.1 (Colour-preserving frequency inclusion).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.internalInclusion`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.internalInclusion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The embedding retains every colour and the value of each positive frequency in a larger frequency box.

**Theorem 1.2 (Complete transported covariance restriction).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_right_covariance_restrict`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_right_covariance_restrict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All four internal and external block cases use the actual complete inverse colour transport before restriction. The finite colour sums are identical at retained frequencies.

**Theorem 1.3 (Opposite-charge mean restriction).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_right_mean_restrict`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_right_mean_restrict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete inverse transport of the original mean at charge minus a commutes with nested frequency-box restriction.

**Theorem 1.4 (Actual native row coefficient stabilization).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_row_coefficients_restrict`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_row_coefficients_restrict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Both full affine row coefficients are preserved by the internal frequency inclusion and the identity on external coordinates. The right equality consumes the full transported covariance and mean restriction results; external degrees remain literal.

**Theorem 1.5 (Finite source energy stabilization).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_row_energy_layer_stabilizes`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_row_energy_layer_stabilizes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every occupation at energy n has positive frequencies at most n. The colour-preserving inclusion is therefore a bijection on energy layers once the cutoff is at least n. Native row restriction and invariance of the single internal factorial preserve the energy sum, including its zero-energy layer.

**Theorem 1.6 (Original Wick contraction in one common box).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_fixed_energy_common_box`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_fixed_energy_common_box` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every common box strictly larger than n and containing all four external supports, the original fixed-energy Wick contraction equals its native affine energy layer. Both charge scalars, all four external factorials and both integer Laurent selectors remain literal. The right covariance and opposite-charge mean use the complete original inverse colour transport before any restriction.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.internalInclusion`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_fixed_energy_common_box`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_right_covariance_restrict`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_right_mean_restrict`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_row_coefficients_restrict`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_row_energy_layer_stabilizes`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm](OriginalGaussianSourceGerm.md)
