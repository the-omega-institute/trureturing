# Frequency restriction after full inverse colour transport

## Abstract

OriginalGaussianSourceRestriction

The inverse substitution is diagonal only in frequency. At each frequency its action still sums over every original colour. Expanding this action proves that full right covariance and opposite-charge mean entries restrict across nested frequency boxes. Both mixed rectangles and the external block are included. Native affine coefficient enlargement then gives full-row stabilization while retaining each external occupation in its row degree. Empty colour, frequency and external types are in scope. The original Wick contraction is also reduced to one arbitrary common box that contains the fixed external supports and the energy layer. The compact four-support external family is embedded in any containing common box, preserving the full original rows for subsequent ordinary extraction.

**Definition 1.1 (Colour-preserving frequency inclusion).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.internalInclusion`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.internalInclusion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The embedding retains every colour and the value of each positive frequency in a larger frequency box.

**Definition 1.2 (Common-box external labels).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.boxExternal`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.boxExternal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two copies of the box index label input and output coordinates.

**Definition 1.3 (Four fixed external supports).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.fourSupport`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.fourSupport` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The union of the two input and two output supports is finite.

**Definition 1.4 (Compact external coordinate family).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.CompactExternal`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.CompactExternal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Two copies of the support distinguish input and output labels.

**Definition 1.5 (Actual compact external labels).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.compactExternal`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.compactExternal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The compact labels retain the literal input or output flag and original colour and frequency.

**Definition 1.6 (Four fixed occupations).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.externalOccupation`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.externalOccupation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The full external occupation stores left input, left output, right input and right output in that order.

**Theorem 1.7 (Complete transported covariance restriction).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_right_covariance_restrict`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_right_covariance_restrict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

All four internal and external block cases use the actual complete inverse colour transport before restriction. The finite colour sums are identical at retained frequencies.

**Theorem 1.8 (Opposite-charge mean restriction).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_right_mean_restrict`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_right_mean_restrict` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The complete inverse transport of the original mean at charge minus a commutes with nested frequency-box restriction.

**Theorem 1.9 (External box reindexing).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_external_box_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_external_box_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An arbitrary embedded finite external family identifies both original common-box row coefficients with their actual full native source rows. Complete colour sums are taken before frequency restriction.

**Theorem 1.10 (Four-support common-box rows).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_compact_box_coefficients`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_compact_box_coefficients` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The compact input and output supports embed into any common frequency box containing the support. The two native coefficients equal the corrected common-box occupations, including the full opposite-charge right transport.

**Theorem 1.11 (Original fixed energy in compact external coordinates).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_fixed_energy_compact`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_fixed_energy_compact` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The original Wick energy finsum equals its compact full native row layer in every sufficiently large common box. Both charge scalars, four external factorials, one internal factorial and both literal Laurent selectors remain unchanged.

**Theorem 1.12 (Original Wick contraction in one common box).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_fixed_energy_common_box`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_fixed_energy_common_box` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every common box strictly larger than n and containing all four external supports, the original fixed-energy Wick contraction equals its native affine energy layer. Both charge scalars, all four external factorials and both integer Laurent selectors remain literal. The right covariance and opposite-charge mean use the complete original inverse colour transport before any restriction.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.CompactExternal`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.boxExternal`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.compactExternal`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.externalOccupation`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.fourSupport`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.internalInclusion`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_compact_box_coefficients`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_external_box_coefficients`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_fixed_energy_common_box`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_fixed_energy_compact`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_right_covariance_restrict`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction.original_right_mean_restrict`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceGerm](OriginalGaussianSourceGerm.md)
