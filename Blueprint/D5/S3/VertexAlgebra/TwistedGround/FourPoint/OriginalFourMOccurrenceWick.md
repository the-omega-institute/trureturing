# Fixed-charge marking and charge summation

## Abstract

Correction partitions for the physical four-point coefficient

**Definition 1.1 (Signed correction covariance).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccurrenceWick.correctionEntry`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccurrenceWick.correctionEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each entry is the negative inverse-coordinate correction divided by the two half-Jacobians and weighted by the Gram entry and both relative signs. Corrections between different punctures vanish.

**Definition 1.2 (Signed native covariance).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccurrenceWick.nativeEntry`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccurrenceWick.nativeEntry` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each entry is the chart covariance evaluated in the two raw local coordinates, divided by both half-Jacobians and weighted by the Gram entry and both relative signs.

**Theorem 1.3 (Partition of the fixed-charge mark derivative).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccurrenceWick.physical_mark_jet_partition`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccurrenceWick.physical_mark_jet_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The ordered mark derivative of the physical summand equals its charge-energy exponential times a position partition sum. The correction covariance supplies the first subword with zero mean. The pulled-back chart covariance and the physical mean supply the second subword. Symmetry of the two covariances permits the Wick convolution.

**Theorem 1.4 (Partition of the literal physical marked coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccurrenceWick.physical_marked_coefficient_partition`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccurrenceWick.physical_marked_coefficient_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a word of distinct mark labels, extract degree one in each selected weight and the prescribed spatial degree at each mark. The result is the fixed-charge exponential times the same spatial extraction of the correction and native Wick partition sum. Distinct mark labels can have equal colours or punctures.

**Theorem 1.5 (Charge-fiber sum of partitioned coefficients).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccurrenceWick.physical_marked_partition_hasSum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccurrenceWick.physical_marked_partition_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a word of distinct mark labels, assume a unit Gram determinant, a positive definite real Gram form and 0 < x < 1. Sum the partitioned coefficients over charges reducing to the given mod-two sector. The inverse twelfth power of the chart period weights each term. The sum is the literal marked coefficient of the physical four-point product.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccurrenceWick.correctionEntry`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccurrenceWick.nativeEntry`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccurrenceWick.physical_mark_jet_partition`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccurrenceWick.physical_marked_coefficient_partition`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccurrenceWick.physical_marked_partition_hasSum`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWick](OriginalFourMSpatialWick.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickConvolution](../Wick/AffineWickConvolution.md)
