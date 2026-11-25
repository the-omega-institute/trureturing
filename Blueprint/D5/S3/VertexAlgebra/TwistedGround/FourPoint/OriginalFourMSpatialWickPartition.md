# Native entries and inverse-coordinate corrections

## Abstract

Fixed-charge spatial Wick factors in the physical charts

**Definition 1.1 (Signed inverse scale).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickPartition.liftedScale`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickPartition.liftedScale` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each occurrence contributes the relative chart sign, the inverse chosen root, and the inverse chart scale to the power of its requested mode.

**Theorem 1.2 (Physical correction and the oscillator pair polynomial).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickPartition.correction_pair_coefficient`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickPartition.correction_pair_coefficient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any chart, puncture and two oscillator indices at an interior real argument, the signed two-variable Taylor coefficient of the physical slot correction divided by its two Jacobians is the evaluated central pair polynomial times the two signed inverse scales. The evaluation uses the negative lowering parameter and takes the constant oscillator coefficient.

**Definition 1.3 (Native spatial entries).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickPartition.nativeTaylor`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickPartition.nativeTaylor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Take both ordinary Taylor coefficients of the signed native chart covariance after coordinate substitution and division by the two Jacobians.

**Definition 1.4 (Same-puncture spatial entries).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickPartition.correctionTaylor`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickPartition.correctionTaylor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Within one puncture the correction entry is the evaluated oscillator pair polynomial times both signed scales. Across distinct punctures it is zero.

**Theorem 1.5 (Exact physical marked coefficient at fixed charge).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickPartition.physical_marked_coefficient_wick_partition`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickPartition.physical_marked_coefficient_wick_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any fixed charge, chart and chart flag, an interior argument and a word of distinct marks with prescribed punctures, colours and modes, take first degree in the chosen mark variables and the prescribed degrees in the spatial variables. The coefficient equals the charge exponential times the finite sum over ordered position partitions. Evaluate the first subword with the same-puncture correction matrix and zero mean. Evaluate the second subword with the native Taylor covariance and the extracted signed charge-linear means.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickPartition.correctionTaylor`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickPartition.correction_pair_coefficient`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickPartition.liftedScale`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickPartition.nativeTaylor`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickPartition.physical_marked_coefficient_wick_partition`
- Dependency: [D5/S3/VertexAlgebra/HalfFock/OriginalHalfCurrentWickPolynomial](../../HalfFock/OriginalHalfCurrentWickPolynomial.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMCorrectionJets](OriginalFourMCorrectionJets.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMOccurrenceWick](OriginalFourMOccurrenceWick.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickExtraction](OriginalFourMSpatialWickExtraction.md)
