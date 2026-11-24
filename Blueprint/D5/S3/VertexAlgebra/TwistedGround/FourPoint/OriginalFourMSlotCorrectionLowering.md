# Signed scales and correction endpoint partitions

## Abstract

Lowering and physical Wick corrections at the four punctures

**Theorem 1.1 (Signed scales at one puncture).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlotCorrectionLowering.same_slot_correction`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlotCorrectionLowering.same_slot_correction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any lattice, chart, real argument, puncture and word with prescribed colours and modes, the zero-mean physical correction Wick value is the product of the lifted signed scales at every occurrence times the zero-mean Wick value of the central pair evaluated at the negative lowering parameter of the puncture.

**Theorem 1.2 (Inverse lowering as a partition sum).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlotCorrectionLowering.slot_lowering_partition`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlotCorrectionLowering.slot_lowering_partition` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a lattice with unit Gram determinant and a finite label type, take a word with prescribed colours and modes at one chart puncture. With a cutoff strictly above the degree of its Wick polynomial, the sum of lowering powers on the occurrence monomial, weighted by powers of the negative lowering parameter divided by the corresponding factorials, equals the position partition sum of central contractions and surviving evaluated creators.

**Theorem 1.3 (Independent four-puncture correction factors).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlotCorrectionLowering.physical_correction_by_slot`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlotCorrectionLowering.physical_correction_by_slot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a lattice with unit Gram determinant and a finite label type, assign a puncture, colour and mode to each label. In any chart and at any real argument, the physical correction Wick value of a word with zero mean is the product of the signed scales over all occurrences times the product of four central contraction sums. Each uses the ordered subword at the corresponding puncture and its own negative lowering parameter.

**Theorem 1.4 (Within-puncture factors in the fixed-charge marked coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlotCorrectionLowering.physical_marked_coefficient_by_slot`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlotCorrectionLowering.physical_marked_coefficient_by_slot` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a lattice with unit Gram determinant, a fixed charge, a chart and chart flag, and a real argument strictly between zero and one, take the specified spatial degrees and first degree in each mark of a word of distinct labels from a finite type with decidable equality. The physical Taylor coefficient at zero equals the charge exponential times the ordered position partition sum. Correction endpoints contribute their signed scales and four within-puncture contraction sums. The complement contributes the native Taylor covariance and the extracted signed charge-linear means through the affine Wick value.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlotCorrectionLowering.physical_correction_by_slot`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlotCorrectionLowering.physical_marked_coefficient_by_slot`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlotCorrectionLowering.same_slot_correction`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlotCorrectionLowering.slot_lowering_partition`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSpatialWickPartition](OriginalFourMSpatialWickPartition.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMWickLowering](OriginalFourMWickLowering.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Wick/AffineWickBlocks](../Wick/AffineWickBlocks.md)
