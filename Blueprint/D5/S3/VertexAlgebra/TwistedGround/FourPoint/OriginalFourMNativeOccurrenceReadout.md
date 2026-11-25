# Four independent factorial weights

## Abstract

Native occupations of a labelled affine word

**Definition 1.1 (Occupation of one native slot).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeOccurrenceReadout.slotOccupation`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeOccurrenceReadout.slotOccupation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Count the letters of a list of oscillators in the finite support and extend the occupation by zero along the support embedding.

**Theorem 1.2 (Affine moment in four occupations).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeOccurrenceReadout.native_occurrence_readout`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeOccurrenceReadout.native_occurrence_readout` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the occurrence labels form a finite type and map them into the two compact external legs, each with an input and an output slot. Given a symmetric complex matrix on the tagged support and a complex mean on it, evaluate the affine moment at the word's occupation using the pulled-back matrix and mean. It equals the affine coefficient of the original matrix and mean at the joined external occupation, multiplied by the four factorial weights. Compute each occupation by filtering the mapped word first by leg and then by slot. Repeated labels and coincident images count with their full multiplicities.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeOccurrenceReadout.native_occurrence_readout`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMNativeOccurrenceReadout.slotOccupation`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianSourceRestriction](../OriginalGaussianSourceRestriction.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/Wick/AffineOccurrenceWick](../Wick/AffineOccurrenceWick.md)
