# Affine occupation moments

## Abstract

Wick evaluation by occurrence positions

**Definition 1.1 (Ordered Wick evaluation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineOccurrenceWick.wick`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineOccurrenceWick.wick` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty word evaluates to one. The head either contributes its mean or pairs with a tail position. A paired position is removed before evaluating the remaining word. Equal labels at distinct positions contribute separately.

**Theorem 1.2 (Affine moment as a Wick evaluation).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineOccurrenceWick.affineMoment_eq_wick`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineOccurrenceWick.affineMoment_eq_wick` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a symmetric covariance, take the occupation of the mapped word and evaluate its affine moment. The result is the Wick evaluation on the original word with both covariance entries and means pulled back along the label map. The occupation recurrence gives one term per tail occurrence, with multiplicity for repeated labels.

**Theorem 1.3 (Affine moments under a label map).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineOccurrenceWick.affineMoment_pullback`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineOccurrenceWick.affineMoment_pullback` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a finite occurrence type, pulling the symmetric covariance and the mean back before taking the moment gives the same result as mapping the occurrence word first. The map can identify distinct positions.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineOccurrenceWick.affineMoment_eq_wick`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineOccurrenceWick.affineMoment_pullback`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/Wick/AffineOccurrenceWick.wick`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/NativeAffineExternalCoefficient](../NativeAffineExternalCoefficient.md)
