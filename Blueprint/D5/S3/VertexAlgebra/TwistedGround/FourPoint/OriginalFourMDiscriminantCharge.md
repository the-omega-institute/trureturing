# Representatives and rational shifts

## Abstract

The original charge sectors in the doubled Gram quotient

Let G be the unimodular integral Gram matrix. Doubling the Gram keeps the same integer coordinates and replaces the lattice of representatives of zero by the image of 2G.

**Theorem 1.1 (Equality in the literal quotient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDiscriminantCharge.classOf_gram_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDiscriminantCharge.classOf_gram_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The classes of Ga and Gb in the actual cokernel of 2G agree exactly when a and b reduce to the same mod-two charge.

**Theorem 1.2 (The additive sector equivalence).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDiscriminantCharge.sectorEquiv_reduceCharge`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDiscriminantCharge.sectorEquiv_reduceCharge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The equivalence sends the original reduction of a to the class of Ga. Since G is invertible over the integers, every class has a representative of this form.

**Theorem 1.3 (The rational dual shift).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDiscriminantCharge.dualVector_gram_image`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDiscriminantCharge.dualVector_gram_image` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the existing dual-vector map for 2G to Ga gives a/2 in every original coordinate.

**Theorem 1.4 (All half-charges in a sector).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDiscriminantCharge.dual_sector_iff`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDiscriminantCharge.dual_sector_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A rational point whose doubled Gram image is integral and of the specified discriminant class is exactly a half-charge whose reduction is the given original charge sector.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDiscriminantCharge.classOf_gram_eq_iff`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDiscriminantCharge.dualVector_gram_image`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDiscriminantCharge.dual_sector_iff`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMDiscriminantCharge.sectorEquiv_reduceCharge`
- Dependency: [D5/S3/VertexAlgebra/Characters/LatticeDiscriminantTheta](../../Characters/LatticeDiscriminantTheta.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeTwistedGroundRealization](../../LatticeTwistedGroundRealization.md)
