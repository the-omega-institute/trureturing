# Marked coefficients and the signed Fourier overlaps

## Abstract

Charge sums in independent native mode assignments

**Definition 1.1 (Assigned charge summand).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOverlap.assignedChargeTerm`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOverlap.assignedChargeTerm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Multiply the inverse twelfth power of the chart period and the chart charge exponential by the physical partition sum of the marked word. In each partition the correction endpoints carry the lifted scales and four puncture contraction factors. The surviving endpoints are evaluated by the independent mode assignments of the native Wick word.

**Definition 1.2 (Assigned charge sector).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOverlap.assignedSector`

*Formalization.* `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOverlap.assignedSector` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sum the assigned charge summand over all charges reducing to the prescribed mod-two class.

**Theorem 1.3 (Assigned sum of a marked coefficient).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOverlap.assigned_charge_hasSum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOverlap.assigned_charge_hasSum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume unit Gram determinant, positive definite real Gram form, a finite decidable label type and a word without repeated labels. At a real argument strictly between zero and one, use either A or B with slit parameter of norm less than one, or D with the upper selection set to true. The charge sum on each mod-two fibre has sum equal to the physical product's marked Taylor coefficient at the origin. The copied labels have spatial degrees on the left and mark degree one on the right.

**Theorem 1.4 (Absolute summability of assigned charges).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOverlap.assigned_charge_summable_norm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOverlap.assigned_charge_summable_norm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same lattice, chart and distinct-label hypotheses, the norms of the assigned charge terms are summable on each mod-two fibre.

**Theorem 1.5 (Signed overlaps of assigned charge sectors).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOverlap.assigned_fourier_overlap`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOverlap.assigned_fourier_overlap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let the lattice have rank 24, unit Gram determinant and positive definite real Gram form. Take a finite decidable label type, a word of distinct labels and a real argument strictly between zero and one whose A parameter has a square root of norm less than one. Use the upper chart selection throughout. D in class a is the Fourier sum of the A sectors with signs at (a,b) and factor 2⁻¹². B is the corresponding sum with the additional quadratic sign of b and the inverse twelfth power of the A period root.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOverlap.assignedChargeTerm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOverlap.assignedSector`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOverlap.assigned_charge_hasSum`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOverlap.assigned_charge_summable_norm`
- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAssignedOverlap.assigned_fourier_overlap`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMFixedChargeWick](OriginalFourMFixedChargeWick.md)
