# Absolute-zero classes in the full original BRST quotient

## Abstract

Absolute-zero classes in the full original BRST quotient

The carrier is the literal original State D, containing all lattice charges, all matter oscillators and the complete ghost Fock space. Q is the existing totalCharge D H. The source constructs an actual chain retraction into the already calculated absolute-zero sector and descends it to the existing full critical BRST quotient. The ambient boundary primitive remains arbitrary throughout.

This is a repository-derived original-operator bridge. It reuses the private frame-free charge projection lemmas in LatticeRelativeBRSTGround, the actual energy projector and commutation results in LatticeBRSTZeroEnergyReduction, the literal Q0 and four-coordinate cohomology in LatticeOriginalAbsoluteZeroCohomology, and the full quotient API in LatticeBRSTCohomologyField. Original lattice, ghost and BRST suppliers retain their attribution: Bakalov--Kac lattice structure, Scott Carnahan field/residue calculus, Kalle Kytola Sugawara work and the repository original tensor construction. Mathlib quotient and basis results are Apache 2.0. The supplied Pro reasoning proposes the projection route; source presence and all proof terms are checked by native Lean implementation. No literature novelty, independent review, canonical freeze, complete string theory or AdS/CFT result is asserted.

**Definition 1.1 (The actual original charge-zero and total-energy-zero projector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.rho`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.rho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rho D = chargeProject (0 : Charge D) composed with LatticeBRSTZeroEnergyReduction.P0 D. The latter is the actual total-energy spectral projector on all original matter and ghost states; it is not the quartet zero-count projector. No frame, positive-definiteness or antighost constraint enters this definition.

**Theorem 1.2 (Original-operator chain equation on all states).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.rho_chain`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.rho_chain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For D : LatticeData, H : Matrix (Fin D.rank) (Fin D.rank) complex, h26 : D.rank = 26, hHG : H * gramComplex D = 1 and hGH : gramComplex D * H = 1, rho D * totalCharge D H = totalCharge D H * rho D. On each original tensorBasis vector the charge projector has its supplied diagonal action. The proof checks both equal-charge and unequal-charge sectors, using preservation of every original momentum by Q; unequal sectors vanish coefficientwise. Charge projection also commutes with the actual totalL0 on that same original basis, and totalL0 P0 = 0 gives the image in E0.

**Definition 1.3 (Constructed retraction into the literal absolute-zero sector).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.retractState`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.retractState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For D, H and both inverse-Gram proofs, retractState is rho with codomain restricted to the existing E0 = fixedMomentum D 0 intersect ker(totalL0 D H). E0 has no b0 constraint. P0 fixes ker(totalL0), and the original charge projector fixes fixedMomentum D 0, so retractState fixes every E0 state. The chain equation for this restricted map additionally uses h26.

**Theorem 1.4 (Every ambient primitive yields a genuine restricted primitive).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.ambient_primitive`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.ambient_primitive` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For D, H, h26, hHG and hGH as above, every x : E0 D H and every y : State D with totalCharge D H y = (x : State D) satisfy Q0 D H hHG hGH (retractState D H hHG hGH y) = x. The primitive y is arbitrary in the original full state space; no charge, energy, cycle or b0 assumption is made on y. Its constructed replacement is precisely chargeProject 0 (P0 y), with membership in E0 proved from the actual operators.

**Theorem 1.5 (Restricted incoming range equals the full incoming range pulled back to E0).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.range_Q0_eq_comap`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.range_Q0_eq_comap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the full D, H, h26, hHG, hGH telescope, range(Q0 D H hHG hGH) = (range(totalCharge D H)).comap (E0 D H).subtype. The reverse direction uses the explicit primitive from ambient_primitive. This equality is consumed when testing whether an included restricted cycle is zero in the actual full quotient, through the existing full classOf_eq_zero with its arbitrary State primitive.

**Definition 1.6 (Inclusion into the existing full critical BRST quotient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.inclusion`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.inclusion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For the full critical telescope, inclusion maps the existing restricted Cycles/Boundaries cohomology linearly into LatticeBRSTCohomologyField.Cohomology D H h26 hHG hGH. It is descended from literal subtype inclusion using Submodule.mapQ. The restricted and full boundaries are submodules of different cycle types; the source maps the actual incoming ranges rather than identifying these types.

**Definition 1.7 (Actual projection descended from the full quotient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.retraction`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.retraction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The linear retraction has source the existing full Cohomology D H h26 hHG hGH and target the existing absolute-zero Cohomology D H hHG hGH. It descends retractState on cycles through Submodule.mapQ. If a full cycle is Q y for an arbitrary original y, its projected cycle has restricted primitive retractState y by the proved chain equation. Neither a retraction nor boundary reflection is an assumed input.

**Theorem 1.8 (The absolute-zero cohomology is a split subspace of the full quotient).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.retraction_inclusion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.retraction_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every c : LatticeOriginalAbsoluteZeroCohomology.Cohomology D H hHG hGH, with D, H, h26 and both inverse-Gram laws, retraction (inclusion c) = c. The proof descends the original state identity rho x = x on E0. This asserts a split inclusion; it does not identify the full complex or full quotient with E0 and gives no homotopy equivalence to E0.

**Definition 1.9 (One canonical full class map for the original four coordinates).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.fullClass`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.fullClass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

fullClass is inclusion composed with the existing absolute-zero classOf. Thus for t = (a,(v,(u,d))), its full representative is the literal original state Psi D H hHG hGH (a,(v,0)) + ghostC D 0 (Psi D H hHG hGH (0,(u,d))). The existing representative and canonicalState supply this state; no new coordinate differential or abstract cohomology replaces them. The two scalar and two rank-vector slots retain the original ghost and lattice suppliers and conventions.

**Definition 1.10 (Coordinate readout after the actual full-quotient retraction).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.fullCoordinates`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.fullCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

fullCoordinates is the existing cohomologyEquiv after retraction. It is defined on every full critical cohomology class. Its left inverse identity on fullClass is part of fullClasses_independent and follows from the proved retraction_inclusion and the existing cohomologyEquiv_classOf. It makes no assertion that every full class is in the image of fullClass.

**Definition 1.11 (Explicit finite family of actual full classes).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.fullClasses`

*Formalization.* `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.fullClasses` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

ClassIndex D is Unit plus (Fin D.rank plus (Fin D.rank plus Unit)). Take the product of Mathlib singleton, standard Pi, standard Pi and singleton bases in that order, and apply fullClass. The four index sectors give respectively the actual full classes with coordinates (1,(0,(0,0))), (0,(e_i,(0,0))), (0,(0,(e_i,0))) and (0,(0,(0,1))). Here e_i is the standard coordinate vector and every class uses the original four-slot state representative just specified.

**Theorem 1.12 (A coordinate left inverse and 54 independent full classes at critical rank).**

Lean statement: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.fullClasses_independent`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.fullClasses_independent` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the complete D, H, h26 : D.rank = 26, hHG and hGH telescope, the theorem jointly proves Function.LeftInverse fullCoordinates fullClass, LinearIndependent complex fullClasses, card(ClassIndex D) = 2 + 2 * D.rank and card(ClassIndex D) = 54. Independence uses the arbitrary-primitive range reflection in the actual full classOf_eq_zero: a full boundary represented by an E0 cycle is already a restricted boundary, and the existing four-coordinate equivalence then forces its coordinates to vanish. Mathlib basis transport supplies the finite family; the new operator and ambient-boundary bridge supplies the actual injectivity. There is no finite-dimensionality assertion for the full quotient.

## References

- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.ambient_primitive`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.fullClass`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.fullClasses`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.fullClasses_independent`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.fullCoordinates`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.inclusion`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.range_Q0_eq_comap`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.retractState`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.retraction`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.retraction_inclusion`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.rho`
- Truth anchor: `D5/S3/VertexAlgebra/Lattice/LatticeAbsoluteZeroFullCohomology.rho_chain`
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeBRSTZeroEnergyReduction](LatticeBRSTZeroEnergyReduction.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeOriginalAbsoluteZeroCohomology](LatticeOriginalAbsoluteZeroCohomology.md)
- Dependency: [D5/S3/VertexAlgebra/Lattice/LatticeRelativeBRSTGround](LatticeRelativeBRSTGround.md)
