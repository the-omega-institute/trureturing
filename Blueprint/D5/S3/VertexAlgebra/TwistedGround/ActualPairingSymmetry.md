# Symmetry of the Original Selected Actual Tensor Pairing

## Abstract

Symmetry of the Original Selected Actual Tensor Pairing

**Theorem 1.1 (Symmetry of the Original Selected Actual Tensor Pairing).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ActualPairingSymmetry.actualForm_symmetric`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ActualPairingSymmetry.actualForm_symmetric` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every integral symmetric even lattice D and integer unit determinant witness hu, the literal existing ActualChargedAdjoint.actualForm(D,hu) is symmetric on the original ActualTensor(D,hu). There is no positivity, positive-rank, pairing-choice or additional symmetry premise. Its selectedGroundPairing is the original Classical.choice(actual_ground_pairing D hu); the definition and the choice are unchanged.

Let B be any GroundPairing on the existing ActualGround(D,hu). Choose an already constructed symmetric nondegenerate invariant form S on that same selected representation. Mathlib's symmCompOfNondegenerate gives A=S.toDual inverse composed with B, with S(Ax,y)=B(x,y). Invariance and the actual representation inverse show S(A rho(g)x,y)=S(rho(g)Ax,y). Nondegeneracy of S implies A commutes with every actual representation operator.

The selected representation supplies its original rank equation and central sign. The existing actual_operator_algebra scalar_commutant therefore gives A=c times the identity. Consequently B(x,y)=c S(x,y)=c S(y,x)=B(y,x). This argument applies to the unchanged selected B and includes rank zero. It needs neither a new selected symmetric pairing nor a proof that c is nonzero.

The signed oscillator Wick form is symmetric by its existing owner theorem. Mathlib's scalar-valued tensor-product symmetry theorem transports these two factor symmetries to the literal actualForm. The consumed comparison-operator argument supplies the new proof content; finite-dimensional duality and tensor symmetry are reused. This is classical invariant bilinear-form theory, with no literature novelty claim.

This symmetry substep does not prove the full ordered-kernel exchange identity, original-source skew exchange, three-twisted crossing, an extension VOA, Monster symmetry, string theory or AdS/CFT. It leaves the existing all-state BPZ theorem unchanged.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ActualPairingSymmetry.actualForm_symmetric`
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint](ActualChargedAdjoint.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/SymmetricPairing](SymmetricPairing.md)
