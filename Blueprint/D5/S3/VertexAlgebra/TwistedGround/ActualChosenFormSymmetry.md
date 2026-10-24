# Symmetry of the Original Chosen Ground Form

## Abstract

Symmetry of the Original Chosen Ground Form

The selected ActualGround, original GroundPairing structure, private selectedGroundPairing and public ActualChargedAdjoint.actualForm are unchanged. In particular the original choice remains Classical.choice (actual_ground_pairing D hu), not a choice of SymmetricGroundPairing.

For any two original GroundPairings, the generic invariant-form comparison and the already proved actual operator algebra give a unique nonzero proportionality scalar. Applying this comparison to the symmetric witness of SymmetricPairing proves that every original GroundPairing is symmetric. This includes the exact original chosen pairing. The two bind-only comparison helpers remain private and are consumed in the final proof.

Mathlib tensor symmetry combines the derived ground symmetry with the original SignedOscillatorWick.wick_symmetric. The sole new visibility change removes private from wick_symmetric while preserving its statement and proof. No positive-definite metric, fixed rank, new carrier or new representation is used. All integral lattices with IsUnit D.G.det remain in scope, including rank zero and indefinite lattices.

This closes symmetry of the old actual tensor bilinear form. It neither changes the orientations of existing charged adjoint laws nor proves restricted-dual representability, inversion, mixed Jacobi, a twisted intertwiner, fusion, string theory or AdS/CFT. Classical Schur duality and bilinear tensor symmetry are the literature source; no novelty claim.

The accompanying Reg source has compiled the faithful equality-readout family, exact full-telescope bridge, positive law, whole-family intervention, sensitivity and observational dependence. Typed elaboration and current four-slot admission are separate checks. The source-selection and reconstruction boundary remains unfinished at https://github.com/the-omega-institute/trureturing/issues/21214; no current declared_validated status is claimed.

**Theorem 1.1 (Symmetry of the Original Chosen Ground Form).**

Lean statement: `D5/S3/VertexAlgebra/TwistedGround/ActualChosenFormSymmetry.actualForm_isSymm`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/TwistedGround/ActualChosenFormSymmetry.actualForm_isSymm` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selected ActualGround, original GroundPairing structure, private selectedGroundPairing and public ActualChargedAdjoint.actualForm are unchanged. In particular the original choice remains Classical.choice (actual_ground_pairing D hu), not a choice of SymmetricGroundPairing.

## References

- Truth anchor: `D5/S3/VertexAlgebra/TwistedGround/ActualChosenFormSymmetry.actualForm_isSymm`
- Dependency: [D5/S3/Quantum/Algebra/InvariantFormProportionality](../../Quantum/Algebra/InvariantFormProportionality.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/ActualChargedAdjoint](ActualChargedAdjoint.md)
- Dependency: [D5/S3/VertexAlgebra/TwistedGround/SymmetricPairing](SymmetricPairing.md)
