/- GID: D5/S3/VertexAlgebra/TwistedGround/SymmetricPairing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/SymmetricPairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RepresentationTheory.Invariants]
   utility: none
   digest: A nondegenerate symmetric invariant pairing on the exact selected actual ground. -/

import D5.S3.VertexAlgebra.TwistedGround.FlipAverage
import Mathlib.RepresentationTheory.Invariants

/-! Symmetrizing the invariant average on the selected actual ground. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TwistedGround.SymmetricPairing

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open LatticeHalfFockChargedTensorCoefficients
open InvariantPairing

noncomputable section
attribute [local instance] InvariantPairing.reducedFintype
  InvariantPairing.quotientFintype InvariantPairing.cardInvertible

/-- The symmetric form has the original invariance and same-charge adjointness laws. -/
structure SymmetricGroundPairing (D : LatticeData) (hu : IsUnit D.G.det)
    extends GroundPairing D hu where
  symmetric : form.IsSymm

/-- Symmetrizing the finite average is nonzero because both relevant traces are one. -/
theorem actual_symmetric_ground_pairing (D : LatticeData) (hu : IsUnit D.G.det) :
    Nonempty (SymmetricGroundPairing D hu) := by
  classical
  let flip : Module.End ℂ (LinearMap.BilinForm ℂ (ActualGround D hu)) :=
    LinearMap.BilinForm.flipHom.toLinearMap
  let S := formAverage D hu + flip.comp (formAverage D hu)
  have tr : LinearMap.trace ℂ _ S = 2 := by
    change LinearMap.trace ℂ _ (formAverage D hu + flip.comp (formAverage D hu)) = _
    rw [map_add, average_trace D hu]
    have ht := FlipAverage.actual_flip_average_trace D hu
    change LinearMap.trace ℂ _ (flip.comp (formAverage D hu)) = 1 at ht
    rw [ht]
    norm_num
  have nonzero : S ≠ 0 := by
    intro h
    rw [h, map_zero] at tr
    norm_num at tr
  let basis := (Pi.basisFun ℂ (Half (groundRank D hu))).linearMap
    (Pi.basisFun ℂ (Half (groundRank D hu))).dualBasis
  have seed : ∃ i, S (basis i) ≠ 0 := by
    by_contra absent
    push Not at absent
    exact nonzero (basis.ext fun i => by simpa using absent i)
  obtain ⟨i, hn⟩ := seed
  let B := S (basis i)
  have invariant (g : Extension D ⧸ K D) (u v : ActualGround D hu) :
      B (groundRepresentation D hu g u) (groundRepresentation D hu g v) = B u v := by
    change formAverage D hu (basis i) _ _ + formAverage D hu (basis i) _ _ = _
    rw [averaged_invariant, averaged_invariant]
    rfl
  refine ⟨{
    form := B
    nondegenerate := invariant_nondegenerate D hu B hn invariant
    invariant := invariant
    signed_adjoint := ground_signed_adjoint D hu B invariant
    symmetric := ?_ }⟩
  constructor
  intro u v
  change formAverage D hu (basis i) u v + formAverage D hu (basis i) v u =
    formAverage D hu (basis i) v u + formAverage D hu (basis i) u v
  exact add_comm _ _

#print axioms actual_symmetric_ground_pairing

end
end D5.S3.VertexAlgebra.TwistedGround.SymmetricPairing
