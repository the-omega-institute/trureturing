/- GID: D5/S3/VertexAlgebra/TwistedGround/LeechQuadratic
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/LeechQuadratic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A literal hyperbolic frame certifies the original Leech mod-two quadratic form. -/

import D5.S3.VertexAlgebra.GolayLeech.ExplicitLeechLattice
import D5.S3.VertexAlgebra.TwistedGround.OperatorAlgebra
import D5.S3.VertexAlgebra.TwistedGround.LeechQuadraticReduction
import D5.S3.VertexAlgebra.TwistedGround.LeechHyperbolicCertificate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace D5.S3.VertexAlgebra.TwistedGround.LeechQuadratic

open LatticeGeneratingFieldLocality LatticeTwistedGroundRealization
open LatticeTwistedGroundRealization.SignQuotient
open GolayLeech.ExplicitLeechLattice GolayLeech.ExplicitLeechBasis
open scoped BigOperators

noncomputable section

theorem frame_independent : LinearIndependent F₂ frame := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro coefficients vanishes index
  have evaluated := congrArg ((modTwoPairing data).flip (frame (partner index))) vanishes
  have relation : (∑ first, coefficients first *
      modTwoPairing data (frame first) (frame (partner index))) = 0 := by
    simpa only [map_sum, map_smul, LinearMap.BilinForm.flip_apply,
      LinearMap.flip_apply, smul_eq_mul, map_zero] using evaluated
  have partner_injective : Function.Injective partner := by
    intro first second equality
    cases first <;> cases second <;> simpa [partner] using equality
  simp only [literal_certificate.2, partner_injective.eq_iff] at relation
  simpa using relation

def hyperbolicBasis : Module.Basis (Fin 12 ⊕ Fin 12) F₂ (ModTwoCharge data) :=
  basisOfLinearIndependentOfCardEqFinrank frame_independent (by
    change Fintype.card (Fin 12 ⊕ Fin 12) = Module.finrank F₂ (Fin 24 → F₂)
    simp [Module.finrank_fintype_fun_eq_card])

theorem hyperbolic_basis_apply (index : Fin 12 ⊕ Fin 12) :
    hyperbolicBasis index = frame index := by
  simp [hyperbolicBasis]

theorem original_plus_type :
    (∀ index, quadratic data (hyperbolicBasis index) = 0) ∧
    (∀ first second, modTwoPairing data (hyperbolicBasis first) (hyperbolicBasis second) =
      if partner first = second then 1 else 0) ∧
    (∀ charge : Charge data, quadratic data (reduceCharge data charge) =
      (bilinear data charge charge / 2 : ℤ)) := by
  simpa only [hyperbolic_basis_apply] using
    And.intro literal_certificate.1 (And.intro literal_certificate.2 (quadratic_integral data))

end

end D5.S3.VertexAlgebra.TwistedGround.LeechQuadratic
