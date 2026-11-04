/- GID: D5/S3/VertexAlgebra/TwistedGround/CorrectedDualCoefficient
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/CorrectedDualCoefficient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original corrected source has a nonzero dual coefficient for two actual twisted inputs. -/

import D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
import D5.S3.VertexAlgebra.ChargedResidue.LatticeHalfFockChargedResidue

/-!
K_L(e)(x,y)(a) is B((correctedField a).coeff e x,y), a full algebraic
functional on the original Carrier. K_R is not identified using symmetry.
For any charge and any nonzero actual ground second input, some actual first
input detects the generator coordinate at e=-bilinear D a a. The proof
consumes actual_charged_coefficient_adjoint, tensor nondegeneracy and the
existing charged_ground_leading through the charged dual consumer.
There is no claim of a restricted-dual representative, a full corrected
adjoint, a two-twisted intertwiner, Jacobi, fusion, or a string/AdS bridge.
The original singleton coefficient proof and its addition and scalar laws
are reused through their canonical public names in the original owner.
Their statements and proof bodies are unchanged.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct

namespace D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockCorrectedField LatticeHalfFockFiniteCorrection



/-- The left orientation on two actual twisted inputs and the original source. -/
def correctedDualCoefficient (D : LatticeData) (hu : IsUnit D.G.det)
    (e : ℤ) (x y : ActualTensor D hu) : Module.Dual ℂ (Carrier D) where
  toFun a := actualForm D hu ((correctedField D hu a).coeff e x) y
  map_add' a b := by
    rw [D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue.corrected_coeff_add]
    exact LinearMap.BilinForm.add_left _ _ _
  map_smul' c a := by
    rw [D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue.corrected_coeff_smul]
    exact LinearMap.BilinForm.smul_left _ _ _

/-- A nonzero original generator coordinate, with no symmetry or Jacobi premise. -/
theorem correctedDualCoefficient_nonzero_second_ground (D : LatticeData)
    (hu : IsUnit D.G.det) (a : Charge D) (u : ActualGround D hu) (hu0 : u ≠ 0) :
    ∃ x : ActualTensor D hu,
      correctedDualCoefficient D hu (-chargeNorm D a) x ((1 : Oscillator D) ⊗ₜ[ℂ] u)
        (Finsupp.single a (1 : Oscillator D)) ≠ 0 := by
  obtain ⟨x, hx⟩ := chargedDualCoefficient_nonzero_second_ground D hu a u hu0
  refine ⟨x, ?_⟩
  change actualForm D hu
    ((correctedField D hu (Finsupp.single a (1 : Oscillator D))).coeff
      (-chargeNorm D a) x) ((1 : Oscillator D) ⊗ₜ[ℂ] u) ≠ 0
  rw [D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue.corrected_singleton_coeff_charged]
  simpa only [chargedDualCoefficient, Finsupp.linearCombination_single, one_smul,
    chargedField, HVertexOperator.coeff_of_coeff] using hx

#print axioms correctedDualCoefficient_nonzero_second_ground
end D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
