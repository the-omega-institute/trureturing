/- Faithful full-statement registration attempt. The source bridge, actual law,
whole-family variation and sensitivity are kernel obligations; structural source
reconstruction is separately assessed, not claimed declared_validated here. -/
import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.ActualChargeCompletion
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct BigOperators
namespace Reg.D5.S3.VertexAlgebra.TwistedGround.ActualChargeCompletion
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticeHalfFockChargedTensorCoefficients
open _root_.D5.S3.VertexAlgebra.TwistedGround.ActualChargedAdjoint
open _root_.D5.S3.VertexAlgebra.TwistedGround.ActualChargeCompletion
open Reg.D5.S3.VertexAlgebra.FactorialFockMetric
  (complexSignature complexNotEqual complexFalse complexNotEqualDependence)
namespace actual_even_isotropic_completion_boundary
def arena : Arena where
  signature := complexSignature
  Law R := ∀ (D : LatticeData)
    (hu : IsUnit D.G.det) (c : ℕ → Charge D)
    (hi : Function.Injective (fun n => c n + c n))
    (hz : ∀ n : ℕ, chargeNorm D (c n + c n) = 0),
    ∃ u v : ActualGround D hu,
      let x : ActualTensor D hu := (1 : Oscillator D) ⊗ₜ[ℂ] u
      let y : ActualTensor D hu := (1 : Oscillator D) ⊗ₜ[ℂ] v
      let ell := correctedDualCoefficient D hu 0 x y
      let K := completedCorrectedCoefficient D hu 0 x y
      R.readout () () (actualForm D hu x y) 0 ∧
      (∀ n : ℕ, ell (Finsupp.single (c n + c n) (1 : Oscillator D)) =
        actualForm D hu x y) ∧
      ¬ ChargeFinite D ell ∧
      (∀ sigma : Charge D → Charge D,
        ∀ P : LinearMap.BilinForm ℂ (Carrier D), ChargeOrthogonal D sigma P →
          ¬ ∃ a : Carrier D, P a = ell) ∧
      (¬ ∃ F : Charge D →₀ Module.Dual ℂ (Oscillator D),
        Finsupp.lsum ℂ (fun q => F q) = ell) ∧
      ¬ Function.HasFiniteSupport K ∧
      (Finsupp.lsum ℂ K = ell) ∧
      (∀ a : Carrier D, ell a = ∑ q ∈ a.support, K q (a q))
theorem sourceBridge : (type_of% (@D5.S3.VertexAlgebra.TwistedGround.ActualChargeCompletion.actual_even_isotropic_completion_boundary)) ↔ arena.Law complexNotEqual := Iff.rfl
private theorem rejectedLaw : ¬ arena.Law complexFalse := by
  intro h
  have hu : IsUnit hyperbolic.G.det := by
    norm_num [hyperbolic, Matrix.det_fin_two]
  let c : ℕ → Charge hyperbolic := fun n i => if i = 0 then (n : ℤ) else 0
  have hi : Function.Injective (fun n => c n + c n) := by
    intro m n same
    have at_zero := congrFun same (0 : Fin hyperbolic.rank)
    simp only [Pi.add_apply, c, if_pos rfl] at at_zero
    omega
  have hz (n : ℕ) : chargeNorm hyperbolic (c n + c n) = 0 := by
    simp [chargeNorm, bilinear, hyperbolic, c, Fin.sum_univ_two]
  obtain ⟨u, v, hv⟩ := h hyperbolic hu c hi hz
  exact hv.1
def family : Registration arena (type_of% (@D5.S3.VertexAlgebra.TwistedGround.ActualChargeCompletion.actual_even_isotropic_completion_boundary)) where
  actual := complexNotEqual
  bridge := sourceBridge
  variation := ⟨sourceBridge.mp D5.S3.VertexAlgebra.TwistedGround.ActualChargeCompletion.actual_even_isotropic_completion_boundary, complexFalse, rejectedLaw⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law complexNotEqual complexFalse rejectedLaw
  dependence := complexNotEqualDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.VertexAlgebra.TwistedGround.ActualChargeCompletion.actual_even_isotropic_completion_boundary) (type_of% (realize complexSignature complexNotEqual.readout complexNotEqual.anchor)) Type Unit where
  unitName := Lean.Name.str `D5.S3.VertexAlgebra.TwistedGround.ActualChargeCompletion.actual_even_isotropic_completion_boundary "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.ActualChargeCompletion.actual_even_isotropic_completion_boundary.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexNotEqual.readout complexNotEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.ActualChargeCompletion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
end actual_even_isotropic_completion_boundary
end Reg.D5.S3.VertexAlgebra.TwistedGround.ActualChargeCompletion
