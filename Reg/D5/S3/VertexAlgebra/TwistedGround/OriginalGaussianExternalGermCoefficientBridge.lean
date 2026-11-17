import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGermCoefficientBridge

/-! Faithful equality observations for selected exact source theorems.
Other source declarations have no completed registration in this checkpoint. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open _root_.D5.S3.VertexAlgebra.TwistedGround
open OriginalGaussianExternalGermCoefficientBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGermCoefficientBridge

namespace two_mul_radial_deriv_eq_euler
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ {f : ℂ → ℂ} {r : ℝ} (_hr : 0 < r)
    (_hf : DifferentiableAt ℂ f (Real.sqrt r : ℂ)),
    R.readout () ()
      (2 * (r : ℂ) * deriv (fun t : ℝ => f (Real.sqrt t : ℂ)) r)
      ((Real.sqrt r : ℂ) * deriv f (Real.sqrt r : ℂ))

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h (f := fun _ : ℂ => 0) (r := 1) (by norm_num) (differentiableAt_const (0 : ℂ))

def family : Registration arena (type_of% (@two_mul_radial_deriv_eq_euler)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@two_mul_radial_deriv_eq_euler, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@two_mul_radial_deriv_eq_euler) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGermCoefficientBridge.two_mul_radial_deriv_eq_euler.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGermCoefficientBridge.two_mul_radial_deriv_eq_euler.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize complexSignature complexEqual.readout complexEqual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGermCoefficientBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end two_mul_radial_deriv_eq_euler

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGermCoefficientBridge
