import Reg.Support.FactorialFockMetric
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes

/-! Faithful equality observations for selected exact source theorems.
Other source declarations have no completed registration in this checkpoint. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open _root_.D5.S3.VertexAlgebra.TwistedGround
open _root_.D5.S3.VertexAlgebra.TwistedGround.FiniteMode
open OriginalGaussianFiniteCandidateModes
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.VertexAlgebra.FactorialFockMetric
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes

namespace a_euler_mode_step
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (p : ℕ) (r : ℂ),
    R.readout () () (r * aPrime (p + 1) r)
      ((p + 1 : ℂ) * (a (p + 1) r - a p r))

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h 0 0

def family : Registration arena (type_of% (@a_euler_mode_step)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@a_euler_mode_step, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@a_euler_mode_step) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.a_euler_mode_step.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.a_euler_mode_step.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end a_euler_mode_step

namespace externalT_negative_zero_positive_finite
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (p : ℕ) {r : ℝ} (_hr : 0 < r) (_hr1 : r < 1),
    R.readout () ()
      (OriginalGaussianExternalResolvent.externalT false 0 true p (Real.sqrt r : ℂ))
      (negativeZeroT p r)

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h 0 (r := 1/2) (by norm_num) (by norm_num)

def family : Registration arena (type_of% (@externalT_negative_zero_positive_finite)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@externalT_negative_zero_positive_finite, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@externalT_negative_zero_positive_finite) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.externalT_negative_zero_positive_finite.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.externalT_negative_zero_positive_finite.family
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
    owner := `D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes
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
end externalT_negative_zero_positive_finite

end Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes
