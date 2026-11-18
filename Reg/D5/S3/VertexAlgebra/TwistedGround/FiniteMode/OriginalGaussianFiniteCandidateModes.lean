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

namespace a_derivative_mode_step
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (p : ℕ) (r : ℂ),
    R.readout () ()
      (2 * (aPrime (p + 1) r - (1 - r) * aPrime p r))
      (-a p r)

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h 0 0

def family : Registration arena (type_of% (@a_derivative_mode_step)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@a_derivative_mode_step, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@a_derivative_mode_step) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.a_derivative_mode_step.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.a_derivative_mode_step.family
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
end a_derivative_mode_step

namespace h_pascal
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (p q : ℕ) (r : ℂ),
    R.readout () ()
      (h (p + 1) (q + 1) r - h p (q + 1) r - h (p + 1) q r + h p q r)
      (r * h p q r)

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h 0 0 0

def family : Registration arena (type_of% (@h_pascal)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@h_pascal, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@h_pascal) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.h_pascal.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.h_pascal.family
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
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end h_pascal

namespace h_euler_mode_step
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (p q : ℕ) (r : ℂ),
    R.readout () ()
      (r * hPrime (p + 1) q r)
      ((p + 1 : ℂ) * (h (p + 1) q r - h p q r))

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h 0 0 0

def family : Registration arena (type_of% (@h_euler_mode_step)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@h_euler_mode_step, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@h_euler_mode_step) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.h_euler_mode_step.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.h_euler_mode_step.family
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
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end h_euler_mode_step

namespace hPrime_succ_succ
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (p q : ℕ) (r : ℂ),
    R.readout () ()
      (hPrime (p + 1) (q + 1) r)
      (h2 p q r)

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h 0 0 0

def family : Registration arena (type_of% (@hPrime_succ_succ)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@hPrime_succ_succ, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hPrime_succ_succ) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.hPrime_succ_succ.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.hPrime_succ_succ.family
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
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end hPrime_succ_succ

namespace h_inverse_stencil
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (p q : ℕ) (r : ℂ),
    R.readout () ()
      (denominatorStencil h p q r)
      (if p = 0 ∧ q = 0 then 1 else 0)

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h 0 0 0

def family : Registration arena (type_of% (@h_inverse_stencil)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@h_inverse_stencil, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@h_inverse_stencil) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.h_inverse_stencil.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.h_inverse_stencil.family
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
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end h_inverse_stencil

namespace hPrime_eq_shift11
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (p q : ℕ) (r : ℂ),
    R.readout () ()
      (hPrime p q r)
      (shift11 h2 p q r)

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h 0 0 0

def family : Registration arena (type_of% (@hPrime_eq_shift11)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@hPrime_eq_shift11, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hPrime_eq_shift11) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.hPrime_eq_shift11.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.hPrime_eq_shift11.family
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
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end hPrime_eq_shift11

namespace h2_inverse_stencil
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (p q : ℕ) (r : ℂ),
    R.readout () ()
      (denominatorStencil h2 p q r)
      (h p q r)

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h 0 0 0

def family : Registration arena (type_of% (@h2_inverse_stencil)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@h2_inverse_stencil, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@h2_inverse_stencil) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.h2_inverse_stencil.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.h2_inverse_stencil.family
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
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end h2_inverse_stencil

namespace L_h_inverse_stencil
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (p q : ℕ) (r : ℂ),
    R.readout () ()
      (denominatorStencil L_h p q r)
      (a p r * a q r)

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h 0 0 0

def family : Registration arena (type_of% (@L_h_inverse_stencil)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@L_h_inverse_stencil, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@L_h_inverse_stencil) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.L_h_inverse_stencil.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.L_h_inverse_stencil.family
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
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end L_h_inverse_stencil

namespace L_h2_inverse_stencil
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (p q : ℕ) (r : ℂ),
    R.readout () ()
      (denominatorStencil L_h2 p q r)
      (L_h p q r)

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h 0 0 0

def family : Registration arena (type_of% (@L_h2_inverse_stencil)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@L_h2_inverse_stencil, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@L_h2_inverse_stencil) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.L_h2_inverse_stencil.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.L_h2_inverse_stencil.family
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
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end L_h2_inverse_stencil

namespace h2_euler_mode_step
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (p q : ℕ) (r : ℂ),
    R.readout () ()
      (r * h2Prime (p + 1) q r)
      ((p + 1 : ℂ) * h2 (p + 1) q r - (p + 2 : ℂ) * h2 p q r)

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h 0 0 0

def family : Registration arena (type_of% (@h2_euler_mode_step)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@h2_euler_mode_step, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@h2_euler_mode_step) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.h2_euler_mode_step.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.h2_euler_mode_step.family
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
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end h2_euler_mode_step

namespace P_inverse_stencil
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (p q : ℕ) (r : ℂ),
    R.readout () ()
      (denominatorStencil P p q r)
      (r / 2 * (a p r * a q r + (1 - r) *
        shift11 (fun i j u => a i u * a j u) p q r) + r ^ 2 * shift11 L_h p q r)

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h 0 0 0

def family : Registration arena (type_of% (@P_inverse_stencil)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@P_inverse_stencil, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@P_inverse_stencil) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.P_inverse_stencil.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.P_inverse_stencil.family
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
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end P_inverse_stencil

namespace sourceDerivativeConvolution_step
abbrev arena : Arena where
  signature := complexSignature
  Law R := ∀ (H : ℕ → ℕ → ℂ → ℂ) (p q : ℕ) (r : ℂ),
    R.readout () ()
      (2 * (sourceDerivativeConvolution H p q r -
        (1 - r) * shiftY (sourceDerivativeConvolution H) p q r))
      (-r * shiftY (L H) p q r)

private theorem rejected_fails : ¬ arena.Law complexFalse := by
  intro h
  exact h (fun _ _ _ => 0) 0 0 0

def family : Registration arena (type_of% (@sourceDerivativeConvolution_step)) where
  actual := complexEqual
  bridge := Iff.rfl
  variation := ⟨@sourceDerivativeConvolution_step, complexFalse, rejected_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law complexEqual complexFalse rejected_fails
  dependence := complexEqualDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sourceDerivativeConvolution_step) (Realization complexSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.sourceDerivativeConvolution_step.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes.sourceDerivativeConvolution_step.family
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
end sourceDerivativeConvolution_step

end Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes
