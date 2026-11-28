import Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.Common

/-! Complete source laws with single function-operand interventions. -/

open _root_.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Lorentz
open LeanInformationAudit Real Set Filter
open scoped Topology

namespace Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace DeSitterEtaRange

abbrev signature : Signature := operandSignature (ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => deSitterEta x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ => -π) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ (t : ℝ),
    -(π / 2) < (obs.readout () ()) t ∧ deSitterEta t < π / 2

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := (h 0).1
  linarith [Real.pi_pos]

def family : Registration arena (type_of% (@deSitterEta_range)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@deSitterEta_range, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change deSitterEta (0) ≠ deSitterEta (1)
    exact eta_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@deSitterEta_range) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.deSitterEta_range.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.DeSitterEtaRange.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => deSitterEta x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DeSitterEtaRange

namespace DeSitterTimeLeftInverse

abbrev signature : Signature := operandSignature (ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => deSitterTime x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ => 1) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ (t : ℝ),
    (obs.readout () ()) (deSitterEta t) = t

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := h 0
  norm_num at e

def family : Registration arena (type_of% (@deSitterTime_left_inverse)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@deSitterTime_left_inverse, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), deSitterEta 0, deSitterEta 1, ?_⟩
    change deSitterTime (deSitterEta 0) ≠ deSitterTime (deSitterEta 1)
    exact time_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@deSitterTime_left_inverse) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.deSitterTime_left_inverse.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.DeSitterTimeLeftInverse.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => deSitterTime x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DeSitterTimeLeftInverse

namespace DeSitterTimeRightInverse

abbrev signature : Signature := operandSignature (ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => deSitterEta x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ => π) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {η : ℝ}
    (hη : -(π / 2) < η) (hπ : η < π / 2),
    (obs.readout () ()) (deSitterTime η) = η

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := h (η := 0) (by linarith [Real.pi_pos]) (by positivity)
  exact Real.pi_ne_zero e

def family : Registration arena (type_of% (@deSitterTime_right_inverse)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@deSitterTime_right_inverse, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change deSitterEta (0) ≠ deSitterEta (1)
    exact eta_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@deSitterTime_right_inverse) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.deSitterTime_right_inverse.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.DeSitterTimeRightInverse.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => deSitterEta x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DeSitterTimeRightInverse

namespace DeSitterCosCosh

abbrev signature : Signature := operandSignature (ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => cos x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ => 0) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ (t : ℝ),
    (obs.readout () ()) (deSitterEta t) = 1 / cosh t

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := h 0
  norm_num at e

def family : Registration arena (type_of% (@deSitter_cos_cosh)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@deSitter_cos_cosh, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, π, ?_⟩
    change cos (0) ≠ cos (π)
    exact cos_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@deSitter_cos_cosh) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.deSitter_cos_cosh.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.DeSitterCosCosh.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => cos x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DeSitterCosCosh

namespace DeSitterCoshSec

abbrev signature : Signature := operandSignature (ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => cos x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ => 0) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ (t : ℝ),
    cosh t = 1 / (obs.readout () ()) (deSitterEta t)

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := h 0
  norm_num at e

def family : Registration arena (type_of% (@deSitter_cosh_sec)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@deSitter_cosh_sec, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, π, ?_⟩
    change cos (0) ≠ cos (π)
    exact cos_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@deSitter_cosh_sec) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.deSitter_cosh_sec.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.DeSitterCoshSec.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => cos x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DeSitterCoshSec

namespace DeSitterEtaDerivative

abbrev signature : Signature := operandSignature (ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => deSitterEta x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ => 0) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ (t : ℝ),
    HasDerivAt (obs.readout () ()) (cos (deSitterEta t)) t

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := (h 0).unique (hasDerivAt_const 0 (0 : ℝ))
  have hc : cos (deSitterEta 0) = 1 := by simpa using deSitter_cos_cosh 0
  rw [hc] at e
  norm_num at e

def family : Registration arena (type_of% (@deSitterEta_derivative)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@deSitterEta_derivative, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), 0, 1, ?_⟩
    change deSitterEta (0) ≠ deSitterEta (1)
    exact eta_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@deSitterEta_derivative) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.deSitterEta_derivative.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.DeSitterEtaDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => deSitterEta x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DeSitterEtaDerivative

namespace DeSitterTimeDerivative

abbrev signature : Signature := operandSignature (ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => deSitterTime x) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ x => (fun _ => 0) x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {η : ℝ} (hη : -(π / 2) < η) (hπ : η < π / 2),
    HasDerivAt (obs.readout () ()) (1 / cos η) η

private theorem rejected : ¬ arena.Law erased := by
  intro h
  dsimp only [arena, erased, realize] at h
  have e := (h (η := 0) (by linarith [Real.pi_pos]) (by positivity)).unique
    (hasDerivAt_const 0 (0 : ℝ))
  norm_num at e

def family : Registration arena (type_of% (@deSitterTime_derivative)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@deSitterTime_derivative, erased, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual erased rejected
  dependence := by
    intro _
    refine ⟨(), deSitterEta 0, deSitterEta 1, ?_⟩
    change deSitterTime (deSitterEta 0) ≠ deSitterTime (deSitterEta 1)
    exact time_changes

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@deSitterTime_derivative) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.deSitterTime_derivative.__information_unit
  realizationName :=
    `Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D.DeSitterTimeDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => deSitterTime x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DeSitterTimeDerivative

end
end Reg.D5.S3.Geometry.Lorentz.PenroseCarterCausalCompactification4D
