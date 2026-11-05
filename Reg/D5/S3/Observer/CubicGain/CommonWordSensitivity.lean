import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.CommonWordSensitivity
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Observer.CubicGain.CommonWordSensitivity
open _root_.D5.S3.Observer.CubicGain
open _root_.D5.S3.Observer.CubicGain.CommonWordSensitivity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- The complete source telescope and its final real comparison. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (W W' : OriginalWorld) (H : ℝ), 1 ≤ H →
    (∀ i, |sourceCoordinates W i| ≤ H) →
    (∀ i, |sourceCoordinates W' i| ≤ H) → ∀ u : List Bool,
    R.readout () () |futureRead W u-futureRead W' u|
      ((1+1048576*H)*Real.goldenRatio^u.length*(1+(u.length:ℝ))^3*
        ‖sourceCoordinates W-sourceCoordinates W'‖)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (0,0,0,0) (0,0,0,0) 1 (by norm_num)
    (by intro i; fin_cases i <;> norm_num [sourceCoordinates])
    (by intro i; fin_cases i <;> norm_num [sourceCoordinates]) []

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),0,1,?_⟩
  intro h
  have hh : (1:ℝ) ≤ 0 := Eq.mp (congrFun h 0) le_rfl
  norm_num at hh

def source_registration :
    Registration arena (type_of% @common_word_source_sensitivity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨common_word_source_sensitivity,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@common_word_source_sensitivity) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.CommonWordSensitivity.common_word_source_sensitivity.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.CommonWordSensitivity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.CommonWordSensitivity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
end Reg.D5.S3.Observer.CubicGain.CommonWordSensitivity
