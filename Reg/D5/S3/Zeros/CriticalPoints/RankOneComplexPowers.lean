import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.CriticalPoints.RankOneComplexPowers
import Reg.Support.SingleDependentReadout

/-! Source-bound scalar complex-power registrations retain their full original telescopes. -/

namespace Reg.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers
open _root_.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Complex
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Add

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ x t => positivePower x t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (x : ℝ) (s t : ℂ),
    positivePower x (s + t) = positivePower x s * R.readout () x t

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 0 0
  norm_num [rejected, realize, positivePower] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  change positivePower 2 0 ≠ positivePower 2 1
  rw [positivePower_one (by norm_num : (0 : ℝ) < 2)]
  norm_num [positivePower]

def source_registration : Registration arena (type_of% @positivePower_add) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positivePower_add, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers.positivePower_add)
      (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers.Add.unit
  realizationName := `Reg.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers.Add.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x t => positivePower x t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.Zeros.CriticalPoints.RankOneComplexPowers
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Add

namespace One

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ x => (x : ℂ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {x : ℝ} (hx : 0 < x), positivePower x 1 = R.readout () () x

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (x := 1) (by norm_num)
  norm_num [rejected, realize, positivePower] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @positivePower_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positivePower_one, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers.positivePower_one)
      (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers.One.unit
  realizationName := `Reg.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers.One.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => (x : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Zeros.CriticalPoints.RankOneComplexPowers
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end One

namespace OfReal

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ x s => ((x ^ s : ℝ) : ℂ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {x : ℝ} (hx : 0 < x) (s : ℝ),
    positivePower x (s : ℂ) = R.readout () x s

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (x := 1) (by norm_num) 0
  norm_num [rejected, realize, positivePower] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @positivePower_ofReal) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positivePower_ofReal, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers.positivePower_ofReal)
      (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers.OfReal.unit
  realizationName := `Reg.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers.OfReal.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x s => ((x ^ s : ℝ) : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Zeros.CriticalPoints.RankOneComplexPowers
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end OfReal

namespace Norm

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ x s => Real.exp (s.re * Real.log x)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (x : ℝ) (s : ℂ), ‖positivePower x s‖ = R.readout () x s

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 1 0
  norm_num [rejected, realize, positivePower] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  norm_num [actual, realize, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

def source_registration : Registration arena (type_of% @norm_positivePower) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨norm_positivePower, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers.norm_positivePower)
      (Realization signature) Type Unit := {
  unitName := `Reg.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers.Norm.unit
  realizationName := `Reg.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers.Norm.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x s => Real.exp (s.re * Real.log x)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.Zeros.CriticalPoints.RankOneComplexPowers
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Norm

end
end Reg.D5.S3.Zeros.CriticalPoints.RankOneComplexPowers
