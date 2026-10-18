import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.CriticalPoints.ThreeLinesSchurMoment
import Reg.Support.SingleDependentReadout

/-! Source-bound observation of the frequency in rotating-phase injectivity. -/

namespace Reg.D5.S3.Zeros.CriticalPoints.ThreeLinesSchurMoment

open _root_.D5.S3.Zeros.CriticalPoints.ThreeLinesSchurMoment
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Complex

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ b => b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ b => b + 1) (fun e => nomatch e)

/-- The original implication with only its final frequency occurrence observed. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {u v : ℂ} {a b : ℝ} (hu : u ≠ 0)
    (h : ∀ y : ℝ, u * exp ((y : ℂ) * (a : ℂ) * I) =
      v * exp ((y : ℂ) * (b : ℂ) * I)),
      u = v ∧ a = R.readout () () b

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (u := 1) (v := 1) (a := 0) (b := 0) one_ne_zero (by
    intro y
    rfl)
  have hh' : (0 : ℝ) = 0 + 1 := hh.2
  norm_num at hh'

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena (type_of% @rotating_phase_injective) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rotating_phase_injective, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Zeros.CriticalPoints.ThreeLinesSchurMoment.rotating_phase_injective)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Zeros.CriticalPoints.ThreeLinesSchurMoment.unit
  realizationName := `Reg.D5.S3.Zeros.CriticalPoints.ThreeLinesSchurMoment.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.CriticalPoints.ThreeLinesSchurMoment
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Zeros.CriticalPoints.ThreeLinesSchurMoment
