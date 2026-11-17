import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.PowerSeries.DottieInverseSeries
import Reg.Support.SingleDependentReadout

/-! The endpoint audit observes summation of the full signed coefficient sequence. -/

noncomputable section
open _root_.D5.S3.Analytic.PowerSeries.DottieInverseSeries
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Classical

namespace Reg.D5.S3.Analytic.PowerSeries.DottieInverseSeries

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℕ → ℝ) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ θ s => decide (HasSum s θ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ Real.cos θ = θ ∧
    (∀ t : ℝ, 0 < t → Real.cos t = t → t = θ) ∧
    Summable (fun n : ℕ => |((PowerSeries.coeff n inverse : ℚ) : ℝ)| * Real.pi ^ n) ∧
    R.readout () θ (fun n : ℕ => ((PowerSeries.coeff n inverse : ℚ) : ℝ) * Real.pi ^ n) = true

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨θ, _, _, _, _, _, h⟩
  norm_num [rejected, realize] at h

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ => 0), (fun n => if n = 0 then 1 else 0), ?_⟩
  intro he
  have h0 : actual.readout i 0 (fun _ => 0) = true := by
    exact decide_eq_true hasSum_zero
  have h1 : HasSum (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) 0 := by
    have hb := he ▸ h0
    exact of_decide_eq_true hb
  have hsum : HasSum (fun n : ℕ => if n = 0 then (1 : ℝ) else 0) 1 :=
    hasSum_ite_eq 0 1
  have := h1.unique hsum
  norm_num at this

def family : Registration arena (type_of% rational_inverse_endpoint) where
  actual := actual
  bridge := by simp [arena, actual, realize]
  variation := ⟨by simpa [arena, actual, realize] using rational_inverse_endpoint,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    rational_inverse_endpoint (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.PowerSeries.DottieInverseSeries.endpoint_unit
  realizationName := `Reg.D5.S3.Analytic.PowerSeries.DottieInverseSeries.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ θ s => decide (HasSum s θ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PowerSeries.DottieInverseSeries
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.PowerSeries.DottieInverseSeries
