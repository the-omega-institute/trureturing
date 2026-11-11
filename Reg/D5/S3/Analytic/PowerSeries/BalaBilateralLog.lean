import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.PowerSeries.BalaBilateralLog
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Analytic.PowerSeries.BalaBilateralLog
open _root_.D5.S3.Analytic.PowerSeries.BalaBilateralLog
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Filter Finset
open scoped Topology
noncomputable section

abbrev signature := _root_.Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℂ) (fun _ => ℂ)
def actual : Realization signature := realize signature (fun _ _ z => Complex.log z) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ x a : ℂ, ‖x‖ < 1 → ‖a‖ < 1 →
      Summable (fun k => ‖positive x a k‖) ∧
      Summable (fun k => ‖negative x a k‖) ∧
      regularSum x a = -(R.readout () ()) (1 - x) ∧
      (∀ k : ℕ, (k : ℂ) + 1 ≠ 0 ∧ 1 - x * a ^ (k + 1) ≠ 0) ∧
      (0 < (1 - x).re)) ∧
    (∀ (x : ℂ) (a : {a : ℂ // a ≠ 0}), ‖x‖ < 1 → ‖(a : ℂ)‖ < 1 →
      (∀ n : {n : ℤ // n ≠ 0}, (a : ℂ) ^ (n : ℤ) ≠ 0 ∧
        ((n : ℤ) : ℂ) ≠ 0 ∧ ((n : ℤ) < 0 → x - (a : ℂ) ^ (n : ℤ) ≠ 0)) ∧
      (∀ k : ℕ,
        raw x a ⟨(k : ℤ) + 1, by omega⟩ = positive x a k ∧
        raw x a ⟨-((k : ℤ) + 1), by omega⟩ = negative x a k) ∧
      Summable (fun n => ‖raw x a n‖) ∧ HasSum (raw x a) (regularSum x a) ∧
      (∑' n, raw x a n) = regularSum x a ∧
      ((∑' k : ℕ, raw x a ⟨(k : ℤ) + 1, by omega⟩) +
        ∑' k : ℕ, raw x a ⟨-((k : ℤ) + 1), by omega⟩) = regularSum x a ∧
      Tendsto (fun N : ℕ => ∑ k ∈ range N,
        (raw x a ⟨(k : ℤ) + 1, by omega⟩ +
          raw x a ⟨-((k : ℤ) + 1), by omega⟩)) atTop (𝓝 (regularSum x a))) ∧
    (∀ (x : ℝ) (a : {a : ℝ // a ≠ 0}), |x| < 1 → |(a : ℝ)| < 1 →
      Summable (fun n => ‖realRaw x a n‖) ∧ HasSum (realRaw x a) (-Real.log (1 - x))) ∧
    (∀ x : ℂ, ‖x‖ < 1 →
      (∀ k : ℕ, positive x 0 k = x ^ (k + 1) / (k + 1) ∧ negative x 0 k = 0) ∧
      ContinuousAt (regularSum x) 0 ∧
      ∀ H : ℂ → ℂ, ContinuousWithinAt H {a | ‖a‖ < 1} 0 →
        (∀ a : {a : ℂ // a ≠ 0}, ‖(a : ℂ)‖ < 1 → H a = ∑' n, raw x a n) →
          Set.EqOn H (regularSum x) {a | ‖a‖ < 1})

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hv := (h.1 0 0 (by simp) (by simp)).2.2.1
  have ht := (full_event.1 0 0 (by simp) (by simp)).2.2.1
  simp only [rejected, realize] at hv
  rw [ht] at hv
  norm_num at hv

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 2, ?_⟩
  change Complex.log 0 ≠ Complex.log 2
  intro he
  have hl : Complex.log 2 = 0 := by simpa using he.symm
  have h := Complex.exp_log (by norm_num : (2 : ℂ) ≠ 0)
  rw [hl] at h
  norm_num at h

def family : Registration arena (type_of% full_event) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨full_event, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    full_event (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.PowerSeries.BalaBilateralLog.unit
  realizationName := `Reg.D5.S3.Analytic.PowerSeries.BalaBilateralLog.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => Complex.log z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PowerSeries.BalaBilateralLog
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end
end Reg.D5.S3.Analytic.PowerSeries.BalaBilateralLog
