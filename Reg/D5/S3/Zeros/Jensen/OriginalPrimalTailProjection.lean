import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
open LeanInformationAudit MeasureTheory Set Real

noncomputable section
namespace Reg.D5.S3.Zeros.Jensen.OriginalPrimalTailProjection

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => |x|) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ a : ℝ, 0 < a →
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∀ α : ℝ, 0 ≤ α → α ≤ a →
      ContDiff ℝ 4 (originalTail N) ∧
      originalFlux N = -deriv (originalTail N) 0 ∧ 0 < originalFlux N ∧
      IntegrableOn (fun x : ℝ => exp (a*x^2/2)*
        R.readout () () (densityAdjoint α (densityAdjoint α (originalTail N)) x)) (Ioi 0) ∧
      |deriv (densityAdjoint α (originalTail N)) 0|+
        (∫ x in Ioi (0 : ℝ), exp (a*x^2/2)*
          |densityAdjoint α (densityAdjoint α (originalTail N)) x|) ≤
            C*((N : ℝ)+1)^4*originalFlux N

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨C, _, hC⟩ := h 1 (by norm_num)
  have hi := (hC 1 (by omega) 0 (by norm_num) (by norm_num)).2.2.2.1
  change IntegrableOn (fun x : ℝ => exp (1*x^2/2)*1) (Ioi 0) at hi
  have hc : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Ioi (0 : ℝ))) := by
    apply hi.mono' aestronglyMeasurable_const
    exact Filter.Eventually.of_forall (fun x => by
      simp only [Real.norm_eq_abs, abs_one, mul_one, one_mul]
      exact one_le_exp (by positivity))
  have hfinite := (integrable_const_iff_isFiniteMeasure (c := (1 : ℝ)) one_ne_zero).mp hc
  have hnot : ¬IsFiniteMeasure (volume.restrict (Ioi (0 : ℝ))) := by
    rw [not_isFiniteMeasure_iff]
    simp [volume_Ioi]
  exact hnot hfinite

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change |(0 : ℝ)| ≠ |(1 : ℝ)|
  norm_num

def evidence : Registration arena (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨original_primal_tail_budget, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

noncomputable def registration_1 :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Zeros.Jensen.OriginalPrimalTailProjection.original_primal_tail_budget)
    (type_of% (realize signature (fun _ _ x => |x|) (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Zeros.Jensen.OriginalPrimalTailProjection.absolute_budget_unit
  realizationName := `Reg.D5.S3.Zeros.Jensen.OriginalPrimalTailProjection.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => |x|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "body", "body",
        "body", "body", "arg", "arg", "arg", "fn", "arg", "fn", "fn", "arg",
        "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration_1
end Reg.D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
