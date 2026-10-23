import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.IncompleteBeta.Comparison
import D5.S3.Analytic.IncompleteBeta.Moment
import Reg.Support.SingleDependentReadout

/-! Dependent-family evidence for the strict beta comparison. -/

open _root_.D5.S3.Analytic.IncompleteBeta.Comparison
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set

namespace Reg.D5.S3.Analytic.IncompleteBeta.Comparison
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℝ → ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ q d => betaMean q.1 q.2 d) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {W : ℝ → ℝ}, ContinuousOn W (Icc 0 1) →
    (∀ u ∈ Icc 0 1, W (1-u) = W u) →
    StrictMonoOn W (Ioc 0 (1/2)) → ∀ {m : ℝ}, 0 < m →
    StrictAntiOn (R.readout () ⟨W, m⟩) (Ico 0 m)

private theorem quadratic_mono : StrictMonoOn (fun u : ℝ => u * (1-u)) (Ioc 0 (1/2)) := by
  have h := (_root_.D5.S3.Analytic.IncompleteBeta.Moment.W_strictMonoOn
    (a := 1) (by norm_num) 0).mono Ioc_subset_Icc_self
  have hW : _root_.D5.S3.Analytic.IncompleteBeta.W 1 0 =
      (fun u : ℝ => u * (1-u)) := by
    funext u
    delta _root_.D5.S3.Analytic.IncompleteBeta.W
    norm_num [Real.Gamma_add_one]
  simpa only [hW] using h

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := h (W := fun u => u * (1-u)) (by fun_prop)
    (by intro u _; ring) quadratic_mono (m := 1) (by norm_num)
    (show (0:ℝ) ∈ Ico 0 1 by norm_num)
    (show (1/2:ℝ) ∈ Ico 0 1 by norm_num) (by norm_num : (0:ℝ)<1/2)
  exact (lt_irrefl (0:ℝ)) H

def family : Registration arena (type_of% @betaMean_strictAntiOn) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@betaMean_strictAntiOn, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨⟨fun u : ℝ => u * (1-u), 1⟩, 0, 1/2, ?_⟩
    have H := betaMean_strictAntiOn (W := fun u => u * (1-u)) (by fun_prop)
      (by intro u _; ring) quadratic_mono (m := 1) (by norm_num)
      (show (0:ℝ) ∈ Ico 0 1 by norm_num)
      (show (1/2:ℝ) ∈ Ico 0 1 by norm_num) (by norm_num : (0:ℝ)<1/2)
    exact ne_of_gt H

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@betaMean_strictAntiOn) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.IncompleteBeta.Comparison.unit
  realizationName := `Reg.D5.S3.Analytic.IncompleteBeta.Comparison.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q d => betaMean q.1 q.2 d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.IncompleteBeta.Comparison
    definition := none
    coordinates := #[0, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Analytic.IncompleteBeta.Comparison
