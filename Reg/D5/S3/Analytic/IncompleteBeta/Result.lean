import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.IncompleteBeta.Result
import Reg.Support.SingleDependentReadout

/-! Dependent-family evidence for the coefficient convolution comparison. -/

open _root_.D5.S3.Analytic.IncompleteBeta
open _root_.D5.S3.Analytic.IncompleteBeta.Result
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set

namespace Reg.D5.S3.Analytic.IncompleteBeta.Result
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℝ, Σ _ : ℝ, ℕ) (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ q d => convolution q.1 (q.2.1+d) (q.2.1-d) q.2.2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {a m : ℝ}, 0 < a → 0 < m → ∀ n : ℕ,
    StrictAntiOn (R.readout () ⟨a, m, n⟩) (Ico 0 m)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have H := h (a := 1) (m := 1) (by norm_num) (by norm_num) 0
    (show (0:ℝ) ∈ Ico 0 1 by norm_num)
    (show (1/2:ℝ) ∈ Ico 0 1 by norm_num) (by norm_num : (0:ℝ)<1/2)
  exact (lt_irrefl (0:ℝ)) H

def family : Registration arena (type_of% @convolution_strictAnti_imbalance) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@convolution_strictAnti_imbalance, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨⟨1, 1, 0⟩, 0, 1/2, ?_⟩
    have H := convolution_strictAnti_imbalance (a := 1) (m := 1)
      (by norm_num) (by norm_num) 0
      (show (0:ℝ) ∈ Ico 0 1 by norm_num)
      (show (1/2:ℝ) ∈ Ico 0 1 by norm_num) (by norm_num : (0:ℝ)<1/2)
    exact ne_of_gt H

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@convolution_strictAnti_imbalance) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.IncompleteBeta.Result.unit
  realizationName := `Reg.D5.S3.Analytic.IncompleteBeta.Result.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ q d => convolution q.1 (q.2.1+d) (q.2.1-d) q.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.IncompleteBeta.Result
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end
end Reg.D5.S3.Analytic.IncompleteBeta.Result
