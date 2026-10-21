import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Result
import Reg.Support.SingleDependentReadout

/-! A source-bound audit of the interior evaluation point. -/

noncomputable section
open _root_.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Defs
open _root_.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Result
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ENNReal

namespace Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Result

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p : ℝ} {q : ℝ≥0∞} {α : ℝ},
    0 < p → ENNReal.ofReal p < q → 0 < α →
    ∃ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball 0 1) ∧
      mixedNorm (ENNReal.ofReal p) q α f < ∞ ∧
      ∃ z : ℂ, R.readout () () z < 1 ∧ mixedNorm (ENNReal.ofReal p) q α f <
        ENNReal.ofReal ‖f z‖ *
          ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ (α + 1 / (ENNReal.ofReal p).toReal))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨f, _, _, z, hz, _⟩ := h (p := 1) (q := 2) (α := 1)
    (by norm_num) (by norm_num) (by norm_num)
  exact (lt_irrefl (1 : ℝ)) hz

def registration : Registration arena (type_of% @fails_off_contractive_range) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fails_off_contractive_range, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@fails_off_contractive_range) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Result.fails_off_contractive_range.audit
  realizationName :=
    `Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Result.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Result
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "arg", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Result
