import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.FirstOrderGap
import Reg.Support.DependentFamily

/-! A source-bound audit of the positive separating parameter. -/

noncomputable section
namespace Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.FirstOrderGap
open _root_.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Radial
open _root_.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.FirstOrderGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ t => t) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {p q α : ℝ}, 0 < p → p < q → 0 < α →
    ∃ t : ℝ, 0 < R.readout () () t ∧ t < 1 ∧
      radialIntegral p q α t < evaluationExcess p q α t

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨t, ht, _, _⟩ := h (p := 1) (q := 2) (α := 1)
    (by norm_num) (by norm_num) (by norm_num)
  exact (lt_irrefl (0 : ℝ)) ht

def registration : Registration arena (type_of% @exists_gap) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_gap, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    change ∃ (_ : Unit) (x y : ℝ), x ≠ y
    exact ⟨(), 0, 1, zero_ne_one⟩

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_gap)
    (type_of% (realize signature (fun _ _ t => t) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.FirstOrderGap.exists_gap.audit
  realizationName :=
    `Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.FirstOrderGap.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.FirstOrderGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "body", "fn", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit
end Reg.D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.FirstOrderGap
