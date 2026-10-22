import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.ExpRatioCM.Positive
import Reg.D5.S3.Analytic.ExpRatioCM.Extraction

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.ExpRatioCM.Defs
open _root_.D5.S3.Analytic.ExpRatioCM.Positive
open LeanInformationAudit
open Set

noncomputable section
namespace Reg.D5.S3.Analytic.ExpRatioCM.Positive

abbrev functionSignature := _root_.Reg.D5.S3.Analytic.ExpRatioCM.Extraction.functionSignature
abbrev functionActual := _root_.Reg.D5.S3.Analytic.ExpRatioCM.Extraction.functionActual

def negativeFunction : Realization functionSignature :=
  realize functionSignature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

private theorem negative_not_cm : ¬ CompletelyMonotoneOn (fun _ : ℝ => (-1 : ℝ)) := by
  intro h
  have hz := h.2 0 1 (by norm_num)
  norm_num at hz

namespace Criterion

def arena : Arena where
  signature := functionSignature
  Law R := ∀ {h : ℝ → ℝ} {c r : ℕ → ℝ},
    ContDiffOn ℝ ⊤ h (Ioi 0) →
    (∀ k : ℕ, ∀ t : ℝ, 0 < t →
      iteratedDeriv k h t = (-1 : ℝ) ^ k *
        (∑' n : ℕ, c n * r n ^ k * Real.exp (-r n * t))) →
    (∀ n : ℕ, 0 ≤ c n) → (∀ n : ℕ, 0 ≤ r n) →
    CompletelyMonotoneOn (R.readout () h)

private theorem rejected : ¬ arena.Law negativeFunction := by
  intro h
  have hz := @h (fun _ => 0) (fun _ => 0) (fun _ => 0) contDiffOn_const
    (fun k t ht => by simp) (fun n => le_refl _) (fun n => le_refl _)
  exact negative_not_cm hz

def family : Registration arena (type_of% @cm_of_nonnegative_exponential_expansion) where
  actual := functionActual
  bridge := Iff.rfl
  variation := ⟨@cm_of_nonnegative_exponential_expansion, negativeFunction, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law functionActual negativeFunction rejected
  dependence := _root_.Reg.D5.S3.Analytic.ExpRatioCM.Extraction.Obstruction.family.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cm_of_nonnegative_exponential_expansion) (Realization functionSignature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Positive.Criterion.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Positive.Criterion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize functionSignature (fun _ h t => h t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Positive
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end Criterion

abbrev signature := _root_.Reg.D5.S3.Analytic.ExpRatioCM.Series.momentSignature
abbrev actual := _root_.Reg.D5.S3.Analytic.ExpRatioCM.Series.ratioActual

def negativeRatio : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

namespace LowIndices

def arena : Arena where
  signature := signature
  Law R := ∀ (i : ℕ), i ≤ 2 →
    CompletelyMonotoneOn (R.readout () i) ∧ CompletelyMonotoneOn (ratioG i)

private theorem rejected : ¬ arena.Law negativeRatio := by
  intro h
  exact negative_not_cm (h 0 (by norm_num)).1

def family : Registration arena (type_of% @cm_of_le_two) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cm_of_le_two, negativeRatio, rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual negativeRatio rejected
  dependence := _root_.Reg.D5.S3.Analytic.ExpRatioCM.Series.FirstRatioSmooth.family.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cm_of_le_two) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.ExpRatioCM.Positive.LowIndices.unit
  realizationName := `Reg.D5.S3.Analytic.ExpRatioCM.Positive.LowIndices.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ i t => ratioF i t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.ExpRatioCM.Positive
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit
end LowIndices

end Reg.D5.S3.Analytic.ExpRatioCM.Positive
end
