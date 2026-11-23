import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S1.Words.AdmissibleWords.FIBCycleRelaxation

/-! Source observation for the common pair-distance family. -/

set_option autoImplicit false

namespace Reg.D5.S1.Words.AdmissibleWords.FIBCycleRelaxation

open LeanInformationAudit
open _root_.D5.S1.Words.AdmissibleWords.FIBCycleRelaxation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

private abbrev signature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 6 → Fin 6 → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ p b => completion p.1 p.2.1 p.2.2 b (max p.2.2 (2 * b)))
    (fun a => nomatch a)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => 2) (fun a => nomatch a)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {q c a b : ℝ}, 0 ≤ q → 0 ≤ c → q + c ≤ 1 →
    (HasCycleCompletion (R.readout () ⟨q, c, a⟩ b) ↔
      (0 ≤ a ∧ a ≤ q ∧ a ≤ c) ∧ (0 ≤ b ∧ b ≤ q ∧ b ≤ c ∧ b ≤ 1 - (q + c)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨d, symmetric, valid, agrees⟩ :=
    (h (q := 0) (c := 0) (a := 0) (b := 0) le_rfl le_rfl (by norm_num)).2 (by norm_num)
  have os : d 0 1 = 2 := agrees (0, 1) (by decide)
  have sh : d 1 2 = 2 := agrees (1, 2) (by decide)
  have oh : d 0 2 = 2 := agrees (0, 2) (by decide)
  have impossible := valid 0 [(1, true), (2, false)]
  change (1 : ℝ) ≤ (1 - d 0 1) + ((1 - d 1 2) + (1 - d 2 0)) at impossible
  rw [os, sh, symmetric 2 0, oh] at impossible
  norm_num at impossible

def familyRegistration : Registration arena (type_of% (@cycle_completion_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cycle_completion_iff, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := by
    rintro ⟨⟩
    refine ⟨⟨0, 0, 0⟩, 0, 1, ?_⟩
    intro equal
    have read := congrFun (congrFun equal 4) 2
    change (0 : ℝ) + 2 * 0 = 0 + 2 * 1 at read
    norm_num at read

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cycle_completion_iff) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.FIBCycleRelaxation.cycle_completion_iff.audit
  realizationName := `Reg.D5.S1.Words.AdmissibleWords.FIBCycleRelaxation.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p b => completion p.1 p.2.1 p.2.2 b (max p.2.2 (2 * b))) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.FIBCycleRelaxation
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S1.Words.AdmissibleWords.FIBCycleRelaxation
