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
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fin 6 → Fin 6 → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ q c => family q c) (fun a => nomatch a)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => 2) (fun a => nomatch a)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {q c : ℝ}, 0 < c → c ≤ q → q + 2 * c ≤ 1 →
    CycleConsistent (R.readout () q c) ∧ ¬ HasJointLaw (R.readout () q c)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have impossible := (h (q := 1 / 3) (c := 1 / 3) (by norm_num) le_rfl (by norm_num)).1 0 []
  change (1 : ℝ) ≤ 1 - 2 at impossible
  norm_num at impossible

def familyRegistration : Registration arena (type_of% (@cycle_consistent_without_joint_law)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨cycle_consistent_without_joint_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := by
    rintro ⟨⟩
    refine ⟨0, 0, 1, ?_⟩
    intro equal
    have read := congrFun (congrFun equal 5) 1
    change (0 - 0) * (0 : ℝ) + 0 * 2 = (0 - 1) * 0 + 1 * 2 at read
    norm_num at read

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cycle_consistent_without_joint_law) (Realization signature) Unit Unit where
  unitName := `D5.S1.Words.AdmissibleWords.FIBCycleRelaxation.cycle_consistent_without_joint_law.audit
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
  readout := some (realize signature (fun _ q c => family q c) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.FIBCycleRelaxation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S1.Words.AdmissibleWords.FIBCycleRelaxation
