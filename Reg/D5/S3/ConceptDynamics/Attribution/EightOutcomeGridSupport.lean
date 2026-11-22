import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Attribution.EightOutcomeGridSupport
import Reg.Support.SingleDependentReadout

/-! The sharp support law depends on the supplied budget. -/

namespace Reg.D5.S3.ConceptDynamics.Attribution.EightOutcomeGridSupport

open _root_.D5.S3.ConceptDynamics.Attribution.EightOutcomeGridSupport
open _root_.D5.S3.ConceptDynamics.Attribution.PermutationGridSupport (CalibratingLaw)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Finset

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ budget => budget) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ budget : ℕ,
    (∃ (S : Type) (_ : Fintype S) (_ : MulAction (Equiv.Perm (Fin 8)) S)
      (w : S → ℝ) (f : {p : Fin 8 → ℕ // ∑ i, p i = 210} → S → Fin 8),
      CalibratingLaw S w f ∧ Fintype.card S ≤ budget) ↔
      120960 ≤ R.readout () () budget

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (by decide : ¬ 120960 ≤ (0 : ℕ))
    ((h 120960).mp ((grid_support_budget_iff 120960).mpr le_rfl))

def family : Registration arena (type_of% grid_support_budget_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨grid_support_budget_iff, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro role
    exact ⟨(), 0, 1, (by decide : (0 : ℕ) ≠ 1)⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    grid_support_budget_iff (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Attribution.EightOutcomeGridSupport.information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Attribution.EightOutcomeGridSupport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ budget => budget) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.EightOutcomeGridSupport
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.ConceptDynamics.Attribution.EightOutcomeGridSupport
