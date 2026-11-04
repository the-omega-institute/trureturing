import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.TsiCoordinationSequence
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the tsi shell count in the odd coordination formula. -/

namespace Reg.D5.S3.StatisticalMechanics.TsiCoordinationSequence

open _root_.D5.S3.StatisticalMechanics.TsiCoordinationSequence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => shell n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ n : ℕ, 0 < n → Even n →
      2 * shell n = 13 * n ^ 2 + 4) ∧
    (∀ n : ℕ, Odd n →
      2 * R.readout () () n = 13 * n ^ 2 + 3)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.2 1 (by decide)
  norm_num [rejected, realize] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 3, ?_⟩
  change shell 1 ≠ shell 3
  have h1 := result.2 1 (by decide)
  have h3 := result.2 3 (by decide)
  omega

def source_registration : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.StatisticalMechanics.TsiCoordinationSequence.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.TsiCoordinationSequence.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => shell n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.TsiCoordinationSequence
    definition := some {
      owner := `D5.S3.StatisticalMechanics.TsiCoordinationSequence
      name := `D5.S3.StatisticalMechanics.TsiCoordinationSequence.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.StatisticalMechanics.TsiCoordinationSequence
