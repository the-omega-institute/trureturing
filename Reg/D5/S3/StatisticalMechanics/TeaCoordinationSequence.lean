import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.TeaCoordinationSequence
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the tea shell count; hexagon, hexagon_mem and hexagon_card are shared source interfaces. -/

namespace Reg.D5.S3.StatisticalMechanics.TeaCoordinationSequence

open _root_.D5.S3.StatisticalMechanics.TeaCoordinationSequence
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
  Law R := ∀ n : ℕ, 0 < n →
    (n % 4 = 0 → 8 * R.readout () () n = 63 * n ^ 2 + 16) ∧
    (n % 4 = 1 → 8 * R.readout () () n = 63 * n ^ 2 + 17) ∧
    (n % 4 = 2 → 8 * R.readout () () n = 63 * n ^ 2 + 12) ∧
    (n % 4 = 3 → 8 * R.readout () () n = 63 * n ^ 2 + 17)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h 4 (by decide)).1 (by decide)
  norm_num [rejected, realize] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 4, 8, ?_⟩
  change shell 4 ≠ shell 8
  have h4 := (result 4 (by decide)).1 (by decide)
  have h8 := (result 8 (by decide)).1 (by decide)
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
  unitName := `Reg.D5.S3.StatisticalMechanics.TeaCoordinationSequence.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.TeaCoordinationSequence.source_registration
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
    owner := `D5.S3.StatisticalMechanics.TeaCoordinationSequence
    definition := some {
      owner := `D5.S3.StatisticalMechanics.TeaCoordinationSequence
      name := `D5.S3.StatisticalMechanics.TeaCoordinationSequence.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print _root_.D5.S3.StatisticalMechanics.TeaCoordinationSequence.result
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.StatisticalMechanics.TeaCoordinationSequence
