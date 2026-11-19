import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.SandpileCompleteMaximalIdentity
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the complete maximal identity classification. -/

namespace Reg.D5.S3.StatisticalMechanics.SandpileCompleteMaximalIdentity
open _root_.D5.S3.StatisticalMechanics.SandpileCompleteMaximalIdentity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the classification predicate as the path length varies. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ i j => @decide (i = 4 ∧ j = 2) (Classical.propDecidable _))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ i j : ℕ, 2 ≤ i → 2 ≤ j →
    ((∀ s : Fin i × Fin j, maximalIdentityAt i j s) ↔ R.readout () i j = true)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := (h 4 2 (by omega) (by omega)).mp
    ((result 4 2 (by omega) (by omega)).mpr ⟨rfl, rfl⟩)
  norm_num [rejected, realize] at hb

theorem dependence : ObservationalDependence signature actual := by
  intro r
  refine ⟨4, 2, 3, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena claim where
  actual := actual
  bridge := by simp [actual, realize, claim]
  variation := ⟨by simpa [arena, actual, realize, claim] using result,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.StatisticalMechanics.SandpileCompleteMaximalIdentity.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.StatisticalMechanics.SandpileCompleteMaximalIdentity.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.SandpileCompleteMaximalIdentity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ i j => @decide (i = 4 ∧ j = 2) (Classical.propDecidable _))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.SandpileCompleteMaximalIdentity
    definition := some {
      owner := `D5.S3.StatisticalMechanics.SandpileCompleteMaximalIdentity
      name := `D5.S3.StatisticalMechanics.SandpileCompleteMaximalIdentity.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.StatisticalMechanics.SandpileCompleteMaximalIdentity
