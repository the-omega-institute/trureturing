import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses
import Reg.Support.DependentFamily

/-! Source-bound audit of the transposition degree in the tensor leading classes. -/

namespace Reg.D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses

open _root_.D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses
open _root_.D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity (onesPartition)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the transposition degree as the tensor exponent varies. -/
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n s => degree s (transpositionClass n)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain both closed forms and the complete ordering of partition classes. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ n ≥ 2, ∀ s ≥ 1,
    degree s (onesPartition n) = (n : ℚ) ^ s ∧
      r.readout () n s = ((n : ℚ) ^ s + ((n - 2 : ℕ) : ℚ) ^ s) / 2 ∧
      degree s (transpositionClass n) < degree s (onesPartition n) ∧
      ∀ p : Nat.Partition n,
        p ≠ onesPartition n → p ≠ transpositionClass n →
          degree s p < degree s (transpositionClass n)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 2 (by decide) 1 (by decide)).2.1
  change (0 : ℚ) = ((2 : ℚ) ^ 1 + ((2 - 2 : ℕ) : ℚ) ^ 1) / 2 at hbad
  norm_num at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 1, 2, ?_⟩
  change degree 1 (transpositionClass 2) ≠ degree 2 (transpositionClass 2)
  rw [(result 2 (by decide) 1 (by decide)).2.1,
    (result 2 (by decide) 2 (by decide)).2.1]
  norm_num

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ n s => degree s (transpositionClass n)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses
    definition := some {
      owner := `D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses
      name := `D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses
