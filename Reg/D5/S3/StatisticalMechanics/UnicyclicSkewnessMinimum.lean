import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum
import Reg.Support.DependentFamily

/-! Source-bound audit of the sharp minimum of unicyclic current skewness. -/

namespace Reg.D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum

open _root_.D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the sharp minimum as the number of cycle states varies. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => minimumValue n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain attainment and the universal lower bound over all positive rate vectors. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, 2 ≤ n →
    IsLeast {s : ℝ | ∃ k : Fin n → ℝ, (∀ i, 0 < k i) ∧ s = skewness k}
      (r.readout () () n)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hvalue := (result 2 (by norm_num)).unique (h 2 (by norm_num))
  change minimumValue 2 = 0 at hvalue
  norm_num [minimumValue] at hvalue

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 3, ?_⟩
  change minimumValue 2 ≠ minimumValue 3
  norm_num [minimumValue]

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
      (@_root_.D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.unit
  realizationName :=
    `Reg.D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.source_registration
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
    (realize signature (fun _ _ n => minimumValue n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum
    definition := some {
      owner := `D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum
      name := `D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
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
end Reg.D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum
