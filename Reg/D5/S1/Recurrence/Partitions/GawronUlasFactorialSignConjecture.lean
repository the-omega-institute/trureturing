import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Partitions.GawronUlasFactorialSignConjecture
import Reg.Support.DependentFamily

/-! Source-bound audit of the published partition parts identity. -/

namespace Reg.D5.S1.Recurrence.Partitions.GawronUlasFactorialSignConjecture

open _root_.D5.S1.Recurrence.Partitions.GawronUlasFactorialSignConjecture
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the published partition parts coordinate over its admissible parameters. -/
abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Multiset ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p z =>
      Multiset.replicate (p.1 - 2 * p.2 - 6 * z) 1 +
        Multiset.replicate p.2 2 + Multiset.replicate z 6)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n y z : ℕ) (h : 2 * y + 6 * z ≤ n),
    (partition126 n y z h).parts = r.readout () ⟨n, y⟩ z

private theorem actual_law : arena.Law actual := by
  intro n y z h
  simpa [actual, realize] using partition126_parts n y z h

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 2 1 0 (by decide)
  rw [partition126_parts] at hbad
  change ({2} : Multiset ℕ) = 0 at hbad
  norm_num at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, 1⟩, 0, 1, ?_⟩
  change
    (Multiset.replicate (2 - 2 * 1 - 6 * 0) 1 +
      Multiset.replicate 1 2 + Multiset.replicate 0 6) ≠
    (Multiset.replicate (2 - 2 * 1 - 6 * 1) 1 +
      Multiset.replicate 1 2 + Multiset.replicate 1 6)
  intro he
  have hc := congrArg (Multiset.count 6) he
  simp at hc

def source_registration : Registration arena (type_of% @partition126_parts) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S1.Recurrence.Partitions.GawronUlasFactorialSignConjecture.partition126_parts)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S1.Recurrence.Partitions.GawronUlasFactorialSignConjecture.unit
  realizationName :=
    `Reg.D5.S1.Recurrence.Partitions.GawronUlasFactorialSignConjecture.source_registration
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
    (realize signature
      (fun _ p z =>
        Multiset.replicate (p.1 - 2 * p.2 - 6 * z) 1 +
          Multiset.replicate p.2 2 + Multiset.replicate z 6)
      (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Partitions.GawronUlasFactorialSignConjecture
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
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
end Reg.D5.S1.Recurrence.Partitions.GawronUlasFactorialSignConjecture
