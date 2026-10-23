import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.ToralCharacterSupport
import Reg.Support.DependentFamily

/-! # The odd-factor order in the complete support classification -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.FiniteGroups.ToralCharacterSupport

open _root_.D5.S3.FiniteGroups.ToralCharacterSupport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature := realize signature
  (fun _ _ m => m) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b m : ℕ), a ≤ b → 1 ≤ m → Odd m →
    (Supports (Source a b m) ↔ a = 1 ∧ b = 1 ∧ R.readout () ⟨a, b⟩ m = 3)

private theorem actual_law : arena.Law actual := support_iff

noncomputable def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hpos := (support_iff 1 1 3 (by omega) (by omega) (by decide)).mpr ⟨rfl, rfl, rfl⟩
  have heq := ((h 1 1 3 (by omega) (by omega) (by decide)).mp hpos).2.2
  exact (by decide : (0 : ℕ) ≠ 3) heq

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨1, 1⟩, 3, 1, ?_⟩
  change (3 : ℕ) ≠ 1
  decide

noncomputable def sourceRegistration : Registration arena (type_of% support_iff) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.FiniteGroups.ToralCharacterSupport.support_iff)
      (Realization signature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.ToralCharacterSupport.support_iff.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.ToralCharacterSupport.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ m => m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.ToralCharacterSupport
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.ToralCharacterSupport
