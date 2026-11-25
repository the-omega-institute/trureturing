import D5.S1.Words.Powers.ConjugacyNormalForm
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option Elab.async false

open D5.S1.Words.Powers
open D5.S1.Words.Powers.ConjugacyNormalForm
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S1.Words.Powers.ConjugacyNormalForm

universe u

abbrev signature : Signature where
  Params := Σ α : Type u, List α
  State p := List p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := List p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p z => p.2 ++ z) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e _ => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α : Type u} (a b z : List α), a ≠ [] →
    (R.readout () ⟨α, a⟩ z = z ++ b ↔ ∃! t : Nat × List α × List α,
      a = t.2.1 ++ t.2.2 ∧ b = t.2.2 ++ t.2.1 ∧
        z = wordPower t.1 a ++ t.2.1 ∧ t.2.1.length < a.length)

private theorem rejected_law : ¬ arena.Law rejected.{u} := by
  intro h
  have impossible :=
    (conjugacy_iff_exists_unique_short_cut ([ULift.up ()] : List (ULift.{u} Unit)) [] []
      (by simp)).mpr
      ((h [ULift.up ()] [] [] (by simp)).mp rfl)
  simpa using impossible

def family : Registration arena (∀ {α : Type u} (a b z : List α), a ≠ [] →
    (a ++ z = z ++ b ↔ ∃! t : Nat × List α × List α,
      a = t.2.1 ++ t.2.2 ∧ b = t.2.2 ++ t.2.1 ∧
        z = wordPower t.1 a ++ t.2.1 ∧ t.2.1.length < a.length)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨conjugacy_iff_exists_unique_short_cut, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨⟨ULift.{u} Unit, [ULift.up ()]⟩, [], [ULift.up ()], by simp [actual, realize]⟩

noncomputable def audit : Contract.Registration
    (@conjugacy_iff_exists_unique_short_cut.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S1.Words.Powers.ConjugacyNormalForm.conjugacy_iff_exists_unique_short_cut.__information_unit,
  realizationName := `Reg.D5.S1.Words.Powers.ConjugacyNormalForm.family,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨family⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p z => p.2 ++ z) (fun e _ => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S1.Words.Powers.ConjugacyNormalForm
    definition := none
    coordinates := #[0, 1],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

end Reg.D5.S1.Words.Powers.ConjugacyNormalForm
