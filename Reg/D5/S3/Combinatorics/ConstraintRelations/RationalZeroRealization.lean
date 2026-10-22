import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.ConstraintRelations.RationalZeroRealization

/-! # Source-bound audit of exact finite rational realization -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.ConstraintRelations.RationalZeroRealization

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.ConstraintRelations.RationalZeroRealization
open _root_.D5.S3.ConceptDynamics.InformationEscape

noncomputable section
attribute [local instance] Classical.propDecidable

def signature : DependentFamily.Signature where
  Params := Σ n : Nat, Σ m : Nat, Σ k : Nat, Network n m k
  State := fun p => Fin p.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ p a => p.2.2.2.law a) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun R => ∀ (n : Nat), 1 ≤ n → ∀ P : (Fin n → Bool) → ℚ,
    (∀ a, 0 ≤ P a) → (∑ a, P a = 1) →
    ∃ m k : Nat, ∃ net : Network n m k,
      0 < net.partition ∧ ∀ a, R.readout () ⟨n, m, k, net⟩ a = P a

abbrev sourceScope := type_of% (@result)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := source_bridge.mp result

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : ℚ)) (fun e => nomatch e)

def delta : (Fin 1 → Bool) → ℚ := fun a => if a = (fun _ => false) then 1 else 0

theorem delta_nonneg : ∀ a, 0 ≤ delta a := by
  intro a; unfold delta; split <;> norm_num

theorem delta_sum : ∑ a, delta a = 1 := by classical simp [delta]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨m, k, net, _, hl⟩ := h 1 (by decide) delta delta_nonneg delta_sum
  have hf := hl (fun _ => false)
  change (0 : ℚ) = delta (fun _ => false) at hf
  norm_num [delta] at hf

def familyRegistration : DependentFamily.Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_positive, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (@Subsingleton.elim Unit _ j i)).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    obtain ⟨m, k, net, _, hl⟩ := result 1 (by decide) delta delta_nonneg delta_sum
    refine ⟨⟨1, m, k, net⟩, (fun _ => false), (fun _ => true), ?_⟩
    change net.law (fun _ => false) ≠ net.law (fun _ => true)
    rw [hl, hl]
    norm_num [delta, funext_iff]

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@result) (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.ConstraintRelations.RationalZeroRealization.result.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.ConstraintRelations.RationalZeroRealization.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun _ p a => p.2.2.2.law a) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.ConstraintRelations.RationalZeroRealization
    definition := none
    coordinates := #[0, 5, 6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "body", "arg", "body", "fn", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration
end
end Reg.D5.S3.Combinatorics.ConstraintRelations.RationalZeroRealization
