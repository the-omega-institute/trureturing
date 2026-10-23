import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization

/-! # Source-bound classification of strictly positive five-mode networks -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.ConstraintRelations.RationalZeroRealization
open _root_.D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization
open _root_.D5.S3.ConceptDynamics.InformationEscape

noncomputable section
attribute [local instance] Classical.propDecidable

def signature : DependentFamily.Signature where
  Params := Σ n : Nat, Σ m : Nat, Σ k : Nat, Network n m k
  State p := Fin p.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ p a => p.2.2.2.law a) (fun e => nomatch e)

def arena : DependentFamily.Arena where
  signature := signature
  Law R := ∀ (n : Nat) (P : (Fin n → Bool) → ℚ),
    (∀ a, 0 ≤ P a) → (∑ a, P a = 1) →
    ((∃ m k : Nat, ∃ net : Network n m k,
      (∀ j, Strict (net.factor j).table) ∧ 0 < net.partition ∧
        ∀ a, R.readout () ⟨n, m, k, net⟩ a = P a) ↔
      ∃ K : LoopGraph n, ∀ a, 0 < P a ↔ Independent K a)

abbrev sourceScope := type_of%
  (@_root_.D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization.result)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem actual_positive : arena.Law actual := source_bridge.mp
  _root_.D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization.result

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ => (0 : ℚ)) (fun e => nomatch e)

def delta : (Fin 1 → Bool) → ℚ := fun a => if a = (fun _ => false) then 1 else 0

def loop : LoopGraph 1 where
  edge _ _ := True
  symm := by intros; trivial

theorem delta_nonneg : ∀ a, 0 ≤ delta a := by
  intro a; unfold delta; split <;> norm_num

theorem delta_sum : ∑ a, delta a = 1 := by classical simp [delta]

theorem delta_support : ∀ a, 0 < delta a ↔ Independent loop a := by
  intro a
  have hi : Independent loop a ↔ a = (fun _ => false) := by
    constructor
    · intro h
      have hz := h 0 0 trivial
      have hb : a 0 = false := by cases hv : a 0 <;> simpa [hv] using hz
      funext i
      have he : i = 0 := Subsingleton.elim _ _
      simpa [he] using hb
    · intro h
      subst a
      intro i j _; rfl
  rw [hi]
  by_cases ha : a = (fun _ => false) <;> simp [delta, ha]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨m, k, net, _, _, hl⟩ :=
    (h 1 delta delta_nonneg delta_sum).mpr ⟨loop, delta_support⟩
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
    obtain ⟨m, k, net, _, _, hl⟩ :=
      (_root_.D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization.result
        1 delta delta_nonneg delta_sum).mpr ⟨loop, delta_support⟩
    refine ⟨⟨1, m, k, net⟩, (fun _ => false), (fun _ => true), ?_⟩
    change net.law (fun _ => false) ≠ net.law (fun _ => true)
    rw [hl, hl]
    norm_num [delta, funext_iff]

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@_root_.D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization.result)
      (DependentFamily.Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization.result.__information_unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization.familyRegistration
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
    owner := `D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization
    definition := none
    coordinates := #[0, 4, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg",
        "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration
end
end Reg.D5.S3.Combinatorics.ConstraintRelations.RationalPositiveRealization
