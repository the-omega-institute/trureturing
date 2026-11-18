import D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound cardinality readouts on the whole dependent families. -/
namespace Reg.D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory
open _root_.D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory
open _root_.D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Equiv Relation
noncomputable section
attribute [local instance] Classical.propDecidable
universe u

namespace Inventory
abbrev signature : Signature where
  Params := Σ C : Type u, C → Bool
  State p := p.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p d => Nat.card (Compatible p.2 d)) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {C : Type u} [Finite C] (s d : C → Bool),
    inventory s d false true = inventory s d true false →
    R.readout () ⟨C, s⟩ d =
      if Nat.card C = 0 then 0
      else if 0 < inventory s d false true then
        inventory s d false true * (Nat.card (Side s false) - 1).factorial *
          (Nat.card (Side s true) - 1).factorial
      else if inventory s d false false = 0 ∨ inventory s d true true = 0 then
        (Nat.card C - 1).factorial else 0

private theorem source_bridge :
    (type_of% @compatible_cycle_card.{u}) ↔ arena.{u}.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  have h := law (C := ULift.{u} Empty) (fun _ => false) (fun _ => false) (by
    simp [inventory, Nat.card_eq_fintype_card])
  simpa [rejected, realize] using h

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let C := ULift.{u} Unit
  let s : C → Bool := fun _ => false
  have hcard : Nat.card (Compatible s (fun _ : C => false)) = 1 := by
    rw [compatible_cycle_card s (fun _ : C => false) (by
      simp [inventory, s, Nat.card_eq_fintype_card])]
    simp [C, s, inventory, Side, Nat.card_eq_fintype_card]
  have hz : Nat.card (Compatible s (fun _ : C => true)) = 0 := by
    letI : IsEmpty (Compatible s (fun _ : C => true)) := ⟨fun σ => by
      have h := σ.2.2.2 ⟨()⟩
      exact (by decide : true ≠ false) h⟩
    simp
  refine ⟨⟨C, s⟩, (fun _ => false), (fun _ => true), ?_⟩
  change Nat.card (Compatible s (fun _ : C => false)) ≠
    Nat.card (Compatible s (fun _ : C => true))
  rw [hcard, hz]
  decide

def family : Registration arena.{u} (type_of% @compatible_cycle_card.{u}) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp @compatible_cycle_card.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@compatible_cycle_card.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory.Inventory.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory.Inventory.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p d => Nat.card (Compatible p.2 d)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Inventory

namespace Forest
abbrev signature : Signature where
  Params := Σ V : Type u, V → V → Prop
  State p := p.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p k => Nat.card (AlternatingCompletion p.2 k))
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Finite V] (n : ℕ) (E : V → V → Prop) (k : V → Bool),
    Relator.RightUnique E → Relator.LeftUnique E →
    (∀ x, ¬ TransGen E x x) → (∀ x y, E x y → k x ≠ k y) →
    Nat.card (Side k false) = n → Nat.card (Side k true) = n →
    ∃ (t : Component E ≃ Tail E) (h : Component E ≃ Head E)
      (Φ : AlternatingCompletion E k ≃
        Compatible (fun A => k (h A)) (fun A => !(k (t A)))),
      (∀ A, Quotient.mk (EqvGen.setoid E) (t A).1 = A) ∧
      (∀ A, Quotient.mk (EqvGen.setoid E) (h A).1 = A) ∧
      (∀ σ A, σ.1 (t A) = h ((Φ σ).1 A)) ∧
      let s := fun A => k (h A)
      let d := fun A => !(k (t A))
      let a := inventory s d false true
      let b := inventory s d true false
      let p := inventory s d false false
      let q := inventory s d true true
      a = b ∧ Nat.card (Component E) = a + b + p + q ∧
      (n ≠ 0 → 0 < Nat.card (Component E)) ∧
      R.readout () ⟨V, E⟩ k =
        if n = 0 then 0
        else if 0 < a then a * (a + p - 1).factorial * (a + q - 1).factorial
        else if p * q = 0 then (p + q - 1).factorial else 0

private theorem source_bridge :
    (type_of% @alternating_completion_classification.{u}) ↔ arena.{u}.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  let V := ULift.{u} Empty
  let E : V → V → Prop := fun _ _ => False
  obtain ⟨t, h, Φ, ht, hh, hΦ, hrest⟩ := law 0 E (fun _ => false)
    (by intro _ _ _ h; exact h.elim) (by intro _ _ _ h; exact h.elim)
    (by intro x; exact isEmptyElim x) (by intro x; exact isEmptyElim x)
    (by simp [V, Side]) (by simp [V, Side])
  have he := hrest.2.2.2
  simpa [rejected, realize] using he

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let V := ULift.{u} Bool
  let E : V → V → Prop := fun _ _ => False
  let k : V → Bool := ULift.down
  have hz : Nat.card (AlternatingCompletion E (fun _ => false)) = 0 := by
    letI : IsEmpty (AlternatingCompletion E (fun _ => false)) := ⟨fun σ =>
      σ.2.2.2.2 ⟨false⟩ rfl⟩
    simp
  have hp : 0 < Nat.card (AlternatingCompletion E k) := by
    apply Finite.card_pos_iff.mpr
    let σ : Perm V := swap ⟨false⟩ ⟨true⟩
    have hu : (Set.univ : Set V) = {⟨false⟩, ⟨true⟩} := by
      ext x
      rcases x with ⟨x⟩
      cases x <;> simp
    have hc : σ.IsCycleOn Set.univ := by
      rw [hu]
      exact Perm.isCycleOn_swap (by decide)
    refine ⟨⟨σ, inferInstance, hc, (by intro _ _ h; exact h.elim), ?_⟩⟩
    rintro ⟨x⟩
    cases x <;> simp [σ, k, swap_apply_def]
  refine ⟨⟨V, E⟩, (fun _ => false), k, ?_⟩
  change Nat.card (AlternatingCompletion E (fun _ => false)) ≠
    Nat.card (AlternatingCompletion E k)
  omega

def family : Registration arena.{u} (type_of% @alternating_completion_classification.{u}) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp @alternating_completion_classification.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e; exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@alternating_completion_classification.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory.Forest.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory.Forest.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p k => Nat.card (AlternatingCompletion p.2 k)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "arg", "arg", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Forest
end
end Reg.D5.S3.Combinatorics.Graph.LinearForests.CompatibleCycleInventory
