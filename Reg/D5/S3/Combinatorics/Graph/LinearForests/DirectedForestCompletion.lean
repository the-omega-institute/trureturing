import D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The actual completion family and its endpoint readout. -/
namespace Reg.D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion
open _root_.D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Equiv Relation
noncomputable section
attribute [local instance] Classical.propDecidable
universe u

abbrev signature : Signature where
  Params := Σ V : Type u, V → V → Prop
  State p := CycleCompletion p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Perm p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ σ => σ.1) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => Equiv.refl _) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Finite V] (E : V → V → Prop),
    Relator.RightUnique E → Relator.LeftUnique E →
    (∀ x, ¬ TransGen E x x) → 2 ≤ Nat.card (Component E) →
    ∃ (q : Component E ≃ Tail E) (h : Component E ≃ Head E)
      (Φ : CycleCompletion E ≃ FullCycle (Component E)),
      (∀ A, Quotient.mk (EqvGen.setoid E) (q A).1 = A) ∧
      (∀ A, Quotient.mk (EqvGen.setoid E) (h A).1 = A) ∧
      (∀ σ A, R.readout () ⟨V, E⟩ σ (q A) = h ((Φ σ).1 A)) ∧
      Nonempty (CycleCompletion E) ∧
      Nat.card (CycleCompletion E) = (Nat.card (Component E) - 1).factorial ∧
      UniformCompletionLaw E q h Φ

private theorem source_bridge :
    (type_of% @directed_forest_completion.{u}) ↔ arena.{u}.Law actual := Iff.rfl

private def emptyComponentEquiv (V : Type u) :
    Component (fun (_ _ : V) => False) ≃ V where
  toFun := Quotient.lift id (by
    intro x y h
    induction h with
    | rel _ _ h => exact h.elim
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)
  invFun := Quotient.mk _
  left_inv := by intro A; induction A using Quotient.inductionOn; rfl
  right_inv := fun _ => rfl

private theorem empty_acyclic (V : Type u) :
    ∀ x, ¬ TransGen (fun (_ _ : V) => False) x x := by
  intro x h
  cases h with
  | single h => exact h
  | tail _ h => exact h

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  let V := ULift.{u} (Fin 2)
  let E : V → V → Prop := fun _ _ => False
  let e : Component E ≃ V := emptyComponentEquiv V
  have hc : 2 ≤ Nat.card (Component E) := by
    rw [Nat.card_congr e]
    simp [V]
  obtain ⟨q, h, Φ, hq, hh, hΦ, hne, _, _⟩ := law E
    (fun _ _ _ h => h.elim) (fun _ _ _ h => h.elim) (empty_acyclic V) hc
  let : Nontrivial (Component E) := e.nontrivial_congr.mpr inferInstance
  let σ : CycleCompletion E := Classical.choice hne
  let A : Component E := Quotient.mk _ (⟨0⟩ : V)
  have he : (q A).1 = (h ((Φ σ).1 A)).1 := hΦ σ A
  have hec := congrArg (Quotient.mk (EqvGen.setoid E)) he
  rw [hq A, hh ((Φ σ).1 A)] at hec
  exact (Φ σ).2.apply_ne Set.nontrivial_univ (Set.mem_univ A) hec.symm

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let V := ULift.{u} (Fin 3)
  let E : V → V → Prop := fun _ _ => False
  have hc : 2 ≤ Nat.card (Component E) := by
    rw [Nat.card_congr (emptyComponentEquiv V)]
    simp [V]
  obtain ⟨_, _, _, _, _, _, _, hcard, _⟩ := directed_forest_completion E
    (fun _ _ _ h => h.elim) (fun _ _ _ h => h.elim) (empty_acyclic V) hc
  have htwo : Nat.card (CycleCompletion E) = 2 := by
    rw [hcard, Nat.card_congr (emptyComponentEquiv V)]
    norm_num [V]
  let := Fintype.ofFinite (CycleCompletion E)
  let : Nontrivial (CycleCompletion E) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      rw [← Nat.card_eq_fintype_card, htwo]
      decide)
  obtain ⟨σ, τ, hne⟩ := exists_pair_ne (CycleCompletion E)
  refine ⟨⟨V, E⟩, σ, τ, ?_⟩
  intro he
  exact hne (Subtype.ext he)

def family : Registration arena.{u} (type_of% @directed_forest_completion.{u}) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp @directed_forest_completion.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@directed_forest_completion.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion.unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ σ => σ.1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "arg", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion
