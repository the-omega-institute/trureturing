import D5.S3.Combinatorics.Graph.LinearForests.DirectedForestPathOrder
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! The path equivalences of an actual component, read out as the pulled-back edge relation. -/
namespace Reg.D5.S3.Combinatorics.Graph.LinearForests.DirectedForestPathOrder
open _root_.D5.S3.Combinatorics.Graph.LinearForests.DirectedForestCompletion
open _root_.D5.S3.Combinatorics.Graph.LinearForests.DirectedForestPathOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Relation
noncomputable section
attribute [local instance] Classical.propDecidable
universe u

/-- A graph on a vertex type together with one of its components. -/
abbrev Instance := Σ V : Type u, Σ E : V → V → Prop, Component E

abbrev signature : Signature where
  Params := Instance.{u}
  State p := Fin (Nat.card (ComponentFiber p.2.1 p.2.2)) ≃ ComponentFiber p.2.1 p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin (Nat.card (ComponentFiber p.2.1 p.2.2)) →
    Fin (Nat.card (ComponentFiber p.2.1 p.2.2)) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p e i j => p.2.1 (e i).1 (e j).1) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Finite V] (E : V → V → Prop),
    Relator.RightUnique E → Relator.LeftUnique E → (∀ x, ¬ TransGen E x x) →
    ∀ A : Component E,
      ∃! e : Fin (Nat.card (ComponentFiber E A)) ≃ ComponentFiber E A,
        ∀ i j, R.readout () ⟨V, E, A⟩ e i j ↔ i.1 + 1 = j.1

private theorem source_bridge :
    (type_of% @component_path_order.{u}) ↔ arena.{u}.Law actual := Iff.rfl

/-- The two-vertex path `0 → 1` on `ULift (Fin 2)`. -/
private def edge : ULift.{u} (Fin 2) → ULift.{u} (Fin 2) → Prop :=
  fun x y => x.down = 0 ∧ y.down = 1

private theorem edge_right_unique : Relator.RightUnique edge.{u} := by
  intro x y z hxy hxz
  exact ULift.ext (hxy.2.trans hxz.2.symm)

private theorem edge_left_unique : Relator.LeftUnique edge.{u} := by
  intro x y z hxz hyz
  exact ULift.ext (hxz.1.trans hyz.1.symm)

private theorem edge_acyclic : ∀ x, ¬ TransGen edge.{u} x x := by
  intro x h
  have key : ∀ a b, TransGen edge.{u} a b → b.down = 1 ∧ (a.down = 0) := by
    intro a b hab
    induction hab with
    | single h => exact ⟨h.2, h.1⟩
    | tail _ h ih => exact ⟨h.2, ih.2⟩
  have := key x x h
  omega

/-- The common component of both vertices. -/
private def comp : Component edge.{u} := Quotient.mk (EqvGen.setoid edge) ⟨0⟩

private def v0 : ComponentFiber edge.{u} comp := ⟨⟨0⟩, rfl⟩

private def v1 : ComponentFiber edge.{u} comp :=
  ⟨⟨1⟩, Quotient.sound (EqvGen.symm _ _ (EqvGen.rel _ _ ⟨rfl, rfl⟩))⟩

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  have := Fintype.ofFinite (ComponentFiber edge.{u} comp)
  obtain ⟨e, he, _⟩ := law edge edge_right_unique edge_left_unique edge_acyclic comp
  have hne : v0.{u} ≠ v1.{u} := by
    intro h
    have := congrArg (fun x => x.1.down) h
    simp [v0, v1] at this
  have h2 : 2 ≤ Nat.card (ComponentFiber edge.{u} comp) := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card_iff.mpr ⟨v0, v1, hne⟩
  have := (he ⟨0, by dsimp only; omega⟩ ⟨1, by dsimp only; omega⟩).mpr rfl
  exact this

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  have := Fintype.ofFinite (ComponentFiber edge.{u} comp)
  let σ : Fin (Nat.card (ComponentFiber edge.{u} comp)) ≃ ComponentFiber edge.{u} comp :=
    (Finite.equivFin _).symm
  let τ := σ.trans (Equiv.swap v0.{u} v1.{u})
  refine ⟨⟨_, edge, comp⟩, σ, τ, ?_⟩
  intro h
  have h01 := congrFun (congrFun h (σ.symm v0)) (σ.symm v1)
  simp only [actual, realize, τ, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_right] at h01
  have : edge.{u} v0.1 v1.1 := ⟨rfl, rfl⟩
  have h10 := h01.mp this
  simp [edge, v0, v1] at h10

def family : Registration arena.{u} (type_of% @component_path_order.{u}) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp @component_path_order.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

end

end Reg.D5.S3.Combinatorics.Graph.LinearForests.DirectedForestPathOrder
