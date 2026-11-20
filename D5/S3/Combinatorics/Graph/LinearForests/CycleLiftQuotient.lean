/- GID: D5/S3/Combinatorics/Graph/LinearForests/CycleLiftQuotient
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LinearForests/CycleLiftQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reversal classes are actual completed graphs and additions preserve cycle lifts. -/

import D5.S3.Combinatorics.Graph.LinearForests.UndirectedCycleCompletionLaw
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Order.Setoid.Basic

/-! Restricting or extending prescribed edges keeps the successor permutation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.LinearForests.CycleLiftQuotient

open UndirectedCycleCompletionLaw

variable {V : Type*} [Fintype V]

/-- Equal shadows identify precisely the reversal classes of lifts. -/
abbrev reversalSetoid (hn : 3 ≤ Fintype.card V) (F : SimpleGraph V) : Setoid (Lift F) :=
  Setoid.ker (forget hn)

private def liftWithEdges (hn : 3 ≤ Fintype.card V) {F G : SimpleGraph V}
    (l : Lift F) (hG : G ≤ shadow l.σ) : Lift G :=
  canonicalLift hn G l.σ l.full fun x y h => (shadow_adj hn l.σ l.full x y).mp (hG h)

private def restrictLift (hn : 3 ≤ Fintype.card V) {F G : SimpleGraph V} (hFG : F ≤ G)
    (l : Lift G) : {a : Lift F // G ≤ shadow a.σ} :=
  ⟨liftWithEdges hn l (hFG.trans (forget hn l).property.2.2), (forget hn l).property.2.2⟩

private def prescribedEdgesEquiv (hn : 3 ≤ Fintype.card V) {F G : SimpleGraph V} (hFG : F ≤ G) :
    Lift G ≃ {a : Lift F // G ≤ shadow a.σ} where
  toFun := restrictLift hn hFG
  invFun a := liftWithEdges hn a.1 a.2
  left_inv _ := lift_ext hn rfl
  right_inv _ := Subtype.ext (lift_ext hn rfl)

private def singleEdgeEquiv (hn : 3 ≤ Fintype.card V) (F : SimpleGraph V)
    {u v : V} (hne : u ≠ v) :
    Lift (F ⊔ SimpleGraph.edge u v) ≃ {a : Lift F // (shadow a.σ).Adj u v} :=
  (prescribedEdgesEquiv hn (le_sup_left : F ≤ F ⊔ SimpleGraph.edge u v)).trans
    (Equiv.subtypeEquivRight fun a => by
      rw [sup_le_iff, SimpleGraph.edge_le_iff]
      exact ⟨fun h => h.2.resolve_left hne, fun h => ⟨(forget hn a).property.2.2, Or.inr h⟩⟩)

/-- The lift quotient keeps the actual completed graph, and adding prescribed
edges cuts out precisely the lifts whose same shadow contains them. -/
theorem reversal_quotient_and_added_edges (hn : 3 ≤ Fintype.card V) (F : SimpleGraph V) :
    (∀ (a : Lift F) x y, (forget hn a).1.Adj x y ↔ a.σ x = y ∨ a.σ y = x) ∧
    (∀ (a : Lift F) x y, a.E x y ↔ F.Adj x y ∧ a.σ x = y) ∧
    Function.Surjective (forget hn (F := F)) ∧
    (∀ a b : Lift F, forget hn b = forget hn a ↔ b = a ∨ b = reverseLift a) ∧
    Function.Involutive (reverseLift (F := F)) ∧
    (∀ a : Lift F, a ≠ reverseLift a) ∧
    (∃ e : Quotient (reversalSetoid hn F) ≃ CompletedGraph F,
      ∀ a : Lift F, e (Quotient.mk _ a) = forget hn a) ∧
    (∀ u v, u ≠ v →
      ∃ e : Lift (F ⊔ SimpleGraph.edge u v) ≃ {a : Lift F // (shadow a.σ).Adj u v},
        (∀ a, (e a).1.σ = a.σ ∧ (forget hn (e a).1).1 = (forget hn a).1) ∧
        (∀ a, (e (reverseLift a)).1 = reverseLift (e a).1)) := by
  refine ⟨fun a => shadow_adj hn a.σ a.full, ?_, forget_surjective hn F, forget_fiber hn,
    ?_, reverse_distinct hn, ?_, ?_⟩
  · intro a x y
    change a.E x y ↔ (liftWithEdges hn a (forget hn a).property.2.2).E x y
    rw [show liftWithEdges hn a (forget hn a).property.2.2 = a from lift_ext hn rfl]
  · intro a
    apply lift_ext hn
    change (a.σ⁻¹)⁻¹ = a.σ
    exact inv_inv a.σ
  · exact ⟨Setoid.quotientKerEquivOfSurjective (forget hn) (forget_surjective hn F),
      fun _ => rfl⟩
  · intro u v hne
    refine ⟨singleEdgeEquiv hn F hne, fun _ => ⟨rfl, rfl⟩, fun a => ?_⟩
    exact lift_ext hn rfl

end D5.S3.Combinatorics.Graph.LinearForests.CycleLiftQuotient
