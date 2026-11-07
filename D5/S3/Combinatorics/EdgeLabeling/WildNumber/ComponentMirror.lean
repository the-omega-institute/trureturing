/- GID: D5/S3/Combinatorics/EdgeLabeling/WildNumber/ComponentMirror
   generality: G
   mirror-B: D5/B/S3/Combinatorics/EdgeLabeling/WildNumber/ComponentMirror
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Component counting by recursively merging vertex labels. -/

/-
admission_basis: escape-witness (labels_valid)
escape_witness: labels_valid
Direct frozen dependencies: none.
HasReps.eq_of_reachable: proof_shape: bind-only; escape_witness: none; consumer: kappa_eq_image_card.
componentCount_eq_kappa: proof_shape: content; escape_witness: none; Direct frozen dependencies: none.
labels_valid: proof_shape: content; escape_witness: labels_valid; Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21209
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

namespace D5.S3.Combinatorics.EdgeLabeling.WildNumber.ComponentMirror
open SimpleGraph
variable {V : Type*}
private structure HasReps (G : SimpleGraph V) (ρ : V → V) : Prop where
  invariant : ∀ {u v}, G.Adj u v → ρ u = ρ v
  reachable : ∀ u, G.Reachable u (ρ u)
private theorem HasReps.eq_of_reachable {G : SimpleGraph V} {ρ : V → V} (h : HasReps G ρ)
    {u v} (huv : G.Reachable u v) : ρ u = ρ v := by
  have hh : Relation.ReflTransGen Eq (ρ u) (ρ v) :=
    Relation.ReflTransGen.lift ρ (fun _ _ ha => h.invariant ha) _ _
      ((G.reachable_iff_reflTransGen _ _).mp huv)
  simpa only [Relation.reflTransGen_eq_self] using hh
private theorem kappa_eq_image_card [Fintype V] [DecidableEq V] {G : SimpleGraph V} {ρ : V → V}
    (h : HasReps G ρ) : Nat.card G.ConnectedComponent = (Finset.univ.image ρ).card := by
  classical
  have hrel : ∀ u v, G.Reachable u v ↔ ρ u = ρ v := fun u v =>
    ⟨fun hr => h.eq_of_reachable hr,
      fun he => (h.reachable u).trans (by rw [he]; exact (h.reachable v).symm)⟩
  have hs : Set.range ρ = (Finset.univ.image ρ : Set V) := Fintype.coe_image_univ.symm
  have hcard : Nat.card G.ConnectedComponent = Nat.card (Set.range ρ) :=
    Nat.card_congr ((Quot.congrRight hrel).trans (Setoid.quotientKerEquivRange ρ))
  rw [hcard,hs]
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_of_subtype _ (fun _ => Iff.rfl)
private theorem le_addEdge (G : SimpleGraph V) (u v : V) : G ≤ (G ⊔ SimpleGraph.edge u v) := le_sup_left
private theorem addEdge_reachable (G : SimpleGraph V) (u v : V) :
    (G ⊔ SimpleGraph.edge u v).Reachable u v := by
  by_cases h : u = v
  · subst v; exact .rfl
  · exact (show (G ⊔ SimpleGraph.edge u v).Adj u v from Or.inr (by simp [SimpleGraph.edge, h])).reachable
def renameLabels [DecidableEq V] (ρ : V → V) (u v : V) (x : V) : V :=
  ({ρ u} : Finset V).piecewise (Function.const V (ρ v)) id (ρ x)
private theorem rename_endpoints [DecidableEq V] (ρ : V → V) (u v : V) :
    renameLabels ρ u v u = renameLabels ρ u v v := by
  by_cases h : ρ v = ρ u <;> simp [renameLabels,Finset.piecewise,h]
private theorem HasReps.rename [DecidableEq V] {G : SimpleGraph V} {ρ : V → V}
    (h : HasReps G ρ) (u v : V) : HasReps ((G ⊔ SimpleGraph.edge u v)) (renameLabels ρ u v) := by
  constructor
  · intro x y hxy
    change G.Adj x y ∨ (SimpleGraph.edge u v).Adj x y at hxy
    simp only [SimpleGraph.edge, SimpleGraph.fromEdgeSet_adj, Set.mem_singleton_iff] at hxy
    rcases hxy with hxy | ⟨hxy, _⟩
    · have heq := h.invariant hxy
      unfold renameLabels
      rw [heq]
    · rcases Sym2.eq_iff.mp hxy with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact rename_endpoints ρ _ _
      · exact (rename_endpoints ρ _ _).symm
  · intro x
    unfold renameLabels
    simp only [Finset.piecewise,Finset.mem_singleton,Function.const,id_eq]
    split_ifs with hx
    · have hxu : G.Reachable x u := (h.reachable x).trans (by rw [hx]; exact (h.reachable u).symm)
      exact (hxu.mono (le_addEdge G u v)).trans
        ((addEdge_reachable G u v).trans ((h.reachable v).mono (le_addEdge G u v)))
    · exact (h.reachable x).mono (le_addEdge G u v)
def labels [DecidableEq V] : List (V × V) → V → V
  | [] => id
  | (u,v)::L => renameLabels (labels L) u v
private theorem labels_valid [DecidableEq V] (L : List (V × V)) :
    HasReps (SimpleGraph.fromRel (fun u v => (u,v) ∈ L)) (labels L) := by
  induction L with
  | nil =>
    refine ⟨?_,fun _ => .rfl⟩
    intro u v h
    simpa [SimpleGraph.fromRel_adj] using h
  | cons e L ih =>
    have heq : SimpleGraph.fromRel (fun u v => (u,v) ∈ e :: L) =
        SimpleGraph.fromRel (fun u v => (u,v) ∈ L) ⊔ SimpleGraph.edge e.1 e.2 := by
      rcases e with ⟨a,b⟩
      ext u v
      simp only [SimpleGraph.sup_adj,SimpleGraph.edge,SimpleGraph.fromEdgeSet_adj,
        Set.mem_singleton_iff,SimpleGraph.fromRel_adj,List.mem_cons,Prod.mk.injEq,Sym2.eq_iff]
      tauto
    rw [heq]
    exact ih.rename e.1 e.2
def componentCount [Fintype V] [DecidableEq V] (L : List (V × V)) : ℕ :=
  (Finset.univ.image (labels L)).card
theorem componentCount_eq_kappa [Fintype V] [DecidableEq V] (L : List (V × V)) :
    componentCount L = Nat.card (SimpleGraph.fromRel (fun u v => (u,v) ∈ L)).ConnectedComponent := (kappa_eq_image_card (labels_valid L)).symm
end D5.S3.Combinatorics.EdgeLabeling.WildNumber.ComponentMirror
