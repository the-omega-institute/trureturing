/- GID: D5/S3/Combinatorics/SpectralGraph/NormalizedCographCotree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/NormalizedCographCotree
   mirror-E: none
   anchors: []
   digest: Native component cotrees and their vicinal width recurrence. -/

import D5.S3.Combinatorics.Graph.CographSeinsche
import D5.S3.Combinatorics.SpectralGraph.CographVicinalWidth

/-! # Normalized cotrees on native graph vertices -/

namespace D5.S3.Combinatorics.SpectralGraph.NormalizedCographCotree

open SimpleGraph
open CographVicinalWidth (width width_components width_compl width_singleton NontrivialComponent)

/-- A union cuts by components of the graph, and a join cuts by components of its complement. -/
def cutGraph {V : Type} (G : SimpleGraph V) (join : Bool) : SimpleGraph V :=
  if join then Gᶜ else G

/-- The component cut is labeled false for union and true for join.
The graph at each child is the ambient graph induced on its component support. -/
inductive Cotree : {V : Type} → SimpleGraph V → Option Bool → Type 1
  | leaf {V : Type} {G : SimpleGraph V} (v : V) (unique : ∀ w, w = v) : Cotree G none
  | node {V : Type} {G : SimpleGraph V} (join : Bool)
      (arity : Nontrivial (cutGraph G join).ConnectedComponent)
      (kind : (cutGraph G join).ConnectedComponent → Option Bool)
      (alternates : ∀ C, kind C ≠ some join)
      (child : ∀ C, Cotree (G.induce C.supp) (kind C)) : Cotree G (some join)

/-- The root is a leaf exactly on a singleton. Nontrivial roots have the connectivity label. -/
noncomputable def rootKind {V : Type} (G : SimpleGraph V) : Option Bool := by
  classical
  exact if Subsingleton V then none else if G.Connected then some true else some false

/-- The exact induced P₄ exclusion on a finite nontrivial connected graph forces
its complement to be disconnected. -/
theorem not_connected_compl_of_not_induced_pathFour {V : Type} [Finite V] [Nontrivial V]
    {G : SimpleGraph V} (hG : G.Connected) (hP : ¬(pathGraph 4).IsIndContained G) :
    ¬Gᶜ.Connected := by
  intro hc
  exact ((isP4Free_iff_not_pathGraph_four_isIndContained.mpr hP).not_preconnected_or_compl.resolve_left
    (not_not_intro hG.preconnected)) hc.preconnected

private theorem components_nontrivial {V : Type} {H : SimpleGraph V}
    (h : ¬H.Preconnected) : Nontrivial H.ConnectedComponent := by
  classical
  obtain ⟨u, v, huv⟩ : ∃ u v, ¬H.Reachable u v := by
    simpa only [Preconnected, not_forall] using h
  exact ⟨⟨H.connectedComponentMk u, H.connectedComponentMk v,
    fun he => huv (ConnectedComponent.exact he)⟩⟩

private theorem card_component_lt {V : Type} [Finite V] {H : SimpleGraph V}
    [Nontrivial H.ConnectedComponent] (C : H.ConnectedComponent) : Nat.card C.supp < Nat.card V := by
  classical
  let := Fintype.ofFinite V
  let := Fintype.ofFinite C.supp
  obtain ⟨D, hD⟩ := exists_ne C
  obtain ⟨v, hv⟩ := D.nonempty_supp
  simpa only [Nat.card_eq_fintype_card] using
    (Fintype.card_lt_of_injective_of_notMem (f := fun x : C.supp => x.val) (b := v)
      Subtype.val_injective (by
        rintro ⟨x, rfl⟩
        exact hD (D.eq_of_common_vertex hv x.property)))

private theorem not_subsingleton_of_components_nontrivial {V : Type} {H : SimpleGraph V}
    (h : Nontrivial H.ConnectedComponent) : ¬Subsingleton V := by
  intro hV
  obtain ⟨C, D, hCD⟩ := h.exists_pair_ne
  obtain ⟨u, hu⟩ := C.nonempty_supp
  obtain ⟨v, hv⟩ := D.nonempty_supp
  exact hCD (C.eq_of_common_vertex hu ((hV.elim u v).symm ▸ hv))

private theorem exists_cotree_of_card_le (n : ℕ) :
    ∀ (V : Type) [Finite V] [Nonempty V] (G : SimpleGraph V),
      Nat.card V ≤ n → G.IsP4Free → Nonempty (Cotree G (rootKind G)) := by
  classical
  induction n with
  | zero =>
    intro V _ _ G h _
    exact (Nat.not_lt_zero _ ((Nat.card_pos (α := V)).trans_le h)).elim
  | succ n ih =>
    intro V _ _ G hcard hp
    by_cases hs : Subsingleton V
    · obtain ⟨v⟩ := ‹Nonempty V›
      simpa only [rootKind, if_pos hs] using
        (show Nonempty (Cotree G none) from ⟨.leaf v (fun u => hs.elim u v)⟩)
    · let : Nontrivial V := not_subsingleton_iff_nontrivial.mp hs
      have build (join : Bool) (hd : ¬(cutGraph G join).Preconnected)
          (ha : ∀ C : (cutGraph G join).ConnectedComponent, rootKind (G.induce C.supp) ≠ some join) :
          Nonempty (Cotree G (some join)) := by
        let hcomponents := components_nontrivial hd
        let child (C : (cutGraph G join).ConnectedComponent) :
            Cotree (G.induce C.supp) (rootKind (G.induce C.supp)) := by
          let := C.connected_toSimpleGraph.nonempty
          have hlt := card_component_lt C
          exact Classical.choice (ih C.supp (G.induce C.supp) (by omega) (hp.induce C.supp))
        exact ⟨.node join hcomponents _ ha child⟩
      by_cases hc : G.Connected
      · rw [rootKind, if_neg hs, if_pos hc]
        refine build true (hp.not_preconnected_or_compl.resolve_left (not_not_intro hc.preconnected)) ?_
        intro C
        by_cases hC : Subsingleton C.supp
        · simp [rootKind, hC]
        · let : Nontrivial C.supp := not_subsingleton_iff_nontrivial.mp hC
          have hnot : ¬(G.induce C.supp).Connected := by
            intro h
            have hcompl : (G.induce C.supp)ᶜ.Connected := by
              rw [compl_induce_eq_induce_compl]
              exact C.connected_toSimpleGraph
            exact ((hp.induce C.supp).not_preconnected_or_compl.resolve_left
              (not_not_intro h.preconnected)) hcompl.preconnected
          simp [rootKind, hC, hnot]
      · rw [rootKind, if_neg hs, if_neg hc]
        refine build false (fun h => hc ⟨h, ‹Nonempty V›⟩) ?_
        intro C
        by_cases hC : Subsingleton C.supp
        · simp [rootKind, hC]
        · simp [rootKind, hC, show (G.induce C.supp).Connected from C.connected_toSimpleGraph]

/-- Every finite nonempty native P₄-free graph has a normalized component cotree. -/
theorem exists_cotree {V : Type} [Finite V] [Nonempty V] {G : SimpleGraph V}
    (hP : ¬(pathGraph 4).IsIndContained G) : Nonempty (Cotree G (rootKind G)) :=
  exists_cotree_of_card_le (Nat.card V) V G le_rfl
    (isP4Free_iff_not_pathGraph_four_isIndContained.mpr hP)

namespace Cotree

/-- Leaf addresses form a singleton at a leaf and a dependent union of child addresses at a node. -/
def Leaves : {V : Type} → {G : SimpleGraph V} → {kind : Option Bool} → Cotree G kind → Type
  | _, _, _, .leaf _ _ => Unit
  | _, _, _, .node _ _ _ _ child => Σ C, Leaves (child C)

/-- The leaf addresses enumerate the actual vertices, each exactly once. -/
noncomputable def leavesEquiv : {V : Type} → {G : SimpleGraph V} → {kind : Option Bool} →
    (t : Cotree G kind) → t.Leaves ≃ V
  | _, _, _, .leaf v h =>
    { toFun := fun _ => v
      invFun := fun _ => ()
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun w => (h w).symm }
  | _, _, _, .node _ _ _ _ child =>
    (Equiv.sigmaCongrRight fun C => leavesEquiv (child C)).trans
      (Equiv.sigmaFiberEquiv _)

/-- Cross edges at an internal node are exactly the edges of a join. -/
theorem adj_iff_join_of_component_ne {V : Type} {G : SimpleGraph V} (join : Bool)
    {u v : V} (h : (cutGraph G join).connectedComponentMk u ≠
      (cutGraph G join).connectedComponentMk v) : G.Adj u v ↔ join = true := by
  cases join with
  | false =>
    simp only [Bool.false_eq_true, iff_false]
    exact fun e => h (ConnectedComponent.connectedComponentMk_eq_of_adj e)
  | true =>
    simp only [iff_true]
    by_contra hn
    have he : u ≠ v := fun e => h (congrArg (cutGraph G true).connectedComponentMk e)
    exact h (ConnectedComponent.connectedComponentMk_eq_of_adj
      (show (cutGraph G true).Adj u v from ⟨he, hn⟩))

/-- A child has a non-leaf root precisely when its support is nontrivial. -/
theorem nontrivial_iff {V : Type} {G : SimpleGraph V} {kind : Option Bool}
    (t : Cotree G kind) : Nontrivial V ↔ kind ≠ none := by
  cases t with
  | leaf v h =>
    simp only [ne_eq, not_true_eq_false, iff_false]
    rintro ⟨a, b, hab⟩
    exact hab ((h a).trans (h b).symm)
  | node _ arity _ _ _ =>
    exact iff_of_true (not_subsingleton_iff_nontrivial.mp
      (not_subsingleton_of_components_nontrivial arity)) (by simp)

/-- A nontrivial connected native P₄-free graph has a normalized join root. -/
theorem exists_join_root {V : Type} [Finite V] [Nontrivial V] {G : SimpleGraph V}
    (hc : G.Connected) (hP : ¬(pathGraph 4).IsIndContained G) :
    Nonempty (Cotree G (some true)) := by
  classical
  let := hc.nonempty
  simpa only [rootKind, if_neg (not_subsingleton_iff_nontrivial.mpr ‹Nontrivial V›), if_pos hc]
    using exists_cotree hP

end Cotree

end D5.S3.Combinatorics.SpectralGraph.NormalizedCographCotree
