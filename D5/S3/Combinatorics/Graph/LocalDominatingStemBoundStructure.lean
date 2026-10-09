/- GID: D5/S3/Combinatorics/Graph/LocalDominatingStemBoundStructure
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LocalDominatingStemBoundStructure
   mirror-E: none(waiver:finite-combinatorial-identities)
   anchors: []
   utility: none
   digest: Removing a stem and its leaves preserves absence of isolated vertices. -/

import D5.S3.Combinatorics.Graph.DominatingSetAverage

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.LocalDominatingStemBoundStructure

open Finset DominatingSetAverage

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Vertices remaining after removal of a vertex and all its leaf neighbours. -/
noncomputable def remaining (G : SimpleGraph V) (v : V) : Finset V :=
  univ \ insert v (leafNeighbors G v)

@[simp] theorem mem_remaining {G : SimpleGraph V} {v x : V} :
    x ∈ remaining G v ↔ x ≠ v ∧ ¬ (G.Adj v x ∧ Leaf G x) := by
  classical
  simp [remaining, not_or]

theorem remaining_neighbor {G : SimpleGraph V} {v x : V}
    [DecidableRel G.Adj] (hpos : ∀ y, 0 < G.degree y)
    (hx : x ∈ remaining G v) :
    ∃ y ∈ remaining G v, G.Adj x y := by
  classical
  obtain ⟨hxv, hxl⟩ := mem_remaining.mp hx
  have hex : ∃ y, G.Adj x y ∧ y ≠ v := by
    by_contra hn
    have hall : ∀ y, G.Adj x y → y = v := by
      intro y hy
      by_contra hyv
      exact hn ⟨y, hy, hyv⟩
    obtain ⟨y, hy⟩ := (G.degree_pos_iff_exists_adj x).mp (hpos x)
    have hxv' : G.Adj x v := hall y hy ▸ hy
    have hdegree : G.degree x = 1 :=
      SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr ⟨v, hxv', hall⟩
    have hleaf : Leaf G x := by
      unfold Leaf
      rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card]
      rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card] at hdegree
      exact hdegree
    exact hxl ⟨hxv'.symm, hleaf⟩
  obtain ⟨y, hxy, hyv⟩ := hex
  refine ⟨y, mem_remaining.mpr ⟨hyv, ?_⟩, hxy⟩
  rintro ⟨hvy, hly⟩
  exact hxv (leaf_adj_unique hly hvy.symm hxy.symm)

/-- The induced graph on the remaining vertices. -/
noncomputable def residualGraph (G : SimpleGraph V) (v : V) :
    SimpleGraph {x // x ∈ remaining G v} := G.induce (remaining G v : Set V)

theorem residualGraph_no_isolates {G : SimpleGraph V} (v : V)
    [DecidableRel G.Adj] (hpos : ∀ y, 0 < G.degree y) :
    ∀ x, ∃ y, (residualGraph G v).Adj x y := by
  intro x
  obtain ⟨y, hy, hxy⟩ := remaining_neighbor hpos x.property
  exact ⟨⟨y, hy⟩, hxy⟩

theorem remaining_card {G : SimpleGraph V} (v : V) :
    (remaining G v).card + leafCount G v + 1 = Fintype.card V := by
  classical
  have hvl : v ∉ leafNeighbors G v := by simp
  have hsub : insert v (leafNeighbors G v) ⊆ (univ : Finset V) := subset_univ _
  rw [remaining, card_sdiff_of_subset hsub, card_insert_of_notMem hvl]
  unfold leafCount
  have hle := card_le_card hsub
  rw [card_insert_of_notMem hvl, card_univ] at hle
  simp only [card_univ]
  omega

/-- Subsets of the residual vertices dominating every vertex not adjacent to the removed stem. -/
noncomputable def partialDomSets (G : SimpleGraph V) (v : V) : Finset (Finset V) := by
  classical
  exact (remaining G v).powerset.filter
    (fun T => ∀ x ∈ remaining G v, ¬ G.Adj v x →
      x ∈ T ∨ ∃ y ∈ T, G.Adj x y)

@[simp] theorem mem_partialDomSets {G : SimpleGraph V} {v : V} {T : Finset V} :
    T ∈ partialDomSets G v ↔ T ⊆ remaining G v ∧
      ∀ x ∈ remaining G v, ¬ G.Adj v x → x ∈ T ∨ ∃ y ∈ T, G.Adj x y := by
  classical
  simp [partialDomSets]

theorem partialDomSets_nonempty (G : SimpleGraph V) (v : V) :
    (partialDomSets G v).Nonempty := by
  refine ⟨remaining G v, mem_partialDomSets.mpr ⟨Subset.refl _, ?_⟩⟩
  intro x hx _
  exact Or.inl hx

/-- Adjoining the stem and any selection of its leaves to an admissible residual set dominates G. -/
theorem dominating_stem_union {G : SimpleGraph V} {v : V} {T K : Finset V}
    (hT : T ∈ partialDomSets G v) (hK : K ⊆ leafNeighbors G v) :
    G.IsDominating ((insert v (K ∪ T) : Finset V) : Set V) := by
  classical
  obtain ⟨_, hT⟩ := mem_partialDomSets.mp hT
  intro x
  by_cases hxv : x = v
  · subst x
    exact Or.inl (mem_insert_self _ _)
  by_cases hvx : G.Adj v x
  · exact Or.inr ⟨v, mem_insert_self _ _, hvx.symm⟩
  have hxr : x ∈ remaining G v := mem_remaining.mpr ⟨hxv, by simp [hvx]⟩
  rcases hT x hxr hvx with hx | ⟨y, hy, hxy⟩
  · exact Or.inl (mem_insert_of_mem (mem_union_right _ hx))
  · exact Or.inr ⟨y, mem_insert_of_mem (mem_union_right _ hy), hxy⟩

/-- A dominating set containing the stem leaves an admissible set on the residual vertices. -/
theorem dominating_residual_partial {G : SimpleGraph V} {v : V} {S : Finset V}
    (hS : G.IsDominating (S : Set V)) (hv : v ∈ S) :
    S ∩ remaining G v ∈ partialDomSets G v := by
  classical
  refine mem_partialDomSets.mpr ⟨inter_subset_right, ?_⟩
  intro x hx hvx
  rcases hS x with hxs | ⟨y, hy, hxy⟩
  · exact Or.inl (mem_inter.mpr ⟨hxs, hx⟩)
  · refine Or.inr ⟨y, mem_inter.mpr ⟨hy, ?_⟩, hxy⟩
    refine mem_remaining.mpr ⟨?_, ?_⟩
    · rintro rfl
      exact hvx hxy.symm
    · rintro ⟨hvy, hly⟩
      exact (mem_remaining.mp hx).1 (leaf_adj_unique hly hvy.symm hxy.symm)

end D5.S3.Combinatorics.Graph.LocalDominatingStemBoundStructure
