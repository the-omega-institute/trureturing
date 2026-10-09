/- GID: D5/S3/Combinatorics/Graph/DominatingSetAverage
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DominatingSetAverage
   mirror-E: none(waiver:finite-combinatorial-identities)
   anchors: []
   utility: none
   digest: Finite dominating-set families, rational averages, and leaf-stem structure. -/

import D5.S3.ConceptDynamics.GraphColoring.GraphCoverDomination
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.DominatingSetAverage

open Finset

variable {V W : Type*} [Fintype V] [DecidableEq V]

/-- All dominating sets of a finite graph. -/
noncomputable def domSets (G : SimpleGraph V) : Finset (Finset V) := by
  classical
  exact univ.powerset.filter (fun S => G.IsDominating (S : Set V))

/-- Dominating sets containing the specified vertex. -/
noncomputable def domSetsAt (G : SimpleGraph V) (v : V) : Finset (Finset V) := by
  classical
  exact (domSets G).filter (fun S => v ∈ S)

/-- The average cardinality of a nonempty finite family of finite sets. -/
noncomputable def familyAverage (F : Finset (Finset V)) : ℚ :=
  (∑ S ∈ F, (S.card : ℚ)) / F.card

/-- The global average order of dominating sets. -/
noncomputable def avd (G : SimpleGraph V) : ℚ := familyAverage (domSets G)

/-- The local average order, conditioned on containing a given vertex. -/
noncomputable def avdAt (G : SimpleGraph V) (v : V) : ℚ :=
  familyAverage (domSetsAt G v)

/-- A leaf has degree exactly one. -/
noncomputable def Leaf (G : SimpleGraph V) (v : V) : Prop := by
  classical
  exact G.degree v = 1

/-- The leaf neighbours of a vertex. -/
noncomputable def leafNeighbors (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact univ.filter (fun x => G.Adj v x ∧ Leaf G x)

/-- The number of leaf neighbours. -/
noncomputable def leafCount (G : SimpleGraph V) (v : V) : ℕ :=
  (leafNeighbors G v).card

/-- Every vertex is a leaf or a stem with one or two leaf neighbours. -/
def StarLike (G : SimpleGraph V) : Prop :=
  ∀ x, Leaf G x ∨ leafCount G x = 1 ∨ leafCount G x = 2

@[simp] theorem mem_domSets {G : SimpleGraph V} {S : Finset V} :
    S ∈ domSets G ↔ G.IsDominating (S : Set V) := by
  classical
  simp [domSets]

@[simp] theorem mem_domSetsAt {G : SimpleGraph V} {S : Finset V} {v : V} :
    S ∈ domSetsAt G v ↔ G.IsDominating (S : Set V) ∧ v ∈ S := by
  classical
  simp [domSetsAt]

theorem dominating_mono {G : SimpleGraph V} {S T : Finset V}
    (hS : G.IsDominating (S : Set V)) (hST : S ⊆ T) :
    G.IsDominating (T : Set V) := by
  intro x
  rcases hS x with hx | ⟨y, hy, hxy⟩
  · exact Or.inl (hST hx)
  · exact Or.inr ⟨y, hST hy, hxy⟩

theorem univ_dominating (G : SimpleGraph V) : G.IsDominating ((univ : Finset V) : Set V) :=
  fun x => Or.inl (mem_univ x)

theorem domSets_nonempty (G : SimpleGraph V) : (domSets G).Nonempty :=
  ⟨univ, mem_domSets.mpr (univ_dominating G)⟩

theorem domSets_card_pos (G : SimpleGraph V) : 0 < (domSets G).card :=
  card_pos.mpr (domSets_nonempty G)

@[simp] theorem mem_leafNeighbors {G : SimpleGraph V} {v x : V} :
    x ∈ leafNeighbors G v ↔ G.Adj v x ∧ Leaf G x := by
  classical
  simp [leafNeighbors]

theorem leaf_adj_unique {G : SimpleGraph V} {x v y : V}
    (hx : Leaf G x) (hv : G.Adj x v) (hy : G.Adj x y) : y = v := by
  classical
  obtain ⟨z, hz, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hx
  exact (huniq y hy).trans (huniq v hv).symm

theorem leaf_dominated_iff {G : SimpleGraph V} {x v : V}
    (hx : Leaf G x) (hv : G.Adj x v) (S : Finset V) :
    (x ∈ S ∨ ∃ y ∈ S, G.Adj x y) ↔ x ∈ S ∨ v ∈ S := by
  constructor
  · rintro (h | ⟨y, hy, hxy⟩)
    · exact Or.inl h
    · exact Or.inr (leaf_adj_unique hx hv hxy ▸ hy)
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨v, h, hv⟩

theorem familyAverage_nonneg (F : Finset (Finset V)) : 0 ≤ familyAverage F := by
  apply div_nonneg
  · exact sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  · exact Nat.cast_nonneg _

theorem avd_nonneg (G : SimpleGraph V) : 0 ≤ avd G :=
  familyAverage_nonneg _

section Isomorphism

variable [Fintype W] [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W}

theorem dominating_map_iff (e : G ≃g H) (S : Finset V) :
    H.IsDominating (S.map e.toEquiv.toEmbedding : Set W) ↔
      G.IsDominating (S : Set V) := by
  constructor
  · intro h x
    rcases h (e x) with hx | ⟨y, hy, hxy⟩
    · exact Or.inl (by simpa using hx)
    · obtain ⟨z, hz, rfl⟩ := mem_map.mp hy
      exact Or.inr ⟨z, hz, e.map_adj_iff.mp hxy⟩
  · intro h y
    obtain ⟨x, rfl⟩ := e.surjective y
    rcases h x with hx | ⟨z, hz, hxz⟩
    · exact Or.inl (mem_map.mpr ⟨x, hx, rfl⟩)
    · exact Or.inr ⟨e z, mem_map.mpr ⟨z, hz, rfl⟩, e.map_adj_iff.mpr hxz⟩

/-- The finite-set map associated to a graph isomorphism. -/
def setEmbedding (e : G ≃g H) : Finset V ↪ Finset W :=
  ⟨fun S => S.map e.toEquiv.toEmbedding, fun _ _ h => Finset.map_injective _ h⟩

theorem domSets_map (e : G ≃g H) :
    (domSets G).map (setEmbedding e) = domSets H := by
  classical
  ext S
  simp only [mem_map, mem_domSets]
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact (dominating_map_iff e T).mpr hT
  · intro hS
    refine ⟨S.map e.symm.toEquiv.toEmbedding,
      (dominating_map_iff e.symm S).mpr hS, ?_⟩
    change (S.map e.symm.toEquiv.toEmbedding).map e.toEquiv.toEmbedding = S
    ext x
    simp
    change e (e.symm x) ∈ S ↔ x ∈ S
    rw [e.apply_symm_apply]

/-- Graph isomorphisms preserve the global average. -/
theorem avd_iso (e : G ≃g H) : avd G = avd H := by
  classical
  unfold avd familyAverage
  rw [← domSets_map e, card_map, sum_map]
  congr 1
  apply sum_congr rfl
  intro S _
  change (S.card : ℚ) = ((S.map e.toEquiv.toEmbedding).card : ℚ)
  simp

end Isomorphism

end D5.S3.Combinatorics.Graph.DominatingSetAverage
