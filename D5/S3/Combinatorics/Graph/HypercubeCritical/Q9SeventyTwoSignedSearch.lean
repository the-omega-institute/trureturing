import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoEmbeddingSearch
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixSignedModelProbe
import Batteries.Tactic.OpenPrivate

/-! The actual normalized embedding carries integer switching values. Their
restriction to the chosen half determines all values across the cut. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoSignedSearch

open scoped BigOperators
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeLowerBound (coordinateSlice)
open Q9EightCubicGraphCertificate (modelAdj)
open private cube_action_regular_balanced from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixNormalizeProbe
open private cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum

attribute [local instance] Classical.propDecidable
local notation "flip" => BalancedCriticalSpectrum.flip

/-- Undirected model edges, represented by their increasing endpoint pair. -/
def modelEdges (wagner : Bool) : Finset (Fin 8 × Fin 8) :=
  Finset.univ.filter fun e => e.1 < e.2 ∧ modelAdj wagner e.1 e.2 = true

private theorem constant_on_model (wagner : Bool) (c : Fin 8 → Bool)
    (h : ∀ i j, modelAdj wagner i j = true → c i = c j) : ∀ i, c i = c 0 := by
  have paths : ∀ (w : Bool) (i : Fin 8),
      i = 0 ∨ modelAdj w i 0 = true ∨
      (∃ j, modelAdj w i j = true ∧ modelAdj w j 0 = true) ∨
      ∃ j k, modelAdj w i j = true ∧ modelAdj w j k = true ∧ modelAdj w k 0 = true := by
    decide +kernel
  intro i
  rcases paths wagner i with rfl | h0 | ⟨j, hij, hj0⟩ | ⟨j, k, hij, hjk, hk0⟩
  · rfl
  · exact h _ _ h0
  · exact (h _ _ hij).trans (h _ _ hj0)
  · exact (h _ _ hij).trans ((h _ _ hjk).trans (h _ _ hk0))

/-- The eight embedded vertices and their twelve realized edge middles
exhaust the actual twenty-point half. -/
theorem slice_eq_highs_union_middles (S : Finset (Q 9)) (hS : S.card = 20)
    (wagner : Bool) (p : Fin 8 ↪ Q 9) (hp : ∀ k, p k ∈ S)
    (hm : ∀ i j, modelAdj wagner i j = true → ∃ m ∈ S,
      ∀ k, (hypercube 9).Adj m (p k) ↔ k = i ∨ k = j) :
    ∃ (m : (modelEdges wagner : Set (Fin 8 × Fin 8)) ↪ Q 9),
      S = Finset.univ.map p ∪ Finset.univ.map m ∧
      ∀ e k, (hypercube 9).Adj (m e) (p k) ↔ k = e.val.1 ∨ k = e.val.2 := by
  classical
  have edges (e : (modelEdges wagner : Set (Fin 8 × Fin 8))) :
      e.val.1 < e.val.2 ∧ modelAdj wagner e.val.1 e.val.2 = true :=
    (Finset.mem_filter.mp e.property).2
  choose mid hmS hmAdj using fun e : (modelEdges wagner : Set (Fin 8 × Fin 8)) =>
    hm e.val.1 e.val.2 (edges e).2
  have hpar : ∀ i, cubeParity (p i) = cubeParity (p 0) := by
    apply constant_on_model
    intro i j hij
    obtain ⟨m, _, hadj⟩ := hm i j hij
    have hbool : ∀ a b c : Bool, a ≠ b → a ≠ c → b = c := by decide
    exact hbool _ _ _
      (cubeParity_ne_of_adj ((hadj i).mpr (Or.inl rfl)))
      (cubeParity_ne_of_adj ((hadj j).mpr (Or.inr rfl)))
  have hinj : Function.Injective mid := by
    intro e f hef
    have hpair (k : Fin 8) : (k = e.val.1 ∨ k = e.val.2) ↔
        (k = f.val.1 ∨ k = f.val.2) := by
      rw [← hmAdj e k, ← hmAdj f k, hef]
    have he1 := (hpair e.val.1).mp (Or.inl rfl)
    have he2 := (hpair e.val.2).mp (Or.inr rfl)
    have hlt := (edges e).1
    have hlt' := (edges f).1
    apply Subtype.ext
    rcases he1 with h1 | h1 <;> rcases he2 with h2 | h2
    · exact (by omega : False).elim
    · exact Prod.ext h1 h2
    · exact (by omega : False).elim
    · exact (by omega : False).elim
  let m : (modelEdges wagner : Set (Fin 8 × Fin 8)) ↪ Q 9 := ⟨mid, hinj⟩
  have hsub : Finset.univ.map p ∪ Finset.univ.map m ⊆ S := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hv
      exact hp k
    · obtain ⟨e, _, rfl⟩ := Finset.mem_map.mp hv
      exact hmS e
  have hdis : Disjoint (Finset.univ.map p) (Finset.univ.map m) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨e, _, he⟩ := Finset.mem_map.mp hw
    have hn := cubeParity_ne_of_adj ((hmAdj e e.val.1).mpr (Or.inl rfl))
    apply hn
    change mid e = p k at he
    rw [he, hpar k, hpar e.val.1]
  have hedges : (modelEdges wagner).card = 12 := by
    cases wagner <;> decide +kernel
  have hcard : (Finset.univ.map p ∪ Finset.univ.map m).card = 20 := by
    rw [Finset.card_union_of_disjoint hdis, Finset.card_map, Finset.card_map,
      Finset.card_univ, Finset.card_univ, Fintype.card_fin]
    change 8 + Fintype.card ↥(modelEdges wagner) = 20
    rw [Fintype.card_coe, hedges]
  exact ⟨m, (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hS])).symm, hmAdj⟩

/-- A geometric candidate obtained from an actual support admits signed
integer values for its highs and selected middles, together with all of
the ambient row constraints. -/
theorem exists_signed_candidate {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 20) :
    ∃ (g : Q 9 ≃ Q 9) (σ : Fin 9 ≃ Fin 9) (wagner : Bool) (pattern : Fin 5)
      (p : Fin 8 ↪ Q 9) (m : (modelEdges wagner : Set (Fin 8 × Fin 8)) ↪ Q 9)
      (z : Q 9 → ℤ),
      (∀ x i, g (flip x i) = flip (g x) (σ i)) ∧
      (∀ x, g x 0 = false ↔ x 0 = b) ∧
      (fun i => (cubeBitVec 9).symm (p i)) ∈ Q9SeventyTwoEmbeddingSearch.candidates wagner pattern ∧
      (coordinateSlice C b).image g = Finset.univ.map p ∪ Finset.univ.map m ∧
      (∀ e k, (hypercube 9).Adj (m e) (p k) ↔ k = e.val.1 ∨ k = e.val.2) ∧
      (∀ x ∈ C.image g, z x = 1 ∨ z x = -1) ∧ (∀ x ∉ C.image g, z x = 0) ∧
      (∀ x ∈ C.image g, ∀ i : Fin 9, flip x i ∈ C.image g →
        truePrefixSign x i = z x * z (flip x i)) ∧
      ∀ y, z (flip y 0) =
        3 * z y - ∑ i ∈ Finset.univ.erase (0 : Fin 9), truePrefixSign y i * z (flip y i) := by
  obtain ⟨g, σ, wagner, pattern, p, hg, hcut, hhigh, hmem, hmid⟩ :=
    Q9SeventyTwoEmbeddingSearch.exists_member hC hr hb b hs
  have hcard : ((coordinateSlice C b).image g).card = 20 := by
    rw [Finset.card_image_of_injective _ g.injective, hs]
  obtain ⟨m, hslice, hAdj⟩ := slice_eq_highs_union_middles _ hcard wagner p hhigh
    (by
      intro i j hij
      obtain ⟨v, hv, _, hvAdj⟩ := hmid i j hij
      exact ⟨v, hv, hvAdj⟩)
  obtain ⟨hrg, hbg⟩ := cube_action_regular_balanced g σ hg hr hb
  obtain ⟨z, hunit, hzero, hsign, hrow⟩ := q9_integral_true_prefix_switching hrg hbg
  refine ⟨g, σ, wagner, pattern, p, m, z, hg, hcut, hmem, hslice, hAdj, hunit, hzero, hsign, ?_⟩
  intro y
  have h := hrow y
  have hz : truePrefixSign y (0 : Fin 9) = 1 := by
    simp [truePrefixSign]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin 9)), hz, one_mul] at h
  rw [← h, add_sub_cancel_left]

#print axioms exists_signed_candidate

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoSignedSearch
