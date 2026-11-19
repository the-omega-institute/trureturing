/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSaturatedCore
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SymmetricSaturatedCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: Use actual saturated neighbor-degree sums and side counts to extract the high centers, leaves and their exact neighbor sets in the B/B case. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

/-! Actual neighbor structure forced by the saturated high-graph inequalities.
No abstract skeleton or adjacency certificate is an input. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricSaturatedCore

open SimpleGraph
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V}

private theorem leaf_neighbor_degree_three
    (hsat : ∀ x, (∑ y ∈ H.neighborFinset x, H.degree y) = H.degree x + 2)
    {x y : V} (hx : H.degree x = 1) (hxy : H.Adj x y) :
    H.degree y = 3 := by
  have hc : (H.neighborFinset x).card = 1 := by
    simpa only [H.card_neighborFinset_eq_degree] using hx
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hc
  have hyz : y = z := by
    have hy : y ∈ H.neighborFinset x := (H.mem_neighborFinset _ _).mpr hxy
    simpa only [hz, Finset.mem_singleton] using hy
  subst y
  have hs := hsat x
  simpa only [hz, Finset.sum_singleton, hx] using hs

private theorem degree_two_neighbor_degree_two
    (hdeg : ∀ x, H.degree x = 1 ∨ H.degree x = 2 ∨ H.degree x = 3)
    (hsat : ∀ x, (∑ y ∈ H.neighborFinset x, H.degree y) = H.degree x + 2)
    {x y : V} (hx : H.degree x = 2) (hxy : H.Adj x y) :
    H.degree y = 2 := by
  have hc : (H.neighborFinset x).card = 2 := by
    simpa only [H.card_neighborFinset_eq_degree] using hx
  obtain ⟨a, b, hab, hN⟩ := Finset.card_eq_two.mp hc
  have ha : H.Adj x a := (H.mem_neighborFinset _ _).mp (by simp [hN])
  have hb : H.Adj x b := (H.mem_neighborFinset _ _).mp (by simp [hN])
  have hna : H.degree a ≠ 1 := by
    intro ha1
    have ht := leaf_neighbor_degree_three hsat ha1 ha.symm
    omega
  have hnb : H.degree b ≠ 1 := by
    intro hb1
    have ht := leaf_neighbor_degree_three hsat hb1 hb.symm
    omega
  have hs : H.degree a + H.degree b = 4 := by
    simpa [hN, hab, hx] using hsat x
  have hda := hdeg a
  have hdb := hdeg b
  have ha2 : H.degree a = 2 := by omega
  have hb2 : H.degree b = 2 := by omega
  have hy : y = a ∨ y = b := by
    have hyN : y ∈ H.neighborFinset x := (H.mem_neighborFinset _ _).mpr hxy
    simpa only [hN, Finset.mem_insert, Finset.mem_singleton] using hyN
  rcases hy with rfl | rfl
  · exact ha2
  · exact hb2

private theorem degree_three_neighbor_one_or_three
    (hdeg : ∀ x, H.degree x = 1 ∨ H.degree x = 2 ∨ H.degree x = 3)
    (hsat : ∀ x, (∑ y ∈ H.neighborFinset x, H.degree y) = H.degree x + 2)
    {x y : V} (hx : H.degree x = 3) (hxy : H.Adj x y) :
    H.degree y = 1 ∨ H.degree y = 3 := by
  rcases hdeg y with hy | hy | hy
  · exact Or.inl hy
  · have ht := degree_two_neighbor_degree_two hdeg hsat hy hxy.symm
    omega
  · exact Or.inr hy

private theorem degree_three_has_degree_three_neighbor
    (hdeg : ∀ x, H.degree x = 1 ∨ H.degree x = 2 ∨ H.degree x = 3)
    (hsat : ∀ x, (∑ y ∈ H.neighborFinset x, H.degree y) = H.degree x + 2)
    {x : V} (hx : H.degree x = 3) :
    ∃ y, H.Adj x y ∧ H.degree y = 3 := by
  by_contra! hn
  have hall : ∀ y ∈ H.neighborFinset x, H.degree y = 1 := by
    intro y hy
    have hxy := (H.mem_neighborFinset _ _).mp hy
    rcases degree_three_neighbor_one_or_three hdeg hsat hx hxy with h1 | h3
    · exact h1
    · exact False.elim (hn y hxy h3)
  have hs : (∑ y ∈ H.neighborFinset x, H.degree y) = 3 := by
    calc
      _ = ∑ _y ∈ H.neighborFinset x, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        exact hall
      _ = 3 := by simp [hx]
  have ht := hsat x
  omega

private theorem three_vertex_neighbor_finset
    {L R : Finset V}
    (hpart : H.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ x, H.degree x = 1 ∨ H.degree x = 2 ∨ H.degree x = 3)
    (hsat : ∀ x, (∑ y ∈ H.neighborFinset x, H.degree y) = H.degree x + 2)
    {a b : V} (haL : a ∈ L) (ha3 : H.degree a = 3) (hb3 : H.degree b = 3)
    (huniqR : ∀ y ∈ R, H.degree y = 3 → y = b)
    (hR1 : (R.filter fun y => H.degree y = 1).card = 2) :
    H.Adj a b ∧
    H.neighborFinset a = insert b (R.filter fun y => H.degree y = 1) ∧
    ∃ u v, u ≠ v ∧ u ∈ R ∧ v ∈ R ∧ H.degree u = 1 ∧ H.degree v = 1 ∧
      H.neighborFinset a = {b, u, v} := by
  obtain ⟨c, hac, hc3⟩ := degree_three_has_degree_three_neighbor hdeg hsat ha3
  have hcR : c ∈ R := hpart.mem_of_mem_adj haL hac
  have hcb := huniqR c hcR hc3
  have hab : H.Adj a b := by simpa only [hcb] using hac
  have hsub : H.neighborFinset a ⊆ insert b (R.filter fun y => H.degree y = 1) := by
    intro y hy
    have hay := (H.mem_neighborFinset _ _).mp hy
    have hyR : y ∈ R := hpart.mem_of_mem_adj haL hay
    rcases degree_three_neighbor_one_or_three hdeg hsat ha3 hay with hy1 | hy3
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hyR, hy1⟩)
    · have hyb := huniqR y hyR hy3
      simp only [hyb, Finset.mem_insert_self]
  have hbn : b ∉ R.filter (fun y => H.degree y = 1) := by
    intro hb
    have hb1 := (Finset.mem_filter.mp hb).2
    omega
  have htarget : (insert b (R.filter fun y => H.degree y = 1)).card = 3 := by
    simp only [Finset.card_insert_of_notMem hbn, hR1]
  have hN : H.neighborFinset a = insert b (R.filter fun y => H.degree y = 1) := by
    apply Finset.eq_of_subset_of_card_le hsub
    simpa only [htarget, H.card_neighborFinset_eq_degree, ha3] using (le_refl 3)
  obtain ⟨u, v, huv, huvset⟩ := Finset.card_eq_two.mp hR1
  have hu : u ∈ R ∧ H.degree u = 1 := by
    apply Finset.mem_filter.mp
    rw [huvset]
    simp
  have hv : v ∈ R ∧ H.degree v = 1 := by
    apply Finset.mem_filter.mp
    rw [huvset]
    simp
  refine ⟨hab, hN, u, v, huv, hu.1, hv.1, hu.2, hv.2, ?_⟩
  rw [hN, huvset]

/-- A saturated bipartite graph with exactly one degree-three point and two
leaves on each side has the actual central edge and both exact three-point
neighbor sets. All premises concern the graph itself. -/
private theorem symmetric_saturated_core
    {L R : Finset V}
    (hpart : H.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ x, H.degree x = 1 ∨ H.degree x = 2 ∨ H.degree x = 3)
    (hsat : ∀ x, (∑ y ∈ H.neighborFinset x, H.degree y) = H.degree x + 2)
    (hL3 : (L.filter fun x => H.degree x = 3).card = 1)
    (hR3 : (R.filter fun x => H.degree x = 3).card = 1)
    (hL1 : (L.filter fun x => H.degree x = 1).card = 2)
    (hR1 : (R.filter fun x => H.degree x = 1).card = 2) :
    ∃ a b, a ∈ L ∧ b ∈ R ∧ H.degree a = 3 ∧ H.degree b = 3 ∧ H.Adj a b ∧
      H.neighborFinset a = insert b (R.filter fun y => H.degree y = 1) ∧
      H.neighborFinset b = insert a (L.filter fun x => H.degree x = 1) ∧
      (∃ r₁ r₂, r₁ ≠ r₂ ∧ r₁ ∈ R ∧ r₂ ∈ R ∧
        H.degree r₁ = 1 ∧ H.degree r₂ = 1 ∧ H.neighborFinset a = {b, r₁, r₂}) ∧
      (∃ l₁ l₂, l₁ ≠ l₂ ∧ l₁ ∈ L ∧ l₂ ∈ L ∧
        H.degree l₁ = 1 ∧ H.degree l₂ = 1 ∧ H.neighborFinset b = {a, l₁, l₂}) := by
  obtain ⟨a, hA⟩ := Finset.card_eq_one.mp hL3
  obtain ⟨b, hB⟩ := Finset.card_eq_one.mp hR3
  have ha : a ∈ L ∧ H.degree a = 3 := by
    apply Finset.mem_filter.mp
    rw [hA]
    simp
  have hb : b ∈ R ∧ H.degree b = 3 := by
    apply Finset.mem_filter.mp
    rw [hB]
    simp
  have huniqL : ∀ x ∈ L, H.degree x = 3 → x = a := by
    intro x hx hx3
    have hm : x ∈ L.filter (fun y => H.degree y = 3) :=
      Finset.mem_filter.mpr ⟨hx, hx3⟩
    simpa only [hA, Finset.mem_singleton] using hm
  have huniqR : ∀ x ∈ R, H.degree x = 3 → x = b := by
    intro x hx hx3
    have hm : x ∈ R.filter (fun y => H.degree y = 3) :=
      Finset.mem_filter.mpr ⟨hx, hx3⟩
    simpa only [hB, Finset.mem_singleton] using hm
  obtain ⟨hab, hNa, hr⟩ :=
    three_vertex_neighbor_finset hpart hdeg hsat ha.1 ha.2 hb.2 huniqR hR1
  obtain ⟨_, hNb, hl⟩ :=
    three_vertex_neighbor_finset hpart.symm hdeg hsat hb.1 hb.2 ha.2 huniqL hL1
  exact ⟨a, b, ha.1, hb.1, ha.2, hb.2, hab, hNa, hNb, hr, hl⟩

end D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricSaturatedCore
