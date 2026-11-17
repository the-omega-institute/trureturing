/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/SymmetricMixedCore
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/SymmetricMixedCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Girth]
   utility: none
   digest: One-sided saturation in the actual A/B high profiles forces a closed six-point Y: a degree-three center, its leaf, two degree-two arms, and their leaves. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.GirthSliceCounting

/-! The actual six-point Y core in the mixed A/B high-graph branch.
Only the left-side neighbor-degree inequalities are assumed saturated. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricMixedCore

open SimpleGraph
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V}

omit [DecidableEq V] in
private theorem leaf_neighbor_data {x : V} (hx : H.degree x = 1) :
    ∃ y, H.neighborFinset x = {y} ∧ H.Adj x y := by
  have hc : (H.neighborFinset x).card = 1 := by
    simpa only [H.card_neighborFinset_eq_degree] using hx
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hc
  refine ⟨y, hy, ?_⟩
  apply (H.mem_neighborFinset _ _).mp
  rw [hy]
  simp

omit [DecidableEq V] in
private theorem saturated_leaf_neighbor_degree_three {x y : V}
    (hx : H.degree x = 1)
    (hsat : (∑ z ∈ H.neighborFinset x, H.degree z) = H.degree x + 2)
    (hxy : H.Adj x y) : H.degree y = 3 := by
  obtain ⟨z, hN, _hxz⟩ := leaf_neighbor_data hx
  have hyz : y = z := by
    have hm := (H.mem_neighborFinset _ _).mpr hxy
    simpa only [hN, Finset.mem_singleton] using hm
  have hz3 : H.degree z = 3 := by
    simpa only [hN, Finset.sum_singleton, hx] using hsat
  exact (congrArg (fun v => H.degree v) hyz).trans hz3

private theorem saturated_two_neighbor_finset
    {L R : Finset V}
    (hpart : H.IsBipartiteWith (L : Set V) (R : Set V))
    {x r t : V} (hxL : x ∈ L) (hx2 : H.degree x = 2) (hr1 : H.degree r = 1)
    (hxr : H.Adj x r)
    (hsat : (∑ z ∈ H.neighborFinset x, H.degree z) = H.degree x + 2)
    (huniq : ∀ y ∈ R, H.degree y = 3 → y = t) :
    H.neighborFinset x = {t, r} ∧ H.Adj x t := by
  have hrN : r ∈ H.neighborFinset x := (H.mem_neighborFinset _ _).mpr hxr
  have hc : ((H.neighborFinset x).erase r).card = 1 := by
    rw [Finset.card_erase_of_mem hrN, H.card_neighborFinset_eq_degree, hx2]
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp hc
  have huN : u ∈ (H.neighborFinset x).erase r := by
    rw [hu]
    simp
  have hxu : H.Adj x u :=
    (H.mem_neighborFinset _ _).mp (Finset.mem_erase.mp huN).2
  have huR : u ∈ R := hpart.mem_of_mem_adj hxL hxu
  have hs := Finset.sum_erase_add (H.neighborFinset x) (fun z => H.degree z) hrN
  rw [hu, Finset.sum_singleton, hr1, hsat, hx2] at hs
  have hu3 : H.degree u = 3 := by omega
  have hut := huniq u huR hu3
  have hNraw := Finset.insert_erase hrN
  rw [hu] at hNraw
  refine ⟨?_, by simpa only [hut] using hxu⟩
  rw [← hNraw, hut]
  exact Finset.pair_comm r t

/-- The mixed profiles force a six-point Y with arms of lengths one, two, two.
All six vertices, degrees, memberships and exact neighbor sets are extracted
from the actual graph. Right-side saturation is not a premise. -/
private theorem mixed_saturated_y_core
    {L R : Finset V}
    (hpart : H.IsBipartiteWith (L : Set V) (R : Set V))
    (hdeg : ∀ x, H.degree x = 1 ∨ H.degree x = 2 ∨ H.degree x = 3)
    (hL : ((L.filter fun x => H.degree x = 1).card,
      (L.filter fun x => H.degree x = 2).card,
      (L.filter fun x => H.degree x = 3).card) = (1, 6, 0))
    (hR : ((R.filter fun x => H.degree x = 1).card,
      (R.filter fun x => H.degree x = 2).card,
      (R.filter fun x => H.degree x = 3).card) = (2, 4, 1))
    (hsatL : ∀ x ∈ L, (∑ y ∈ H.neighborFinset x, H.degree y) = H.degree x + 2) :
    ∃ t a s₁ s₂ r₁ r₂,
      t ∈ R ∧ a ∈ L ∧ s₁ ∈ L ∧ s₂ ∈ L ∧ r₁ ∈ R ∧ r₂ ∈ R ∧
      H.degree t = 3 ∧ H.degree a = 1 ∧ H.degree s₁ = 2 ∧ H.degree s₂ = 2 ∧
      H.degree r₁ = 1 ∧ H.degree r₂ = 1 ∧
      ([a, s₁, s₂, t, r₁, r₂] : List V).Nodup ∧
      H.neighborFinset t = {a, s₁, s₂} ∧ H.neighborFinset a = {t} ∧
      H.neighborFinset s₁ = {t, r₁} ∧ H.neighborFinset s₂ = {t, r₂} ∧
      H.neighborFinset r₁ = {s₁} ∧ H.neighborFinset r₂ = {s₂} := by
  have hL1 : (L.filter fun x => H.degree x = 1).card = 1 :=
    congrArg (fun p : ℕ × ℕ × ℕ => p.1) hL
  have hL3 : (L.filter fun x => H.degree x = 3).card = 0 :=
    congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hL
  have hR1 : (R.filter fun x => H.degree x = 1).card = 2 :=
    congrArg (fun p : ℕ × ℕ × ℕ => p.1) hR
  have hR3 : (R.filter fun x => H.degree x = 3).card = 1 :=
    congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) hR
  obtain ⟨a, hA⟩ := Finset.card_eq_one.mp hL1
  obtain ⟨t, hT⟩ := Finset.card_eq_one.mp hR3
  obtain ⟨r₁, r₂, hr₁r₂, hRs⟩ := Finset.card_eq_two.mp hR1
  have ha : a ∈ L ∧ H.degree a = 1 := by
    apply Finset.mem_filter.mp
    rw [hA]
    simp
  have ht : t ∈ R ∧ H.degree t = 3 := by
    apply Finset.mem_filter.mp
    rw [hT]
    simp
  have hr₁ : r₁ ∈ R ∧ H.degree r₁ = 1 := by
    apply Finset.mem_filter.mp
    rw [hRs]
    simp
  have hr₂ : r₂ ∈ R ∧ H.degree r₂ = 1 := by
    apply Finset.mem_filter.mp
    rw [hRs]
    simp
  have huniqR : ∀ y ∈ R, H.degree y = 3 → y = t := by
    intro y hy hy3
    have hm : y ∈ R.filter (fun z => H.degree z = 3) :=
      Finset.mem_filter.mpr ⟨hy, hy3⟩
    simpa only [hT, Finset.mem_singleton] using hm
  have hnoL3 : ∀ y ∈ L, H.degree y ≠ 3 := by
    intro y hy hy3
    have hm : y ∈ L.filter (fun z => H.degree z = 3) :=
      Finset.mem_filter.mpr ⟨hy, hy3⟩
    have hp : 0 < (L.filter fun z => H.degree z = 3).card :=
      Finset.card_pos.mpr ⟨y, hm⟩
    omega
  obtain ⟨u, hNa, hau⟩ := leaf_neighbor_data ha.2
  have huR : u ∈ R := hpart.mem_of_mem_adj ha.1 hau
  have hu3 := saturated_leaf_neighbor_degree_three ha.2 (hsatL a ha.1) hau
  have hut := huniqR u huR hu3
  have hNa' : H.neighborFinset a = {t} := by simpa only [hut] using hNa
  have hat : H.Adj a t := by simpa only [hut] using hau
  obtain ⟨s₁, hNr₁, hr₁s₁⟩ := leaf_neighbor_data hr₁.2
  obtain ⟨s₂, hNr₂, hr₂s₂⟩ := leaf_neighbor_data hr₂.2
  have hs₁L : s₁ ∈ L := hpart.symm.mem_of_mem_adj hr₁.1 hr₁s₁
  have hs₂L : s₂ ∈ L := hpart.symm.mem_of_mem_adj hr₂.1 hr₂s₂
  have hs₁2 : H.degree s₁ = 2 := by
    rcases hdeg s₁ with hs | hs | hs
    · have he := saturated_leaf_neighbor_degree_three hs (hsatL s₁ hs₁L) hr₁s₁.symm
      have hr₁1 := hr₁.2
      omega
    · exact hs
    · exact False.elim (hnoL3 s₁ hs₁L hs)
  have hs₂2 : H.degree s₂ = 2 := by
    rcases hdeg s₂ with hs | hs | hs
    · have he := saturated_leaf_neighbor_degree_three hs (hsatL s₂ hs₂L) hr₂s₂.symm
      have hr₂1 := hr₂.2
      omega
    · exact hs
    · exact False.elim (hnoL3 s₂ hs₂L hs)
  obtain ⟨hNs₁, hs₁t⟩ := saturated_two_neighbor_finset hpart hs₁L hs₁2 hr₁.2
    hr₁s₁.symm (hsatL s₁ hs₁L) huniqR
  obtain ⟨hNs₂, hs₂t⟩ := saturated_two_neighbor_finset hpart hs₂L hs₂2 hr₂.2
    hr₂s₂.symm (hsatL s₂ hs₂L) huniqR
  have htr₁ : t ≠ r₁ := by intro he; have hd := hr₁.2; rw [← he, ht.2] at hd; omega
  have htr₂ : t ≠ r₂ := by intro he; have hd := hr₂.2; rw [← he, ht.2] at hd; omega
  have has₁ : a ≠ s₁ := by intro he; have hd := ha.2; rw [he, hs₁2] at hd; omega
  have has₂ : a ≠ s₂ := by intro he; have hd := ha.2; rw [he, hs₂2] at hd; omega
  have hs₁s₂ : s₁ ≠ s₂ := by
    intro he
    have hm : r₂ ∈ H.neighborFinset s₁ :=
      (H.mem_neighborFinset _ _).mpr (by simpa only [he] using hr₂s₂.symm)
    rw [hNs₁] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hrt | hrr
    · exact htr₂ hrt.symm
    · exact hr₁r₂ hrr.symm
  have hsub : ({a, s₁, s₂} : Finset V) ⊆ H.neighborFinset t := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact (H.mem_neighborFinset _ _).mpr hat.symm
    · exact (H.mem_neighborFinset _ _).mpr hs₁t.symm
    · exact (H.mem_neighborFinset _ _).mpr hs₂t.symm
  have htarget : ({a, s₁, s₂} : Finset V).card = 3 := by simp [has₁, has₂, hs₁s₂]
  have hNt : H.neighborFinset t = {a, s₁, s₂} := by
    apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
    simpa only [H.card_neighborFinset_eq_degree, ht.2, htarget] using (le_refl 3)
  have hcross {x y : V} (hx : x ∈ L) (hy : y ∈ R) : x ≠ y := by
    intro he
    have hxR : x ∈ R := by simpa only [he] using hy
    exact Set.disjoint_left.mp hpart.disjoint hx hxR
  have hnodes : ([a, s₁, s₂, t, r₁, r₂] : List V).Nodup := by
    simp [has₁, has₂, hs₁s₂, htr₁, htr₂, hr₁r₂,
      hcross ha.1 ht.1, hcross ha.1 hr₁.1, hcross ha.1 hr₂.1,
      hcross hs₁L ht.1, hcross hs₁L hr₁.1, hcross hs₁L hr₂.1,
      hcross hs₂L ht.1, hcross hs₂L hr₁.1, hcross hs₂L hr₂.1]
  exact ⟨t, a, s₁, s₂, r₁, r₂, ht.1, ha.1, hs₁L, hs₂L, hr₁.1, hr₂.1,
    ht.2, ha.2, hs₁2, hs₂2, hr₁.2, hr₂.2, hnodes, hNt, hNa', hNs₁, hNs₂, hNr₁, hNr₂⟩

#print axioms mixed_saturated_y_core

end D5.S3.Combinatorics.Graph.HypercubeCritical.SymmetricMixedCore
