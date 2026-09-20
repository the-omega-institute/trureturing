/- GID: D5/S3/Combinatorics/Graph/DUFSeparation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/DUFSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Combinatorics/Graph/DUFComponentCounts]
   utility: none
   digest: Distinct saturated link components require at least fifteen vertices including centers. -/

import D5.S3.Combinatorics.Graph.DUFComponentCounts

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.DUFSeparation

open Finset DUFStructure DUFCounting DUFComponents DUFComponentCounts
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Two sides of blocks with different centers have at most one common vertex. -/
theorem block_cell_bound (H : Finset (Finset V)) (hd : DUF H)
    (c d : V) (hcd : c ≠ d) (A S C D : Finset V)
    (hb : CompleteBlock H c A S) (hb' : CompleteBlock H d C D) :
    (A ∩ C).card ≤ 1 := by
  by_contra hn
  obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.mp (by omega : 1 < (A ∩ C).card)
  obtain ⟨s, hs, hsd⟩ := exists_mem_notMem_of_card_lt_card
    (by rw [card_singleton, hb.2.1]; decide : ({d} : Finset V).card < S.card)
  obtain ⟨t, ht, htc⟩ := exists_mem_notMem_of_card_lt_card
    (by have h2 := card_insert_le c ({s} : Finset V); simp only [card_singleton] at h2; rw [hb'.2.1]; omega : ({c, s} : Finset V).card < D.card)
  have hsc : s ≠ c := by intro h; subst s; exact hb.2.2.2.1 hs
  have htd : t ≠ d := by intro h; subst t; exact hb'.2.2.2.1 ht
  have hsd' : s ≠ d := by simpa only [mem_singleton] using hsd
  have htc' : t ≠ c ∧ t ≠ s := by simpa only [mem_insert, mem_singleton, not_or] using htc
  have hm (c : V) (A S : Finset V) (hb : CompleteBlock H c A S)
      (s : V) (hs : s ∈ S) (hu : u ∈ A) (hv : v ∈ A) :
      ({c, s} : Finset V) ∈ common H {u, v} := by
    have hcs : c ≠ s := by intro h; subst c; exact hb.2.2.2.1 hs
    refine mem_filter.mpr ⟨by simp [pairs, hcs], ?_⟩
    intro x hx
    have hxA : x ∈ A := by
      rcases mem_insert.mp hx with rfl | hx
      · exact hu
      · simpa using (mem_singleton.mp hx) ▸ hv
    have hxc : x ≠ c := by intro h; subst x; exact hb.2.2.1 hxA
    have hxs : x ≠ s := by intro h; subst x; exact disjoint_left.mp hb.2.2.2.2.1 hxA hs
    simp only [neighbors, mem_filter, mem_univ, true_and]
    refine ⟨by simp [hxc, hxs], ?_⟩
    have he : insert x ({c, s} : Finset V) = {c, x, s} := by
      ext z; simp only [mem_insert, mem_singleton]; tauto
    rw [he]; exact hb.2.2.2.2.2 x hxA s hs
  have hp := hm c A S hb s hs (mem_inter.mp hu).1 (mem_inter.mp hv).1
  have hr := hm d C D hb' t ht (mem_inter.mp hu).2 (mem_inter.mp hv).2
  apply common_intersecting H hd {u, v} (by simp [huv]) {c, s} hp {d, t} hr
  simp only [disjoint_left, mem_insert, mem_singleton]
  grind

/-- The four intersection cells cannot all be occupied: their diagonals would be
two disjoint edges in the common link of the centers. -/
theorem block_support_overlap (H : Finset (Finset V)) (hd : DUF H)
    (c d : V) (hcd : c ≠ d) (A S C D : Finset V)
    (hb : CompleteBlock H c A S) (hb' : CompleteBlock H d C D) :
    ((A ∪ S) ∩ (C ∪ D)).card ≤ 3 := by
  have swap (c : V) (A S : Finset V) (hb : CompleteBlock H c A S) :
      CompleteBlock H c S A := by
    refine ⟨hb.2.1, hb.1, hb.2.2.2.1, hb.2.2.1, hb.2.2.2.2.1.symm, ?_⟩
    intro s hs a ha; simpa [pair_comm] using hb.2.2.2.2.2 a ha s hs
  have h11 := block_cell_bound H hd c d hcd A S C D hb hb'
  have h12 := block_cell_bound H hd c d hcd A S D C hb (swap d C D hb')
  have h21 := block_cell_bound H hd c d hcd S A C D (swap c A S hb) hb'
  have h22 := block_cell_bound H hd c d hcd S A D C (swap c A S hb) (swap d C D hb')
  have empty_cell : A ∩ C = ∅ ∨ A ∩ D = ∅ ∨ S ∩ C = ∅ ∨ S ∩ D = ∅ := by
    by_contra he
    push Not at he
    obtain ⟨x, hx⟩ := he.1
    obtain ⟨y, hy⟩ := he.2.1
    obtain ⟨z, hz⟩ := he.2.2.1
    obtain ⟨w, hw⟩ := he.2.2.2
    have hAS := disjoint_left.mp hb.2.2.2.2.1
    have hCD := disjoint_left.mp hb'.2.2.2.2.1
    have hm (x w : V) (hx : x ∈ A ∩ C) (hw : w ∈ S ∩ D) :
        ({x, w} : Finset V) ∈ common H {c, d} := by
      have hxw : x ≠ w := by intro h; subst x; exact hAS (mem_inter.mp hx).1 (mem_inter.mp hw).1
      refine mem_filter.mpr ⟨by simp [pairs, hxw], ?_⟩
      simp only [insert_subset_iff, singleton_subset_iff, neighbors,
        mem_filter, mem_univ, true_and]
      refine ⟨⟨?_, hb.2.2.2.2.2 x (mem_inter.mp hx).1 w (mem_inter.mp hw).1⟩,
        ⟨?_, hb'.2.2.2.2.2 x (mem_inter.mp hx).2 w (mem_inter.mp hw).2⟩⟩
      · simp only [mem_insert, mem_singleton, not_or]
        constructor <;> intro h
        · exact hb.2.2.1 (h.symm ▸ (mem_inter.mp hx).1)
        · exact hb.2.2.2.1 (h.symm ▸ (mem_inter.mp hw).1)
      · simp only [mem_insert, mem_singleton, not_or]
        constructor <;> intro h
        · exact hb'.2.2.1 (h.symm ▸ (mem_inter.mp hx).2)
        · exact hb'.2.2.2.1 (h.symm ▸ (mem_inter.mp hw).2)
    have hp := hm x w hx hw
    have hr : ({y, z} : Finset V) ∈ common H {c, d} := by
      have hyz : y ≠ z := by intro h; subst y; exact hAS (mem_inter.mp hy).1 (mem_inter.mp hz).1
      refine mem_filter.mpr ⟨by simp [pairs, hyz], ?_⟩
      simp only [insert_subset_iff, singleton_subset_iff, neighbors,
        mem_filter, mem_univ, true_and]
      refine ⟨⟨?_, hb.2.2.2.2.2 y (mem_inter.mp hy).1 z (mem_inter.mp hz).1⟩, ⟨?_, ?_⟩⟩
      · simp only [mem_insert, mem_singleton, not_or]
        constructor <;> intro h
        · exact hb.2.2.1 (h.symm ▸ (mem_inter.mp hy).1)
        · exact hb.2.2.2.1 (h.symm ▸ (mem_inter.mp hz).1)
      · simp only [mem_insert, mem_singleton, not_or]
        constructor <;> intro h
        · exact hb'.2.2.2.1 (h.symm ▸ (mem_inter.mp hy).2)
        · exact hb'.2.2.1 (h.symm ▸ (mem_inter.mp hz).2)
      · simpa [pair_comm] using hb'.2.2.2.2.2 z (mem_inter.mp hz).2 y (mem_inter.mp hy).2
    apply common_intersecting H hd {c, d} (by simp [hcd]) {x, w} hp {y, z} hr
    simp only [mem_inter] at hx hy hz hw
    simp only [disjoint_left, mem_insert, mem_singleton]
    grind
  have heq : (A ∪ S) ∩ (C ∪ D) = (A ∩ C ∪ A ∩ D) ∪ (S ∩ C ∪ S ∩ D) := by
    ext x; simp only [mem_union, mem_inter]; tauto
  have hsum := card_union_le (A ∩ C ∪ A ∩ D) (S ∩ C ∪ S ∩ D)
  have htop := card_union_le (A ∩ C) (A ∩ D)
  have hbot := card_union_le (S ∩ C) (S ∩ D)
  rw [heq]
  rcases empty_cell with he | he | he | he <;>
    have hz := congrArg card he <;> simp only [card_empty] at hz <;> omega

/-- A center can lie in the other support in only one direction. In that case
the two supports share at most two vertices. -/
theorem block_center_overlap (H : Finset (Finset V)) (hd : DUF H) (hc : CapFour H)
    (c d : V) (hcd : c ≠ d) (A S C D : Finset V)
    (hb : CompleteBlock H c A S) (hb' : CompleteBlock H d C D)
    (hdU : d ∈ A ∪ S) :
    c ∉ C ∪ D ∧ ((A ∪ S) ∩ (C ∪ D)).card ≤ 2 := by
  have swap (c : V) (A S : Finset V) (hb : CompleteBlock H c A S) :
      CompleteBlock H c S A := by
    refine ⟨hb.2.1, hb.1, hb.2.2.2.1, hb.2.2.1, hb.2.2.2.2.1.symm, ?_⟩
    intro s hs a ha; simpa [pair_comm] using hb.2.2.2.2.2 a ha s hs
  have one (A S : Finset V) (hb : CompleteBlock H c A S) (hdA : d ∈ A) :
      c ∉ C ∪ D ∧ ((A ∪ S) ∩ (C ∪ D)).card ≤ 2 := by
    have hn := (block_component H hc c A S hb).1.1 d hdA
    have hnot : c ∉ C ∪ D := by
      intro hmem
      rcases mem_union.mp hmem with hcC | hcD
      · have hn' := (block_component H hc d C D hb').1.1 c hcC
        have hSD : S = D := hn.symm.trans (by simpa only [pair_comm d c] using hn')
        have hi := block_cell_bound H hd c d hcd S A D C (swap c A S hb) (swap d C D hb')
        rw [← hSD, inter_self, hb.2.1] at hi
        omega
      · have hn' := (block_component H hc d C D hb').1.2 c hcD
        have hSC : S = C := hn.symm.trans (by simpa only [pair_comm d c] using hn')
        have hi := block_cell_bound H hd c d hcd S A C D (swap c A S hb) hb'
        rw [← hSC, inter_self, hb.2.1] at hi
        omega
    have hSY : Disjoint S (C ∪ D) := by
      apply disjoint_left.mpr
      intro s hs hsY
      have hsc : s ≠ c := by intro h; subst s; exact hb.2.2.2.1 hs
      have hds : d ≠ s := by intro h; subst d; exact disjoint_left.mp hb.2.2.2.2.1 hdA hs
      have hadj : (link H d).Adj s c := by
        refine ⟨hsc, by simp [hds, (Ne.symm hcd)], ?_⟩
        have he : ({d, s, c} : Finset V) = {c, d, s} := by
          ext z; simp only [mem_insert, mem_singleton]; tauto
        rw [he]; exact hb.2.2.2.2.2 d hdA s hs
      rcases ((block_component H hc d C D hb').2.1 s hsY c).mp hadj with h | h
      · exact hnot (mem_union_right _ h.2)
      · exact hnot (mem_union_left _ h.2)
    have h11 := block_cell_bound H hd c d hcd A S C D hb hb'
    have h12 := block_cell_bound H hd c d hcd A S D C hb (swap d C D hb')
    have hcard := card_union_le (A ∩ C) (A ∩ D)
    refine ⟨hnot, ?_⟩
    rw [union_inter_distrib_right, disjoint_iff_inter_eq_empty.mp hSY,
      union_empty, inter_union_distrib_left]
    omega
  rcases mem_union.mp hdU with hdA | hdS
  · exact one A S hb hdA
  · simpa only [union_comm S A] using one S A (swap c A S hb) hdS

/-- Two distinct components, with their centers, occupy at least fifteen vertices.
For a common center the two disjoint eight-vertex supports occupy exactly seventeen. -/
theorem components_separated (H : Finset (Finset V)) (hd : DUF H) (hc : CapFour H)
    (z w : V × Finset V) (hz : z ∈ blocks H) (hw : w ∈ blocks H) (hne : z ≠ w) :
    15 ≤ (insert z.1 z.2 ∪ insert w.1 w.2).card ∧
      (z.1 = w.1 → (insert z.1 z.2 ∪ insert w.1 w.2).card = 17) := by
  obtain ⟨c, U⟩ := z
  obtain ⟨d, W⟩ := w
  obtain ⟨A, S, hb, hU⟩ := (mem_filter.mp hz).2
  obtain ⟨C, D, hb', hW⟩ := (mem_filter.mp hw).2
  change U = A ∪ S at hU
  change W = C ∪ D at hW
  subst U; subst W
  have hU8 : (A ∪ S).card = 8 := by
    rw [card_union_of_disjoint hb.2.2.2.2.1, hb.1, hb.2.1]
  have hW8 : (C ∪ D).card = 8 := by
    rw [card_union_of_disjoint hb'.2.2.2.2.1, hb'.1, hb'.2.1]
  have hcU : c ∉ A ∪ S := by
    simp only [mem_union, not_or]; exact ⟨hb.2.2.1, hb.2.2.2.1⟩
  have hdW : d ∉ C ∪ D := by
    simp only [mem_union, not_or]; exact ⟨hb'.2.2.1, hb'.2.2.2.1⟩
  have hU9 : (insert c (A ∪ S)).card = 9 := by rw [card_insert_of_notMem hcU, hU8]
  have hW9 : (insert d (C ∪ D)).card = 9 := by rw [card_insert_of_notMem hdW, hW8]
  by_cases hcd : c = d
  · subst d
    obtain ⟨_, _, K, hK⟩ := block_component H hc c A S hb
    obtain ⟨_, _, L, hL⟩ := block_component H hc c C D hb'
    have hdis : Disjoint (A ∪ S) (C ∪ D) := by
      apply disjoint_left.mpr
      intro x hx hy
      have hxK : x ∈ K.supp := by rw [hK]; exact hx
      have hxL : x ∈ L.supp := by rw [hL]; exact hy
      have hKL := SimpleGraph.ConnectedComponent.eq_of_common_vertex hxK hxL
      have hUW : A ∪ S = C ∪ D := coe_injective
        (hK.symm.trans ((congrArg SimpleGraph.ConnectedComponent.supp hKL).trans hL))
      exact hne (Prod.ext rfl hUW)
    have hcUW : c ∉ (A ∪ S) ∪ (C ∪ D) := by
      intro hm
      rcases mem_union.mp hm with hm | hm
      · exact hcU hm
      · exact hdW hm
    have h17 : (insert c (A ∪ S) ∪ insert c (C ∪ D)).card = 17 := by
      rw [insert_union, union_insert, insert_idem,
        card_insert_of_notMem hcUW, card_union_of_disjoint hdis, hU8, hW8]
    exact ⟨by simpa only using h17.ge.trans' (by decide : 15 ≤ 17), fun _ => h17⟩
  · have insbound (c d : V) (U W : Finset V) (hcd : c ≠ d) (hcW : c ∉ W)
        (hUW : (U ∩ W).card ≤ 2) : (insert c U ∩ insert d W).card ≤ 3 := by
      have hsub : insert c U ∩ insert d W ⊆ insert d (U ∩ W) := by
        intro x hx
        obtain ⟨hxU, hxW⟩ := mem_inter.mp hx
        rcases mem_insert.mp hxW with hxd | hxW
        · exact mem_insert.mpr (Or.inl hxd)
        · have hxU' : x ∈ U := (mem_insert.mp hxU).resolve_left (by
            intro h; subst x; exact hcW hxW)
          exact mem_insert_of_mem (mem_inter.mpr ⟨hxU', hxW⟩)
      have hi := card_le_card hsub
      have hj := card_insert_le d (U ∩ W)
      omega
    have hi : (insert c (A ∪ S) ∩ insert d (C ∪ D)).card ≤ 3 := by
      by_cases hdU : d ∈ A ∪ S
      · obtain ⟨hcW, hUW⟩ := block_center_overlap H hd hc c d hcd A S C D hb hb' hdU
        exact insbound c d (A ∪ S) (C ∪ D) hcd hcW hUW
      · by_cases hcW : c ∈ C ∪ D
        · obtain ⟨_, hWU⟩ := block_center_overlap H hd hc d c (Ne.symm hcd) C D A S hb' hb hcW
          rw [inter_comm]
          exact insbound d c (C ∪ D) (A ∪ S) (Ne.symm hcd) hdU hWU
        · have he : insert c (A ∪ S) ∩ insert d (C ∪ D) = (A ∪ S) ∩ (C ∪ D) := by
            ext x
            by_cases hxc : x = c <;> by_cases hxd : x = d <;>
              simp [mem_inter, mem_insert, hxc, hxd, hcU, hdW, hdU, hcW, (Ne.symm hcd)]
          rw [he]
          exact block_support_overlap H hd c d hcd A S C D hb hb'
    have hcard := card_union_add_card_inter (insert c (A ∪ S)) (insert d (C ∪ D))
    simp only [hU9, hW9] at hcard
    exact ⟨by dsimp; omega, fun he => (hcd he).elim⟩

/-- On at most fourteen vertices, a DUF triple family of maximum codegree four
has at most as many triples as ground pairs. -/
theorem fourteen_vertex_bound (H : Finset (Finset V)) (hu : ∀ e ∈ H, e.card = 3)
    (hd : DUF H) (hc : CapFour H) (hn : Fintype.card V ≤ 14) :
    H.card ≤ (Fintype.card V).choose 2 := by
  have hB : B H ≤ 1 := by
    by_contra hB
    obtain ⟨z, hz, w, hw, hzw⟩ := one_lt_card.mp (by
      change ¬ (blocks H).card ≤ 1 at hB
      omega : 1 < (blocks H).card)
    have hs := (components_separated H hd hc z w hz hw hzw).1
    have hu' := card_le_univ (insert z.1 z.2 ∪ insert w.1 w.2)
    omega
  have hi := (component_counting H hu hd hc).2.2.1
  omega

end D5.S3.Combinatorics.Graph.DUFSeparation
