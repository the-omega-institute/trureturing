/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/HuangThreeColumnParity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/HuangThreeColumnParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.SymmDiff]
   utility: none
   digest: Nonempty sums of three four-row cube columns have even weight at least four. -/

module

public import Mathlib.Data.Finset.Fold
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Powerset

/-! The binary weight obstruction for the three minority columns of the 18+3 fold
in Hong–Wu–Xia Problem 2 (arXiv:2610.09483v1, Section 7). -/

set_option autoImplicit false

public section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnParity

open Finset
open scoped symmDiff

variable {n : ℕ}

/-- The number of rows meeting an odd number of the selected cube columns. -/
@[expose] def cubeColumnParityWeight (rows : Finset (Finset (Fin n)))
    (center : Fin 3 ↪ Finset (Fin n)) (selected : Finset (Fin 3)) : ℕ :=
  (selected.fold symmDiff ⊥ (fun j => rows.filter fun r => (center j ∆ r).card = 1)).card

private def neighbors (x : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  univ.image (fun i : Fin n => x ∆ {i})

private theorem mem_neighbors {x r : Finset (Fin n)} :
    r ∈ neighbors x ↔ (x ∆ r).card = 1 := by
  simp only [neighbors, mem_image, mem_univ, true_and, card_eq_one]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, symmDiff_symmDiff_cancel_left _ _⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [← hi, symmDiff_symmDiff_cancel_left]⟩

/-- Translate to a common neighbor. The centers become different singletons, and
the axis from the first center to that neighbor belongs to their difference. -/
private theorem common_neighbor_axes {x y r : Finset (Fin n)} (hxy : x ≠ y)
    (hx : r ∈ neighbors x) (hy : r ∈ neighbors y) :
    (x ∆ y).card = 2 ∧
      r ∈ (x ∆ y).image (fun i => x ∆ {i}) := by
  obtain ⟨i, hi⟩ := card_eq_one.mp (mem_neighbors.mp hx)
  obtain ⟨j, hj⟩ := card_eq_one.mp (mem_neighbors.mp hy)
  have hd : x ∆ y = ({i} : Finset (Fin n)) ∆ {j} := by
    rw [← hi, ← hj, ← symmDiff_symmDiff_symmDiff_comm, symmDiff_self, symmDiff_bot]
  have hij : i ≠ j := by
    intro h
    subst j
    exact hxy (symmDiff_eq_empty.mp (by simpa using hd))
  rw [Finset.symmDiff_eq_union (disjoint_singleton.mpr hij), singleton_union] at hd
  refine ⟨by rw [hd, card_pair hij], mem_image.mpr ⟨i, by simp [hd], ?_⟩⟩
  rw [← hi, symmDiff_symmDiff_cancel_left]

private theorem pair_overlap {x y : Finset (Fin n)} (hxy : x ≠ y) :
    ((neighbors x) ∩ (neighbors y)).card ≤ 2 := by
  by_cases h : ((neighbors x) ∩ (neighbors y)).Nonempty
  · obtain ⟨r, hr⟩ := h
    have hcard := (common_neighbor_axes hxy (mem_inter.mp hr).1 (mem_inter.mp hr).2).1
    have hsub : neighbors x ∩ neighbors y ⊆ (x ∆ y).image (fun i => x ∆ {i}) := by
      intro t ht
      exact (common_neighbor_axes hxy (mem_inter.mp ht).1 (mem_inter.mp ht).2).2
    exact (card_le_card hsub).trans (card_image_le.trans_eq hcard)
  · simp [not_nonempty_iff_eq_empty.mp h]

private theorem triple_neighbor {x y z : Finset (Fin n)}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hXY : (neighbors x ∩ neighbors y).Nonempty)
    (hXZ : (neighbors x ∩ neighbors z).Nonempty)
    (hYZ : (neighbors y ∩ neighbors z).Nonempty) :
    ∃ r ∈ neighbors x, r ∈ neighbors y ∧ r ∈ neighbors z := by
  have distance_two {u v : Finset (Fin n)} (hne : u ≠ v)
      (h : (neighbors u ∩ neighbors v).Nonempty) : (u ∆ v).card = 2 := by
    obtain ⟨r, hr⟩ := h
    exact (common_neighbor_axes hne (mem_inter.mp hr).1 (mem_inter.mp hr).2).1
  have hAB : ((x ∆ y) ∆ (x ∆ z)).card = 2 := by
    rw [← symmDiff_symmDiff_symmDiff_comm, symmDiff_self, bot_symmDiff]
    exact distance_two hyz hYZ
  have hAx := distance_two hxy hXY
  have hBx := distance_two hxz hXZ
  have hmeet : ((x ∆ y) ∩ (x ∆ z)).Nonempty := by
    by_contra hn
    have hd := disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hn)
    rw [Finset.symmDiff_eq_union hd, card_union_of_disjoint hd, hAx, hBx] at hAB
    omega
  obtain ⟨i, hi⟩ := hmeet
  have crosses {v : Finset (Fin n)} (hcard : (x ∆ v).card = 2) (hmem : i ∈ x ∆ v) :
      x ∆ {i} ∈ neighbors v := by
    have he : ((x ∆ v).erase i).card = 1 := by
      rw [card_erase_of_mem hmem, hcard]
    obtain ⟨j, hj⟩ := card_eq_one.mp he
    have hpair : insert i ((x ∆ v).erase i) = x ∆ v := insert_erase hmem
    rw [hj, insert_eq] at hpair
    have hij : i ≠ j := by
      have hnot := notMem_erase i (x ∆ v)
      rwa [hj, mem_singleton] at hnot
    apply mem_neighbors.mpr
    rw [← symmDiff_assoc, symmDiff_comm v x, ← hpair,
      ← Finset.symmDiff_eq_union (disjoint_singleton.mpr hij)]
    rw [symmDiff_symmDiff_self', card_singleton]
  exact ⟨x ∆ {i}, mem_neighbors.mpr (by simp),
    crosses hAx (mem_inter.mp hi).1, crosses hBx (mem_inter.mp hi).2⟩

private theorem xor_card {α : Type*} [DecidableEq α] (a b : Finset α) :
    (a ∆ b).card + 2 * (a ∩ b).card = a.card + b.card := by
  rw [Finset.symmDiff_def, card_union_of_disjoint (by
    exact disjoint_left.mpr fun x ha hb => (mem_sdiff.mp ha).2 (mem_sdiff.mp hb).1)]
  have ha := card_sdiff_add_card_inter a b
  have hb := card_sdiff_add_card_inter b a
  rw [inter_comm b a] at hb
  omega

private theorem private_rows_subset_xor {α : Type*} [DecidableEq α] (a b c : Finset α) :
    a \ (b ∪ c) ⊆ a ∆ (b ∆ c) := by
  intro r hr
  obtain ⟨ha, hbc⟩ := mem_sdiff.mp hr
  exact mem_symmDiff.mpr (Or.inl ⟨ha, fun hx => hbc (symmDiff_subset_union hx)⟩)

private theorem three_xor_lower {x y z : Finset (Fin n)}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {a b c : Finset (Finset (Fin n))}
    (ha : a ⊆ neighbors x) (hb : b ⊆ neighbors y) (hc : c ⊆ neighbors z)
    (ha4 : a.card = 4) (hb4 : b.card = 4) (hc4 : c.card = 4) :
    4 ≤ (a ∆ (b ∆ c)).card := by
  have h_even := xor_card a (b ∆ c)
  have h_pair := xor_card b c
  have privateCount {u v w : Finset (Fin n)} {s t q : Finset (Finset (Fin n))}
      (hs : s ⊆ neighbors u) (ht : t ⊆ neighbors v) (hq : q ⊆ neighbors w)
      (huv : u ≠ v) (huw : u ≠ w)
      (hr : (neighbors u ∩ neighbors v ∩ (neighbors u ∩ neighbors w)).Nonempty)
      (hs4 : s.card = 4) : 1 ≤ (s \ (t ∪ q)).card := by
    have hsub := card_le_card (inter_subset_inter hs (union_subset_union ht hq))
    have hcover := card_union_add_card_inter (neighbors u ∩ neighbors v)
      (neighbors u ∩ neighbors w)
    have hpos := card_pos.mpr hr
    have h₁ := pair_overlap huv
    have h₂ := pair_overlap huw
    have hdiff := card_sdiff_add_card_inter s (t ∪ q)
    simp only [inter_union_distrib_left] at hsub hdiff
    omega
  have disjointCase {u v w : Finset (Fin n)} {s t q : Finset (Finset (Fin n))}
      (hs : s ⊆ neighbors u) (ht : t ⊆ neighbors v) (hq : q ⊆ neighbors w)
      (huw : u ≠ w) (hvw : v ≠ w) (hs4 : s.card = 4) (ht4 : t.card = 4)
      (hempty : ¬ (neighbors u ∩ neighbors v).Nonempty) :
      4 ≤ (s ∆ (t ∆ q)).card := by
    have hst : Disjoint s t :=
      (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hempty)).mono hs ht
    have hs2 : 2 ≤ (s \ q).card := by
      have hbound := (card_le_card (inter_subset_inter hs hq)).trans (pair_overlap huw)
      have hdiff := card_sdiff_add_card_inter s q
      omega
    have ht2 : 2 ≤ (t \ q).card := by
      have hbound := (card_le_card (inter_subset_inter ht hq)).trans (pair_overlap hvw)
      have hdiff := card_sdiff_add_card_inter t q
      omega
    have hsX : s \ q ⊆ s ∆ (t ∆ q) := by
      apply Subset.trans _ (private_rows_subset_xor s t q)
      intro r hr
      obtain ⟨hrs, hrq⟩ := mem_sdiff.mp hr
      exact mem_sdiff.mpr ⟨hrs, fun h => (mem_union.mp h).elim
        (disjoint_left.mp hst hrs) hrq⟩
    have htX : t \ q ⊆ s ∆ (t ∆ q) := by
      rw [symmDiff_left_comm]
      apply Subset.trans _ (private_rows_subset_xor t s q)
      intro r hr
      obtain ⟨hrt, hrq⟩ := mem_sdiff.mp hr
      exact mem_sdiff.mpr ⟨hrt, fun h => (mem_union.mp h).elim
        (fun hrs => disjoint_left.mp hst hrs hrt) hrq⟩
    have hbound := card_le_card (union_subset hsX htX)
    rw [card_union_of_disjoint (hst.mono sdiff_subset sdiff_subset)] at hbound
    omega
  by_cases hXY : (neighbors x ∩ neighbors y).Nonempty
  · by_cases hXZ : (neighbors x ∩ neighbors z).Nonempty
    · by_cases hYZ : (neighbors y ∩ neighbors z).Nonempty
      · obtain ⟨r, hrx, hry, hrz⟩ := triple_neighbor hxy hxz hyz hXY hXZ hYZ
        let A := a \ (b ∪ c)
        let B := b \ (a ∪ c)
        let C := c \ (a ∪ b)
        have hA : 1 ≤ A.card := privateCount ha hb hc hxy hxz
          ⟨r, mem_inter.mpr ⟨mem_inter.mpr ⟨hrx, hry⟩, mem_inter.mpr ⟨hrx, hrz⟩⟩⟩ ha4
        have hB : 1 ≤ B.card := privateCount hb ha hc hxy.symm hyz
          ⟨r, mem_inter.mpr ⟨mem_inter.mpr ⟨hry, hrx⟩, mem_inter.mpr ⟨hry, hrz⟩⟩⟩ hb4
        have hC : 1 ≤ C.card := privateCount hc ha hb hxz.symm hyz.symm
          ⟨r, mem_inter.mpr ⟨mem_inter.mpr ⟨hrz, hrx⟩, mem_inter.mpr ⟨hrz, hry⟩⟩⟩ hc4
        have hAB : Disjoint A B := by
          simp only [A, B, disjoint_left, mem_sdiff, mem_union, not_or]
          exact fun _ ha' hb' => ha'.2.1 hb'.1
        have hABC : Disjoint (A ∪ B) C := by
          simp only [A, B, C, disjoint_left, mem_sdiff, mem_union, not_or]
          exact fun _ h hc' => h.elim (fun ha' => ha'.2.2 hc'.1) (fun hb' => hb'.2.2 hc'.1)
        have hsub : A ∪ B ∪ C ⊆ a ∆ (b ∆ c) := by
          apply union_subset (union_subset (private_rows_subset_xor a b c) _) _
          · rw [symmDiff_left_comm]
            exact private_rows_subset_xor b a c
          · rw [← symmDiff_assoc, symmDiff_comm (a ∆ b) c]
            exact private_rows_subset_xor c a b
        have hbound := card_le_card hsub
        rw [card_union_of_disjoint hABC, card_union_of_disjoint hAB] at hbound
        omega
      · rw [symmDiff_left_comm, symmDiff_comm a c]
        exact disjointCase hb hc ha hxy.symm hxz.symm hb4 hc4 hYZ
    · rw [symmDiff_comm b c]
      exact disjointCase ha hc hb hxy hyz.symm ha4 hc4 hXZ
  · exact disjointCase ha hb hc hxz hyz ha4 hb4 hXY

/-- For three distinct centers with four neighbors each on a common row set,
every nonempty symmetric difference of their retained supports has even weight
between four and twelve. -/
theorem cube_column_parity_weight (rows : Finset (Finset (Fin n)))
    (center : Fin 3 ↪ Finset (Fin n))
    (hsize : ∀ j, (rows.filter fun r => (center j ∆ r).card = 1).card = 4)
    (selected : Finset (Fin 3)) (hselected : selected.Nonempty) :
    cubeColumnParityWeight rows center selected ∈ ({4, 6, 8, 10, 12} : Finset ℕ) := by
  let support (j : Fin 3) := rows.filter fun r => (center j ∆ r).card = 1
  have hsub (j : Fin 3) : support j ⊆ neighbors (center j) :=
    fun _ hr => mem_neighbors.mpr (mem_filter.mp hr).2
  change (selected.fold symmDiff ⊥ support).card ∈ _
  have single (i : Fin 3) : (({i} : Finset (Fin 3)).fold symmDiff ⊥ support).card ∈
      ({4, 6, 8, 10, 12} : Finset ℕ) := by
    have hi : (support i).card = 4 := hsize i
    rw [fold_singleton, symmDiff_bot, hi]
    simp
  have pair (i j : Fin 3) (hij : i ≠ j) :
      (({i, j} : Finset (Fin 3)).fold symmDiff ⊥ support).card ∈
        ({4, 6, 8, 10, 12} : Finset ℕ) := by
    rw [fold_insert (show i ∉ ({j} : Finset (Fin 3)) by simpa only [mem_singleton] using hij),
      fold_singleton, symmDiff_bot]
    have hcard := xor_card (support i) (support j)
    have hbound := (card_le_card (inter_subset_inter (hsub i) (hsub j))).trans
      (pair_overlap (fun he => hij (center.injective he)))
    have hi : (support i).card = 4 := hsize i
    have hj : (support j).card = 4 := hsize j
    simp only [mem_insert, mem_singleton]
    omega
  have choices : ∀ s : Finset (Fin 3), s = ∅ ∨ s = {0} ∨ s = {1} ∨ s = {2} ∨
      s = {0, 1} ∨ s = {0, 2} ∨ s = {1, 2} ∨ s = {0, 1, 2} := by decide
  rcases choices selected with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (not_nonempty_empty hselected).elim
  · exact single 0
  · exact single 1
  · exact single 2
  · exact pair 0 1 (by decide)
  · exact pair 0 2 (by decide)
  · exact pair 1 2 (by decide)
  · rw [fold_insert (show (0 : Fin 3) ∉ ({1, 2} : Finset (Fin 3)) by decide),
      fold_insert (show (1 : Fin 3) ∉ ({2} : Finset (Fin 3)) by decide),
      fold_singleton, symmDiff_bot]
    have distinct {i j : Fin 3} (h : i ≠ j) : center i ≠ center j :=
      fun he => h (center.injective he)
    have hlower := three_xor_lower
      (distinct (show (0 : Fin 3) ≠ 1 by decide))
      (distinct (show (0 : Fin 3) ≠ 2 by decide))
      (distinct (show (1 : Fin 3) ≠ 2 by decide))
      (hsub 0) (hsub 1) (hsub 2) (hsize 0) (hsize 1) (hsize 2)
    have houter := xor_card (support 0) (support 1 ∆ support 2)
    have hinner := xor_card (support 1) (support 2)
    have h0 : (support 0).card = 4 := hsize 0
    have h1 : (support 1).card = 4 := hsize 1
    have h2 : (support 2).card = 4 := hsize 2
    simp only [mem_insert, mem_singleton]
    omega

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnParity
