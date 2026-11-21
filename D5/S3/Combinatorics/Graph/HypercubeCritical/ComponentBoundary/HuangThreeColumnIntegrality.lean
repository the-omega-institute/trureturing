/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/HuangThreeColumnIntegrality
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/HuangThreeColumnIntegrality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.SymmDiff]
   utility: none
   digest: Even row sums force even coefficients for three signed cube columns. -/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-! Three signed Huang columns restricted to empty rows in the 18+3 fold of
Hong–Wu–Xia Problem 2 (arXiv:2610.09483v1, Section 7). -/

set_option autoImplicit false

public section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnIntegrality

open Finset
open scoped BigOperators symmDiff

variable {n : ℕ}

def neighbors (x : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  univ.image (fun i : Fin n => x ∆ {i})

theorem mem_neighbors {x r : Finset (Fin n)} :
    r ∈ neighbors x ↔ (x ∆ r).card = 1 := by
  simp only [neighbors, mem_image, mem_univ, true_and, card_eq_one]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, symmDiff_symmDiff_cancel_left _ _⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [← hi, symmDiff_symmDiff_cancel_left]⟩

private theorem singleton_symmDiff {i j : Fin n} (h : i ≠ j) :
    ({i} : Finset (Fin n)) ∆ {j} = {i, j} := by
  rw [Finset.symmDiff_eq_union (disjoint_singleton.mpr h), singleton_union]

private theorem common_neighbor_axes {x y r : Finset (Fin n)} (hxy : x ≠ y)
    (hx : r ∈ neighbors x) (hy : r ∈ neighbors y) :
    ∃ i j : Fin n, i ≠ j ∧ x ∆ y = {i, j} ∧ r = x ∆ {i} := by
  obtain ⟨i, hi⟩ := card_eq_one.mp (mem_neighbors.mp hx)
  obtain ⟨j, hj⟩ := card_eq_one.mp (mem_neighbors.mp hy)
  have hr : r = x ∆ {i} := by rw [← hi, symmDiff_symmDiff_cancel_left]
  have hd : x ∆ y = ({i} : Finset (Fin n)) ∆ {j} := by
    rw [← hi, ← hj, ← symmDiff_symmDiff_symmDiff_comm]
    rw [symmDiff_self, symmDiff_bot]
  have hij : i ≠ j := by
    intro h
    subst j
    exact hxy (symmDiff_eq_empty.mp (by simpa using hd))
  exact ⟨i, j, hij, hd.trans (singleton_symmDiff hij), hr⟩

theorem common_neighbors_card_le_two {x y : Finset (Fin n)} (hxy : x ≠ y) :
    (neighbors x ∩ neighbors y).card ≤ 2 := by
  by_cases hn : (neighbors x ∩ neighbors y).Nonempty
  · obtain ⟨r, hr⟩ := hn
    obtain ⟨i, j, _, hd, _⟩ :=
      common_neighbor_axes hxy (mem_inter.mp hr).1 (mem_inter.mp hr).2
    have hsub : neighbors x ∩ neighbors y ⊆ ({x ∆ {i}, x ∆ {j}} :
        Finset (Finset (Fin n))) := by
      intro s hs
      obtain ⟨a, b, _, hab, rfl⟩ :=
        common_neighbor_axes hxy (mem_inter.mp hs).1 (mem_inter.mp hs).2
      have ha : a ∈ ({i, j} : Finset (Fin n)) := by rw [← hd, hab]; simp
      rcases mem_insert.mp ha with h | h
      · simp [h]
      · have h' := mem_singleton.mp h
        simp [h']
    exact (card_le_card hsub).trans card_le_two
  · simp [not_nonempty_iff_eq_empty.mp hn]

theorem triple_common_neighbor {x y z : Finset (Fin n)} (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) (hXY : (neighbors x ∩ neighbors y).Nonempty)
    (hXZ : (neighbors x ∩ neighbors z).Nonempty)
    (hYZ : (neighbors y ∩ neighbors z).Nonempty) :
    ∃ r ∈ neighbors x, r ∈ neighbors y ∧ r ∈ neighbors z := by
  obtain ⟨r, hr⟩ := hXY
  obtain ⟨s, hs⟩ := hXZ
  obtain ⟨t, ht⟩ := hYZ
  obtain ⟨i, j, hij, hxy', _⟩ :=
    common_neighbor_axes hxy (mem_inter.mp hr).1 (mem_inter.mp hr).2
  obtain ⟨k, l, hkl, hxz', _⟩ :=
    common_neighbor_axes hxz (mem_inter.mp hs).1 (mem_inter.mp hs).2
  obtain ⟨a, b, hab, hyz', _⟩ :=
    common_neighbor_axes hyz (mem_inter.mp ht).1 (mem_inter.mp ht).2
  have hcard : ((x ∆ y) ∆ (x ∆ z)).card = 2 := by
    rw [← symmDiff_symmDiff_symmDiff_comm, symmDiff_self, bot_symmDiff, hyz']
    exact card_pair hab
  have hmeet : ((x ∆ y) ∩ (x ∆ z)).Nonempty := by
    by_contra hn
    have hd : Disjoint (x ∆ y) (x ∆ z) :=
      disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hn)
    rw [Finset.symmDiff_eq_union hd, card_union_of_disjoint hd, hxy', hxz'] at hcard
    rw [card_pair hij, card_pair hkl] at hcard
    omega
  obtain ⟨e, he⟩ := hmeet
  have crosses {u v : Finset (Fin n)} {p q : Fin n} (hpq : p ≠ q)
      (hd : u ∆ v = {p, q}) (he : e ∈ (u ∆ v)) : (u ∆ {e}) ∈ neighbors v := by
    have he' : e = p ∨ e = q := by simpa [hd] using he
    apply mem_neighbors.mpr
    rw [← symmDiff_assoc, symmDiff_comm v u, hd, ← singleton_symmDiff hpq]
    rcases he' with rfl | rfl
    · simp
    · simp
  refine ⟨x ∆ {e}, mem_neighbors.mpr (by simp), ?_, ?_⟩
  · exact crosses hij hxy' (mem_inter.mp he).1
  · exact crosses hkl hxz' (mem_inter.mp he).2

private theorem exists_private_column (center : Fin 3 ↪ Finset (Fin n))
    (support : Fin 3 → Finset (Finset (Fin n)))
    (hsub : ∀ j, support j ⊆ neighbors (center j))
    (h0 : 4 ≤ (support 0).card) (h1 : 3 ≤ (support 1).card) :
    ∃ j, (j = 0 ∨ j = 1) ∧ ∃ r ∈ support j, ∀ k, k ≠ j → r ∉ neighbors (center k) := by
  have peel (i j k : Fin 3) (hall : ∀ t, t = i ∨ t = j ∨ t = k)
      (hbound :
        (neighbors (center i) ∩ (neighbors (center j) ∪ neighbors (center k))).card <
          (support i).card) :
      ∃ r ∈ support i, ∀ q, q ≠ i → r ∉ neighbors (center q) := by
    have hnot : ¬ support i ⊆ neighbors (center j) ∪ neighbors (center k) := by
      intro h
      exact (not_le_of_gt hbound) (card_le_card (subset_inter (hsub i) h))
    obtain ⟨r, hr, hrnot⟩ := not_subset.mp hnot
    refine ⟨r, hr, fun q hqi hq => ?_⟩
    rcases hall q with rfl | rfl | rfl
    · exact hqi rfl
    · exact hrnot (mem_union_left _ hq)
    · exact hrnot (mem_union_right _ hq)
  have different {i j : Fin 3} (h : i ≠ j) : center i ≠ center j :=
    fun he => h (center.injective he)
  have pair (i j : Fin 3) (h : i ≠ j) :
      (neighbors (center i) ∩ neighbors (center j)).card ≤ 2 :=
    common_neighbors_card_le_two (different h)
  have empty_case (i j k : Fin 3) (hik : i ≠ k)
      (hempty : ¬ (neighbors (center i) ∩ neighbors (center j)).Nonempty) :
      (neighbors (center i) ∩ (neighbors (center j) ∪ neighbors (center k))).card ≤ 2 := by
    rw [inter_union_distrib_left, not_nonempty_iff_eq_empty.mp hempty, empty_union]
    exact pair i k hik
  by_cases h01 : (neighbors (center 0) ∩ neighbors (center 1)).Nonempty
  · by_cases h02 : (neighbors (center 0) ∩ neighbors (center 2)).Nonempty
    · by_cases h12 : (neighbors (center 1) ∩ neighbors (center 2)).Nonempty
      · refine ⟨0, Or.inl rfl, peel 0 1 2 (by decide) ?_⟩
        obtain ⟨r, hr0, hr1, hr2⟩ := triple_common_neighbor
          (different (show (0 : Fin 3) ≠ 1 by decide))
          (different (show (0 : Fin 3) ≠ 2 by decide))
          (different (show (1 : Fin 3) ≠ 2 by decide)) h01 h02 h12
        rw [inter_union_distrib_left]
        have hcard := card_union_add_card_inter
          (neighbors (center 0) ∩ neighbors (center 1))
          (neighbors (center 0) ∩ neighbors (center 2))
        have hpos := card_pos.mpr
          ⟨r, mem_inter.mpr ⟨mem_inter.mpr ⟨hr0, hr1⟩, mem_inter.mpr ⟨hr0, hr2⟩⟩⟩
        have h₁ := pair 0 1 (by decide)
        have h₂ := pair 0 2 (by decide)
        omega
      · refine ⟨1, Or.inr rfl, peel 1 2 0 (by decide) ?_⟩
        exact lt_of_le_of_lt (empty_case 1 2 0 (by decide) h12) h1
    · refine ⟨0, Or.inl rfl, peel 0 2 1 (by decide) ?_⟩
      exact lt_of_le_of_lt (empty_case 0 2 1 (by decide) h02) (by omega)
  · refine ⟨0, Or.inl rfl, peel 0 1 2 (by decide) ?_⟩
    exact lt_of_le_of_lt (empty_case 0 1 2 (by decide) h01) (by omega)

/-- On a common set of rows, signed cube columns 0, 1, and 2 have at least four,
three, and one neighboring rows respectively. Even integer row sums force each real
coefficient to be an even integer. -/
theorem even_coefficients_of_three_cube_columns (rows : Finset (Finset (Fin n)))
    (center : Fin 3 ↪ Finset (Fin n)) (entry : Fin 3 → Finset (Fin n) → ℤ)
    (hsign : ∀ j r, r ∈ rows → (center j ∆ r).card = 1 →
      entry j r = 1 ∨ entry j r = -1)
    (hzero : ∀ j r, r ∈ rows → (center j ∆ r).card ≠ 1 → entry j r = 0)
    (hsize : 4 ≤ (rows.filter (fun r => (center 0 ∆ r).card = 1)).card ∧
      3 ≤ (rows.filter (fun r => (center 1 ∆ r).card = 1)).card ∧
      1 ≤ (rows.filter (fun r => (center 2 ∆ r).card = 1)).card)
    (coeff : Fin 3 → ℝ)
    (hrow : ∀ r ∈ rows, ∃ z : ℤ, (∑ j, (entry j r : ℝ) * coeff j) = 2 * (z : ℝ)) :
    ∀ j, ∃ z : ℤ, coeff j = 2 * (z : ℝ) := by
  let E := AddSubgroup.zmultiples (2 : ℝ)
  have even_iff (v : ℝ) : v ∈ E ↔ ∃ z : ℤ, v = 2 * (z : ℝ) := by
    change (∃ z : ℤ, z • (2 : ℝ) = v) ↔ _
    simp only [zsmul_eq_mul]
    exact exists_congr (fun z => by rw [mul_comm (z : ℝ) 2, eq_comm])
  let support (j : Fin 3) := rows.filter (fun r => (center j ∆ r).card = 1)
  change 4 ≤ (support 0).card ∧ 3 ≤ (support 1).card ∧ 1 ≤ (support 2).card at hsize
  have hsub (j : Fin 3) : support j ⊆ neighbors (center j) :=
    fun _ hr => mem_neighbors.mpr (mem_filter.mp hr).2
  have recover (j : Fin 3) (r : Finset (Fin n)) (hr : r ∈ support j)
      (known : ∀ k, k ≠ j → r ∈ neighbors (center k) → coeff k ∈ E) :
      coeff j ∈ E := by
    obtain ⟨hrRows, hnear⟩ := mem_filter.mp hr
    have hrest : (∑ k ∈ univ.erase j, (entry k r : ℝ) * coeff k) ∈ E := by
      apply sum_mem
      intro k hk
      by_cases hn : r ∈ neighbors (center k)
      · have hc := known k (mem_erase.mp hk).1 hn
        rcases hsign k r hrRows (mem_neighbors.mp hn) with h | h
        · simpa [h] using hc
        · simpa [h] using E.neg_mem hc
      · rw [hzero k r hrRows (fun he => hn (mem_neighbors.mpr he))]
        simpa using E.zero_mem
    have htotal := (even_iff _).mpr (hrow r hrRows)
    rw [← add_sum_erase univ _ (mem_univ j)] at htotal
    have hj : (entry j r : ℝ) * coeff j ∈ E := by
      simpa only [add_sub_cancel_right] using E.sub_mem htotal hrest
    rcases hsign j r hrRows hnear with h | h
    · simpa [h] using hj
    · simpa [h] using E.neg_mem hj
  obtain ⟨p, hpIndex, r, hr, hprivate⟩ :=
    exists_private_column center support hsub hsize.1 hsize.2.1
  have hp : coeff p ∈ E :=
    recover p r hr (fun k hk hn => (hprivate k hk hn).elim)
  have recover_second (j k : Fin 3) (hk : coeff k ∈ E) (hj2 : j ≠ 2)
      (hall : ∀ t, t = j ∨ t = k ∨ t = 2) (hsizej : 3 ≤ (support j).card) :
      coeff j ∈ E := by
    have hnot : ¬ support j ⊆ neighbors (center 2) := by
      intro h
      have hc := card_le_card (subset_inter (hsub j) h)
      have hb := common_neighbors_card_le_two (fun he => hj2 (center.injective he))
      omega
    obtain ⟨s, hs, hsnot⟩ := not_subset.mp hnot
    apply recover j s hs
    intro t ht hnear
    rcases hall t with rfl | rfl | rfl
    · exact (ht rfl).elim
    · exact hk
    · exact (hsnot hnear).elim
  have all_columns : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  have h0Size : 3 ≤ (support 0).card := le_trans (by decide) hsize.1
  obtain ⟨h0, h1⟩ : coeff 0 ∈ E ∧ coeff 1 ∈ E := by
    rcases hpIndex with rfl | rfl
    · exact ⟨hp, recover_second 1 0 hp (by decide) (by decide) hsize.2.1⟩
    · exact ⟨recover_second 0 1 hp (by decide) all_columns h0Size, hp⟩
  have h2 : coeff 2 ∈ E := by
    obtain ⟨s, hs⟩ := card_pos.mp hsize.2.2
    apply recover 2 s hs
    intro k hk _
    rcases all_columns k with rfl | rfl | rfl
    · exact h0
    · exact h1
    · exact (hk rfl).elim
  intro j
  apply (even_iff _).mp
  rcases all_columns j with rfl | rfl | rfl <;> assumption

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnIntegrality
