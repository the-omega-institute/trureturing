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

private theorem common_neighbors_card_le_two {x y : Finset (Fin n)} (hxy : x ≠ y) :
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

private theorem triple_common_neighbor {x y z : Finset (Fin n)} (hxy : x ≠ y)
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
    (hsub : ∀ j, support j ⊆ neighbors (center j)) (hsize : ∀ j, 4 ≤ (support j).card) :
    ∃ j, ∃ r ∈ support j, ∀ k, k ≠ j → r ∉ neighbors (center k) := by
  have peel (i j k : Fin 3) (hall : ∀ t, t = i ∨ t = j ∨ t = k)
      (hbound : (neighbors (center i) ∩ (neighbors (center j) ∪ neighbors (center k))).card ≤ 3) :
      ∃ p, ∃ r ∈ support p, ∀ q, q ≠ p → r ∉ neighbors (center q) := by
    have hnot : ¬ support i ⊆ neighbors (center j) ∪ neighbors (center k) := by
      intro h
      have hcard := card_le_card (subset_inter (hsub i) h)
      have hi := hsize i
      omega
    obtain ⟨r, hr, hrnot⟩ := not_subset.mp hnot
    refine ⟨i, r, hr, fun q hqi hq => ?_⟩
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
      (neighbors (center i) ∩ (neighbors (center j) ∪ neighbors (center k))).card ≤ 3 := by
    rw [inter_union_distrib_left, not_nonempty_iff_eq_empty.mp hempty, empty_union]
    exact (pair i k hik).trans (by decide)
  by_cases h01 : (neighbors (center 0) ∩ neighbors (center 1)).Nonempty
  · by_cases h02 : (neighbors (center 0) ∩ neighbors (center 2)).Nonempty
    · by_cases h12 : (neighbors (center 1) ∩ neighbors (center 2)).Nonempty
      · apply peel 0 1 2 (by decide)
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
      · exact peel 1 2 0 (by decide) (empty_case 1 2 0 (by decide) h12)
    · exact peel 0 2 1 (by decide) (empty_case 0 2 1 (by decide) h02)
  · exact peel 0 1 2 (by decide) (empty_case 0 1 2 (by decide) h01)

/-- On a common set of rows, each of three signed cube columns has at least four
neighbors. If the row sums are even integers, each real coefficient is an even integer. -/
theorem even_coefficients_of_three_cube_columns (rows : Finset (Finset (Fin n)))
    (center : Fin 3 ↪ Finset (Fin n)) (entry : Fin 3 → Finset (Fin n) → ℤ)
    (hsign : ∀ j r, r ∈ rows → (center j ∆ r).card = 1 →
      entry j r = 1 ∨ entry j r = -1)
    (hzero : ∀ j r, r ∈ rows → (center j ∆ r).card ≠ 1 → entry j r = 0)
    (hsize : ∀ j, 4 ≤ (rows.filter (fun r => (center j ∆ r).card = 1)).card)
    (coeff : Fin 3 → ℝ)
    (hrow : ∀ r ∈ rows, ∃ z : ℤ, (∑ j, (entry j r : ℝ) * coeff j) = 2 * (z : ℝ)) :
    ∀ j, ∃ z : ℤ, coeff j = 2 * (z : ℝ) := by
  let E := AddSubgroup.zmultiples (2 : ℝ)
  have even_iff (v : ℝ) : v ∈ E ↔ ∃ z : ℤ, v = 2 * (z : ℝ) := by
    change (∃ z : ℤ, z • (2 : ℝ) = v) ↔ _
    simp only [zsmul_eq_mul]
    exact exists_congr (fun z => by rw [mul_comm (z : ℝ) 2, eq_comm])
  let support (j : Fin 3) := rows.filter (fun r => (center j ∆ r).card = 1)
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
  obtain ⟨p, r, hr, hprivate⟩ := exists_private_column center support hsub hsize
  have hp : coeff p ∈ E :=
    recover p r hr (fun k hk hn => (hprivate k hk hn).elim)
  intro j
  apply (even_iff _).mp
  by_cases hj : j = p
  · simpa [hj] using hp
  have hother : ∃ k : Fin 3, k ≠ j ∧ k ≠ p ∧ ∀ t, t = j ∨ t = p ∨ t = k := by
    have h : ∀ a b : Fin 3, a ≠ b →
        ∃ c : Fin 3, c ≠ a ∧ c ≠ b ∧ ∀ t, t = a ∨ t = b ∨ t = c := by decide
    exact h j p hj
  obtain ⟨k, hkj, _, hall⟩ := hother
  have hnot : ¬ support j ⊆ neighbors (center k) := by
    intro h
    have hc := card_le_card (subset_inter (hsub j) h)
    have hb := common_neighbors_card_le_two
      (fun he => hkj (center.injective he.symm))
    have hs := hsize j
    change 4 ≤ (support j).card at hs
    omega
  obtain ⟨s, hs, hsnot⟩ := not_subset.mp hnot
  apply recover j s hs
  intro t ht hnear
  rcases hall t with rfl | rfl | rfl
  · exact (ht rfl).elim
  · exact hp
  · exact (hsnot hnear).elim

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnIntegrality
