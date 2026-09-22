/- GID: D5/S3/Combinatorics/Graph/ThreeColorIncidence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/ThreeColorIncidence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: Incidence reduction for properly three-colored graphs with mixed degree two. -/

import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.ThreeColorReciprocal

open Finset
open scoped Classical

variable {W : Type*} [DecidableEq W]

/-- The neighbors inside the specified finite vertex set. -/
noncomputable def neighborhood (s : Finset W) (adj : W → W → Prop) (v : W) : Finset W :=
  s.filter (adj v)

/-- A vertex is mixed when two neighbors have different colors. -/
def Mixed (s : Finset W) (adj : W → W → Prop) (color : W → Fin 3) (v : W) : Prop :=
  ∃ u ∈ neighborhood s adj v, ∃ w ∈ neighborhood s adj v, color u ≠ color w

/-- Nonisolated vertices of color i whose neighbors all have color j. -/
noncomputable def ordinary (s : Finset W) (adj : W → W → Prop) (color : W → Fin 3)
    (i j : Fin 3) : Finset W :=
  s.filter fun v => color v = i ∧ (neighborhood s adj v).Nonempty ∧
    ∀ w ∈ neighborhood s adj v, color w = j

/-- Mixed vertices in a specified color class. -/
noncomputable def mixedColor (s : Finset W) (adj : W → W → Prop) (color : W → Fin 3)
    (i : Fin 3) : Finset W := s.filter fun v => color v = i ∧ Mixed s adj color v

/-- The sum of the three class reciprocals and half the degree reciprocals. -/
noncomputable def potential (s : Finset W) (adj : W → W → Prop)
    (color : W → Fin 3) : ℚ :=
  (∑ i : Fin 3, 1 / (((s.filter fun v => color v = i).card : ℚ) + 1)) +
    (1/2 : ℚ) * ∑ v ∈ s, 1 / ((neighborhood s adj v).card + 1 : ℚ)

/-- The available mixed incidences, with the exact subtraction at an empty opposite side. -/
def incoming (m : Fin 3 → ℕ) (x : Fin 3 → Fin 3 → ℕ) (i j : Fin 3) : ℕ :=
  if x j i = 0 then m j - m i else m j

/-- The ordinary complete-piece weight after charging each mixed attachment once. -/
def chargedLower (m : Fin 3 → ℕ) (x : Fin 3 → Fin 3 → ℕ) : ℚ :=
  (∑ i : Fin 3, 1 / ((m i + ∑ j, x i j : ℕ) + 1 : ℚ)) +
    (∑ i : Fin 3, (m i : ℚ)) / 6 +
      (1/2 : ℚ) * ∑ i : Fin 3, ∑ j : Fin 3,
        if i = j then 0 else
          (x i j : ℚ) / ((x j i : ℚ) + 1) -
            (m j : ℚ) / (((x j i : ℚ) + 1) * ((x j i : ℚ) + 2))

/-- A lower expression using the ordinary degree sum in Cauchy's inequality. -/
def quadraticLower (m : Fin 3 → ℕ) (x : Fin 3 → Fin 3 → ℕ) : ℚ :=
  (∑ i : Fin 3, 1 / ((m i + ∑ j, x i j : ℕ) + 1 : ℚ)) +
    (∑ i : Fin 3, (m i : ℚ)) / 6 +
      (1/2 : ℚ) * ∑ i : Fin 3, ∑ j : Fin 3,
        (x i j : ℚ)^2 / ((x i j * (x j i + 1) + incoming m x i j : ℕ) : ℚ)

/-- The two ordinary degree sums differ by the opposite mixed populations. -/
theorem incidence_reduction (s : Finset W) (adj : W → W → Prop)
    (color : W → Fin 3)
    (hsym : ∀ u ∈ s, ∀ v ∈ s, adj u v → adj v u)
    (hproper : ∀ u ∈ s, ∀ v ∈ s, adj u v → color u ≠ color v)
    (hm : ∀ v ∈ s, Mixed s adj color v → (neighborhood s adj v).card = 2)
    (i j : Fin 3) (hij : i ≠ j) :
    ((∑ v ∈ ordinary s adj color i j, (neighborhood s adj v).card) +
        (mixedColor s adj color i).card =
      (∑ v ∈ ordinary s adj color j i, (neighborhood s adj v).card) +
        (mixedColor s adj color j).card) ∧
    (∑ v ∈ ordinary s adj color i j, (neighborhood s adj v).card) ≤
      (ordinary s adj color i j).card * (ordinary s adj color j i).card +
        (mixedColor s adj color j).card ∧
    (∑ v ∈ ordinary s adj color i j, ((mixedColor s adj color j).filter (adj v)).card) ≤
      (mixedColor s adj color j).card ∧
    (∀ v ∈ ordinary s adj color i j, (neighborhood s adj v).card ≤
      (ordinary s adj color j i).card + ((mixedColor s adj color j).filter (adj v)).card) := by
  have cross (v : W) (hv : v ∈ s) (hvm : Mixed s adj color v)
      (k : Fin 3) (hkv : k ≠ color v) :
      ((neighborhood s adj v).filter fun w => color w = k).card = 1 := by
    obtain ⟨u, w, huw, hn⟩ := card_eq_two.mp (hm v hv hvm)
    have hu : u ∈ neighborhood s adj v := hn.symm ▸ (by simp)
    have hw : w ∈ neighborhood s adj v := hn.symm ▸ (by simp)
    have huc := hproper v hv u (mem_filter.mp hu).1 (mem_filter.mp hu).2
    have hwc := hproper v hv w (mem_filter.mp hw).1 (mem_filter.mp hw).2
    have hcolors : color u ≠ color w := by
      intro hc
      obtain ⟨a, ha, b, hb, hab⟩ := hvm
      rw [hn] at ha hb
      simp only [mem_insert, mem_singleton] at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
    have either : color u = k ∨ color w = k := by
      have hv0 := (color v).isLt
      have hu0 := (color u).isLt
      have hw0 := (color w).isLt
      have hk0 := k.isLt
      simp only [ne_eq, Fin.ext_iff] at huc hwc hcolors hkv ⊢
      omega
    rcases either with hu' | hw'
    · have hw' : color w ≠ k := by simpa [hu'] using hcolors.symm
      simp [hn, filter_insert, filter_singleton, hu', hw']
    · have hu' : color u ≠ k := by simpa [hw'] using hcolors
      simp [hn, filter_insert, filter_singleton, hu', hw']
  have expand (i j : Fin 3) (hij : i ≠ j) :
      (∑ v ∈ ordinary s adj color i j, (neighborhood s adj v).card) +
          (mixedColor s adj color i).card =
        ∑ v ∈ s.filter (fun v => color v = i),
          ((s.filter fun w => color w = j).filter (adj v)).card := by
    rw [ordinary, mixedColor, card_filter, sum_filter, sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    have same : ((s.filter fun w => color w = j).filter (adj v)) =
        (neighborhood s adj v).filter fun w => color w = j := by
      ext w
      simp [neighborhood, and_assoc, and_comm]
    rw [same]
    by_cases hvi : color v = i
    · simp only [hvi, true_and, if_true]
      by_cases hvm : Mixed s adj color v
      · have hnot : ¬ ((neighborhood s adj v).Nonempty ∧
            ∀ w ∈ neighborhood s adj v, color w = j) := by
          rintro ⟨_, hall⟩
          obtain ⟨u, hu, w, hw, hne⟩ := hvm
          exact hne ((hall u hu).trans (hall w hw).symm)
        rw [if_neg hnot, if_pos hvm, zero_add]
        exact (cross v hv hvm j (by simpa [hvi] using hij.symm)).symm
      · simp only [hvm, if_false, add_zero]
        by_cases he : ((neighborhood s adj v).filter fun w => color w = j).Nonempty
        · obtain ⟨w, hw⟩ := he
          obtain ⟨hwn, hwj⟩ := mem_filter.mp hw
          have hall : ∀ u ∈ neighborhood s adj v, color u = j := by
            intro u hu
            by_contra hne
            exact hvm ⟨u, hu, w, hwn, by simpa [hwj] using hne⟩
          rw [if_pos ⟨⟨w, hwn⟩, hall⟩, filter_eq_self.mpr hall]
        · have hnot : ¬ ((neighborhood s adj v).Nonempty ∧
              ∀ w ∈ neighborhood s adj v, color w = j) := by
            rintro ⟨⟨w, hw⟩, hall⟩
            exact he ⟨w, mem_filter.mpr ⟨hw, hall w hw⟩⟩
          rw [if_neg hnot, not_nonempty_iff_eq_empty.mp he, card_empty]
    · simp [hvi]
  have balance :
      (∑ v ∈ ordinary s adj color i j, (neighborhood s adj v).card) +
          (mixedColor s adj color i).card =
        (∑ v ∈ ordinary s adj color j i, (neighborhood s adj v).card) +
          (mixedColor s adj color j).card := by
    rw [expand i j hij, expand j i hij.symm]
    have hc := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := s.filter fun v => color v = i) (t := s.filter fun v => color v = j) adj
    apply hc.trans
    apply sum_congr rfl
    intro v hv
    congr 1
    ext u
    simp only [bipartiteBelow, mem_filter]
    constructor
    · rintro ⟨hu, huv⟩
      exact ⟨hu, hsym u hu.1 v (mem_filter.mp hv).1 huv⟩
    · rintro ⟨hu, hvu⟩
      exact ⟨hu, hsym v (mem_filter.mp hv).1 u hu.1 hvu⟩

  let U := ordinary s adj color i j
  let T := ordinary s adj color j i
  let M := mixedColor s adj color j
  have disj : Disjoint T M := by
    apply disjoint_left.mpr
    intro v hv hvm
    obtain ⟨_, _, _, hall⟩ := mem_filter.mp hv
    obtain ⟨_, _, u, hu, w, hw, hne⟩ := mem_filter.mp hvm
    exact hne ((hall u hu).trans (hall w hw).symm)
  have cover (v : W) (hv : v ∈ U) : neighborhood s adj v ⊆ T ∪ M := by
    intro w hw
    obtain ⟨hvs, hvi, _, hall⟩ := mem_filter.mp hv
    obtain ⟨hws, hvw⟩ := mem_filter.mp hw
    have hwj := hall w hw
    have hwv := hsym v hvs w hws hvw
    by_cases hwm : Mixed s adj color w
    · exact mem_union_right _ (mem_filter.mpr ⟨hws, hwj, hwm⟩)
    · apply mem_union_left
      refine mem_filter.mpr ⟨hws, hwj, ⟨v, mem_filter.mpr ⟨hvs, hwv⟩⟩, ?_⟩
      intro z hz
      by_contra hzi
      exact hwm ⟨z, hz, v, mem_filter.mpr ⟨hvs, hwv⟩, by simpa [hvi] using hzi⟩
  have count (v : W) (hv : v ∈ U) :
      (neighborhood s adj v).card = (T.filter (adj v)).card + (M.filter (adj v)).card := by
    have hn : neighborhood s adj v = T.filter (adj v) ∪ M.filter (adj v) := by
      ext w
      constructor
      · intro hw
        have h := cover v hv hw
        rcases mem_union.mp h with h | h
        · exact mem_union_left _ (mem_filter.mpr ⟨h, (mem_filter.mp hw).2⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨h, (mem_filter.mp hw).2⟩)
      · intro hw
        rcases mem_union.mp hw with hw | hw
        · obtain ⟨hwt, hadj⟩ := mem_filter.mp hw
          exact mem_filter.mpr ⟨(mem_filter.mp hwt).1, hadj⟩
        · obtain ⟨hwm, hadj⟩ := mem_filter.mp hw
          exact mem_filter.mpr ⟨(mem_filter.mp hwm).1, hadj⟩
    rw [hn, card_union_of_disjoint (disj.mono (filter_subset _ _) (filter_subset _ _))]
  have mixed_sum : (∑ v ∈ U, (M.filter (adj v)).card) ≤ M.card := by
    have hc := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := U) (t := M) adj
    change (∑ v ∈ U, (bipartiteAbove adj M v).card) ≤ _
    rw [hc]
    calc
      (∑ w ∈ M, (bipartiteBelow adj U w).card) ≤ ∑ _w ∈ M, 1 := by
        apply sum_le_sum
        intro w hw
        obtain ⟨hws, hwj, hwm⟩ := mem_filter.mp hw
        have hc := cross w hws hwm i (by simpa [hwj] using hij)
        rw [← hc]
        apply card_le_card
        intro v hv
        obtain ⟨hvU, hvw⟩ := mem_filter.mp hv
        obtain ⟨hvs, hvi, _⟩ := mem_filter.mp hvU
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨hvs, hsym v hvs w hws hvw⟩, hvi⟩
      _ = M.card := by simp
  have bound : (∑ v ∈ U, (neighborhood s adj v).card) ≤ U.card * T.card + M.card := by
    calc
      (∑ v ∈ U, (neighborhood s adj v).card) =
          (∑ v ∈ U, (T.filter (adj v)).card) + ∑ v ∈ U, (M.filter (adj v)).card := by
        rw [← sum_add_distrib]
        exact sum_congr rfl count
      _ ≤ (∑ _v ∈ U, T.card) + M.card := by
        exact Nat.add_le_add (sum_le_sum fun v hv => card_filter_le _ _) mixed_sum
      _ = U.card * T.card + M.card := by simp
  refine ⟨balance, bound, mixed_sum, ?_⟩
  intro v hv
  rw [count v hv]
  exact Nat.add_le_add_right (card_filter_le _ _) _

set_option maxHeartbeats 1200000 in
/-- Every nonisolated graph has the stated unbounded population reduction. -/
theorem population_reduction (s : Finset W) (adj : W → W → Prop)
    (color : W → Fin 3)
    (hsym : ∀ u ∈ s, ∀ v ∈ s, adj u v → adj v u)
    (hproper : ∀ u ∈ s, ∀ v ∈ s, adj u v → color u ≠ color v)
    (hm : ∀ v ∈ s, Mixed s adj color v → (neighborhood s adj v).card = 2)
    (hne : ∀ v ∈ s, (neighborhood s adj v).Nonempty) :
    let m := fun i => (mixedColor s adj color i).card
    let x := fun i j => (ordinary s adj color i j).card
    (∀ i, x i i = 0) ∧
      (∀ i j, i ≠ j → x i j = 0 → m j + x j i ≤ m i) ∧
      max (chargedLower m x) (quadraticLower m x) ≤ potential s adj color := by
  let m := fun i => (mixedColor s adj color i).card
  let x := fun i j => (ordinary s adj color i j).card
  let D := fun i j => ∑ v ∈ ordinary s adj color i j, (neighborhood s adj v).card
  have diag (i : Fin 3) : ordinary s adj color i i = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hvs, hvi, ⟨w, hw⟩, hall⟩ := mem_filter.mp hv
    exact hproper v hvs w (mem_filter.mp hw).1 (mem_filter.mp hw).2
      (hvi.trans (hall w hw).symm)
  have degpos (i j : Fin 3) : x i j ≤ D i j := by
    calc
      x i j = ∑ _v ∈ ordinary s adj color i j, 1 := by simp [x]
      _ ≤ D i j := sum_le_sum fun v hv => card_pos.mpr ((mem_filter.mp hv).2.2.1)
  have valid (i j : Fin 3) (hij : i ≠ j) (hx : x i j = 0) : m j + x j i ≤ m i := by
    have hzero : ordinary s adj color i j = ∅ := card_eq_zero.mp hx
    have hb := (incidence_reduction s adj color hsym hproper hm i j hij).1
    have hp := degpos j i
    simp only [hzero, sum_empty, zero_add] at hb
    dsimp [D, m] at *
    omega
  have degree_sum (i j : Fin 3) :
      D i j ≤ x i j * x j i + incoming m x i j := by
    by_cases hij : i = j
    · subst j
      simp [D, x, diag, incoming]
    have h := incidence_reduction s adj color hsym hproper hm i j hij
    by_cases ht : x j i = 0
    · have hzero : ordinary s adj color j i = ∅ := card_eq_zero.mp ht
      have hb := h.1
      simp only [hzero, sum_empty, zero_add] at hb
      dsimp [D, m]
      simp only [incoming, ht, if_pos, Nat.mul_zero, zero_add]
      omega
    · simpa only [incoming, ht, if_false] using h.2.1
  have partition (f : W → ℚ) :
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ v ∈ ordinary s adj color i j, f v) +
        (∑ i : Fin 3, ∑ v ∈ mixedColor s adj color i, f v) = ∑ v ∈ s, f v := by
    simp only [ordinary, mixedColor, sum_filter]
    simp_rw [sum_comm (s := (univ : Finset (Fin 3))) (t := s)]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    by_cases hvm : Mixed s adj color v
    · have hnot (j : Fin 3) : ¬ ((neighborhood s adj v).Nonempty ∧
          ∀ w ∈ neighborhood s adj v, color w = j) := by
        rintro ⟨_, hall⟩
        obtain ⟨u, hu, w, hw, hne⟩ := hvm
        exact hne ((hall u hu).trans (hall w hw).symm)
      simp [hnot, hvm]
    · obtain ⟨w, hw⟩ := hne v hv
      have hall : ∀ u ∈ neighborhood s adj v, color u = color w := by
        intro u hu
        by_contra h
        exact hvm ⟨u, hu, w, hw, h⟩
      have iff (i j : Fin 3) :
          (color v = i ∧ (neighborhood s adj v).Nonempty ∧
            ∀ u ∈ neighborhood s adj v, color u = j) ↔ color v = i ∧ color w = j := by
        constructor
        · rintro ⟨hi, _, hh⟩; exact ⟨hi, hh w hw⟩
        · rintro ⟨hi, hj⟩; exact ⟨hi, ⟨w, hw⟩, fun u hu => (hall u hu).trans hj⟩
      simp_rw [iff]
      simp [hvm, ite_and]
  have class_size (k : Fin 3) :
      (s.filter fun v => color v = k).card = m k + ∑ j, x k j := by
    have h := partition (fun v => if color v = k then 1 else 0)
    have ho (i j : Fin 3) :
        (∑ v ∈ ordinary s adj color i j, if color v = k then (1 : ℚ) else 0) =
          if i = k then (x i j : ℚ) else 0 := by
      calc
        _ = ∑ _v ∈ ordinary s adj color i j, if i = k then (1 : ℚ) else 0 := by
          apply sum_congr rfl
          intro v hv
          rw [(mem_filter.mp hv).2.1]
        _ = _ := by by_cases hi : i = k <;> simp [hi, x]
    have hmix (i : Fin 3) :
        (∑ v ∈ mixedColor s adj color i, if color v = k then (1 : ℚ) else 0) =
          if i = k then (m i : ℚ) else 0 := by
      calc
        _ = ∑ _v ∈ mixedColor s adj color i, if i = k then (1 : ℚ) else 0 := by
          apply sum_congr rfl
          intro v hv
          rw [(mem_filter.mp hv).2.1]
        _ = _ := by by_cases hi : i = k <;> simp [hi, m]
    simp_rw [ho, hmix] at h
    simp only [sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, if_true, sum_boole] at h
    exact_mod_cast h.symm.trans (add_comm _ _)
  have weights : (∑ v ∈ s, 1 / ((neighborhood s adj v).card + 1 : ℚ)) =
      (∑ i : Fin 3, ∑ j : Fin 3, ∑ v ∈ ordinary s adj color i j,
        1 / ((neighborhood s adj v).card + 1 : ℚ)) + (∑ i : Fin 3, (m i : ℚ)) / 3 := by
    rw [← partition]
    congr 1
    rw [sum_div]
    apply sum_congr rfl
    intro i hi
    calc
      (∑ v ∈ mixedColor s adj color i, 1 / ((neighborhood s adj v).card + 1 : ℚ)) =
          ∑ _v ∈ mixedColor s adj color i, (1/3 : ℚ) := by
        apply sum_congr rfl
        intro v hv
        rw [hm v (mem_filter.mp hv).1 (mem_filter.mp hv).2.2]
        norm_num
      _ = (m i : ℚ) / 3 := by simp [m, div_eq_mul_inv]
  have charged (i j : Fin 3) :
      (if i = j then 0 else
        (x i j : ℚ) / ((x j i : ℚ) + 1) -
          (m j : ℚ) / (((x j i : ℚ) + 1) * ((x j i : ℚ) + 2))) ≤
        ∑ v ∈ ordinary s adj color i j, 1 / ((neighborhood s adj v).card + 1 : ℚ) := by
    by_cases hij : i = j
    · subst j; simp [diag]
    simp only [hij, if_false]
    have hinc := incidence_reduction s adj color hsym hproper hm i j hij
    let N := fun v => ((mixedColor s adj color j).filter (adj v)).card
    have discrete (y h : ℕ) :
        1 / ((y : ℚ) + 1) - (h : ℚ) / (((y : ℚ) + 1) * ((y : ℚ) + 2)) ≤
          1 / ((y + h : ℕ) + 1 : ℚ) := by
      cases h with
      | zero => simp
      | succ h =>
        push_cast
        apply le_of_sub_nonneg
        field_simp
        ring_nf
        positivity
    have hn : (∑ v ∈ ordinary s adj color i j, (N v : ℚ)) ≤ (m j : ℚ) := by
      exact_mod_cast hinc.2.2.1
    calc
      (x i j : ℚ) / ((x j i : ℚ) + 1) -
          (m j : ℚ) / (((x j i : ℚ) + 1) * ((x j i : ℚ) + 2)) ≤
        (x i j : ℚ) / ((x j i : ℚ) + 1) -
          (∑ v ∈ ordinary s adj color i j, (N v : ℚ)) /
            (((x j i : ℚ) + 1) * ((x j i : ℚ) + 2)) := by
        exact sub_le_sub_left (div_le_div_of_nonneg_right hn (by positivity)) _
      _ = ∑ v ∈ ordinary s adj color i j,
          (1 / ((x j i : ℚ) + 1) -
            (N v : ℚ) / (((x j i : ℚ) + 1) * ((x j i : ℚ) + 2))) := by
        simp [sum_sub_distrib, sum_mul, x, div_eq_mul_inv]
      _ ≤ _ := by
        apply sum_le_sum
        intro v hv
        apply (discrete (x j i) (N v)).trans
        apply one_div_le_one_div_of_le (by positivity)
        exact_mod_cast Nat.add_le_add_right (hinc.2.2.2 v hv) 1
  have quadratic (i j : Fin 3) :
      (x i j : ℚ)^2 / ((x i j * (x j i + 1) + incoming m x i j : ℕ) : ℚ) ≤
        ∑ v ∈ ordinary s adj color i j, 1 / ((neighborhood s adj v).card + 1 : ℚ) := by
    by_cases hx : x i j = 0
    · simp only [hx, Nat.cast_zero, zero_pow (by decide : 2 ≠ 0), zero_div]
      exact sum_nonneg fun v hv => by positivity
    have hp : (0 : ℚ) < (D i j : ℚ) + x i j := by
      have : (0 : ℚ) < x i j := by exact_mod_cast Nat.pos_of_ne_zero hx
      exact add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) this
    have hb : (D i j : ℚ) + x i j ≤
        (x i j * (x j i + 1) + incoming m x i j : ℕ) := by
      exact_mod_cast (show D i j + x i j ≤ x i j * (x j i + 1) + incoming m x i j by
        have := degree_sum i j
        nlinarith)
    apply (div_le_div_of_nonneg_left (sq_nonneg _) hp hb).trans
    have hcs := sq_sum_div_le_sum_sq_div (ordinary s adj color i j)
      (fun _v => (1 : ℚ)) (g := fun v => ((neighborhood s adj v).card : ℚ) + 1)
      (fun v hv => by positivity)
    simpa only [sum_const, nsmul_eq_mul, mul_one, one_pow, sum_add_distrib, Nat.cast_sum,
      x, D] using hcs
  refine ⟨fun i => by simp [diag], valid, ?_⟩
  have hl := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin 3))) =>
    sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin 3))) => charged i j))
  have hq := sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin 3))) =>
    sum_le_sum (fun j (_ : j ∈ (univ : Finset (Fin 3))) => quadratic i j))
  simp only [chargedLower, quadraticLower, potential, class_size, weights, max_le_iff]
  constructor <;> linarith

end D5.S3.Combinatorics.Graph.ThreeColorReciprocal
