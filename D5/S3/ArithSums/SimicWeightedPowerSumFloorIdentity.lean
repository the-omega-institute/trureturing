/- GID: D5/S3/ArithSums/SimicWeightedPowerSumFloorIdentity
   generality: G
   mirror-B: D5/B/S3/ArithSums/SimicWeightedPowerSumFloorIdentity
   mirror-E: none(waiver:unbounded-symbolic-floor-identity)
   anchors: [mathlib/module/Mathlib.Algebra.Order.Floor.Ring, mathlib/module/Mathlib.Data.Finset.Max, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Simic H-655(ii) weighted power-sum floor identity for at least two indices. -/

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

open scoped BigOperators

namespace D5.S3.ArithSums.SimicWeightedPowerSumFloorIdentity

/-- Simic's Fibonacci Quarterly Problem H-655(ii), with the necessary exclusion of
the singleton case. -/
theorem simic_h655_ii (s : Finset ℕ) (hs : 2 ≤ s.card)
    (h1 : ∀ i ∈ s, 1 ≤ i) (q : ℕ) (hq : 2 ≤ q) :
    ⌊((q : ℚ) - 1) * (∑ i ∈ s, (i : ℚ) * (q : ℚ) ^ i) /
        (∑ i ∈ s, (q : ℚ) ^ i)⌋ =
      (s.max' (Finset.card_pos.mp (by omega)) : ℤ) * ((q : ℤ) - 1) - 1 := by
  classical
  have tail_sum_identity (c : ℕ) :
      (∑ i ∈ Finset.range c,
          (((q : ℚ) - 1) * ((c - i : ℕ) : ℚ) - 1) * (q : ℚ) ^ i) =
        (q : ℚ) ^ c - (c + 1 : ℕ) := by
    induction c with
    | zero => simp
    | succ c ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ i ∈ Finset.range c,
              (((q : ℚ) - 1) * ((c + 1 - i : ℕ) : ℚ) - 1) * (q : ℚ) ^ i) +
            (((q : ℚ) - 1) * ((c + 1 - c : ℕ) : ℚ) - 1) * (q : ℚ) ^ c =
            (∑ i ∈ Finset.range c,
              ((((q : ℚ) - 1) * ((c - i : ℕ) : ℚ) - 1) * (q : ℚ) ^ i +
                ((q : ℚ) - 1) * (q : ℚ) ^ i)) +
              ((q : ℚ) - 2) * (q : ℚ) ^ c := by
                congr 1
                · apply Finset.sum_congr rfl
                  intro i hi
                  have hic : i < c := Finset.mem_range.mp hi
                  have hsub : c + 1 - i = (c - i) + 1 := by omega
                  rw [hsub]
                  push_cast
                  ring
                · have hsub : c + 1 - c = 1 := by omega
                  rw [hsub]
                  push_cast
                  ring
        _ = (∑ i ∈ Finset.range c,
              (((q : ℚ) - 1) * ((c - i : ℕ) : ℚ) - 1) * (q : ℚ) ^ i) +
              ((q : ℚ) - 1) * (∑ i ∈ Finset.range c, (q : ℚ) ^ i) +
              ((q : ℚ) - 2) * (q : ℚ) ^ c := by
                rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ = (q : ℚ) ^ (c + 1) - ((c + 1) + 1 : ℕ) := by
              rw [ih, mul_geom_sum]
              push_cast
              rw [pow_succ]
              ring
  have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
  let c := s.max' hsne
  have hc_mem : c ∈ s := by
    exact Finset.max'_mem s hsne
  have hc_one : 1 ≤ c := h1 c hc_mem
  have hlt_of_mem_erase {i : ℕ} (hi : i ∈ s.erase c) : i < c := by
    have hi' := Finset.mem_erase.mp hi
    exact lt_of_le_of_ne (Finset.le_max' s i hi'.2) hi'.1
  have herase_nonempty : (s.erase c).Nonempty := by
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
    by_cases hac : a = c
    · refine ⟨b, Finset.mem_erase.mpr ⟨?_, hb⟩⟩
      intro hbc
      exact hab (hac.trans hbc.symm)
    · exact ⟨a, Finset.mem_erase.mpr ⟨hac, ha⟩⟩
  have hq_rat : (2 : ℚ) ≤ q := by exact_mod_cast hq
  have h_adjusted_nonneg {i : ℕ} (hi : i < c) :
      0 ≤ (((q : ℚ) - 1) * ((c - i : ℕ) : ℚ) - 1) * (q : ℚ) ^ i := by
    have hci : (1 : ℚ) ≤ (c - i : ℕ) := by
      exact_mod_cast (by omega : 1 ≤ c - i)
    have hcoeff : (0 : ℚ) ≤ ((q : ℚ) - 1) * (c - i : ℕ) - 1 := by
      nlinarith
    exact mul_nonneg hcoeff (by positivity)
  have h_adjusted_le :
      (∑ i ∈ s.erase c,
          (((q : ℚ) - 1) * ((c - i : ℕ) : ℚ) - 1) * (q : ℚ) ^ i) ≤
        ∑ i ∈ Finset.range c,
          (((q : ℚ) - 1) * ((c - i : ℕ) : ℚ) - 1) * (q : ℚ) ^ i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      exact Finset.mem_range.mpr (hlt_of_mem_erase hi)
    · intro i hi _
      exact h_adjusted_nonneg (Finset.mem_range.mp hi)
  have h_adjusted_lt :
      (∑ i ∈ s.erase c,
          (((q : ℚ) - 1) * ((c - i : ℕ) : ℚ) - 1) * (q : ℚ) ^ i) <
        (q : ℚ) ^ c := by
    rw [tail_sum_identity c] at h_adjusted_le
    have hc_pos : (0 : ℚ) < (c + 1 : ℕ) := by
      exact_mod_cast (by omega : 0 < c + 1)
    linarith
  have hgap_pos :
      0 < ((q : ℚ) - 1) *
        (∑ i ∈ s, ((c - i : ℕ) : ℚ) * (q : ℚ) ^ i) := by
    have hsum_pos :
        0 < ∑ i ∈ s.erase c, ((c - i : ℕ) : ℚ) * (q : ℚ) ^ i := by
      apply Finset.sum_pos
      · intro i hi
        have hi' := hlt_of_mem_erase hi
        have : (0 : ℚ) < (c - i : ℕ) := by
          exact_mod_cast (by omega : 0 < c - i)
        positivity
      · exact herase_nonempty
    have hsum_eq :
        (∑ i ∈ s.erase c, ((c - i : ℕ) : ℚ) * (q : ℚ) ^ i) =
          ∑ i ∈ s, ((c - i : ℕ) : ℚ) * (q : ℚ) ^ i := by
      apply Finset.sum_erase
      simp
    rw [hsum_eq] at hsum_pos
    exact mul_pos (by linarith) hsum_pos
  have hgap_lt_den :
      ((q : ℚ) - 1) *
          (∑ i ∈ s, ((c - i : ℕ) : ℚ) * (q : ℚ) ^ i) <
        ∑ i ∈ s, (q : ℚ) ^ i := by
    have hgap_eq :
        ((q : ℚ) - 1) *
            (∑ i ∈ s, ((c - i : ℕ) : ℚ) * (q : ℚ) ^ i) =
          (∑ i ∈ s.erase c,
            (((q : ℚ) - 1) * ((c - i : ℕ) : ℚ) - 1) * (q : ℚ) ^ i) +
          (∑ i ∈ s.erase c, (q : ℚ) ^ i) := by
      rw [Finset.mul_sum]
      calc
        (∑ i ∈ s,
            ((q : ℚ) - 1) * (((c - i : ℕ) : ℚ) * (q : ℚ) ^ i)) =
            ∑ i ∈ s.erase c,
              ((q : ℚ) - 1) * (((c - i : ℕ) : ℚ) * (q : ℚ) ^ i) := by
                rw [Finset.sum_erase]
                simp
        _ = _ := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring
    have hden_eq :
        (∑ i ∈ s, (q : ℚ) ^ i) =
          (q : ℚ) ^ c + ∑ i ∈ s.erase c, (q : ℚ) ^ i := by
      rw [← Finset.sum_erase_add _ _ hc_mem]
      ring
    rw [hgap_eq, hden_eq]
    linarith
  have hden_pos : (0 : ℚ) < ∑ i ∈ s, (q : ℚ) ^ i := by
    apply Finset.sum_pos
    · intro i _
      positivity
    · exact hsne
  have hcentered :
      (c : ℚ) * (∑ i ∈ s, (q : ℚ) ^ i) -
          (∑ i ∈ s, (i : ℚ) * (q : ℚ) ^ i) =
        ∑ i ∈ s, ((c - i : ℕ) : ℚ) * (q : ℚ) ^ i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hic : i ≤ c := Finset.le_max' s i hi
    rw [Nat.cast_sub hic]
    ring
  have hrecenter :
      ((q : ℚ) - 1) * (∑ i ∈ s, (i : ℚ) * (q : ℚ) ^ i) /
          (∑ i ∈ s, (q : ℚ) ^ i) =
        (c : ℚ) * ((q : ℚ) - 1) -
          (((q : ℚ) - 1) *
            (∑ i ∈ s, ((c - i : ℕ) : ℚ) * (q : ℚ) ^ i)) /
            (∑ i ∈ s, (q : ℚ) ^ i) := by
    field_simp [ne_of_gt hden_pos]
    rw [← hcentered]
    ring
  have hdelta_pos :
      0 < (((q : ℚ) - 1) *
          (∑ i ∈ s, ((c - i : ℕ) : ℚ) * (q : ℚ) ^ i)) /
        (∑ i ∈ s, (q : ℚ) ^ i) :=
    div_pos hgap_pos hden_pos
  have hdelta_lt_one :
      (((q : ℚ) - 1) *
          (∑ i ∈ s, ((c - i : ℕ) : ℚ) * (q : ℚ) ^ i)) /
          (∑ i ∈ s, (q : ℚ) ^ i) < 1 :=
    (div_lt_one hden_pos).mpr hgap_lt_den
  change
    ⌊((q : ℚ) - 1) * (∑ i ∈ s, (i : ℚ) * (q : ℚ) ^ i) /
        (∑ i ∈ s, (q : ℚ) ^ i)⌋ =
      (c : ℤ) * ((q : ℤ) - 1) - 1
  apply Int.floor_eq_iff.mpr
  constructor
  · push_cast
    rw [hrecenter]
    linarith
  · push_cast
    rw [hrecenter]
    linarith

#print axioms simic_h655_ii

end D5.S3.ArithSums.SimicWeightedPowerSumFloorIdentity
