/- GID: D5/S3/Combinatorics/Graph/MultipartiteCHS/Extremal
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MultipartiteCHS/Extremal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coefficient comparison and strict extremal partitions for multipartite reciprocal sequences. -/

import D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence

open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.MultipartiteCHS.Extremal

open D5.S3.Combinatorics.Graph.MultipartiteCHS.Defs
open D5.S3.Combinatorics.Graph.MultipartiteCHS.Recurrence

/-- Elementary coefficient domination propagates through the reciprocal recurrence. -/
theorem recH_mono {r : ℕ} (a b : Fin r → ℕ)
    (hab : ∀ j, 2 ≤ j → esymmParts a j ≤ esymmParts b j) :
    ∀ d, recH a d ≤ recH b d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
      by_cases hd : d = 0
      · simp [hd, recH_zero]
      rw [recH_eq a (by omega), recH_eq b (by omega)]
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hj, hjd⟩ := Finset.mem_Icc.mp hj
      have hc : 0 ≤ (j : ℝ) - 1 := by
        have : (2 : ℝ) ≤ j := by exact_mod_cast hj
        linarith
      have he : (esymmParts a j : ℝ) ≤ esymmParts b j := by
        exact_mod_cast hab j hj
      exact mul_le_mul (mul_le_mul_of_nonneg_left he hc)
        (ih (d - j) (by omega)) (recH_nonneg a _) (by positivity)

/-- A strict increase of the quadratic elementary coefficient is detected at every
positive even degree, provided the smaller partition has positive parts. -/
theorem recH_even_strict_mono {r : ℕ} (hr : 2 ≤ r) (a b : Fin r → ℕ)
    (ha : ∀ i, 0 < a i)
    (hab : ∀ j, 2 ≤ j → esymmParts a j ≤ esymmParts b j)
    (h2 : esymmParts a 2 < esymmParts b 2) {m : ℕ} (hm : 1 ≤ m) :
    recH a (2 * m) < recH b (2 * m) := by
  rw [recH_eq a (by omega), recH_eq b (by omega)]
  apply Finset.sum_lt_sum
  · intro j hj
    obtain ⟨hj, hjd⟩ := Finset.mem_Icc.mp hj
    have hc : 0 ≤ (j : ℝ) - 1 := by
      have : (2 : ℝ) ≤ j := by exact_mod_cast hj
      linarith
    have he : (esymmParts a j : ℝ) ≤ esymmParts b j := by
      exact_mod_cast hab j hj
    exact mul_le_mul (mul_le_mul_of_nonneg_left he hc)
      (recH_mono a b hab _) (recH_nonneg a _) (by positivity)
  · refine ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩, ?_⟩
    have hp : 0 < recH a (2 * m - 2) := by
      by_cases h : m = 1
      · simp [h, recH_zero]
      · have he : 2 * m - 2 = 2 * (m - 1) := by omega
        rw [he]
        exact recH_two_mul_pos hr a ha (by omega)
    have he : (esymmParts a 2 : ℝ) < esymmParts b 2 := by exact_mod_cast h2
    norm_num only [Nat.cast_ofNat, sub_self, add_sub_cancel_left, mul_one, one_mul]
    calc
      (esymmParts a 2 : ℝ) * recH a (2 * m - 2) <
          (esymmParts b 2 : ℝ) * recH a (2 * m - 2) :=
        mul_lt_mul_of_pos_right he hp
      _ ≤ (esymmParts b 2 : ℝ) * recH b (2 * m - 2) :=
        mul_le_mul_of_nonneg_left (recH_mono a b hab _) (by positivity)

end D5.S3.Combinatorics.Graph.MultipartiteCHS.Extremal
