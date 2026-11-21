/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePowerFifthCutoff
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePowerFifthCutoff
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Chebyshev square, cube and fifth-root subtraction leaves a signed sixth-root correction. -/

import Mathlib.NumberTheory.Chebyshev

/-! Finite prime-power cancellation at a real cutoff. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Chebyshev Finset Real

namespace D5.S3.Weil.Mertens.IntegratedExplicit.PrimePowerFifthCutoff

private theorem psi_root_eq_sum_multiples {t : ℝ} (ht : 1 ≤ t) {d N : ℕ} (hd : 2 ≤ d)
    (hN : ⌊log t / log 2⌋₊ ≤ N) :
    psi (t ^ (1 / (d : ℝ))) =
      ∑ k ∈ (Icc 2 N).filter (fun k => d ∣ k), theta (t ^ (1 / (k : ℝ))) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hd0 : 0 < d := by omega
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd0
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  have hroot : 1 ≤ t ^ (1 / (d : ℝ)) := one_le_rpow ht (by positivity)
  have hfloor : ⌊log (t ^ (1 / (d : ℝ))) / log 2⌋₊ ≤ N / d := by
    apply (Nat.le_div_iff_mul_le hd0).2
    refine le_trans (Nat.le_floor ?_) hN
    rw [Nat.cast_mul]
    calc
      _ ≤ (log (t ^ (1 / (d : ℝ))) / log 2) * (d : ℝ) :=
        mul_le_mul_of_nonneg_right
          (Nat.floor_le (div_nonneg (log_nonneg hroot) hlog2.le)) hdR.le
      _ = log t / log 2 := by
        rw [log_rpow ht0]
        field_simp
  rw [psi_eq_sum_theta' (zero_le_one.trans hroot) hfloor]
  refine sum_bij (fun k _ => d * k) ?_ ?_ ?_ ?_
  · intro k hk
    obtain ⟨hk1, hkN⟩ := mem_Icc.mp hk
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right d k⟩
    · exact hd.trans (Nat.le_mul_of_pos_right d (by omega))
    · simpa only [Nat.mul_comm d k] using (Nat.le_div_iff_mul_le hd0).1 hkN
  · intro k _ l _ h
    exact Nat.mul_left_cancel hd0 h
  · intro k hk
    obtain ⟨hk', l, rfl⟩ := mem_filter.mp hk
    obtain ⟨hk2, hkN⟩ := mem_Icc.mp hk'
    refine ⟨l, mem_Icc.mpr ⟨?_, (Nat.le_div_iff_mul_le hd0).2 ?_⟩, rfl⟩
    · by_contra! hl
      have : l = 0 := by omega
      simp [this] at hk2
    · simpa only [Nat.mul_comm l d] using hkN
  · intro k hk
    have hkR : 0 < (k : ℝ) := by exact_mod_cast (mem_Icc.mp hk).1
    rw [← rpow_mul ht0.le, Nat.cast_mul]
    congr 2
    field_simp

def coefficient (k : ℕ) : ℝ :=
  1 - (if 2 ∣ k then 1 else 0) - (if 3 ∣ k then 1 else 0) - (if 5 ∣ k then 1 else 0)

/-- The square, cube and fifth-root cutoffs combine on one finite exponent support. -/
theorem psi_sub_roots_eq_sum {t : ℝ} (ht : 2 ≤ t) {N : ℕ}
    (hN : ⌊log t / log 2⌋₊ ≤ N) :
    psi t - theta t - psi (t ^ (1 / 2 : ℝ)) - psi (t ^ (1 / 3 : ℝ)) -
      psi (t ^ (1 / 5 : ℝ)) =
      ∑ k ∈ Icc 6 N, coefficient k * theta (t ^ (1 / (k : ℝ))) := by
  have ht1 : 1 ≤ t := by linarith
  let f : ℕ → ℝ := fun k => coefficient k * theta (t ^ (1 / (k : ℝ)))
  have hskip : ∑ k ∈ Icc 6 N, f k = ∑ k ∈ Icc 2 N, f k := by
    apply sum_subset
    · intro k hk
      simp only [mem_Icc] at hk ⊢
      omega
    · intro k hk hk'
      simp only [mem_Icc] at hk hk'
      have hk2 := hk.1
      have hk6 : k < 6 := by omega
      interval_cases k <;> norm_num [f, coefficient]
  rw [hskip]
  rw [psi_eq_theta_add_sum_theta' ht hN, add_sub_cancel_left]
  rw [show psi (t ^ (1 / 2 : ℝ)) = _ from
      psi_root_eq_sum_multiples ht1 (d := 2) (by decide) hN,
    show psi (t ^ (1 / 3 : ℝ)) = _ from
      psi_root_eq_sum_multiples ht1 (d := 3) (by decide) hN,
    show psi (t ^ (1 / 5 : ℝ)) = _ from
      psi_root_eq_sum_multiples ht1 (d := 5) (by decide) hN]
  simp only [sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl
  intro k _
  by_cases h2 : 2 ∣ k <;> by_cases h3 : 3 ∣ k <;> by_cases h5 : 5 ∣ k <;>
    simp [f, coefficient, h2, h3, h5] <;> ring

/-- After adding back the sixth-root term, only exponents at least seven contribute. -/
theorem abs_psi_sub_roots_add_theta_sixth_le {t : ℝ} (ht : 2 ≤ t) :
    |psi t - theta t - psi (t ^ (1 / 2 : ℝ)) - psi (t ^ (1 / 3 : ℝ)) -
      psi (t ^ (1 / 5 : ℝ)) + theta (t ^ (1 / 6 : ℝ))| ≤
      4 * log t * t ^ (1 / 7 : ℝ) := by
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 ≤ t := zero_le_one.trans ht1
  have hlog2 : 0 < log 2 := log_pos (by norm_num)
  let M : ℕ := ⌊log t / log 2⌋₊
  let N : ℕ := max M 6
  let f : ℕ → ℝ := fun k => coefficient k * theta (t ^ (1 / (k : ℝ)))
  have hN : M ≤ N := le_max_left _ _
  have hN6 : 6 ≤ N := le_max_right _ _
  have hsum : _ = ∑ k ∈ Icc 6 N, f k := psi_sub_roots_eq_sum ht hN
  have hsplit : Icc 6 N = insert 6 (Icc 7 N) := by
    ext k
    simp only [mem_Icc, mem_insert]
    omega
  have hsix : f 6 = -theta (t ^ (1 / 6 : ℝ)) := by norm_num [f, coefficient]
  rw [hsum, hsplit, sum_insert (by simp), hsix]
  rw [neg_add_eq_sub, sub_add_cancel]
  have hcard : (Icc 7 N).card ≤ M := by
    rw [Nat.card_Icc]
    change max M 6 + 1 - 7 ≤ M
    omega
  have hlog4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    ring
  calc
    _ ≤ ∑ k ∈ Icc 7 N, |f k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Icc 7 N, 2 * (log 4 * t ^ (1 / 7 : ℝ)) := by
      apply sum_le_sum
      intro k hk
      have hk7 : (7 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
      have hc : |coefficient k| ≤ 2 := by
        unfold coefficient
        split_ifs <;> norm_num
      have htheta := theta_le_log4_mul_x (rpow_nonneg ht0 (1 / (k : ℝ)))
      rw [show f k = coefficient k * theta (t ^ (1 / (k : ℝ))) from rfl,
        abs_mul, abs_of_nonneg (theta_nonneg _)]
      refine mul_le_mul hc (htheta.trans ?_) (theta_nonneg _) (by norm_num)
      exact mul_le_mul_of_nonneg_left
        (rpow_le_rpow_of_exponent_le ht1 (one_div_le_one_div_of_le (by norm_num) hk7))
        (log_nonneg (by norm_num))
    _ = ((Icc 7 N).card : ℝ) * (2 * (log 4 * t ^ (1 / 7 : ℝ))) := by simp
    _ ≤ (log t / log 2) * (2 * (log 4 * t ^ (1 / 7 : ℝ))) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (show ((Icc 7 N).card : ℝ) ≤ M by exact_mod_cast hcard).trans
        (Nat.floor_le (div_nonneg (log_nonneg ht1) hlog2.le))
    _ = _ := by
      rw [hlog4]
      field_simp
      ring

/-- The square, cube and fifth-root subtractions leave a uniform sixth-root error. -/
theorem exists_abs_psi_sub_roots_le :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t →
      |psi t - theta t - psi (t ^ (1 / 2 : ℝ)) - psi (t ^ (1 / 3 : ℝ)) -
        psi (t ^ (1 / 5 : ℝ))| ≤ C * t ^ (1 / 6 : ℝ) := by
  refine ⟨log 4 + 168, by positivity, fun t ht => ?_⟩
  have ht0 : 0 ≤ t := by linarith
  have hlog := log_le_rpow_div (ε := 1 / 42) ht0 (by norm_num)
  have htail : 4 * log t * t ^ (1 / 7 : ℝ) ≤ 168 * t ^ (1 / 6 : ℝ) := by
    calc
      _ ≤ 4 * (t ^ (1 / 42 : ℝ) / (1 / 42)) * t ^ (1 / 7 : ℝ) := by
        gcongr
      _ = _ := by
        calc
          _ = 168 * (t ^ (1 / 42 : ℝ) * t ^ (1 / 7 : ℝ)) := by ring
          _ = _ := by
            rw [← rpow_add' ht0 (by norm_num),
              show (1 / 42 + 1 / 7 : ℝ) = 1 / 6 by norm_num]
  let R := psi t - theta t - psi (t ^ (1 / 2 : ℝ)) - psi (t ^ (1 / 3 : ℝ)) -
    psi (t ^ (1 / 5 : ℝ))
  let T := theta (t ^ (1 / 6 : ℝ))
  change |R| ≤ _
  calc
    |R| = |(R + T) - T| := by rw [add_sub_cancel_right]
    _ ≤ |R + T| + |T| := abs_sub _ _
    _ ≤ 168 * t ^ (1 / 6 : ℝ) + log 4 * t ^ (1 / 6 : ℝ) := by
      apply add_le_add ((abs_psi_sub_roots_add_theta_sixth_le ht).trans htail)
      exact (abs_of_nonneg (theta_nonneg _)).trans_le (theta_le_log4_mul_x (rpow_nonneg ht0 _))
    _ = _ := by ring

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePowerFifthCutoff
