/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/FifthExponents
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/PrimePower/FifthExponents
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A common finite Chebyshev exponent sum for the square, cube and fifth cutoffs. -/

import Mathlib.NumberTheory.Chebyshev

/-! A common finite exponent support for the square, cube and fifth root cutoffs. -/

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

end D5.S3.Weil.Mertens.IntegratedExplicit.PrimePowerFifthCutoff
