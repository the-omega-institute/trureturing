/- GID: D5/S3/Arith/Robin/Analytic/OmegaTail/RankinUpper
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTail/RankinUpper
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none -/

import D5.S3.Arith.Robin.Analytic.OmegaTail.FarDeletion
import D5.S3.Arith.Robin.PriceRecord.MovingPrimeSoftplus

/-! The sharp Rankin upper bound at the second distinct-prime threshold. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Finset Real
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.OmegaTail.RankinUpper

open OmegaTailUpper (tailCount threshold scale rankin_exponential_bound)
open FarDeletion (centeredThreshold continuousReserve centered_reserve)
open D5.S3.Arith.Robin.PriceRecord.MovingPrimeSoftplus (weight prime_softplus_asymptotic)
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel (primeCount)

private lemma prime_log_split {P s t : ℝ} (hP : 0 < P) (hs : 0 ≤ s) (ht : 0 < t) :
    log (1 + P ^ s * t ^ (-s)) =
      (if t ≤ P then s * (log P - log t) else 0) + weight P s t := by
  have harg : P ^ s * t ^ (-s) = exp (s * (log P - log t)) := by
    rw [rpow_def_of_pos hP, rpow_def_of_pos ht, ← exp_add]
    congr 1
    ring
  rw [harg, weight, log_div ht.ne' hP.ne']
  by_cases h : t ≤ P
  · rw [if_pos h, abs_of_nonpos (sub_nonpos.mpr (log_le_log ht h))]
    have he :
        1 + exp (s * (log P - log t)) =
          exp (s * (log P - log t)) * (1 + exp (-s * -(log t - log P))) := by
      rw [mul_add, mul_one, ← exp_add]
      ring_nf
      simp [add_comm]
    rw [he, log_mul (exp_pos _).ne' (by positivity), log_exp]
  · have hlog := log_le_log hP (le_of_lt (lt_of_not_ge h))
    rw [if_neg h, zero_add, abs_of_nonneg (sub_nonneg.mpr hlog)]
    congr 3
    ring

private lemma rankin_prime_cancellation {P s : ℝ} (hP : 1 < P) (hs : 0 ≤ s)
    (hR : Summable (fun p : ℕ => if p.Prime then weight P s p else 0)) :
    s * P - threshold 1 (exp P) * log (P ^ s) +
        ∑ p ∈ Icc 1 ⌊exp P⌋₊ with p.Prime, log (1 + P ^ s * (p : ℝ) ^ (-s)) ≤
      s * continuousReserve P + ∑' p : ℕ, if p.Prime then weight P s p else 0 := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  let cutoff := Nat.primesLE ⌊exp P⌋₊
  have hsub : Nat.primesLE ⌊P⌋₊ ⊆ cutoff := by
    intro p hp
    rw [Nat.mem_primesLE] at hp ⊢
    have hPe : P ≤ exp P := by linarith [add_one_le_exp P]
    exact ⟨hp.1.trans (Nat.floor_mono hPe), hp.2⟩
  have hmem {p : ℕ} (hp : p ∈ cutoff) :
      p ∈ Nat.primesLE ⌊P⌋₊ ↔ (p : ℝ) ≤ P := by
    rw [Nat.mem_primesLE, Nat.le_floor_iff hP0.le, and_iff_left (Nat.prime_of_mem_primesLE hp)]
  have hhead :
      (∑ p ∈ cutoff, if (p : ℝ) ≤ P then s * (log P - log p) else 0) =
        s * (primeCount P * log P - Chebyshev.theta P) := by
    calc
      _ = ∑ p ∈ Nat.primesLE ⌊P⌋₊, s * (log P - log p) := by
        symm
        calc
          _ = ∑ p ∈ Nat.primesLE ⌊P⌋₊, if (p : ℝ) ≤ P then s * (log P - log p) else 0 := by
            apply sum_congr rfl
            intro p hp
            rw [if_pos ((hmem (hsub hp)).mp hp)]
          _ = _ := sum_subset hsub (fun p hp hnp => if_neg (fun h => hnp ((hmem hp).mpr h)))
      _ = _ := by
        rw [← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul,
          Nat.primesLE_card_eq_primeCounting, Chebyshev.theta_eq_sum_primesLE, primeCount]
  have htotal : ∑ p ∈ cutoff, weight P s p ≤
      ∑' p : ℕ, if p.Prime then weight P s p else 0 := by
    calc
      _ = ∑ p ∈ cutoff, if p.Prime then weight P s p else 0 := by
        apply sum_congr rfl
        intro p hp
        rw [if_pos (Nat.prime_of_mem_primesLE hp)]
      _ ≤ _ := hR.sum_le_tsum cutoff (fun p _ => by
        split_ifs
        · exact log_nonneg (by unfold weight at *; linarith [exp_pos (-s * |log ((p : ℝ) / P)|)])
        · exact le_rfl)
  rw [← Nat.primesLE_eq_filter_Icc_one]
  change s * P - threshold 1 (exp P) * log (P ^ s) +
    (∑ p ∈ cutoff, log (1 + P ^ s * (p : ℝ) ^ (-s))) ≤ _
  have hsplit :
      (∑ p ∈ cutoff, log (1 + P ^ s * (p : ℝ) ^ (-s))) =
        (∑ p ∈ cutoff, if (p : ℝ) ≤ P then s * (log P - log p) else 0) +
          ∑ p ∈ cutoff, weight P s p := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun p hp =>
      prime_log_split hP0 hs (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos))
  have hthreshold : threshold 1 (exp P) = centeredThreshold P := by
    simp only [threshold, scale, log_exp, one_mul, centeredThreshold, div_div, pow_two]
  rw [hsplit, hhead, log_rpow hP0, hthreshold, continuousReserve]
  linarith only [htotal, show s * P - centeredThreshold P * (s * log P) +
      s * (primeCount P * log P - Chebyshev.theta P) =
      s * (P - Chebyshev.theta P + (primeCount P - centeredThreshold P) * log P) by ring]

private lemma rankin_correction {s : ℝ} (hs : 2 ≤ s) :
    0 ≤ log (1 + ∑' n : ℕ, (n : ℝ) ^ (-s)) ∧
      log (1 + ∑' n : ℕ, (n : ℝ) ^ (-s)) ≤
        log (1 + ∑' n : ℕ, (n : ℝ) ^ (-(2 : ℝ))) := by
  have hn (n : ℕ) : 0 ≤ (n : ℝ) ^ (-s) := rpow_nonneg (Nat.cast_nonneg n) _
  refine ⟨log_nonneg (by linarith [tsum_nonneg hn]), log_le_log (by linarith [tsum_nonneg hn]) ?_⟩
  apply add_le_add_left
  have hsum (t : ℝ) (ht : 2 ≤ t) : Summable (fun n : ℕ => (n : ℝ) ^ (-t)) :=
    summable_nat_rpow.mpr (by linarith)
  refine (hsum s hs).tsum_le_tsum (fun n => ?_) (hsum 2 le_rfl)
  cases n with
  | zero =>
    simp [zero_rpow (show -s ≠ 0 by linarith), zero_rpow (by norm_num : -(2 : ℝ) ≠ 0)]
  | succ n =>
    exact rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_pos n) (by linarith)

private lemma optimizer_constant :
    2 * (π / (2 * sqrt 3)) + (π ^ 2 / 6) / (π / (2 * sqrt 3)) = 2 * π / sqrt 3 := by
  have hs : 0 < sqrt (3 : ℝ) := sqrt_pos.2 (by norm_num)
  have hs2 := sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
  field_simp [pi_ne_zero, hs.ne']
  linear_combination -2 * π ^ 2 * hs2

/-- Sharp upper bound at the second threshold for every positive error and all large real cutoffs. -/
theorem sharp_upper_bound (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ P : ℝ in atTop,
      (tailCount 1 (exp P) : ℝ) ≤ exp ((2 * π / sqrt 3 + epsilon) *
        (P / log P ^ (3 / 2 : ℝ))) := by
  let c : ℝ := π / (2 * sqrt 3)
  let s (P : ℝ) := c * log P ^ (1 / 2 : ℝ)
  let Z (P : ℝ) := P / log P ^ (3 / 2 : ℝ)
  let R (P : ℝ) := ∑' p : ℕ, if p.Prime then weight P (s P) p else 0
  let C (P : ℝ) := log (1 + ∑' n : ℕ, (n : ℝ) ^ (-s P))
  have hc : 0 < c := by dsimp [c]; positivity
  have hs : Tendsto s atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc).mpr
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_log_atTop)
  have hsoft := prime_softplus_asymptotic (by norm_num : (0 : ℝ) < 1 / 2) hc hc.le s
    (Eventually.of_forall (fun _ => ⟨le_rfl, le_rfl⟩))
  have hZ : Tendsto Z atTop atTop := by
    have h := (isLittleO_log_rpow_rpow_atTop (3 / 2 : ℝ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
    rw [show (fun x : ℝ => x ^ (1 : ℝ)) = id from funext rpow_one] at h
    have hpos : ∀ᶠ P : ℝ in atTop, 0 < log P ^ (3 / 2 : ℝ) / P := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
      exact div_pos (rpow_pos_of_pos (log_pos hP) _) (zero_lt_one.trans hP)
    simpa only [Z, Function.comp_def, inv_div, id_eq] using
      tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨h, hpos⟩)
  have hscale₁ {P : ℝ} (hP : 1 < P) :
      log P ^ (3 / 2 : ℝ) * log P ^ (1 / 2 : ℝ) = log P ^ (2 : ℕ) := by
    rw [← rpow_add (log_pos hP), show (3 / 2 : ℝ) + 1 / 2 = (2 : ℕ) by norm_num, rpow_natCast]
  have hscale₂ {P : ℝ} (hP : 1 < P) :
      log P ^ (1 / 2 : ℝ) * log P = log P ^ (3 / 2 : ℝ) := by
    conv_lhs => rw [← rpow_one (log P)] at *
    rw [← rpow_add (log_pos hP)]
    norm_num
  have hreserve : Tendsto (fun P => s P * continuousReserve P / Z P) atTop (𝓝 (2 * c)) := by
    have h := centered_reserve.2.2.2.1.mul_const c
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    dsimp [s, Z]
    rw [div_div_eq_mul_div, div_div_eq_mul_div, ← hscale₁ hP]
    ring
  have hR : Tendsto (fun P => R P / Z P) atTop (𝓝 ((π ^ 2 / 6) / c)) := by
    apply (hsoft.2.div_const c).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    change R P / (P / (s P * log P)) / c = R P / Z P
    dsimp only [s, Z]
    rw [mul_assoc, hscale₂ hP, div_div_eq_mul_div, div_div_eq_mul_div, mul_left_comm,
      mul_div_mul_left _ _ hc.ne']
  have hC : Tendsto (fun P => C P / Z P) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (hZ.const_div_atTop (log (1 + ∑' n : ℕ, (n : ℝ) ^ (-(2 : ℝ)))))
    · filter_upwards [hs.eventually_ge_atTop 2, eventually_gt_atTop (1 : ℝ)] with P hsP hP
      exact div_nonneg (rankin_correction hsP).1 (by
        exact div_nonneg (zero_lt_one.trans hP).le (rpow_nonneg (log_pos hP).le _))
    · filter_upwards [hs.eventually_ge_atTop 2, eventually_gt_atTop (1 : ℝ)] with P hsP hP
      exact div_le_div_of_nonneg_right (rankin_correction hsP).2 (by
        exact div_nonneg (zero_lt_one.trans hP).le (rpow_nonneg (log_pos hP).le _))
  have hlim := (hreserve.add hR).add hC
  rw [add_zero, show 2 * c + (π ^ 2 / 6) / c = 2 * π / sqrt 3 from optimizer_constant] at hlim
  filter_upwards [hlim.eventually_lt_const (lt_add_of_pos_right _ hepsilon),
    hs.eventually_ge_atTop 2, hsoft.1, eventually_gt_atTop (1 : ℝ)] with P hlim hsP hRsum hP
  have hZP : 0 < Z P := div_pos (zero_lt_one.trans hP) (rpow_pos_of_pos (log_pos hP) _)
  have hs1 : 1 < s P := (by norm_num : (1 : ℝ) < 2).trans_le hsP
  have hz : 1 ≤ P ^ s P := one_le_rpow hP.le (zero_lt_one.trans hs1).le
  refine (rankin_exponential_bound (T := threshold 1 (exp P)) hs1 hz (exp_pos P)).trans ?_
  apply exp_le_exp.mpr
  rw [log_exp]
  have hcancel := rankin_prime_cancellation hP (zero_lt_one.trans hs1).le hRsum.of_abs
  have hnormalized : (s P * continuousReserve P + R P + C P) / Z P <
      2 * π / sqrt 3 + epsilon := by
    simpa only [add_div] using hlim
  exact (by linarith only [hcancel] : _ ≤ s P * continuousReserve P + R P + C P).trans
    ((div_lt_iff₀ hZP).mp hnormalized).le

end D5.S3.Arith.Robin.Analytic.OmegaTail.RankinUpper
