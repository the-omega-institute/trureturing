/- GID: D5/S3/Arith/Robin/Analytic/OmegaTail/RankinUpper
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTail/RankinUpper
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp Rankin upper bounds for distinct-prime tails from continuous reserves. -/

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

private lemma prime_log_split {P s t : ℝ} (hP : 0 < P) (ht : 0 < t) :
    log (1 + P ^ s * t ^ (-s)) =
      (if t ≤ P then s * (log P - log t) else 0) + weight P s t := by
  have harg : P ^ s * t ^ (-s) = exp (s * (log P - log t)) := by
    rw [rpow_def_of_pos hP, rpow_def_of_pos ht, ← exp_add]
    congr 1
    ring
  rw [harg, weight, log_div ht.ne' hP.ne']
  by_cases h : t ≤ P
  · rw [ite_eq_left h, abs_of_nonpos (sub_nonpos.mpr (log_le_log ht h))]
    have he :
        1 + exp (s * (log P - log t)) =
          exp (s * (log P - log t)) * (1 + exp (-s * -(log t - log P))) := by
      rw [mul_add, mul_one, ← exp_add]
      ring_nf
      simp [add_comm]
    rw [he, log_mul (exp_pos _).ne' (by positivity), log_exp]
  · have hlog := log_le_log hP (le_of_lt (lt_of_not_ge h))
    rw [ite_eq_right h, zero_add, abs_of_nonneg (sub_nonneg.mpr hlog)]
    congr 3
    ring

private lemma rankin_prime_cancellation {P s : ℝ} (T : ℝ) (hP : 1 < P)
    (hR : Summable (fun p : ℕ => if p.Prime then weight P s p else 0)) :
    s * P - T * log (P ^ s) +
        ∑ p ∈ Icc 1 ⌊exp P⌋₊ with p.Prime, log (1 + P ^ s * (p : ℝ) ^ (-s)) ≤
      s * (P - Chebyshev.theta P + (primeCount P - T) * log P) +
        ∑' p : ℕ, if p.Prime then weight P s p else 0 := by
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
            rw [ite_eq_left ((hmem (hsub hp)).mp hp)]
          _ = _ := sum_subset hsub (fun p hp hnp => ite_eq_right (fun h => hnp ((hmem hp).mpr h)))
      _ = _ := by
        rw [← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul,
          Nat.primesLE_card_eq_primeCounting, Chebyshev.theta_eq_sum_primesLE, primeCount]
  have htotal : ∑ p ∈ cutoff, weight P s p ≤
      ∑' p : ℕ, if p.Prime then weight P s p else 0 := by
    calc
      _ = ∑ p ∈ cutoff, if p.Prime then weight P s p else 0 := by
        apply sum_congr rfl
        intro p hp
        rw [ite_eq_left (Nat.prime_of_mem_primesLE hp)]
      _ ≤ _ := hR.sum_le_tsum cutoff (fun p _ => by
        split_ifs
        · exact log_nonneg (by unfold weight at *; linarith [exp_pos (-s * |log ((p : ℝ) / P)|)])
        · exact le_rfl)
  rw [← Nat.primesLE_eq_filter_Icc_one]
  change s * P - T * log (P ^ s) +
    (∑ p ∈ cutoff, log (1 + P ^ s * (p : ℝ) ^ (-s))) ≤ _
  have hsplit :
      (∑ p ∈ cutoff, log (1 + P ^ s * (p : ℝ) ^ (-s))) =
        (∑ p ∈ cutoff, if (p : ℝ) ≤ P then s * (log P - log p) else 0) +
          ∑ p ∈ cutoff, weight P s p := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun p hp =>
      prime_log_split hP0 (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).pos))
  rw [hsplit, hhead, log_rpow hP0]
  linarith only [htotal, show s * P - T * (s * log P) +
      s * (primeCount P * log P - Chebyshev.theta P) =
      s * (P - Chebyshev.theta P + (primeCount P - T) * log P) by ring]

private lemma rankin_correction {s : ℝ} (hs : 2 ≤ s) :
    0 ≤ log (1 + ∑' n : ℕ, (n : ℝ) ^ (-s)) ∧
      log (1 + ∑' n : ℕ, (n : ℝ) ^ (-s)) ≤
        log (1 + ∑' n : ℕ, (n : ℝ) ^ (-(2 : ℝ))) := by
  have hn (n : ℕ) : 0 ≤ (n : ℝ) ^ (-s) := rpow_nonneg (Nat.cast_nonneg n) _
  have hnonneg : 0 ≤ ∑' n : ℕ, (n : ℝ) ^ (-s) := tsum_nonneg hn
  refine ⟨log_nonneg (by linarith), log_le_log (by linarith) ?_⟩
  apply add_le_add_right
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
  ring_nf
  rw [hs2]
  ring

private lemma sharp_upper_bound_of_reserve (T : ℝ → ℝ) {a b c : ℝ}
    (ha : 0 < a) (hc : 0 < c)
    (hB : Tendsto (fun P : ℝ =>
      (P - Chebyshev.theta P + (primeCount P - T P) * log P) /
        (P / log P ^ (a + 1 + a))) atTop (𝓝 b))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ P : ℝ in atTop,
      (((Icc 1 ⌊exp P⌋₊).filter (fun n =>
        T P < (ArithmeticFunction.cardDistinctFactors n : ℝ))).card : ℝ) <
          exp ((b * c + (π ^ 2 / 6) / c + epsilon) * (P / log P ^ (a + 1))) := by
  let B (P : ℝ) := P - Chebyshev.theta P + (primeCount P - T P) * log P
  let s (P : ℝ) := c * log P ^ a
  let Z (P : ℝ) := P / log P ^ (a + 1)
  let R (P : ℝ) := ∑' p : ℕ, if p.Prime then weight P (s P) p else 0
  let C (P : ℝ) := log (1 + ∑' n : ℕ, (n : ℝ) ^ (-s P))
  have hs : Tendsto s atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc).mpr ((tendsto_rpow_atTop ha).comp tendsto_log_atTop)
  have hsoft := prime_softplus_asymptotic ha hc le_rfl s
    (Eventually.of_forall (fun _ => ⟨le_rfl, le_rfl⟩))
  have hZpos {P : ℝ} (hP : 1 < P) : 0 < Z P :=
    div_pos (zero_lt_one.trans hP) (rpow_pos_of_pos (log_pos hP) _)
  have hZ : Tendsto Z atTop atTop := by
    have h := (isLittleO_log_rpow_rpow_atTop (a + 1)
      (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
    simp only [rpow_one] at h
    have hpos : ∀ᶠ P : ℝ in atTop, 0 < log P ^ (a + 1) / P := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
      exact div_pos (rpow_pos_of_pos (log_pos hP) _) (zero_lt_one.trans hP)
    simpa only [Z, Function.comp_def, inv_div, id_eq] using
      tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨h, hpos⟩)
  have hreserve : Tendsto (fun P => s P * B P / Z P) atTop (𝓝 (b * c)) := by
    apply (hB.mul_const c).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    change B P / (P / log P ^ (a + 1 + a)) * c = s P * B P / Z P
    dsimp [s, Z]
    rw [div_div_eq_mul_div, div_div_eq_mul_div, rpow_add (log_pos hP)]
    ring
  have hR : Tendsto (fun P => R P / Z P) atTop (𝓝 ((π ^ 2 / 6) / c)) := by
    apply (hsoft.2.div_const c).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    change R P / (P / (s P * log P)) / c = R P / Z P
    have hscale : s P * log P = c * log P ^ (a + 1) := by
      dsimp only [s]
      rw [mul_assoc, rpow_add (log_pos hP), rpow_one]
    rw [hscale]
    change R P / (P / (c * log P ^ (a + 1))) / c = R P / (P / log P ^ (a + 1))
    simp only [div_div_eq_mul_div]
    field_simp [hc.ne', (zero_lt_one.trans hP).ne']
    <;> ring
  have hC : Tendsto (fun P => C P / Z P) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ (hZ.const_div_atTop (log (1 + ∑' n : ℕ, (n : ℝ) ^ (-(2 : ℝ)))))
    · filter_upwards [hs.eventually_ge_atTop 2, eventually_gt_atTop (1 : ℝ)] with P hsP hP
      exact div_nonneg (rankin_correction hsP).1 (hZpos hP).le
    · filter_upwards [hs.eventually_ge_atTop 2, eventually_gt_atTop (1 : ℝ)] with P hsP hP
      exact div_le_div_of_nonneg_right (rankin_correction hsP).2 (hZpos hP).le
  have hlim := (hreserve.add hR).add hC
  rw [add_zero] at hlim
  filter_upwards [hlim.eventually_lt_const (lt_add_of_pos_right _ hepsilon),
    hs.eventually_ge_atTop 2, hsoft.1, eventually_gt_atTop (1 : ℝ)] with P hlim hsP hRsum hP
  have hs1 : 1 < s P := (by norm_num : (1 : ℝ) < 2).trans_le hsP
  have hz : 1 ≤ P ^ s P := one_le_rpow hP.le (zero_lt_one.trans hs1).le
  refine (rankin_exponential_bound (T := T P) hs1 hz (exp_pos P)).trans_lt ?_
  apply exp_lt_exp.mpr
  rw [log_exp]
  have hcancel := rankin_prime_cancellation (T P) hP hRsum.of_abs
  have hnormalized : (s P * B P + R P + C P) / Z P < b * c + (π ^ 2 / 6) / c + epsilon := by
    simpa only [add_div] using hlim
  change _ < (b * c + (π ^ 2 / 6) / c + epsilon) * Z P
  exact (by linarith only [hcancel] : _ ≤ s P * B P + R P + C P).trans_lt
    ((div_lt_iff₀ (hZpos hP)).mp hnormalized)

/-- Sharp upper bound at the second threshold for every positive error and all large cutoffs. -/
theorem sharp_upper_bound (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ P : ℝ in atTop,
      (tailCount 1 (exp P) : ℝ) ≤ exp ((2 * π / sqrt 3 + epsilon) *
        (P / log P ^ (3 / 2 : ℝ))) := by
  have hB : Tendsto (fun P : ℝ => continuousReserve P /
      (P / log P ^ ((1 / 2 : ℝ) + 1 + 1 / 2))) atTop (𝓝 2) := by
    rw [show (1 / 2 : ℝ) + 1 + 1 / 2 = (2 : ℕ) by norm_num]
    simpa only [rpow_natCast] using centered_reserve.2.2.2.1
  have h := sharp_upper_bound_of_reserve centeredThreshold (by norm_num : (0 : ℝ) < 1 / 2)
    (show 0 < π / (2 * sqrt 3) by positivity) (by simpa only [continuousReserve] using hB)
    epsilon hepsilon
  rw [optimizer_constant, show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num] at h
  filter_upwards [h] with P hP
  have hthreshold : threshold 1 (exp P) = centeredThreshold P := by
    simp only [threshold, scale, log_exp, one_mul, centeredThreshold, div_div, pow_two]
  simpa only [tailCount, hthreshold] using hP.le

private lemma factorial_optimizer_constant (b : ℝ) (hb : 0 < b) :
    b * (π / sqrt (6 * b)) + (π ^ 2 / 6) / (π / sqrt (6 * b)) =
      π * sqrt (2 * b / 3) := by
  have hd : 0 < sqrt (6 * b) := by positivity
  have hd_sq : sqrt (6 * b) ^ 2 = 6 * b := sq_sqrt (by positivity)
  have hsqrt : sqrt (6 * b) = 3 * sqrt (2 * b / 3) := by
    have hq : sqrt (2 * b / 3) ^ 2 = 2 * b / 3 := sq_sqrt (by positivity)
    have hsq : sqrt (6 * b) ^ 2 = (3 * sqrt (2 * b / 3)) ^ 2 := by nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact h
    · have hpos : 0 < sqrt (2 * b / 3) := by positivity
      linarith
  calc
    _ = (sqrt (6 * b) ^ 2 / 6) * (π / sqrt (6 * b)) +
        (π ^ 2 / 6) / (π / sqrt (6 * b)) := by rw [hd_sq]; ring
    _ = π * sqrt (6 * b) / 3 := by
      field_simp [pi_ne_zero, hd.ne']
      <;> ring
    _ = _ := by rw [hsqrt]; ring

/-- The analytic upper bound in Proposition 7.9 follows from the sharp continuous reserve limit. -/
theorem factorial_sharp_upper_bound (r : ℕ) (hr : 2 ≤ r) (T : ℝ → ℝ)
    (hB : Tendsto (fun P : ℝ =>
      (P - Chebyshev.theta P + (primeCount P - T P) * log P) /
        (P / log P ^ r)) atTop (𝓝 (r.factorial : ℝ)))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ P : ℝ in atTop,
      (((Icc 1 ⌊exp P⌋₊).filter (fun n =>
        T P < (ArithmeticFunction.cardDistinctFactors n : ℝ))).card : ℝ) <
          exp ((π * sqrt (2 * (r.factorial : ℝ) / 3) + epsilon) *
            (P / log P ^ (((r : ℝ) + 1) / 2))) := by
  let a : ℝ := ((r : ℝ) - 1) / 2
  let b : ℝ := r.factorial
  let c : ℝ := π / sqrt (6 * b)
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; exact_mod_cast Nat.factorial_pos r
  have hc : 0 < c := by dsimp [c]; positivity
  have hpower : a + 1 + a = (r : ℝ) := by dsimp [a]; ring
  have hscale : a + 1 = ((r : ℝ) + 1) / 2 := by dsimp [a]; ring
  have h := sharp_upper_bound_of_reserve T ha hc
    (by simpa only [hpower, rpow_natCast] using hB) epsilon hepsilon
  rwa [show b * c + (π ^ 2 / 6) / c = π * sqrt (2 * b / 3) from
    factorial_optimizer_constant b hb, hscale] at h

end D5.S3.Arith.Robin.Analytic.OmegaTail.RankinUpper
