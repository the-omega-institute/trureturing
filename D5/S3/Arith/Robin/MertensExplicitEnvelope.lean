/- GID: D5/S3/Arith/Robin/MertensExplicitEnvelope
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/MertensExplicitEnvelope
   mirror-E: none(waiver:analytic-estimate)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Robin/MertensExplicitEnvelope.prime_product_upper_effective; premises=D5/S3/Arith/Robin/MertensExplicitEnvelope.explicit_mertens_E1_le_four_fifths,D5/S3/Arith/Robin/MertensExplicitEnvelope.effective_E1p_lower,D5/S3/Arith/Robin/MertensExplicitEnvelope.effective_E1p_upper
   digest: A kernel-certified elementary reciprocal prime-product envelope for every real cutoff at least 286. -/

import D5.S3.Weil.Mertens.Third
import D5.S3.Arith.GoldenResource.RobinRationalBasis
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-
The numerical input is the kernel-normalized rational weighted head through 512,
bounded by 39/50, together with the proved integral tail. These imply E1 ≤ 4/5.
The instance classification records the fixed numerical certificates imported
from RobinRationalBasis; the estimate remains uniform for every x ≥ 286.
The full prime-power decomposition pays a 7/25 linear budget above 286. Refined
factorial estimates and fourteen explicit prime powers then put E1p in the
interval [-91/50, 2/25]. The one-sided Mertens identity consumes that interval
in prime_product_upper_effective; every helper below is on that live path.

The constants are a repo-derived elementary estimate. Classical Mertens
identities are imported from the attributed port in Mertens.Third. Rosser and
Schoenfeld's stronger Theorem 8 is documented in Library/Arith/rosser1962approximate.md;
its numerical tables are not an assumption of this proof. This module supplies
an unconditional envelope, not a proof of the Riemann hypothesis.
-/

open Finset Real

noncomputable section

namespace Chebyshev

/-- Isolating squares and cubes sharpens the elementary prime-power error estimate. -/
theorem psi_sub_theta_le_square_cube_fourth {x : ℝ} (hx : 2 ≤ x) :
    psi x - theta x ≤
      log 4 * (x ^ (1 / 2 : ℝ) + x ^ (1 / 3 : ℝ)) +
        2 * log x * x ^ (1 / 4 : ℝ) := by
  have hx0 : 0 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlogx : 0 ≤ log x := log_nonneg hx1
  let N : ℕ := ⌊log x / log 2⌋₊
  let f : ℕ → ℝ := fun k => theta (x ^ ((1 : ℝ) / k))
  have hsub : Icc 2 N ⊆ insert 2 (insert 3 (Icc 4 N)) := by
    intro k hk
    simp only [mem_Icc] at hk
    simp only [mem_insert, mem_Icc]
    omega
  have hs : (∑ k ∈ Icc 2 N, f k) ≤ f 2 + f 3 + ∑ k ∈ Icc 4 N, f k := by
    calc
      _ ≤ ∑ k ∈ insert 2 (insert 3 (Icc 4 N)), f k :=
        sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => theta_nonneg _)
      _ = _ := by rw [sum_insert (by simp), sum_insert (by simp)]; ring
  have ht : (∑ k ∈ Icc 4 N, f k) ≤
      (log x / log 2) * (log 4 * x ^ (1 / 4 : ℝ)) := by
    calc
      _ ≤ ∑ k ∈ Icc 4 N, log 4 * x ^ (1 / 4 : ℝ) := by
        apply sum_le_sum
        intro k hk
        have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
        apply (theta_le_log4_mul_x (rpow_nonneg hx0 _)).trans
        gcongr
      _ = ↑(Icc 4 N).card * (log 4 * x ^ (1 / 4 : ℝ)) := by simp
      _ ≤ (N : ℝ) * (log 4 * x ^ (1 / 4 : ℝ)) := by
        gcongr
        exact_mod_cast (show (Icc 4 N).card ≤ N by simp only [Nat.card_Icc]; omega)
      _ ≤ _ := by gcongr; exact Nat.floor_le (by positivity)
  have hlog4 : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; ring
  rw [psi_eq_theta_add_sum_theta hx, add_sub_cancel_left]
  calc
    _ ≤ f 2 + f 3 + ∑ k ∈ Icc 4 N, f k := hs
    _ ≤ log 4 * x ^ (1 / 2 : ℝ) + log 4 * x ^ (1 / 3 : ℝ) +
        (log x / log 2) * (log 4 * x ^ (1 / 4 : ℝ)) := by
      gcongr
      · exact theta_le_log4_mul_x (rpow_nonneg hx0 _)
      · exact theta_le_log4_mul_x (rpow_nonneg hx0 _)
    _ = _ := by rw [hlog4]; field_simp

private lemma log_286_le : log (286 : ℝ) ≤ 17 / 3 := by
  have htwo : log (2 : ℝ) ≤ 1733 / 2500 := by linarith [log_two_lt_d9]
  have hrat := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 286 / 256)
  have hsplit : log (286 : ℝ) = 8 * log 2 + log (286 / 256 : ℝ) := by
    rw [log_div (by norm_num) (by norm_num), show (256 : ℝ) = 2 ^ 8 by norm_num,
      log_pow]
    ring
  rw [hsplit]
  linarith

private lemma rpow_286_half_le : (286 : ℝ) ^ (1 / 2 : ℝ) ≤ 17 := by
  rw [one_div, rpow_inv_le_iff_of_pos (by norm_num : (0 : ℝ) ≤ 286)
    (by norm_num : (0 : ℝ) ≤ 17) (by norm_num : (0 : ℝ) < 2)]
  norm_num

private lemma rpow_286_third_le : (286 : ℝ) ^ (1 / 3 : ℝ) ≤ 33 / 5 := by
  rw [one_div, rpow_inv_le_iff_of_pos (by norm_num : (0 : ℝ) ≤ 286)
    (by norm_num : (0 : ℝ) ≤ 33 / 5) (by norm_num : (0 : ℝ) < 3)]
  norm_num

private lemma rpow_286_fourth_le : (286 : ℝ) ^ (1 / 4 : ℝ) ≤ 33 / 8 := by
  rw [one_div, rpow_inv_le_iff_of_pos (by norm_num : (0 : ℝ) ≤ 286)
    (by norm_num : (0 : ℝ) ≤ 33 / 8) (by norm_num : (0 : ℝ) < 4)]
  norm_num

private lemma root_ratio_le_at_286 {x r : ℝ} (hx : 286 ≤ x) (hr : r ≤ 1) :
    x ^ r / x ≤ (286 : ℝ) ^ r / 286 := by
  have hx0 : 0 < x := by linarith
  have hid (z : ℝ) (hz : 0 < z) : z ^ r / z = z ^ (r - 1) := by
    rw [rpow_sub hz, rpow_one]
  rw [hid x hx0, hid 286 (by norm_num)]
  exact rpow_le_rpow_of_nonpos (by norm_num) hx (by linarith)

private lemma log_fourth_ratio_le_at_286 {x : ℝ} (hx : 286 ≤ x) :
    log x * x ^ (1 / 4 : ℝ) / x ≤
      log (286 : ℝ) * (286 : ℝ) ^ (1 / 4 : ℝ) / 286 := by
  have hbase : exp ((3 / 4 : ℝ)⁻¹) ≤ 286 := by
    apply (le_log_iff_exp_le (by norm_num : (0 : ℝ) < 286)).mp
    have h4 : log (4 : ℝ) = 2 * log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]; ring
    have hmono := log_le_log (by norm_num : (0 : ℝ) < 4) (by norm_num : (4 : ℝ) ≤ 286)
    rw [h4] at hmono
    norm_num
    linarith [log_two_gt_d9]
  have h := log_div_self_rpow_antitoneOn (by norm_num : (0 : ℝ) < 3 / 4)
    hbase (hbase.trans hx) hx
  have hid (z : ℝ) (hz : 0 < z) :
      log z * z ^ (1 / 4 : ℝ) / z = log z / z ^ (3 / 4 : ℝ) := by
    have hr : z ^ (1 / 4 : ℝ) * z ^ (3 / 4 : ℝ) = z := by
      rw [← rpow_add hz]; norm_num
    field_simp
    rw [mul_assoc, hr]
  rw [hid x (by linarith), hid 286 (by norm_num)]
  exact h

/-- Above 286 the prime-power part of Chebyshev's function uses at most 28 percent
of the linear budget. -/
theorem psi_sub_theta_le_seven_twenty_fifths {x : ℝ} (hx : 286 ≤ x) :
    psi x - theta x ≤ (7 / 25 : ℝ) * x := by
  have hx0 : 0 < x := by linarith
  have hlog4 : log (4 : ℝ) ≤ 7 / 5 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    norm_num
    linarith [log_two_lt_d9]
  have hr2 := root_ratio_le_at_286 (r := 1 / 2) hx (by norm_num)
  have hr3 := root_ratio_le_at_286 (r := 1 / 3) hx (by norm_num)
  have hr4 := log_fourth_ratio_le_at_286 hx
  have hendpoint :
      log 4 * ((286 : ℝ) ^ (1 / 2 : ℝ) / 286 +
        (286 : ℝ) ^ (1 / 3 : ℝ) / 286) +
      2 * (log (286 : ℝ) * (286 : ℝ) ^ (1 / 4 : ℝ) / 286) ≤ 7 / 25 := by
    calc
      _ ≤ (7 / 5 : ℝ) * (17 / 286 + (33 / 5) / 286) +
          2 * ((17 / 3 : ℝ) * (33 / 8) / 286) := by
        gcongr
        · exact rpow_286_half_le
        · exact rpow_286_third_le
        · exact log_286_le
        · exact rpow_286_fourth_le
      _ ≤ _ := by norm_num
  apply (div_le_iff₀ hx0).mp
  calc
    _ ≤ (log 4 * (x ^ (1 / 2 : ℝ) + x ^ (1 / 3 : ℝ)) +
        2 * log x * x ^ (1 / 4 : ℝ)) / x := by
      gcongr
      exact psi_sub_theta_le_square_cube_fourth (by linarith)
    _ = log 4 * (x ^ (1 / 2 : ℝ) / x + x ^ (1 / 3 : ℝ) / x) +
        2 * (log x * x ^ (1 / 4 : ℝ) / x) := by ring
    _ ≤ log 4 * ((286 : ℝ) ^ (1 / 2 : ℝ) / 286 +
        (286 : ℝ) ^ (1 / 3 : ℝ) / 286) +
        2 * (log (286 : ℝ) * (286 : ℝ) ^ (1 / 4 : ℝ) / 286) := by gcongr
    _ ≤ _ := hendpoint


end Chebyshev

namespace D5.S3.Arith.Robin.MertensExplicitEnvelope

open Real Finset MeasureTheory
open Mertens

theorem mertens_tail_nonnegative (x : ℝ) :
    M - γ ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_summand n := by
  have hs (n : ℕ) : M_eq_summand n ≤ 0 := by
    unfold M_eq_summand
    split_ifs with hp
    · have hn : (2 : ℝ) ≤ n := by exact_mod_cast hp.two_le
      have hpos : 0 < 1 - (1 : ℝ) / n := by
        have : (1 : ℝ) / n ≤ 1 / 2 := by gcongr
        linarith
      have hlog := Real.log_le_sub_one_of_pos hpos
      linarith
    · rfl
  have ht := M_eq_summable.neg.sum_le_tsum (Ioc 0 ⌊x⌋₊)
    (fun n _ ↦ neg_nonneg.mpr (hs n))
  simp only [sum_neg_distrib, tsum_neg, tsum_M_eq_summand_eq] at ht
  linarith

theorem mertens_E3_ge_neg_E2p (x : ℝ) : -E₂p x ≤ E₃ x := by
  have ht := mertens_tail_nonnegative x
  have hid : E₃ x =
      (∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_summand n - (M - γ)) - E₂p x := by
    unfold E₃ E₂p
    have hf (n : ℕ) : M_eq_summand n =
        (if n.Prime then log (1 - 1 / n) else 0) +
        (if n.Prime then (1 : ℝ) / n else 0) := by
      unfold M_eq_summand
      split_ifs
      · rfl
      · ring
    simp_rw [hf]
    rw [sum_filter, sum_filter, sum_add_distrib, γ.eq_eulerMascheroni]
    ring
  rw [hid]
  linarith

theorem mertens_E2p_le_of_tail_lower {x a : ℝ} (hx : 2 ≤ x)
    (ha : ∀ t : ℝ, x ≤ t → a ≤ E₁p t) :
    E₂p x ≤ (E₁p x - a) / log x := by
  have hlog : 0 < log x := log_pos (by linarith)
  have hint : a / log x ≤ ∫ t in Set.Ioi x, E₁p t / (t * log t ^ 2) := by
    calc
      _ = ∫ t in Set.Ioi x, a / (t * log t ^ 2) :=
        (integ_div_mul_log_sq a hx).symm
      _ ≤ _ := by
        apply setIntegral_mono_on (integrable_const_div_mul_log_sq a hx)
          (integrable_E₁p_div_mul_log_sq hx) (by measurability)
        intro t ht
        have htx : x < t := ht
        have htpos : 0 < t := by linarith
        have htlog : 0 < log t := log_pos (by linarith)
        exact div_le_div_of_nonneg_right (ha t htx.le) (by positivity)
  rw [E₂p.eq hx]
  calc
    E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t ^ 2) ≤
        E₁p x / log x - a / log x := sub_le_sub_left hint _
    _ = (E₁p x - a) / log x := (sub_div _ _ _).symm

theorem mertens_E3_ge_of_local_envelope {x a b : ℝ} (hx : 2 ≤ x)
    (ha : ∀ t : ℝ, x ≤ t → a ≤ E₁p t) (hb : E₁p x ≤ b) :
    -(b - a) / log x ≤ E₃ x := by
  have hlog : 0 < log x := log_pos (by linarith)
  have hupper := mertens_E2p_le_of_tail_lower hx ha
  have hwidth : (E₁p x - a) / log x ≤ (b - a) / log x := by
    exact div_le_div_of_nonneg_right (sub_le_sub_right hb a) hlog.le
  have hsign := mertens_E3_ge_neg_E2p x
  rw [neg_div]
  linarith

theorem prime_product_upper_of_local_envelope {x a b : ℝ} (hx : 2 ≤ x)
    (ha : ∀ t : ℝ, x ≤ t → a ≤ E₁p t) (hb : E₁p x ≤ b) :
    (∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1 : ℝ) / p))⁻¹ ≤
      exp eulerMascheroniConstant * log x * exp ((b - a) / log x) := by
  have hlog : 0 < log x := log_pos (by linarith)
  have hlow := mertens_E3_ge_of_local_envelope hx ha hb
  rw [neg_div] at hlow
  rw [prod_one_minus_div_prime_eq (by linarith)]
  calc
    (exp (-eulerMascheroniConstant) * exp (E₃ x) / log x)⁻¹ =
        exp eulerMascheroniConstant * log x * exp (-E₃ x) := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, ← Real.exp_neg, neg_neg]
      ring
    _ ≤ _ := by
      gcongr
      linarith

end D5.S3.Arith.Robin.MertensExplicitEnvelope

namespace D5.S3.Arith.Robin.MertensExplicitEnvelope

set_option maxRecDepth 8192

open Real Finset Filter MeasureTheory
open Mertens

private noncomputable def dyadicLogUpper (n : ℕ) : ℝ :=
  (Nat.log 2 n : ℝ) * (347 / 500) + (n : ℝ) / (2 : ℝ) ^ Nat.log 2 n - 1

private def dyadicLogUpperQ (n : ℕ) : ℚ :=
  (Nat.log 2 n : ℚ) * (347 / 500) + (n : ℚ) / (2 : ℚ) ^ Nat.log 2 n - 1

private theorem log_le_dyadicLogUpper {n : ℕ} (hn : 0 < n) :
    log n ≤ dyadicLogUpper n := by
  let k := Nat.log 2 n
  have hpow : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsplit : (n : ℝ) = (2 : ℝ) ^ k * ((n : ℝ) / (2 : ℝ) ^ k) := by
    field_simp
  have hlog2 : log 2 ≤ (347 : ℝ) / 500 := by linarith [Real.log_two_lt_d9]
  calc
    log n = (k : ℝ) * log 2 + log ((n : ℝ) / (2 : ℝ) ^ k) := by
      conv_lhs => rw [hsplit]
      rw [log_mul hpow.ne' (div_pos hnR hpow).ne', log_pow]
    _ ≤ (k : ℝ) * (347 / 500) + ((n : ℝ) / (2 : ℝ) ^ k - 1) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _))
        (Real.log_le_sub_one_of_pos (div_pos hnR hpow))
    _ = dyadicLogUpper n := by unfold dyadicLogUpper; dsimp [k]; ring

set_option maxHeartbeats 1000000 in
-- The rational weighted sum is normalized by the kernel, without a native oracle.
private theorem finite_E1_certificate :
    ∑ n ∈ range 513, (if n.Prime then
      dyadicLogUpper n / ((n : ℝ) * (n - 1)) else 0) ≤ 39 / 50 := by
  have hq :
      ∑ n ∈ range 513, (if n.Prime then
        dyadicLogUpperQ n / ((n : ℚ) * (n - 1)) else 0) ≤ 39 / 50 := by
    decide +kernel
  have hcast := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast [dyadicLogUpperQ] at hcast
  simp only [apply_ite] at hcast
  push_cast at hcast
  exact hcast

private theorem finite_E1_le :
    ∑ n ∈ range 513,
      (if n.Prime then log n / ((n : ℝ) * (n - 1)) else 0) ≤ 39 / 50 := by
  apply le_trans ?_ finite_E1_certificate
  apply sum_le_sum
  intro n hn
  split_ifs with hprime
  · have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hprime.two_le
    exact div_le_div_of_nonneg_right (log_le_dyadicLogUpper hprime.pos)
      (mul_nonneg (Nat.cast_nonneg _) (by linarith))
  · rfl

private noncomputable abbrev logSqTail (t : ℝ) : ℝ := log (t + 512) / (t + 512) ^ 2

private theorem logSqTail_antitone : AntitoneOn logSqTail (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · intro t ht
    simp at ht
    have hz : t + 512 ≠ 0 := by linarith
    have hz2 : (t + 512) ^ 2 ≠ 0 := pow_ne_zero _ hz
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    have hz : t + 512 ≠ 0 := by linarith
    have hz2 : (t + 512) ^ 2 ≠ 0 := pow_ne_zero _ hz
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by positivity),
      deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    have he : exp 1 ≤ t + 512 := by linarith [exp_one_lt_three]
    have hl := log_le_log (exp_pos 1) he
    rw [log_exp] at hl
    linarith

private theorem logSqTail_nonneg : ∀ t ∈ Set.Ioi 0, 0 ≤ logSqTail t := by
  intro t ht
  dsimp [logSqTail]
  exact div_nonneg (log_nonneg (by simp_all; linarith)) (sq_nonneg _)

private theorem logSqTail_hasDeriv : ∀ t ∈ Set.Ici 0,
    HasDerivAt (fun t ↦ (-log (t + 512) - 1) / (t + 512)) (logSqTail t) t := by
  intro t ht
  apply HasDerivAt.comp_add_const (f := fun t : ℝ ↦ (-log t - 1) / t) t 512
  convert! HasDerivAt.fun_div (c' := -1 / (t + 512)) (d' := (1 : ℝ)) _ _ _ using 1
  · dsimp [logSqTail]
    field_simp [show t + 512 ≠ 0 by simp at ht; linarith]
    ring
  · apply HasDerivAt.sub_const
    convert! (hasDerivAt_log (by simp at ht; linarith : t + 512 ≠ 0)).neg using 1
    ring
  · exact hasDerivAt_id _
  · simp at ht; linarith

private theorem logSqTail_primitive_tendsto :
    Tendsto (fun t ↦ (-log (t + 512) - 1) / (t + 512)) atTop (nhds 0) := by
  have ht : Tendsto (fun t : ℝ ↦ t + 512) atTop atTop :=
    tendsto_atTop_add_const_right atTop 512 tendsto_id
  apply Tendsto.comp (g := fun t : ℝ ↦ (-log t - 1) / t) _ ht
  convert! Tendsto.sub (f := fun t : ℝ ↦ -log t / t) (a := 0) _
    tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)).neg using 1
    · ext; ring
    · simp

private theorem logSqTail_integrable : IntegrableOn logSqTail (Set.Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' logSqTail_hasDeriv logSqTail_nonneg
    logSqTail_primitive_tendsto

private theorem logSqTail_integral :
    ∫ t in Set.Ioi 0, logSqTail t = (log 512 + 1) / 512 := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' logSqTail_hasDeriv logSqTail_nonneg
    logSqTail_primitive_tendsto]
  norm_num
  ring

private theorem logSqTail_summable : Summable (fun n : ℕ ↦ logSqTail (n + 1 : ℕ)) := by
  exact (summable_nat_add_iff 1).mpr
    (logSqTail_antitone.summable_of_integrableOn_Ioi_zero
      logSqTail_integrable logSqTail_nonneg)

private theorem logSqTail_sum_le :
    ∑' n : ℕ, logSqTail (n + 1 : ℕ) ≤ (log 512 + 1) / 512 := by
  rw [← logSqTail_integral]
  exact logSqTail_antitone.tsum_add_one_le_integral
    logSqTail_integrable logSqTail_nonneg

set_option maxHeartbeats 1000000 in
-- The finite rational reduction and its cast need a larger elaboration budget.
theorem explicit_mertens_E1_le_four_fifths : E₁ ≤ (4 : ℝ) / 5 := by
  unfold E₁
  rw [← E₁.summable.sum_add_tsum_nat_add 513]
  have htail :
      ∑' n : ℕ, (if (n + 513).Prime then
        log ((n + 513 : ℕ) : ℝ) /
          (((n + 513 : ℕ) : ℝ) * ((n + 513 : ℕ) - 1)) else 0) ≤
        (513 / 512 : ℝ) * ((log 512 + 1) / 512) := by
    apply le_trans ?_ (mul_le_mul_of_nonneg_left logSqTail_sum_le (by norm_num))
    rw [← tsum_mul_left]
    have hs := (summable_nat_add_iff 513).mpr E₁.summable
    simp only [Nat.cast_add, Nat.cast_ofNat] at hs
    have hsRight : Summable (fun n : ℕ ↦ (513 / 512 : ℝ) * logSqTail ((n : ℝ) + 1)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        logSqTail_summable.mul_left (513 / 512 : ℝ)
    simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
    apply Summable.tsum_le_tsum ?_
      hs
      hsRight
    intro n
    split_ifs with hp
    · dsimp [logSqTail]
      push_cast
      have hn : (0 : ℝ) < n + 512 := by positivity
      have hlog : 0 ≤ log ((n : ℝ) + 513) := log_nonneg (by
        have := Nat.cast_nonneg (α := ℝ) n
        linarith)
      rw [show (n : ℝ) + 513 - 1 = (n : ℝ) + 512 by ring,
        show (n : ℝ) + 1 + 512 = (n : ℝ) + 513 by ring]
      apply (div_le_iff₀ (by positivity : (0 : ℝ) <
        ((n : ℝ) + 513) * ((n : ℝ) + 512))).mpr
      field_simp
      nlinarith
    · exact mul_nonneg (by norm_num) (logSqTail_nonneg _ (by
        simp only [Set.mem_Ioi]
        positivity))
  have hlog512 : log (512 : ℝ) ≤ 9 * (347 / 500 : ℝ) := by
    have hlog2 : log 2 ≤ (347 : ℝ) / 500 := by linarith [Real.log_two_lt_d9]
    have : log (512 : ℝ) = 9 * log 2 := by
      calc
        _ = log ((2 : ℝ) ^ 9) := by norm_num
        _ = _ := by rw [log_pow]; norm_num
    rw [this]
    gcongr
  have hfinite := finite_E1_le
  calc
    _ ≤ 39 / 50 + (513 / 512 : ℝ) * ((log 512 + 1) / 512) :=
      add_le_add hfinite htail
    _ ≤ 39 / 50 + (513 / 512 : ℝ) * ((9 * (347 / 500) + 1) / 512) := by
      gcongr
    _ ≤ (4 : ℝ) / 5 := by norm_num


end D5.S3.Arith.Robin.MertensExplicitEnvelope

namespace D5.S3.Arith.Robin.MertensExplicitEnvelope

open Real Finset MeasureTheory
open ArithmeticFunction hiding log
open Mertens
open D5.S3.Arith.GoldenResource.RobinRationalBasis
open scoped Chebyshev

theorem sum_log_lower_refined {x : ℝ} (hx : 1 ≤ x) :
    x * log x - x - log x ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := by
  have hm : 1 ≤ ⌊x⌋₊ := by simpa
  calc
    _ ≤ (∫ t in 1..x, log t) - log x := by
      simp only [integral_log, log_one, mul_zero, sub_zero]
      linarith
    _ ≤ (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
      gcongr
      grw [Mertens.integral_log_le (by simpa) (Nat.floor_le (by linarith))]
      have hlog : 0 ≤ log x := log_nonneg hx
      nlinarith [Nat.lt_floor_add_one x]
    _ = ∫ t in 1..⌊x⌋₊, log t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
        intervalIntegral.intervalIntegrable_log' intervalIntegral.intervalIntegrable_log']
      ring
    _ ≤ ∑ n ∈ Ico 1 ⌊x⌋₊, log ((n + 1 : ℕ)) := by
      convert MonotoneOn.integral_le_sum_Ico hm ?_ using 1
      · norm_cast
      · exact strictMonoOn_log.monotoneOn.mono (by
          intro t ht; simp at ht ⊢; linarith)
    _ = ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := by
      rw [(by rfl : Ioc 0 ⌊x⌋₊ = Icc 1 ⌊x⌋₊),
        ← add_sum_Ioc_eq_sum_Icc hm]
      simp
      have hs := Finset.sum_Ico_add' (fun n : ℕ ↦ log (n : ℝ)) 1 ⌊x⌋₊ 1
      have hsets : Ico (1 + 1) (⌊x⌋₊ + 1) = Ioc 1 ⌊x⌋₊ := by
        ext n; simp only [mem_Ico, mem_Ioc]; omega
      rw [hsets] at hs
      simpa only [Nat.cast_add, Nat.cast_one] using hs

theorem sum_log_upper_refined {x : ℝ} (hx : 1 ≤ x) :
    (∑ n ∈ Ioc 0 ⌊x⌋₊, log n) ≤ x * log x - x + 1 + log x := by
  have hm : 1 ≤ ⌊x⌋₊ := by simpa
  have hmR : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hm
  have hmx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hI : (∫ t in 1..⌊x⌋₊, log t) ≤ ∫ t in 1..x, log t := by
    have hnonneg : 0 ≤ ∫ t in (⌊x⌋₊ : ℝ)..x, log t := by
      apply intervalIntegral.integral_nonneg hmx
      intro t ht
      exact log_nonneg (by linarith [ht.1])
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (a := (1 : ℝ)) (b := (⌊x⌋₊ : ℝ)) (c := x)
      intervalIntegral.intervalIntegrable_log' intervalIntegral.intervalIntegrable_log'
    linarith
  calc
    _ = (∑ n ∈ Ico 1 ⌊x⌋₊, log n) + log ⌊x⌋₊ := by
      rw [(by rfl : Ioc 0 ⌊x⌋₊ = Ico 1 (⌊x⌋₊ + 1)), sum_Ico_succ_top hm]
    _ ≤ (∫ t in 1..⌊x⌋₊, log t) + log x := by
      apply add_le_add
      · have hmono : MonotoneOn log (Set.Icc (1 : ℝ) (⌊x⌋₊ : ℝ)) := by
          exact strictMonoOn_log.monotoneOn.mono (by
            intro t ht; simp at ht ⊢; linarith)
        simpa only [Nat.cast_one] using
          MonotoneOn.sum_le_integral_Ico hm (by simpa using hmono)
      · exact log_le_log (by linarith) hmx
    _ ≤ (∫ t in 1..x, log t) + log x := add_le_add hI (le_refl _)
    _ = _ := by simp only [integral_log, log_one, mul_zero, sub_zero]

theorem E1Lambda_lower_refined {x : ℝ} (hx : 1 ≤ x) :
    -1 - log x / x ≤ E₁Λ x := by
  have hxpos : 0 < x := by linarith
  have hsum : x * (∑ d ∈ Ioc 0 ⌊x⌋₊, vonMangoldt d / d) ≥
      x * log x - x - log x := by
    calc
      _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, vonMangoldt d * (x / d) := by
        rw [mul_sum]; ring_nf
      _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, vonMangoldt d * ⌊x / d⌋₊ := by
        gcongr
        exact Nat.floor_le (div_nonneg hxpos.le (Nat.cast_nonneg _))
      _ = ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := (sum_log_eq_sum_mangoldt).symm
      _ ≥ _ := sum_log_lower_refined hx
  have hmul : -x - log x ≤ E₁Λ x * x := by
    unfold E₁Λ
    nlinarith
  calc
    _ = (-x - log x) / x := by field_simp
    _ ≤ _ := (div_le_iff₀ hxpos).mpr hmul

theorem E1Lambda_upper_refined {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ -1 + (log x + 1) / x + ψ x / x := by
  have hxpos : 0 < x := by linarith
  have hsum : x * (∑ d ∈ Ioc 0 ⌊x⌋₊, vonMangoldt d / d) ≤
      x * log x - x + 1 + log x + ψ x := by
    calc
      _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, vonMangoldt d * (x / d) := by
        rw [mul_sum]; ring_nf
      _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, vonMangoldt d * (⌊x / d⌋₊ + 1) := by
        gcongr
        exact (Nat.lt_floor_add_one _).le
      _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ψ x := by
        simp_rw [mul_add, mul_one]
        rw [sum_add_distrib, ← sum_log_eq_sum_mangoldt]
        rfl
      _ ≤ _ := add_le_add (sum_log_upper_refined hx) (le_refl _)
  have hmul : E₁Λ x * x ≤ -x + log x + 1 + ψ x := by
    unfold E₁Λ
    nlinarith
  calc
    _ ≤ (-x + log x + 1 + ψ x) / x := (le_div_iff₀ hxpos).mpr hmul
    _ = _ := by field_simp; ring

private def selectedPrimePowers : Finset ℕ :=
  {4, 8, 16, 32, 64, 128, 256, 9, 27, 81, 243, 25, 125, 49}

private theorem selectedPrimePowers_value :
    (∑ n ∈ selectedPrimePowers,
      if ¬n.Prime then vonMangoldt n / n else 0) =
      (127 / 256 : ℝ) * log 2 + (40 / 243 : ℝ) * log 3 +
        (6 / 125 : ℝ) * log 5 + (1 / 49 : ℝ) * log 7 := by
  have hv (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
      vonMangoldt (p ^ k) = log p := by
    rw [vonMangoldt_apply_pow hk, vonMangoldt_apply_prime hp]
  have h4 := hv 2 2 (by decide) (by decide)
  have h8 := hv 2 3 (by decide) (by decide)
  have h16 := hv 2 4 (by decide) (by decide)
  have h32 := hv 2 5 (by decide) (by decide)
  have h64 := hv 2 6 (by decide) (by decide)
  have h128 := hv 2 7 (by decide) (by decide)
  have h256 := hv 2 8 (by decide) (by decide)
  have h9 := hv 3 2 (by decide) (by decide)
  have h27 := hv 3 3 (by decide) (by decide)
  have h81 := hv 3 4 (by decide) (by decide)
  have h243 := hv 3 5 (by decide) (by decide)
  have h25 := hv 5 2 (by decide) (by decide)
  have h125 := hv 5 3 (by decide) (by decide)
  have h49 := hv 7 2 (by decide) (by decide)
  norm_num at h4 h8 h16 h32 h64 h128 h256 h9 h27 h81 h243 h25 h125 h49
  norm_num [selectedPrimePowers]
  rw [h4, h8, h16, h32, h64, h128, h256, h9, h27, h81, h243, h25, h125, h49]
  ring

private theorem selectedPrimePowers_lower :
    (319 / 500 : ℝ) ≤ (∑ n ∈ selectedPrimePowers,
      if ¬n.Prime then vonMangoldt n / n else 0) := by
  have h2 : (69 / 100 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have h3 : (109 / 100 : ℝ) < log 3 := by
    have h := (log_pow_two_mul_bounds (3 / 2) 1 4 (by norm_num)
      (by norm_num) (by norm_num)).1
    norm_num [atanhPartial, sum_range_succ] at h
    linarith
  have h5 : (8 / 5 : ℝ) < log 5 := by
    have h := (log_pow_two_mul_bounds (5 / 4) 2 4 (by norm_num)
      (by norm_num) (by norm_num)).1
    norm_num [atanhPartial, sum_range_succ] at h
    linarith
  have h7 : (97 / 50 : ℝ) < log 7 := by
    have h := (log_pow_two_mul_bounds (7 / 4) 2 4 (by norm_num)
      (by norm_num) (by norm_num)).1
    norm_num [atanhPartial, sum_range_succ] at h
    linarith
  rw [selectedPrimePowers_value]
  linarith

theorem E1Lambda_sub_E1p_lower {x : ℝ} (hx : 286 ≤ x) :
    (319 / 500 : ℝ) ≤ E₁Λ x - E₁p x := by
  have hid : E₁Λ x - E₁p x =
      ∑ n ∈ Ioc 0 ⌊x⌋₊, if ¬n.Prime then vonMangoldt n / n else 0 := by
    unfold E₁Λ E₁p
    rw [sum_filter]
    calc
      _ = ∑ n ∈ Ioc 0 ⌊x⌋₊,
          (vonMangoldt n / n - if n.Prime then log n / n else 0) := by
        rw [sum_sub_distrib]; ring
      _ = _ := by
        apply sum_congr rfl
        intro n hn
        split_ifs with hp
        · simp [vonMangoldt_apply_prime hp]
        · simp
  rw [hid]
  apply selectedPrimePowers_lower.trans
  apply sum_le_sum_of_subset_of_nonneg
  · intro n hn
    have hsmall : n ∈ Icc 1 256 := by
      have hset : selectedPrimePowers ⊆ Icc 1 256 := by decide +kernel
      exact hset hn
    rw [mem_Icc] at hsmall
    exact mem_Ioc.mpr ⟨hsmall.1, Nat.le_floor (by
      have hc : (n : ℝ) ≤ 256 := by exact_mod_cast hsmall.2
      linarith)⟩
  · intro n hn _
    split_ifs with hp
    · positivity
    · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)


private theorem log286_upper : log (286 : ℝ) ≤ (567 / 100 : ℝ) := by
  have hlog2 : log 2 ≤ (347 / 500 : ℝ) := by linarith [Real.log_two_lt_d9]
  have hr := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 143 / 128)
  have hid : log (286 : ℝ) = 8 * log 2 + log (143 / 128 : ℝ) := by
    calc
      _ = log ((2 : ℝ) ^ 8 * (143 / 128)) := by norm_num
      _ = _ := by rw [log_mul (by norm_num) (by norm_num), log_pow]; norm_num
  rw [hid]
  linarith

theorem log_div_self_small {x : ℝ} (hx : 286 ≤ x) : log x / x ≤ 1 / 50 := by
  have he : exp 1 ≤ (286 : ℝ) := le_trans exp_one_lt_three.le (by norm_num)
  have h := Real.log_div_self_antitoneOn (a := (286 : ℝ)) (b := x)
    (by exact he) (by exact he.trans hx) hx
  exact h.trans (by linarith [log286_upper])

theorem log_add_one_div_self_small {x : ℝ} (hx : 286 ≤ x) :
    (log x + 1) / x ≤ 3 / 125 := by
  have hlog := log_div_self_small hx
  have hinv : (1 : ℝ) / x ≤ 1 / 286 :=
    div_le_div_of_nonneg_left zero_le_one (by norm_num) hx
  rw [add_div]
  linarith

theorem effective_E1p_lower {x : ℝ} (hx : 286 ≤ x) : -91 / 50 ≤ E₁p x := by
  have hrel := E₁Λ.le_E₁p_add_E₁ (x := x) (by linarith)
  have hL := E1Lambda_lower_refined (x := x) (by linarith)
  have hE := explicit_mertens_E1_le_four_fifths
  have hlog := log_div_self_small hx
  linarith

theorem effective_E1p_upper {x : ℝ} (hx : 286 ≤ x) : E₁p x ≤ 2 / 25 := by
  have hxpos : 0 < x := by linarith
  have htheta := Chebyshev.theta_le_log4_mul_x hxpos.le
  have hgap := Chebyshev.psi_sub_theta_le_seven_twenty_fifths hx
  have hpsi : ψ x ≤ (log 4 + 7 / 25) * x := by nlinarith
  have hpsidiv : ψ x / x ≤ log 4 + 7 / 25 := (div_le_iff₀ hxpos).mpr hpsi
  have hupper := E1Lambda_upper_refined (x := x) (by linarith)
  have hQ := E1Lambda_sub_E1p_lower hx
  have hlog := log_add_one_div_self_small hx
  have hlog4 : log (4 : ℝ) ≤ 347 / 250 := by
    have hlog2 := Real.log_two_lt_d9
    have hid : log (4 : ℝ) = 2 * log 2 := by
      calc
        _ = log ((2 : ℝ) ^ 2) := by norm_num
        _ = _ := by rw [log_pow]; norm_num
    rw [hid]
    linarith
  linarith

theorem prime_product_upper_effective {x : ℝ} (hx : 286 ≤ x) :
    (∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1 : ℝ) / p))⁻¹ ≤
      exp eulerMascheroniConstant * log x * exp ((19 / 10 : ℝ) / log x) := by
  have h := prime_product_upper_of_local_envelope (a := -91 / 50) (b := 2 / 25)
    (x := x) (by linarith)
    (fun t ht ↦ effective_E1p_lower (hx.trans ht)) (effective_E1p_upper hx)
  norm_num at h ⊢
  exact h


end D5.S3.Arith.Robin.MertensExplicitEnvelope

#print axioms D5.S3.Arith.Robin.MertensExplicitEnvelope.explicit_mertens_E1_le_four_fifths
#print axioms D5.S3.Arith.Robin.MertensExplicitEnvelope.effective_E1p_lower
#print axioms D5.S3.Arith.Robin.MertensExplicitEnvelope.effective_E1p_upper
#print axioms D5.S3.Arith.Robin.MertensExplicitEnvelope.prime_product_upper_effective
