/- GID: D5/S3/Arith/FactorialRatio/Compression/OptimalLoss
   generality: I
   mirror-B: D5/B/S3/Arith/FactorialRatio/Compression/OptimalLoss
   mirror-E: none(waiver:symbolic-asymptotic-analysis)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Log.Sum]
   utility: none
   digest: At s=r-1 the normalized logarithmic compression loss tends to Euler's constant. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.CompactQuarticBridge
import D5.S3.Weil.Mertens.WeightedPrimeLimit
import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.Tactic

/-!
The admissible parameter set at rank `n+1` and window `n` is the singleton
`{0}`. Its gcd is `(n!)^(n+1)`. The tail has degree `n*(n+2)` and cutoff
`n`, so the exact floor-error estimate for the tail applies without any
padding. The Mangoldt limit and the prime number theorem then give the
constant in the quadratic loss.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FactorialRatio.Compression.OptimalLoss

open Finset Filter Real
open scoped Topology Nat
open D5.S3.Arith.FactorialRatio.CompactFactorialGcd
open D5.S3.Arith.FactorialRatio.RankOneLCMGcd (tailLCM)
open D5.S3.Weil.Mertens.IntegratedExplicit.CompactQuarticBridge (D U_sub_D_bounds)
open D5.S3.Arith.Robin.CompleteMertensPeak (U)
open D5.S3.Weil.Mertens.WeightedPrimeLimit

/-- The actual integer quotient at rank `n+1`, window `n`. -/
def endpointExcess (n : ℕ) : ℕ :=
  selbergGcd (n + 1) n / tailLCM (n * (n + 2)) n

private theorem endpoint_gcd (n : ℕ) :
    selbergGcd (n + 1) n = (n !) ^ (n + 1) := by
  have hdiv : n / (n + 1) = 0 := Nat.div_eq_of_lt (Nat.lt_succ_self n)
  simp [selbergGcd, hdiv, selbergFactorial]

private theorem endpoint_tail_dvd (n : ℕ) (hn : 0 < n) :
    tailLCM (n * (n + 2)) n ∣ selbergGcd (n + 1) n := by
  have h := (compact_factorial_gcd (n + 1) n (by omega)
    (by nlinarith : n < (n + 1) ^ 2)).1
  have hdeg : (n + 1) * n + (n + 1) - 1 = n * (n + 2) := by
    have : (n + 1) * n + (n + 1) = n * (n + 2) + 1 := by ring
    omega
  simpa only [hdeg, Nat.add_sub_cancel] using h

private theorem endpoint_log (n : ℕ) (hn : 0 < n) :
    log (endpointExcess n : ℝ) =
      ((n : ℝ) + 1) * log (n ! : ℝ) -
        log (tailLCM (n * (n + 2)) n : ℝ) := by
  have ht : tailLCM (n * (n + 2)) n ≠ 0 := by
    unfold tailLCM
    exact Finset.prod_ne_zero_iff.mpr fun k _ => Nat.lcmUpto_ne_zero _
  have hg : selbergGcd (n + 1) n ≠ 0 := by
    rw [endpoint_gcd]
    exact pow_ne_zero _ (Nat.factorial_ne_zero _)
  rw [endpointExcess, Nat.cast_div (endpoint_tail_dvd n hn)
    (Nat.cast_ne_zero.mpr ht), log_div (Nat.cast_ne_zero.mpr hg)
    (Nat.cast_ne_zero.mpr ht), endpoint_gcd, Nat.cast_pow, log_pow]
  push_cast <;> rfl

private theorem shifted_atTop (k : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) + k) atTop atTop :=
  tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds

private theorem shifted_ratio (k : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + k) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add
    ((shifted_atTop 1).const_div_atTop ((k : ℝ) - 1))
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [] with n
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  <;> ring

private theorem log_shifted_ratio :
    Tendsto (fun n : ℕ => log ((n : ℝ) + 2) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have h := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (shifted_atTop 2)).mul (shifted_ratio 2)
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [] with n
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  dsimp [Function.comp_def, id]
  field_simp [h1, h2]

private def factorialError (n : ℕ) : ℝ := log (n ! : ℝ) - n * log n + n

private theorem factorial_error_scaled :
    Tendsto (fun n : ℕ => factorialError n / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have hupper : Tendsto
      (fun n : ℕ => (log ((n : ℝ) + 2) + 1) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have hbase := log_shifted_ratio.add ((shifted_atTop 1).const_div_atTop 1)
    simp only [add_zero] at hbase
    apply hbase.congr'
    filter_upwards [] with n
    field_simp
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [] with n
    apply div_nonneg _ (by positivity)
    have h := Real.le_sum_log_nat n
    rw [Real.sum_log_eq_log_factorial] at h
    dsimp [factorialError]
    linarith only [h]
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h := Real.sum_log_le (x := (n : ℝ)) hnR
    rw [Nat.floor_natCast, Real.sum_log_eq_log_factorial] at h
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hl : log (n : ℝ) ≤ log ((n : ℝ) + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    dsimp [factorialError]
    linarith only [h, hl]

private theorem U_relative_tendsto :
    Tendsto (fun t : ℝ => U t / t) atTop (𝓝 0) := by
  have h := (E1Lambda_tendsto.add_const Real.eulerMascheroniConstant).sub
    relative_chebyshev_error_tendsto
  simp only [neg_add_cancel, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  dsimp [U, _root_.Mertens.E₁Λ]
  field_simp [ht.ne']
  <;> ring

private theorem tail_error_scaled :
    Tendsto (fun n : ℕ => D (n + 2) n / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  let C : ℝ := log 4 + 4
  have hC : 0 ≤ C := by
    dsimp [C]
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  have hu : Tendsto
      (fun n : ℕ => U ((n : ℝ) + 2) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have h := (U_relative_tendsto.comp (shifted_atTop 2)).mul (shifted_ratio 2)
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [] with n
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    dsimp [Function.comp_def]
    field_simp [h1, h2]
  have he : Tendsto (fun n : ℕ =>
      (U ((n : ℝ) + 2) - D (n + 2) n) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      ((shifted_atTop 1).const_div_atTop (3 * C))
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have h := (U_sub_D_bounds (n + 2) n (by omega)).1
      push_cast at h
      exact div_nonneg h (by positivity)
    · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have h := (U_sub_D_bounds (n + 2) n (by omega)).2
      push_cast at h
      have hp := Chebyshev.psi_le_const_mul_self
        (show (0 : ℝ) ≤ (n : ℝ) + 2 by positivity)
      have hb : Chebyshev.psi ((n : ℝ) + 2) / n ≤ 3 * C := by
        apply (div_le_iff₀ (by linarith : (0 : ℝ) < n)).mpr
        change Chebyshev.psi ((n : ℝ) + 2) ≤ 3 * C * n
        calc
          _ ≤ C * ((n : ℝ) + 2) := hp
          _ ≤ _ := by nlinarith only [hC, hnR]
      simpa only [Nat.cast_one] using
        (div_le_div_of_nonneg_right (h.trans hb)
          (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1))
  have h := hu.sub he
  simp only [sub_zero] at h
  convert h using 1
  ext n
  ring

private theorem endpoint_expansion (n : ℕ) (hn : 0 < n) :
    log (endpointExcess n : ℝ) / ((n : ℝ) + 1) ^ 2 =
      factorialError n / ((n : ℝ) + 1) +
      ((n : ℝ) / ((n : ℝ) + 1)) * log ((n : ℝ) / ((n : ℝ) + 2)) -
      ((n : ℝ) / ((n : ℝ) + 1)) * (log ((n : ℝ) + 2) / ((n : ℝ) + 1)) +
      Real.eulerMascheroniConstant * ((n : ℝ) / ((n : ℝ) + 1)) *
        (((n : ℝ) + 2) / ((n : ℝ) + 1)) +
      ((n : ℝ) / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1)) -
      ((n : ℝ) / ((n : ℝ) + 1)) * (D (n + 2) n / ((n : ℝ) + 1)) := by
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have ht : log (tailLCM (n * (n + 2)) n : ℝ) =
      n * (D (n + 2) n + ((n : ℝ) + 2) * log ((n : ℝ) + 2) -
        (1 + Real.eulerMascheroniConstant) * ((n : ℝ) + 2)) := by
    dsimp [D]
    push_cast
    field_simp [hnR]
    <;> ring
  rw [endpoint_log n hn, ht, Real.log_div hnR h2]
  dsimp [factorialError]
  field_simp [h1]
  <;> ring

/-- For the original compact family at `r=n+1`, `s=r-1`, the exact
integer excess has logarithm `gamma*r^2 + o(r^2)`. In particular a
uniform quadratic loss bound cannot be replaced by `o(r^2)`. -/
theorem endpoint_loss_tendsto :
    Tendsto (fun n : ℕ =>
      log (endpointExcess n : ℝ) / ((n : ℝ) + 1) ^ 2)
      atTop (𝓝 Real.eulerMascheroniConstant) := by
  have hn := shifted_ratio 0
  simp only [Nat.cast_zero, add_zero] at hn
  have hlog : Tendsto (fun n : ℕ => log ((n : ℝ) / ((n : ℝ) + 2)))
      atTop (𝓝 0) := by
    have h := hn.div (shifted_ratio 2) (by norm_num : (1 : ℝ) ≠ 0)
    simp only [div_self (by norm_num : (1 : ℝ) ≠ 0)] at h
    have heq : (fun n : ℕ => ((n : ℝ) / ((n : ℝ) + 1)) /
        (((n : ℝ) + 2) / ((n : ℝ) + 1))) =
        (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 2)) := by
      funext n
      have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
      have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp [h1, h2]
      <;> ring
    have h' : Tendsto (fun n : ℕ =>
        ((n : ℝ) / ((n : ℝ) + 1)) /
          (((n : ℝ) + 2) / ((n : ℝ) + 1))) atTop (𝓝 1) := by
      apply h.congr'
      filter_upwards [] with n
      dsimp
    have h'' : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 2))
        atTop (𝓝 1) := by
      apply h'.congr'
      filter_upwards [] with n
      exact congrFun heq n
    simpa only [Function.comp_def, Real.log_one] using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp h''
  have h := (((factorial_error_scaled.add (hn.mul hlog)).sub
      (hn.mul log_shifted_ratio)).add
      (((tendsto_const_nhds (x := Real.eulerMascheroniConstant)).mul hn).mul
        (shifted_ratio 2))).add
      (hn.mul ((shifted_atTop 1).const_div_atTop 1))
  have hfinal := h.sub (hn.mul tail_error_scaled)
  simp only [mul_zero, mul_one, add_zero, zero_add, sub_zero] at hfinal
  apply hfinal.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  convert (endpoint_expansion n (by omega)).symm using 1 <;> norm_num

end D5.S3.Arith.FactorialRatio.Compression.OptimalLoss
