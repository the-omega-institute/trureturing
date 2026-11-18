/- GID: D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaSecond/Upper
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rankin reduction at the exact second distinct-prime threshold. -/

import D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight
import D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingEstimate

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter Finset
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Upper
open D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open D5.S3.Arith.Robin.Analytic.OmegaSecond.PrimeExpansion
open D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight

/-- The finer counting scale at the second threshold. -/
def secondScale (x : ℝ) : ℝ :=
  log x / (log (log x) * sqrt (log (log x)))

/-- The explicit saddle parameter as a function of the prime cutoff. -/
def saddle (P : ℝ) : ℝ := π / (2 * sqrt 3) * sqrt (log P)

/-- A fixed bound for the unweighted inverse Euler factors. -/
def eulerCost : ℝ := log (1 + ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ))

private lemma pseries_le_square {s : ℝ} (hs : 2 ≤ s) :
    (∑' n : ℕ, (n : ℝ) ^ (-s)) ≤ ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ) := by
  apply (Real.summable_nat_rpow.mpr (by linarith : -s < -1)).tsum_le_tsum ?_
    (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1))
  intro n
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (by linarith : -s ≠ 0)]
  · apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    · linarith

/-- The strict integer tail is bounded by the exact prime budget and localized
remainder, uniformly in every real Rankin parameter at least two. -/
theorem rankin_reduction {x s : ℝ} (hx : exp 1 < x) (hs : 2 ≤ s) :
    (tailCount 1 x : ℝ) ≤
      exp (s * budget (log x) + remainder (log x) s x + eulerCost) := by
  have hx0 : 0 < x := (exp_pos 1).trans hx
  have hL : 1 < log x := (lt_log_iff_exp_lt hx0).mpr hx
  have hL0 : 0 < log x := zero_lt_one.trans hL
  have hs0 : 0 < s := by linarith
  have hz : 1 ≤ (log x) ^ s := Real.one_le_rpow hL.le hs0.le
  have h := rankin_exponential_bound (T := threshold 1 x) (by linarith : 1 < s) hz hx0
  have hprimes : ((Icc 1 ⌊x⌋₊).filter Nat.Prime) = Nat.primesLE ⌊x⌋₊ := by
    rw [Nat.primesLE_eq_filter_Ioc_zero]
    congr 1
    ext p
    simp only [mem_Icc, mem_Ioc]
    omega
  rw [hprimes, prime_weight_split hL0 (log_le_sub_one_of_pos hx0 |>.trans (by linarith))
    hs0.le] at h
  have heq : s * log x - threshold 1 x * log ((log x) ^ s) +
      s * ((Nat.primeCounting ⌊log x⌋₊ : ℝ) * log (log x) - Chebyshev.theta (log x)) =
        s * budget (log x) := by
    rw [log_rpow hL0]
    dsimp only [threshold, scale, budget,
      D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel.primeCount]
    field_simp [(log_pos hL).ne']
    <;> ring
  have hcost : log (1 + ∑' n : ℕ, (n : ℝ) ^ (-s)) ≤ eulerCost := by
    apply log_le_log
    · positivity
    · exact add_le_add_left (pseries_le_square hs) 1
  change (tailCount 1 x : ℝ) ≤ _ at h
  refine h.trans (exp_le_exp.mpr ?_)
  linarith only [heq, hcost]

private lemma log_rpow_over_id_zero :
    Tendsto (fun P : ℝ => (log P * sqrt (log P)) / P) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (3 / 2 : ℝ)
    (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
  rw [rpow_one, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    rpow_add (log_pos hP), rpow_one, ← sqrt_eq_rpow]

/-- The second-threshold counting scale diverges. -/
theorem secondScale_top : Tendsto secondScale atTop atTop := by
  have hp : ∀ᶠ P : ℝ in atTop, 0 < (log P * sqrt (log P)) / P := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    exact div_pos (mul_pos (log_pos hP) (sqrt_pos.mpr (log_pos hP))) (by linarith)
  have h := tendsto_inv_nhdsGT_zero.comp
    (tendsto_nhdsWithin_iff.mpr ⟨log_rpow_over_id_zero, hp⟩)
  simpa only [secondScale, inv_div, Function.comp_def] using h.comp tendsto_log_atTop

/-- The budget contribution at the explicit saddle has coefficient pi/sqrt(3). -/
theorem saddle_budget_limit :
    Tendsto (fun P : ℝ =>
      saddle P * budget P / (P / (log P * sqrt (log P))))
      atTop (𝓝 (π / sqrt 3)) := by
  have h := budget_limit.const_mul (π / (2 * sqrt 3))
  convert h.congr' (show (fun P : ℝ =>
      π / (2 * sqrt 3) * (budget P / (P / log P ^ 2))) =ᶠ[atTop]
        (fun P => saddle P * budget P / (P / (log P * sqrt (log P)))) from ?_) using 1
  · field_simp
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    have hlog := log_pos hP
    dsimp only [saddle]
    field_simp [(show P ≠ 0 by linarith), hlog.ne', (sqrt_pos.mpr hlog).ne']
    nlinarith [sq_sqrt hlog.le]

private lemma saddle_top : Tendsto saddle atTop atTop := by
  have hc : 0 < π / (2 * sqrt 3) := by positivity
  exact (tendsto_const_mul_atTop_of_pos hc).mpr
    (tendsto_sqrt_atTop.comp tendsto_log_atTop)

/-- At the second threshold the integer count has upper coefficient two pi
over square root three on the finer logarithmic scale. -/
theorem result : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
    (tailCount 1 x : ℝ) ≤
      exp ((2 * π / sqrt 3 + ε) * log x / (log (log x)) ^ (3 / 2 : ℝ)) := by
  intro ε hε
  have hc : 0 < π / (2 * sqrt 3) := by positivity
  have hb := saddle_budget_limit.comp tendsto_log_atTop
  have he := secondScale_top.const_div_atTop eulerCost
  have hsum := (hb.add he).eventually_lt_const
    (by linarith : π / sqrt 3 + 0 < π / sqrt 3 + ε / 2)
  have hR := (MovingEstimate.moving_weight_upper hc (by linarith : 0 < ε / 2)).comp_tendsto
    tendsto_log_atTop
  have hcoef : π ^ 2 / (6 * (π / (2 * sqrt 3))) = π / sqrt 3 := by
    have hsqrt := sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hp := pi_pos.ne'
    have hs := (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
    field_simp
    nlinarith
  filter_upwards [hsum, hR,
    (saddle_top.comp tendsto_log_atTop).eventually_ge_atTop 2,
    eventually_gt_atTop (exp 1)] with x hsum hR hs hx
  have hx0 : 0 < x := (exp_pos 1).trans hx
  have hL : 1 < log x := (lt_log_iff_exp_lt hx0).mpr hx
  have hell : 0 < log (log x) := log_pos hL
  have hscale : 0 < secondScale x := by dsimp [secondScale]; positivity
  have hfront : saddle (log x) * budget (log x) + eulerCost ≤
      (π / sqrt 3 + ε / 2) * secondScale x := by
    have hsum' : (saddle (log x) * budget (log x) + eulerCost) / secondScale x <
        π / sqrt 3 + ε / 2 := by
      simpa only [secondScale, Function.comp_def, ← add_div] using hsum
    exact ((div_lt_iff₀ hscale).mp hsum').le
  have hrem : remainder (log x) (saddle (log x)) x ≤
      (π / sqrt 3 + ε / 2) * secondScale x := by
    simpa only [saddle, secondScale, hcoef] using hR x
  refine (rankin_reduction hx hs).trans (exp_le_exp.mpr ?_)
  have heq : (log (log x)) ^ (3 / 2 : ℝ) =
      log (log x) * sqrt (log (log x)) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add hell,
      rpow_one, ← sqrt_eq_rpow]
  rw [heq, show (2 * π / sqrt 3 + ε) * log x /
      (log (log x) * sqrt (log (log x))) =
      (2 * π / sqrt 3 + ε) * secondScale x by dsimp [secondScale]; ring]
  linarith only [hfront, hrem]

end D5.S3.Arith.Robin.Analytic.OmegaSecond.Upper
