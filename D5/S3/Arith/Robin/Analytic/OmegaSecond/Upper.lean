/- GID: D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaSecond/Upper
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rankin reduction at the exact second distinct-prime threshold. -/

import D5.S3.Arith.Robin.Analytic.OmegaTail.Selection
import D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingWeight
import D5.S3.Arith.Robin.Analytic.OmegaSecond.MovingEstimate

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter Finset
open scoped Topology BigOperators
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open D5.S3.Arith.Robin.Analytic.OmegaTail.Selection

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
    · simpa only [add_comm] using add_le_add_left (pseries_le_square hs) 1
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
  change Tendsto (fun x : ℝ => log x / (log (log x) * sqrt (log (log x)))) atTop atTop
  simpa only [inv_div, Function.comp_def] using h.comp tendsto_log_atTop

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
    generalize hr : sqrt (log P) = r
    have hr0 : 0 < r := by rw [← hr]; exact sqrt_pos.mpr hlog
    have hr2 : r ^ 2 = log P := by rw [← hr]; exact sq_sqrt hlog.le
    rw [← hr2]
    field_simp [(show P ≠ 0 by linarith), hr0.ne']
    <;> ring

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
  have hR := tendsto_log_atTop.eventually
    (MovingEstimate.moving_weight_upper hc (by linarith : 0 < ε / 2))
  have hcoef : π ^ 2 / (6 * (π / (2 * sqrt 3))) = π / sqrt 3 := by
    have hsqrt := sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hp := pi_pos.ne'
    have hs := (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
    field_simp [hp, hs]
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
  simp only [Function.comp_def]
  calc
    _ = (saddle (log x) * budget (log x) + eulerCost) +
        remainder (log x) (saddle (log x)) x := by ring
    _ ≤ (π / sqrt 3 + ε / 2) * secondScale x +
        (π / sqrt 3 + ε / 2) * secondScale x := add_le_add hfront hrem
    _ = _ := by ring

/-- The integer strictly above the second threshold at the real prime center. -/
def thresholdK (P : ℝ) : ℕ := ⌊P / log P + P / log P ^ 2⌋₊ + 1

/-- The number of primes removed far below the active boxes. -/
def excess (P : ℝ) : ℕ := Nat.primeCounting ⌊P⌋₊ - thresholdK P

/-- The deterministic budget guaranteed after the remote deletion. -/
def coreBudget (P : ℝ) : ℝ :=
  P - Chebyshev.theta P + (excess P : ℝ) * log (P / 2)

private lemma inverse_log_scale (n : ℕ) :
    Tendsto (fun P : ℝ => log P ^ n / P) atTop (𝓝 0) := by
  simpa only [rpow_natCast, rpow_one] using
    (isLittleO_log_rpow_rpow_atTop (n : ℝ)
      (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero

private lemma rounding_error {P : ℝ} (hP : 1 < P) :
    0 ≤ (thresholdK P : ℝ) - (P / log P + P / log P ^ 2) ∧
    (thresholdK P : ℝ) - (P / log P + P / log P ^ 2) ≤ 1 := by
  have hpos : 0 ≤ P / log P + P / log P ^ 2 := by positivity
  have hl := Nat.floor_le hpos
  have hu := Nat.lt_floor_add_one (P / log P + P / log P ^ 2)
  simp only [thresholdK, Nat.cast_add, Nat.cast_one]
  exact ⟨by linarith, by linarith⟩

private lemma rounding_scaled (n : ℕ) :
    Tendsto (fun P : ℝ =>
      ((thresholdK P : ℝ) - (P / log P + P / log P ^ 2)) /
        (P / log P ^ n)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (inverse_log_scale n)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    exact div_nonneg (rounding_error hP).1 (by positivity)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    have hscale : 0 < P / log P ^ n := by positivity
    calc
      _ ≤ 1 / (P / log P ^ n) :=
        div_le_div_of_nonneg_right (rounding_error hP).2 hscale.le
      _ = _ := by ring

private lemma excess_real_limit :
    Tendsto (fun P : ℝ =>
      (D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel.primeCount P - thresholdK P) /
        (P / log P ^ 3)) atTop (𝓝 2) := by
  have hi : Tendsto (fun P : ℝ => 1 / log P) atTop (𝓝 0) :=
    tendsto_log_atTop.const_div_atTop 1
  have h := ((prime_counting_three_terms.mul hi).add_const 2).sub (rounding_scaled 3)
  norm_num only [mul_zero, zero_add, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
  dsimp only [countingThreeTerms]
  field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne']
  <;> ring

/-- There are eventually enough primes at the real center for the strict threshold. -/
theorem thresholdK_le_primeCount :
    ∀ᶠ P : ℝ in atTop, thresholdK P ≤ Nat.primeCounting ⌊P⌋₊ := by
  filter_upwards [excess_real_limit.eventually_const_lt (by norm_num : (0 : ℝ) < 2),
    eventually_gt_atTop (1 : ℝ)] with P h hP
  have hscale : 0 < P / log P ^ 3 := by positivity
  have hd := (div_pos_iff_of_pos_right hscale).mp h
  exact_mod_cast (sub_pos.mp hd).le

/-- The remote deletion has asymptotic size 2P/log(P)^3. -/
theorem excess_limit :
    Tendsto (fun P : ℝ => (excess P : ℝ) / (P / log P ^ 3)) atTop (𝓝 2) := by
  apply excess_real_limit.congr'
  filter_upwards [thresholdK_le_primeCount] with P hP
  simp only [excess, Nat.cast_sub hP,
    D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel.primeCount]

/-- The cost saved by remote deletion has the same leading budget as Rankin's expression. -/
theorem coreBudget_limit :
    Tendsto (fun P : ℝ => coreBudget P / (P / log P ^ 2)) atTop (𝓝 2) := by
  have hi : Tendsto (fun P : ℝ => log 2 / log P) atTop (𝓝 0) :=
    tendsto_log_atTop.const_div_atTop (log 2)
  have h := (budget_limit.sub (rounding_scaled 3)).sub (excess_limit.mul hi)
  norm_num only [sub_zero, mul_zero] at h
  apply h.congr'
  filter_upwards [thresholdK_le_primeCount, eventually_gt_atTop (1 : ℝ)] with P hk hP
  have hp : P ≠ 0 := by linarith
  rw [coreBudget, log_div hp (by norm_num : (2 : ℝ) ≠ 0)]
  dsimp only [budget, excess, D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel.primeCount]
  rw [Nat.cast_sub hk]
  field_simp [hp, (log_pos hP).ne']
  <;> ring

/-- A reserve separated from every fixed active logarithmic box. -/
def reserve (P : ℝ) : Finset ℕ := primeInterval (P / 2) (3 * P / 4)

private lemma reserve_limit :
    Tendsto (fun P : ℝ => ((reserve P).card : ℝ) / (P / log P))
      atTop (𝓝 (1 / 4 : ℝ)) := by
  have hi : Tendsto (fun P : ℝ => 56 / log P) atTop (𝓝 0) :=
    tendsto_log_atTop.const_div_atTop 56
  have he : Tendsto (fun P : ℝ =>
      ((reserve P).card : ℝ) / (P / log P) - 1 / 4) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hi
    filter_upwards [central_prime_counting_bound, eventually_gt_atTop (1 : ℝ)] with P h hP
    have hp : 0 < P := by linarith
    have hl := log_pos hP
    have h1 := h (P / 2) ⟨le_rfl, by linarith⟩
    have h2 := h (3 * P / 4) ⟨by linarith, by linarith⟩
    have heq := primeInterval_card (show P / 2 ≤ 3 * P / 4 by linarith)
    change ((reserve P).card : ℝ) = _ at heq
    rw [Real.norm_eq_abs, heq]
    have habs : |(primeCount (3 * P / 4) - primeCount (P / 2)) - P / (4 * log P)| ≤
        56 * (P / log P ^ 2) := by
      have htri := abs_sub_le (primeCount (3 * P / 4) - (3 * P / 4) / log P)
        (primeCount (P / 2) - (P / 2) / log P) 0
      rw [sub_zero, sub_zero] at htri
      have hid : (primeCount (3 * P / 4) - (3 * P / 4) / log P) -
          (primeCount (P / 2) - (P / 2) / log P) =
          (primeCount (3 * P / 4) - primeCount (P / 2)) - P / (4 * log P) := by ring
      rw [hid] at htri
      linarith
    have hid : (primeCount (3 * P / 4) - primeCount (P / 2)) / (P / log P) - 1 / 4 =
        ((primeCount (3 * P / 4) - primeCount (P / 2)) - P / (4 * log P)) / (P / log P) := by
      field_simp [hp.ne', hl.ne']
      <;> ring
    rw [hid, abs_div, abs_of_pos (div_pos hp hl)]
    apply (div_le_iff₀ (div_pos hp hl)).mpr
    convert habs using 1 <;> field_simp [hl.ne'] <;> ring
  have h := he.add_const (1 / 4 : ℝ)
  simpa only [sub_add_cancel, zero_add] using h

private lemma reserve_enough :
    ∀ᶠ P : ℝ in atTop, excess P ≤ (reserve P).card := by
  have hi : Tendsto (fun P : ℝ => 1 / log P ^ 2) atTop (𝓝 0) := by
    simpa only [one_pow] using ((tendsto_log_atTop.const_div_atTop 1).pow 2)
  have hr : Tendsto (fun P : ℝ => (excess P : ℝ) / (P / log P)) atTop (𝓝 0) := by
    have h := excess_limit.mul hi
    norm_num only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne']
    <;> ring
  filter_upwards [hr.eventually_lt reserve_limit (by norm_num : (0 : ℝ) < 1 / 4),
    eventually_gt_atTop (1 : ℝ)] with P h hP
  have hscale : 0 < P / log P := by positivity
  exact_mod_cast ((div_lt_div_iff_of_pos_right hscale).mp h).le

/-- A remote deletion gives an actual prime base with the exact threshold size
and the deterministic logarithmic budget. -/
private theorem trimmed_core :
    ∀ᶠ P : ℝ in atTop, ∃ R : Finset ℕ,
      R ⊆ reserve P ∧ R.card = excess P ∧
      (Nat.primesLE ⌊P⌋₊ \ R).card = thresholdK P ∧
      (∑ p ∈ Nat.primesLE ⌊P⌋₊ \ R, log (p : ℝ)) ≤ P - coreBudget P := by
  filter_upwards [reserve_enough, thresholdK_le_primeCount,
    eventually_gt_atTop (1 : ℝ)] with P hR hk hP
  obtain ⟨R, hsub, hcard⟩ := exists_subset_card_eq hR
  have hsub' : R ⊆ Nat.primesLE ⌊P⌋₊ := by
    intro p hp
    obtain ⟨hmem, hprime⟩ := mem_filter.mp (hsub hp)
    apply Nat.mem_primesLE.mpr
    exact ⟨(mem_Ioc.mp hmem).2.trans (Nat.floor_mono (by linarith : 3 * P / 4 ≤ P)), hprime⟩
  refine ⟨R, hsub, hcard, ?_, ?_⟩
  · rw [card_sdiff_of_subset hsub', Nat.primesLE_card_eq_primeCounting, hcard, excess]
    omega
  · have hsum : (∑ p ∈ R, log (p : ℝ)) +
        (∑ p ∈ Nat.primesLE ⌊P⌋₊ \ R, log (p : ℝ)) = Chebyshev.theta P := by
      rw [add_comm, sum_sdiff hsub', Chebyshev.theta_eq_sum_primesLE]
    have hsumlo : (excess P : ℝ) * log (P / 2) ≤ ∑ p ∈ R, log (p : ℝ) := by
      rw [← hcard]
      calc
        _ = ∑ _p ∈ R, log (P / 2) := by simp
        _ ≤ _ := by
          apply sum_le_sum
          intro p hp
          have hpmem := (mem_Ioc.mp (mem_filter.mp (hsub hp)).1).1
          exact log_le_log (by positivity : 0 < P / 2) (Nat.lt_of_floor_lt hpmem).le
    dsimp only [coreBudget]
    linarith

end D5.S3.Arith.Robin.Analytic.OmegaSecond.Upper
