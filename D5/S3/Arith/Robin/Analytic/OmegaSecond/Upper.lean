/- GID: D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaSecond/Upper
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rankin reduction at the exact second distinct-prime threshold. -/

import D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
import D5.S3.Arith.Robin.Analytic.OmegaSecond.Grid
import D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
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
theorem upper : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
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
  have hPpos : 0 < P := zero_lt_one.trans hP
  have hlogpos := log_pos hP
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
    have hPpos : 0 < P := zero_lt_one.trans hP
    have hlogpos := log_pos hP
    exact div_nonneg (rounding_error hP).1 (by positivity)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    have hPpos : 0 < P := zero_lt_one.trans hP
    have hlogpos := log_pos hP
    have hscale : 0 < P / log P ^ n := by positivity
    calc
      _ ≤ 1 / (P / log P ^ n) :=
        div_le_div_of_nonneg_right (rounding_error hP).2 hscale.le
      _ = _ := by rw [one_div_div]

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
  have hPpos : 0 < P := zero_lt_one.trans hP
  have hlogpos := log_pos hP
  have hscale : 0 < P / log P ^ 3 := by positivity
  have hd := (div_pos_iff_of_pos_right hscale).mp h
  change 0 < (Nat.primeCounting ⌊P⌋₊ : ℝ) - thresholdK P at hd
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
      have htri := abs_sub (primeCount (3 * P / 4) - (3 * P / 4) / log P)
        (primeCount (P / 2) - (P / 2) / log P)
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
    simpa only [one_div_pow, zero_pow (by decide : (2 : ℕ) ≠ 0)] using ((tendsto_log_atTop.const_div_atTop 1).pow 2)
  have hr : Tendsto (fun P : ℝ => (excess P : ℝ) / (P / log P)) atTop (𝓝 0) := by
    have h := excess_limit.mul hi
    norm_num only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne']
    <;> ring
  filter_upwards [hr.eventually_lt reserve_limit (by norm_num : (0 : ℝ) < 1 / 4),
    eventually_gt_atTop (1 : ℝ)] with P h hP
  have hPpos : 0 < P := zero_lt_one.trans hP
  have hlogpos := log_pos hP
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

/-- Width scale of a fixed logarithmic prime box at a moving saddle. -/
def boxScale (c P : ℝ) : ℝ := P / (log P * (c * sqrt (log P)))

private lemma boxScale_top {c : ℝ} (hc : 0 < c) :
    Tendsto (boxScale c) atTop atTop := by
  have h : Tendsto (fun P : ℝ => P / (log P * sqrt (log P))) atTop atTop := by
    have hp : ∀ᶠ P : ℝ in atTop, 0 < (log P * sqrt (log P)) / P := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
      have hPpos : 0 < P := zero_lt_one.trans hP
      have hlogpos := log_pos hP
      positivity
    have h := tendsto_inv_nhdsGT_zero.comp
      (tendsto_nhdsWithin_iff.mpr ⟨log_rpow_over_id_zero, hp⟩)
    simpa only [inv_div, Function.comp_def] using h
  convert h.atTop_div_const hc using 1
  ext P
  dsimp only [boxScale]
  ring

private lemma exp_saddle_difference {c : ℝ} (hc : 0 < c) (t : ℝ) :
    Tendsto (fun P : ℝ => (exp (t / (c * sqrt (log P))) - 1) *
      (c * sqrt (log P))) atTop (𝓝 t) := by
  have hs : Tendsto (fun P : ℝ => c * sqrt (log P)) atTop atTop :=
    (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_mul_atTop hc
  by_cases ht : t = 0
  · subst t
    simp
  have hi : Tendsto (fun P : ℝ => t / (c * sqrt (log P))) atTop (𝓝[≠] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hs.const_div_atTop t, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact div_ne_zero ht (mul_ne_zero hc.ne' (sqrt_pos.mpr (log_pos hP)).ne')
  have h := ((hasDerivAt_exp (0 : ℝ)).tendsto_slope_zero.comp hi).mul_const t
  norm_num only [exp_zero, one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
  simp only [Function.comp_def, zero_add, smul_eq_mul]
  field_simp [ht, hc.ne', (sqrt_pos.mpr (log_pos hP)).ne']
  <;> ring

private lemma central_endpoint {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ∀ᶠ P : ℝ in atTop, P * exp (t / (c * sqrt (log P))) ∈ Set.Icc (P / 2) (2 * P) := by
  have hs : Tendsto (fun P : ℝ => c * sqrt (log P)) atTop atTop :=
    (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_mul_atTop hc
  have he := (hs.const_div_atTop t).rexp
  rw [exp_zero] at he
  filter_upwards [he.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1),
    he.eventually_lt_const (by norm_num : (1 : ℝ) < 2),
    eventually_gt_atTop (1 : ℝ)] with P hlo hhi hP
  have hp : 0 < P := by linarith
  constructor <;> nlinarith

private lemma box_count_limit {c a b : ℝ} (hc : 0 < c) (hab : a ≤ b) :
    Tendsto (fun P : ℝ =>
      ((primeInterval (P * exp (a / (c * sqrt (log P))))
        (P * exp (b / (c * sqrt (log P))))).card : ℝ) / boxScale c P)
      atTop (𝓝 (b - a)) := by
  let A (P : ℝ) := P * exp (a / (c * sqrt (log P)))
  let B (P : ℝ) := P * exp (b / (c * sqrt (log P)))
  have hm := (exp_saddle_difference hc b).sub (exp_saddle_difference hc a)
  have hi : Tendsto (fun P : ℝ => 56 * c / sqrt (log P)) atTop (𝓝 0) :=
    (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_div_atTop (56 * c)
  have he : Tendsto (fun P : ℝ =>
      (((primeInterval (A P) (B P)).card : ℝ) - (B P - A P) / log P) / boxScale c P)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hi
    filter_upwards [central_prime_counting_bound, central_endpoint hc a,
      central_endpoint hc b, eventually_gt_atTop (1 : ℝ)] with P h ha hb hP
    have hp : 0 < P := by linarith
    have hl := log_pos hP
    have hr := sqrt_pos.mpr hl
    have hab' : A P ≤ B P := by
      dsimp only [A, B]
      gcongr
    have hcard := primeInterval_card hab'
    have h1 := h (A P) ha
    have h2 := h (B P) hb
    have herror : |((primeInterval (A P) (B P)).card : ℝ) - (B P - A P) / log P| ≤
        56 * (P / log P ^ 2) := by
      rw [hcard]
      have ht := abs_sub (primeCount (B P) - B P / log P)
        (primeCount (A P) - A P / log P)
      have hid : (primeCount (B P) - B P / log P) -
          (primeCount (A P) - A P / log P) =
          (primeCount (B P) - primeCount (A P)) - (B P - A P) / log P := by ring
      rw [hid] at ht
      linarith
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (show 0 < boxScale c P by dsimp [boxScale]; positivity)]
    apply (div_le_iff₀ (show 0 < boxScale c P by dsimp [boxScale]; positivity)).mpr
    convert herror using 1
    dsimp only [boxScale]
    have hh := sq_sqrt hl.le
    field_simp [hp.ne', hl.ne', hr.ne']
    nlinarith
  have h := he.add hm
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
  dsimp only [A, B, boxScale]
  field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne', hc.ne',
    (sqrt_pos.mpr (log_pos hP)).ne']
  <;> ring

/-- Prime boxes below and above the real center, with half-open endpoints. -/
def negativeBox (G : Grid.Mesh) (c P : ℝ) (i : Fin G.n) : Finset ℕ :=
  primeInterval (P * exp (-G.node (i + 1) / (c * sqrt (log P))))
    (P * exp (-G.node i / (c * sqrt (log P))))

def positiveBox (G : Grid.Mesh) (c P : ℝ) (i : Fin G.n) : Finset ℕ :=
  primeInterval (P * exp (G.node i / (c * sqrt (log P))))
    (P * exp (G.node (i + 1) / (c * sqrt (log P))))

def capacity (G : Grid.Mesh) (c P : ℝ) (i : Fin G.n) : ℕ :=
  min (negativeBox G c P i).card (positiveBox G c P i).card

def occupancy (G : Grid.Mesh) (c P : ℝ) (i : Fin G.n) : ℕ :=
  ⌊Grid.logistic (G.node (i + 1)) * (capacity G c P i : ℝ)⌋₊

def exchangeCost (G : Grid.Mesh) (c P : ℝ) : ℝ :=
  (2 / (c * sqrt (log P))) * ∑ i, G.node (i + 1) * (occupancy G c P i : ℝ)

def entropyEstimate (G : Grid.Mesh) (c P : ℝ) : ℝ :=
  2 * ∑ i, Entropy.entropyLower (capacity G c P i) (occupancy G c P i)

private lemma mesh_step_pos (G : Grid.Mesh) : 0 < G.step :=
  div_pos G.U_pos (by exact_mod_cast G.n_pos)

private lemma mesh_node_mono (G : Grid.Mesh) : Monotone G.node := by
  intro i j hij
  dsimp [Grid.Mesh.node]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (mesh_step_pos G).le

private lemma mesh_width (G : Grid.Mesh) (i : ℕ) : G.node (i + 1) - G.node i = G.step := by
  dsimp [Grid.Mesh.node]
  push_cast
  ring

private lemma capacity_limit (G : Grid.Mesh) {c : ℝ} (hc : 0 < c) (i : Fin G.n) :
    Tendsto (fun P : ℝ => (capacity G c P i : ℝ) / boxScale c P) atTop (𝓝 G.step) := by
  have hn := box_count_limit hc (neg_le_neg (mesh_node_mono G (Nat.le_succ (i : ℕ))))
  have hp := box_count_limit hc (mesh_node_mono G (Nat.le_succ (i : ℕ)))
  have hn' : Tendsto (fun P : ℝ => ((negativeBox G c P i).card : ℝ) / boxScale c P)
      atTop (𝓝 G.step) := by
    convert hn using 1
    dsimp only [negativeBox]
    all_goals simp only [neg_sub_neg, mesh_width]
  have hp' : Tendsto (fun P : ℝ => ((positiveBox G c P i).card : ℝ) / boxScale c P)
      atTop (𝓝 G.step) := by
    simpa only [positiveBox, mesh_width] using hp
  exact Entropy.min_scaled _ _ _ (boxScale_top hc) hn' hp'

private lemma occupancy_fits (G : Grid.Mesh) (c P : ℝ) (i : Fin G.n) :
    occupancy G c P i ≤ capacity G c P i := by
  have hq0 : 0 ≤ Grid.logistic (G.node (i + 1)) := by dsimp [Grid.logistic]; positivity
  have hq1 : Grid.logistic (G.node (i + 1)) ≤ 1 := by
    dsimp [Grid.logistic]
    exact (inv_le_one₀ (by positivity)).mpr (by linarith [exp_pos (G.node (i+1))])
  have h := Nat.floor_le (mul_nonneg hq0 (Nat.cast_nonneg (capacity G c P i)))
  have h' : (occupancy G c P i : ℝ) ≤ capacity G c P i := by
    exact h.trans (by nlinarith [Nat.cast_nonneg (capacity G c P i)])
  exact_mod_cast h'

private lemma occupancy_limit (G : Grid.Mesh) {c : ℝ} (hc : 0 < c) (i : Fin G.n) :
    Tendsto (fun P : ℝ => (occupancy G c P i : ℝ) / boxScale c P)
      atTop (𝓝 (G.step * Grid.logistic (G.node (i + 1)))) := by
  simpa only [occupancy, mul_comm] using Entropy.floor_scaled (boxScale c)
    (fun P => capacity G c P i) (boxScale_top hc) (mesh_step_pos G)
    (show 0 ≤ Grid.logistic (G.node (i+1)) by dsimp [Grid.logistic]; positivity)
    (capacity_limit G hc i)

private lemma entropyEstimate_limit (G : Grid.Mesh) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun P : ℝ => entropyEstimate G c P / boxScale c P) atTop (𝓝 G.mass) := by
  have h := (tendsto_finset_sum univ (fun i (_ : i ∈ (univ : Finset (Fin G.n))) =>
    Entropy.entropy_lower_scaled (boxScale c) (fun P => capacity G c P i)
      (fun P => occupancy G c P i) (boxScale_top hc) (mesh_step_pos G)
      (capacity_limit G hc i) (occupancy_limit G hc i))).const_mul 2
  convert h using 1
  · ext P
    dsimp only [entropyEstimate]
    rw [mul_div_assoc, sum_div]
  · dsimp only [Grid.Mesh.mass]
    rw [← Fin.sum_univ_eq_sum_range]
    rfl

private lemma exchangeCost_limit (G : Grid.Mesh) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun P : ℝ => exchangeCost G c P / coreBudget P)
      atTop (𝓝 (G.cost / (2 * c ^ 2))) := by
  have hsum := tendsto_finset_sum univ (fun i (_ : i ∈ (univ : Finset (Fin G.n))) =>
    (occupancy_limit G hc i).const_mul (G.node (i + 1)))
  have h := ((hsum.const_mul (2 / c ^ 2)).div coreBudget_limit (by norm_num : (2 : ℝ) ≠ 0))
  convert h.congr' (show (fun P : ℝ =>
      (2 / c ^ 2 * ∑ i : Fin G.n, G.node (i+1) *
        ((occupancy G c P i : ℝ) / boxScale c P)) / (coreBudget P / (P / log P ^ 2)))
      =ᶠ[atTop] (fun P => exchangeCost G c P / coreBudget P) from ?_) using 1
  · dsimp only [Grid.Mesh.cost]
    rw [← Fin.sum_univ_eq_sum_range]
    rw [mul_sum]
    ring
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    have hl := log_pos hP
    have hr := sqrt_pos.mpr hl
    dsimp only [boxScale, exchangeCost]
    simp_rw [← mul_div_assoc]
    rw [← sum_div]
    have hr2 := sq_sqrt hl.le
    field_simp [(show P ≠ 0 by linarith), hl.ne', hc.ne', hr.ne']
    nlinarith

private lemma entropyEstimate_le_log_choices (G : Grid.Mesh) (c P : ℝ) :
    entropyEstimate G c P ≤
      log (∏ i : Fin G.n, ((capacity G c P i).choose (occupancy G c P i)) ^ 2 : ℕ) := by
  have hp (i : Fin G.n) : (0 : ℝ) < (capacity G c P i).choose (occupancy G c P i) := by
    exact_mod_cast Nat.choose_pos (occupancy_fits G c P i)
  rw [Nat.cast_prod, log_prod (fun i _ => by push_cast; positivity)]
  simp_rw [Nat.cast_pow, log_pow]
  dsimp only [entropyEstimate, Entropy.entropyLower]
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left
    (Entropy.log_choose_ge_binEntropy _ _ (occupancy_fits G c P i)) (by norm_num)

/-- Each accuracy is achieved by one grid fixed independently of the prime center. -/
theorem fixed_grid_exists (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∃ G : Grid.Mesh, ∀ᶠ P : ℝ in atTop,
      exchangeCost G c P ≤ coreBudget P ∧
      (2 * π / sqrt 3 - ε) * (P / (log P * sqrt (log P))) ≤
        log (∏ i : Fin G.n, ((capacity G c P i).choose (occupancy G c P i)) ^ 2 : ℕ) := by
  let K : ℝ := 2 * π / sqrt 3
  let c₀ : ℝ := π / (2 * sqrt 3)
  let η : ℝ := ε / (8 * K)
  let ρ : ℝ := ε * c₀ / 8
  have hK : 0 < K := by dsimp [K]; positivity
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  obtain ⟨G, hcost, hmass⟩ := Grid.exists_good_grid hη hρ
  let c : ℝ := (1 + η) * c₀
  have hc : 0 < c := by dsimp [c]; positivity
  have hA : 2 * c ^ 2 = (π ^ 2 / 6) * (1 + η) ^ 2 := by
    dsimp [c, c₀]
    have hs := sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    field_simp
    nlinarith
  have hstrict : G.cost / (2 * c ^ 2) < 1 := by
    apply (div_lt_one (by positivity : 0 < 2 * c ^ 2)).mpr
    rw [hA]
    have hpi : 0 < π ^ 2 / 6 := by positivity
    have hgap : 1 + η / 2 < (1 + η) ^ 2 := by nlinarith
    exact hcost.trans_lt (mul_lt_mul_of_pos_left hgap hpi)
  have hBc : π ^ 2 / 3 = K * c₀ := by
    dsimp [K, c₀]
    have hs := sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    field_simp
    nlinarith
  have hηK : K * η = ε / 8 := by dsimp [η]; field_simp; ring
  have hcoef : K - ε / 2 < G.mass / c := by
    apply (lt_div_iff₀ hc).mpr
    have haux : (K - ε / 2) * (1 + η) < K - ε / 8 := by
      nlinarith [mul_pos hε hη]
    have haux' := mul_lt_mul_of_pos_right haux hc₀
    dsimp only [c]
    rw [hBc] at hmass
    dsimp only [ρ] at hmass
    nlinarith
  have he : Tendsto (fun P : ℝ => entropyEstimate G c P / (P / (log P * sqrt (log P))))
      atTop (𝓝 (G.mass / c)) := by
    apply ((entropyEstimate_limit G hc).div_const c).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    dsimp only [boxScale]
    field_simp [hc.ne', (log_pos hP).ne',
      (sqrt_pos.mpr (log_pos hP)).ne', (show P ≠ 0 by linarith)]
    <;> ring
  refine ⟨c, hc, G, ?_⟩
  filter_upwards [(exchangeCost_limit G hc).eventually_lt_const hstrict,
    coreBudget_limit.eventually_const_lt (by norm_num : (0 : ℝ) < 2),
    he.eventually_const_lt (show K - ε < G.mass / c by linarith),
    eventually_gt_atTop (1 : ℝ)] with P hV hD hE hP
  have hp : 0 < P := zero_lt_one.trans hP
  have hl := log_pos hP
  have hscale : 0 < P / (log P * sqrt (log P)) := by positivity
  have hDpos : 0 < coreBudget P :=
    (div_pos_iff_of_pos_right (show 0 < P / log P ^ 2 by positivity)).mp hD
  constructor
  · exact ((div_lt_one hDpos).mp hV).le
  · change (K - ε) * (P / (log P * sqrt (log P))) ≤ _
    exact ((lt_div_iff₀ hscale).mp hE).le.trans (entropyEstimate_le_log_choices G c P)

private lemma choices_le_tail (G : Grid.Mesh) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ P : ℝ in atTop, exchangeCost G c P ≤ coreBudget P →
      (∏ i : Fin G.n, ((capacity G c P i).choose (occupancy G c P i)) ^ 2 : ℕ) ≤
        tailCount 1 (exp P) := by
  have hs : Tendsto (fun P : ℝ => c * sqrt (log P)) atTop atTop :=
    (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_mul_atTop hc
  have hf := (hs.const_div_atTop (-G.node G.n)).rexp
  rw [exp_zero] at hf
  filter_upwards [trimmed_core, hf.eventually_const_lt (by norm_num : (3 / 4 : ℝ) < 1),
    eventually_gt_atTop (1 : ℝ)] with P hcore hfar hP
  intro hV
  obtain ⟨R, hR, hcard, hsize, hbase⟩ := hcore
  have hp : 0 < P := zero_lt_one.trans hP
  have hl := log_pos hP
  have hspos : 0 < c * sqrt (log P) := by positivity
  have hfar' : 3 * P / 4 ≤ P * exp (-G.node G.n / (c * sqrt (log P))) := by nlinarith
  have hthreshold : threshold 1 (exp P) < ((Nat.primesLE ⌊P⌋₊ \ R).card : ℝ) := by
    rw [hsize]
    have h := Nat.lt_floor_add_one (P / log P + P / log P ^ 2)
    simpa only [threshold, scale, log_exp, thresholdK, Nat.cast_add, Nat.cast_one,
      one_mul, div_div, pow_two] using h
  have hcount := Exchange.logarithmic_exchange_bound G.n P (c * sqrt (log P)) G.node R
    hp hspos (mesh_node_mono G) (by simp [Grid.Mesh.node]) hfar' hR
    (occupancy G c P) (coreBudget P) 1 (exp P) hbase hV hthreshold
    (by rw [log_exp]) (exp_pos P)
  apply le_trans _ hcount
  apply prod_le_prod'
  intro i _
  have hn := Nat.choose_le_choose (occupancy G c P i)
    (min_le_left (negativeBox G c P i).card (positiveBox G c P i).card)
  have hp' := Nat.choose_le_choose (occupancy G c P i)
    (min_le_right (negativeBox G c P i).card (positiveBox G c P i).card)
  simpa only [pow_two, capacity, negativeBox, positiveBox] using Nat.mul_le_mul hn hp'

/-- The lower coefficient at the strict second distinct-prime threshold. -/
theorem lower : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop,
    (2 * π / sqrt 3 - ε) * log x / (log (log x)) ^ (3 / 2 : ℝ) ≤
      log (tailCount 1 x : ℝ) := by
  intro ε hε
  obtain ⟨c, hc, G, hgrid⟩ := fixed_grid_exists ε hε
  have hP : ∀ᶠ P : ℝ in atTop,
      (2 * π / sqrt 3 - ε) * (P / (log P * sqrt (log P))) ≤
        log (tailCount 1 (exp P) : ℝ) := by
    filter_upwards [hgrid, choices_le_tail G hc] with P hgrid hcount
    have hchoose : 0 < (∏ i : Fin G.n,
        ((capacity G c P i).choose (occupancy G c P i)) ^ 2 : ℕ) := by
      exact prod_pos (fun i _ => pow_pos (Nat.choose_pos (occupancy_fits G c P i)) _)
    exact hgrid.2.trans (log_le_log (by exact_mod_cast hchoose)
      (by exact_mod_cast hcount hgrid.1))
  filter_upwards [tendsto_log_atTop.eventually hP, eventually_gt_atTop (exp 1)] with x hx hx1
  have hx0 : 0 < x := (exp_pos 1).trans hx1
  have hell : 0 < log (log x) := log_pos ((lt_log_iff_exp_lt hx0).mpr hx1)
  rw [exp_log hx0] at hx
  rw [show (log (log x)) ^ (3 / 2 : ℝ) = log (log x) * sqrt (log (log x)) by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add hell,
      rpow_one, ← sqrt_eq_rpow]]
  simpa only [mul_div_assoc] using hx

/-- The exact second-threshold logarithmic counting limit. -/
theorem result :
    Tendsto (fun x : ℝ => log (tailCount 1 x : ℝ) /
      (log x / (log (log x)) ^ (3 / 2 : ℝ))) atTop (𝓝 (2 * π / sqrt 3)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hK : 0 < 2 * π / sqrt 3 := by positivity
  filter_upwards [lower (ε / 2) (by positivity), lower (π / sqrt 3) (by positivity),
    upper (ε / 2) (by positivity), eventually_gt_atTop (exp 1)] with x hlo hpositive hup hx
  have hx0 : 0 < x := (exp_pos 1).trans hx
  have hL : 1 < log x := (lt_log_iff_exp_lt hx0).mpr hx
  have hell : 0 < log (log x) := log_pos hL
  have hy : 0 < log x / (log (log x)) ^ (3 / 2 : ℝ) :=
    div_pos (zero_lt_one.trans hL) (rpow_pos_of_pos hell _)
  have hn : 0 < (tailCount 1 x : ℝ) := by
    by_contra h
    have hz : (tailCount 1 x : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
    rw [hz, log_zero] at hpositive
    have hp := mul_pos (show 0 < 2 * π / sqrt 3 - π / sqrt 3 by positivity) hy
    rw [mul_div_assoc] at hpositive
    linarith
  have hlog := log_le_log hn hup
  rw [log_exp, mul_div_assoc] at hlog
  rw [mul_div_assoc] at hlo
  have hhi := (div_le_iff₀ hy).mpr hlog
  have hlo' := (le_div_iff₀ hy).mpr hlo
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end D5.S3.Arith.Robin.Analytic.OmegaSecond.Upper
