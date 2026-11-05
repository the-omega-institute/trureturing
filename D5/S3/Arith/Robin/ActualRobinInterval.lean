/- GID: D5/S3/Arith/Robin/ActualRobinInterval
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualRobinInterval
   mirror-E: none(waiver:general-analytic-results-no-numerical-evidence-artifact)
   anchors: []
   utility: none
   digest: General optimizer interval transfer and original Robin reductions conditional on the unpaid all-price endpoint estimates. -/

/-
The original Robin margin is transferred between same-price optimizers
using the sigma/n support line, optimizer tie equality, and proved strict
concavity of gamma + log(log A). The log-log composition argument follows
the local infrastructure of ThresholdChainReduction.

EndpointRobinEstimates remains an explicit all-price obligation. The finite
branch identifies the actual 5040 boundary and consumes the existing finite
Robin theorem. The same boundary proof is reused by the upper-price range
reduction, which covers every original integer through maximalInteger(q0)
from actual endpoint margins at prices q>=q0. Every positive price and all
simultaneous ties remain in their original domains.
-/

import D5.S3.Arith.Robin.ActualGlobalBracketing
import D5.S3.Arith.Robin.FewDistinctPrimes
import D5.S3.Arith.GoldenResource.ThresholdChainReduction

import D5.S3.Arith.Robin.LogarithmBounds
import D5.S3.Arith.GoldenResource.GoldenResourceSupremum
import D5.S3.Arith.GoldenResource.HarmonicGammaUpperTail
import D5.S3.Arith.GoldenLayerMarginalDecay
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Ring.GeomSum
import D5.S3.Arith.GoldenResource.DirectedLogarithmBounds

noncomputable section

namespace D5.S3.Arith.Robin.ActualRobinInterval

open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.ActualGlobalBracketing
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenLayerMarginalDecay
open D5.S3.Arith.GoldenResource5040PriceInterval
open D5.S3.Weil.GronwallLowerEnvelope

/-- The ORIGINAL Robin threshold as a function of A = log n. -/
def robinThreshold (A : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log (Real.log A)

theorem margin_eq_threshold_sub_W (n : ℕ) :
    robinLogMargin n = robinThreshold (Real.log n) - W n := rfl

/-- Reuse the composition argument in ThresholdChainReduction's private
local infrastructure; the desired Jensen inequality is NOT a premise. -/
theorem loglog_strictConcaveOn :
    StrictConcaveOn ℝ (Set.Ioi (1 : ℝ)) (fun A => Real.log (Real.log A)) := by
  have himage : Real.log '' Set.Ioi (1 : ℝ) ⊆ Set.Ioi 0 := by
    rintro _ ⟨z, hz, rfl⟩
    exact Real.log_pos hz
  have hinner : StrictConcaveOn ℝ (Set.Ioi (1 : ℝ)) Real.log :=
    StrictConcaveOn.subset strictConcaveOn_log_Ioi
      (by intro z hz; change 1 < z at hz; change 0 < z; linarith)
      (convex_Ioi (1 : ℝ))
  have houter : StrictConcaveOn ℝ (Real.log '' Set.Ioi (1 : ℝ)) Real.log := by
    simpa only [Real.image_log_Ioi zero_lt_one, Real.log_one] using
      strictConcaveOn_log_Ioi
  have hmono : StrictMonoOn Real.log (Real.log '' Set.Ioi (1 : ℝ)) :=
    Real.strictMonoOn_log.mono himage
  exact houter.comp hinner hmono (Real.strictMonoOn_log.mono
    (by intro z hz; change 1 < z at hz; change 0 < z; linarith)).injOn

/-- Gamma is retained as an absolute additive anchor. -/
theorem threshold_strictConcaveOn :
    StrictConcaveOn ℝ (Set.Ioi (1 : ℝ)) robinThreshold := by
  refine ⟨convex_Ioi (1 : ℝ), ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hh := loglog_strictConcaveOn.2 hx hy hxy ha hb hab
  have hc : a * Real.eulerMascheroniConstant + b * Real.eulerMascheroniConstant =
      Real.eulerMascheroniConstant := by rw [← add_mul, hab, one_mul]
  simp only [smul_eq_mul] at hh ⊢
  dsimp only [robinThreshold]
  nlinarith only [hh, hc]

theorem log_gt_one {n : ℕ} (hn : 3 ≤ n) : 1 < Real.log n := by
  apply (Real.lt_log_iff_exp_lt (Nat.cast_pos.mpr (by omega) : (0 : ℝ) < n)).mpr
  exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hn)

/-- Exact global support line for sigma(n)/n, over EVERY positive integer. -/
theorem objective_support {q : ℝ} {B n : ℕ} (hB : 1 ≤ B) (hn : 1 ≤ n)
    (hopt : IsGoldenResourceOptimal q B) :
    W n ≤ W B + q * (Real.log n - Real.log B) := by
  have h := hopt n hn
  rw [golden_resource_sigma_identity q hn, golden_resource_sigma_identity q hB] at h
  change W n - q * Real.log n ≤ W B - q * Real.log B at h
  linarith

/-- All same-price optimizers lie on the same support line, including
endpoints separated by simultaneous ties in several prime directions. -/
theorem optimizer_tie_identity {q : ℝ} {B U : ℕ} (hB : 1 ≤ B) (hU : 1 ≤ U)
    (hoptB : IsGoldenResourceOptimal q B) (hoptU : IsGoldenResourceOptimal q U) :
    W U - W B = q * (Real.log U - Real.log B) := by
  have h₁ := hoptB U hU
  have h₂ := hoptU B hB
  rw [golden_resource_sigma_identity q hU, golden_resource_sigma_identity q hB] at h₁ h₂
  change W U - q * Real.log U ≤ W B - q * Real.log B at h₁
  change W B - q * Real.log B ≤ W U - q * Real.log U at h₂
  linarith

/-- Logarithmic barycentric coordinate. At B = U it is exactly zero. -/
def intervalWeight (B U n : ℕ) : ℝ :=
  (Real.log n - Real.log B) / (Real.log U - Real.log B)

theorem intervalWeight_spec {B U n : ℕ} (hB : 1 ≤ B) (hBn : B ≤ n) (hnU : n ≤ U) :
    0 ≤ intervalWeight B U n ∧ intervalWeight B U n ≤ 1 ∧
      Real.log n = (1 - intervalWeight B U n) * Real.log B +
        intervalWeight B U n * Real.log U := by
  have hBU : B ≤ U := hBn.trans hnU
  rcases eq_or_lt_of_le hBU with heq | hlt
  · have hnB : n = B := by omega
    subst U
    subst n
    simp [intervalWeight]
  · have hlog : Real.log B < Real.log U :=
      Real.log_lt_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast hlt)
    have hlogBn : Real.log B ≤ Real.log n :=
      Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast hBn)
    have hlognU : Real.log n ≤ Real.log U :=
      Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast hnU)
    have hden : 0 < Real.log U - Real.log B := sub_pos.mpr hlog
    refine ⟨div_nonneg (sub_nonneg.mpr hlogBn) hden.le,
      (div_le_one hden).mpr (by linarith), ?_⟩
    dsimp only [intervalWeight]
    field_simp [hden.ne'] <;> ring

theorem intervalWeight_interior {B U n : ℕ} (hB : 1 ≤ B) (hBn : B < n) (hnU : n < U) :
    0 < intervalWeight B U n ∧ intervalWeight B U n < 1 := by
  have hlogBn : Real.log B < Real.log n :=
    Real.log_lt_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast hBn)
  have hlognU : Real.log n < Real.log U :=
    Real.log_lt_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast hnU)
  have hden : 0 < Real.log U - Real.log B := by linarith
  exact ⟨div_pos (sub_pos.mpr hlogBn) hden,
    (div_lt_one hden).mpr (by linarith)⟩

/-- The optimizer support line is exactly the endpoint W chord.
The input here is only the barycentric equality, not any Jensen estimate. -/
theorem W_le_endpoint_chord {q t : ℝ} {B U n : ℕ}
    (hB : 1 ≤ B) (hU : 1 ≤ U) (hn : 1 ≤ n)
    (hoptB : IsGoldenResourceOptimal q B) (hoptU : IsGoldenResourceOptimal q U)
    (hblend : Real.log n = (1 - t) * Real.log B + t * Real.log U) :
    W n ≤ (1 - t) * W B + t * W U := by
  have hs := objective_support hB hn hoptB
  have ht := optimizer_tie_identity hB hU hoptB hoptU
  calc
    W n ≤ W B + q * (Real.log n - Real.log B) := hs
    _ = W B + t * (q * (Real.log U - Real.log B)) := by rw [hblend]; ring
    _ = (1 - t) * W B + t * W U := by rw [← ht]; ring

/-- SUBSTANTIVE INTERVAL TRANSFER for arbitrary actual same-price
optimizers. Concavity is proved above and is not a final hypothesis.
The strict inequality is the genuine Jensen improvement in the interior. -/
theorem optimizer_interval_transfer {q : ℝ} (_hq : 0 < q) {B U n : ℕ}
    (hB : 3 ≤ B) (hBn : B ≤ n) (hnU : n ≤ U)
    (hoptB : IsGoldenResourceOptimal q B) (hoptU : IsGoldenResourceOptimal q U) :
    let t := intervalWeight B U n
    (1 - t) * robinLogMargin B + t * robinLogMargin U ≤ robinLogMargin n ∧
      (B < n → n < U →
        (1 - t) * robinLogMargin B + t * robinLogMargin U < robinLogMargin n) := by
  dsimp only
  have hU : 3 ≤ U := hB.trans (hBn.trans hnU)
  have hn : 3 ≤ n := hB.trans hBn
  have hw := intervalWeight_spec (by omega : 1 ≤ B) hBn hnU
  have hW := W_le_endpoint_chord (by omega : 1 ≤ B) (by omega : 1 ≤ U)
    (by omega : 1 ≤ n) hoptB hoptU hw.2.2
  constructor
  · have hφ := threshold_strictConcaveOn.concaveOn.2 (log_gt_one hB) (log_gt_one hU)
      (sub_nonneg.mpr hw.2.1) hw.1 (by ring :
        (1 - intervalWeight B U n) + intervalWeight B U n = 1)
    simp only [smul_eq_mul] at hφ
    rw [← hw.2.2] at hφ
    simp only [margin_eq_threshold_sub_W]
    nlinarith only [hφ, hW]
  · intro hBnt hnUt
    have hi := intervalWeight_interior (by omega : 1 ≤ B) hBnt hnUt
    have hlog : Real.log B < Real.log U :=
      Real.log_lt_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast hBnt.trans hnUt)
    have hφ := threshold_strictConcaveOn.2 (log_gt_one hB) (log_gt_one hU) hlog.ne
      (sub_pos.mpr hi.2) hi.1 (by ring :
        (1 - intervalWeight B U n) + intervalWeight B U n = 1)
    simp only [smul_eq_mul] at hφ
    rw [← hw.2.2] at hφ
    simp only [margin_eq_threshold_sub_W]
    nlinarith only [hφ, hW]

theorem optimizer_interval_positive {q : ℝ} (hq : 0 < q) {B U n : ℕ}
    (hB : 3 ≤ B) (hBn : B ≤ n) (hnU : n ≤ U)
    (hoptB : IsGoldenResourceOptimal q B) (hoptU : IsGoldenResourceOptimal q U)
    (hmarginB : 0 < robinLogMargin B) (hmarginU : 0 < robinLogMargin U) :
    0 < robinLogMargin n := by
  have hw := intervalWeight_spec (by omega : 1 ≤ B) hBn hnU
  have hm := (optimizer_interval_transfer hq hB hBn hnU hoptB hoptU).1
  have hc : 0 < (1 - intervalWeight B U n) * robinLogMargin B +
      intervalWeight B U n * robinLogMargin U := by
    by_cases ht : intervalWeight B U n = 0
    · simpa only [ht, sub_zero, one_mul, zero_mul, add_zero] using hmarginB
    · have htpos : 0 < intervalWeight B U n := by
        have := hw.1
        by_contra h
        apply ht
        linarith
      have hleft := mul_nonneg (sub_nonneg.mpr hw.2.1) hmarginB.le
      have hright := mul_pos htpos hmarginU
      linarith
  exact hc.trans_le hm

/-- UNPAID analytic endpoint estimates, only above the actual 5040 boundary. -/
def EndpointRobinEstimates : Prop :=
  ∀ q : ℝ, 0 < q → 5040 < strictInteger q →
    0 < robinLogMargin (strictInteger q) ∧ 0 < robinLogMargin (maximalInteger q)

private theorem boundaryCap_eq_55440 : boundaryCap = 55440 := by
  let q11 : ℝ := goldenLayerMarginal 11 1

  let targetExponent55440 (p : ℕ) : ℕ :=
    if p = 11 then 1 else D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040 p

  have q11_eq : q11 = Real.log (12 / 11) / Real.log 11 := by
    norm_num [q11, goldenLayerMarginal]

  have q11_pos : 0 < q11 := by
    rw [q11_eq]
    have hlog : 0 < Real.log (11 : ℝ) := Real.log_pos (by norm_num)
    have hratio : 1 < (12 / 11 : ℝ) := by norm_num
    exact div_pos (Real.log_pos hratio) hlog

  have selected_next_below_q11 :
      goldenLayerMarginal 2 5 < q11 ∧
      goldenLayerMarginal 3 3 < q11 ∧
      goldenLayerMarginal 5 2 < q11 ∧
      goldenLayerMarginal 7 2 < q11 := by
    have hq11_lower : (1 / 28 : ℝ) < q11 := by
      have hm : (1 / 28 : ℝ) < goldenLayerMarginal 11 1 :=
        one_div_nat_lt_golden_layer_marginal (p := 11) (a := 1) (k := 28)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have hquot : (1 / 28 : ℝ) < Real.log (12 / 11) / Real.log 11 := by
        simpa only [show goldenLayerMarginal 11 1 =
          Real.log (12 / 11) / Real.log 11 by norm_num [goldenLayerMarginal]] using hm
      rw [q11_eq]
      exact hquot
    have h2 : goldenLayerMarginal 2 5 < (1 / 28 : ℝ) :=
      golden_layer_marginal_lt_one_div_nat (p := 2) (a := 5) (k := 28)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h3 : goldenLayerMarginal 3 3 < (1 / 28 : ℝ) :=
      golden_layer_marginal_lt_one_div_nat (p := 3) (a := 3) (k := 28)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h5 : goldenLayerMarginal 5 2 < (1 / 28 : ℝ) :=
      golden_layer_marginal_lt_one_div_nat (p := 5) (a := 2) (k := 28)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    have h7 : goldenLayerMarginal 7 2 < (1 / 28 : ℝ) :=
      golden_layer_marginal_lt_one_div_nat (p := 7) (a := 2) (k := 28)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    exact ⟨h2.trans hq11_lower, h3.trans hq11_lower,
      h5.trans hq11_lower, h7.trans hq11_lower⟩

  have eleven_tail_below {a : ℕ} (ha : 1 < a) :
      goldenLayerMarginal 11 a < q11 := by
    change goldenLayerMarginal 11 a < goldenLayerMarginal 11 1
    exact golden_layer_strict_decrease (by norm_num) (by norm_num) ha

  have prime_ge_13_tail_below {p : ℕ} (hp : p.Prime) (hp13 : 13 ≤ p)
      {a : ℕ} (ha : 1 ≤ a) : goldenLayerMarginal p a < q11 := by
    have hpLog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
    have h11Log : 0 < Real.log (11 : ℝ) := Real.log_pos (by norm_num)
    have hp13R : (13 : ℝ) ≤ p := by exact_mod_cast hp13
    have hinv : (p : ℝ)⁻¹ ≤ (1 / 13 : ℝ) := by
      simpa only [one_div] using inv_anti₀ (by norm_num : (0 : ℝ) < 13) hp13R
    have hlog : Real.log (11 : ℝ) ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (show 11 ≤ p by omega))
    have hbound : (p : ℝ)⁻¹ / Real.log p ≤ (1 / 13 : ℝ) / Real.log 11 := by
      calc
        (p : ℝ)⁻¹ / Real.log p ≤ (1 / 13 : ℝ) / Real.log p :=
          div_le_div_of_nonneg_right hinv hpLog.le
        _ ≤ (1 / 13 : ℝ) / Real.log 11 :=
          div_le_div_of_nonneg_left (by norm_num) h11Log hlog
    have hlogLower : (1 / 13 : ℝ) < Real.log (12 / 11 : ℝ) := by
      have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 12 / 11 by norm_num)
      norm_num at h ⊢
      linarith
    have hquot : (1 / 13 : ℝ) / Real.log 11 < q11 := by
      rw [q11_eq]
      exact (div_lt_div_iff_of_pos_right h11Log).2 hlogLower
    have hfirst : goldenLayerMarginal p 1 < q11 := by
      apply (golden_layer_marginal_le_inv_pow hp (by omega : 1 ≤ (1 : ℕ))).trans_lt
      simpa only [pow_one] using hbound.trans_lt hquot
    rcases eq_or_lt_of_le ha with rfl | hlt
    · exact hfirst
    · exact (golden_layer_strict_decrease hp (by omega : 1 ≤ (1 : ℕ)) hlt).trans hfirst

  have prime_ge_13_of_not_small {p : ℕ} (hp : p.Prime)
      (h2 : p ≠ 2) (h3 : p ≠ 3) (h5 : p ≠ 5) (h7 : p ≠ 7) (h11 : p ≠ 11) :
      13 ≤ p := by
    by_contra h
    interval_cases p <;> norm_num at *

  have target55440_factorization (p : ℕ) :
      targetExponent55440 p = (55440 : ℕ).factorization p := by
    rw [show (55440 : ℕ) = 2 ^ 4 * 3 ^ 2 * 5 ^ 1 * 7 ^ 1 * 11 ^ 1 by norm_num]
    rw [Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.factorization_mul (by norm_num) (by norm_num),
      (by norm_num : Nat.Prime 2).factorization_pow,
      (by norm_num : Nat.Prime 3).factorization_pow,
      (by norm_num : Nat.Prime 5).factorization_pow,
      (by norm_num : Nat.Prime 7).factorization_pow,
      (by norm_num : Nat.Prime 11).factorization_pow]
    simp only [Finsupp.add_apply, Finsupp.single_apply, targetExponent55440,
      D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040]
    split_ifs <;> omega

  have target5040_zero_of_not_prime {p : ℕ} (hp : ¬ p.Prime) :
      D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040 p = 0 := by
    rw [target_exponent_eq_factorization_5040]
    exact Nat.factorization_eq_zero_of_not_prime 5040 hp

  have selected_above_q11 {p : ℕ} (hp : p.Prime)
      (ht : 0 < D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040 p) :
      q11 < goldenLayerMarginal p (D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040 p) := by
    obtain ⟨n, hn, hcounts, hopt, _⟩ :=
      optimal_layer_count_spec (by norm_num : (0 : ℝ) < 1 / 25)
    have hn5040 : n = 5040 :=
      (golden_resource_unique_optimum hn).2.mp
        (le_antisymm (golden_resource_unique_optimum hn).1
          (hopt 5040 (by norm_num)))
    have hc : optimalLayerCount (1 / 25) p = D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040 p := by
      rw [← hcounts p, hn5040, target_exponent_eq_factorization_5040]
    have hmem : D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040 p ∈
        {k : ℕ | 1 ≤ k ∧ p.Prime ∧ (1 / 25 : ℝ) < goldenLayerMarginal p k} := by
      rw [positive_layers_eq_count_interval (by norm_num : (0 : ℝ) < 1 / 25) hp, hc]
      exact ⟨ht, le_rfl⟩
    have hq11_upper : q11 < (1 / 25 : ℝ) := by
      have hm : goldenLayerMarginal 11 1 < (1 / 25 : ℝ) :=
        golden_layer_marginal_lt_one_div_nat (p := 11) (a := 1) (k := 25)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have hquot : Real.log (12 / 11) / Real.log 11 < (1 / 25 : ℝ) := by
        simpa only [show goldenLayerMarginal 11 1 =
          Real.log (12 / 11) / Real.log 11 by norm_num [goldenLayerMarginal]] using hm
      rw [q11_eq]
      exact hquot
    exact hq11_upper.trans hmem.2.2

  have optimalLayerCount_q11 (p : ℕ) :
      optimalLayerCount q11 p = D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040 p := by
    by_cases hp : p.Prime
    · have hinterval := positive_layers_eq_count_interval q11_pos hp
      have hactive : D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040 p = 0 ∨
          q11 < goldenLayerMarginal p (D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040 p) := by
        by_cases hz : D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040 p = 0
        · exact Or.inl hz
        · exact Or.inr (selected_above_q11 hp (Nat.pos_of_ne_zero hz))
      have hnext : ¬ q11 < goldenLayerMarginal p (D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040 p + 1) := by
        by_cases h2 : p = 2
        · subst p; simpa [D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040] using (not_lt_of_ge selected_next_below_q11.1.le)
        by_cases h3 : p = 3
        · subst p; simpa [D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040] using (not_lt_of_ge selected_next_below_q11.2.1.le)
        by_cases h5 : p = 5
        · subst p; simpa [D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040] using (not_lt_of_ge selected_next_below_q11.2.2.1.le)
        by_cases h7 : p = 7
        · subst p; simpa [D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040] using (not_lt_of_ge selected_next_below_q11.2.2.2.le)
        by_cases h11 : p = 11
        · subst p; simpa [D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040, q11, goldenLayerMarginal]
        have hp13 := prime_ge_13_of_not_small hp h2 h3 h5 h7 h11
        have hbelow := prime_ge_13_tail_below hp hp13
          (a := D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040 p + 1) (by omega)
        simpa [D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040, h2, h3, h5, h7] using (not_lt_of_ge hbelow.le)
      apply Nat.le_antisymm
      · by_contra hle
        have hmem : D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040 p + 1 ∈
            Set.Icc 1 (optimalLayerCount q11 p) := by
          exact ⟨by omega, Nat.succ_le_of_lt (Nat.lt_of_not_ge hle)⟩
        rw [← hinterval] at hmem
        exact hnext hmem.2.2
      · by_cases hz : D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040 p = 0
        · omega
        · have hmem : D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040 p ∈
              {k : ℕ | 1 ≤ k ∧ p.Prime ∧ q11 < goldenLayerMarginal p k} :=
            ⟨Nat.one_le_iff_ne_zero.mpr hz, hp, hactive.resolve_left hz⟩
          rw [hinterval] at hmem
          exact hmem.2
    · rw [target5040_zero_of_not_prime hp]
      simp [optimalLayerCount, hp]

  have weakLayerCount_q11 (p : ℕ) :
      weakLayerCount q11 p = targetExponent55440 p := by
    by_cases hp : p.Prime
    · have hinterval := weak_layers_eq_count_interval q11_pos hp
      have hactive : targetExponent55440 p = 0 ∨
          q11 ≤ goldenLayerMarginal p (targetExponent55440 p) := by
        by_cases h11 : p = 11
        · subst p
          right
          change q11 ≤ goldenLayerMarginal 11 1
          exact le_rfl
        have ht : targetExponent55440 p = D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040 p := by
          simp only [targetExponent55440, if_neg h11]
        rw [ht]
        by_cases hz : D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040 p = 0
        · exact Or.inl hz
        · exact Or.inr (selected_above_q11 hp (Nat.pos_of_ne_zero hz)).le
      have hnext : ¬ q11 ≤ goldenLayerMarginal p (targetExponent55440 p + 1) := by
        by_cases h11 : p = 11
        · subst p; simpa [targetExponent55440] using (not_le_of_gt (eleven_tail_below (by norm_num : 1 < 1 + 1)))
        by_cases h2 : p = 2
        · subst p; simpa [targetExponent55440, D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040] using (not_le_of_gt selected_next_below_q11.1)
        by_cases h3 : p = 3
        · subst p; simpa [targetExponent55440, D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040] using (not_le_of_gt selected_next_below_q11.2.1)
        by_cases h5 : p = 5
        · subst p; simpa [targetExponent55440, D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040] using (not_le_of_gt selected_next_below_q11.2.2.1)
        by_cases h7 : p = 7
        · subst p; simpa [targetExponent55440, D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040] using (not_le_of_gt selected_next_below_q11.2.2.2)
        have hp13 := prime_ge_13_of_not_small hp h2 h3 h5 h7 h11
        have hbelow := prime_ge_13_tail_below hp hp13
          (a := targetExponent55440 p + 1) (by omega)
        simpa [targetExponent55440, D5.S3.Arith.GoldenResource5040PriceInterval.targetExponent5040, h11, h2, h3, h5, h7]
          using (not_le_of_gt hbelow)
      apply Nat.le_antisymm
      · by_contra hle
        have hmem : targetExponent55440 p + 1 ∈ Set.Icc 1 (weakLayerCount q11 p) := by
          exact ⟨by omega, Nat.succ_le_of_lt (Nat.lt_of_not_ge hle)⟩
        rw [← hinterval] at hmem
        exact hnext hmem.2.2
      · by_cases hz : targetExponent55440 p = 0
        · omega
        · have hmem : targetExponent55440 p ∈
              {k : ℕ | 1 ≤ k ∧ p.Prime ∧ q11 ≤ goldenLayerMarginal p k} :=
            ⟨Nat.one_le_iff_ne_zero.mpr hz, hp, hactive.resolve_left hz⟩
          rw [hinterval] at hmem
          exact hmem.2
    · have h11 : p ≠ 11 := by
        rintro rfl
        exact hp (by norm_num)
      simp only [targetExponent55440, if_neg h11, target5040_zero_of_not_prime hp]
      simp [weakLayerCount, hp]

  have strictInteger_q11 : strictInteger q11 = 5040 := by
    apply Nat.factorization_inj
      (Nat.ne_of_gt (strictInteger_pos q11_pos))
      (by norm_num : (5040 : ℕ) ≠ 0)
    ext p
    rw [strictInteger_counts q11_pos, optimalLayerCount_q11, target_exponent_eq_factorization_5040]

  have maximalInteger_q11 : maximalInteger q11 = 55440 := by
    apply Nat.factorization_inj
      (Nat.ne_of_gt (maximalInteger_spec q11_pos).1)
      (by norm_num : (55440 : ℕ) ≠ 0)
    ext p
    rw [(maximalInteger_spec q11_pos).2.1 p, weakLayerCount_q11,
      target55440_factorization]
  have hq11 : 0 < q11 := q11_pos
  have hboundaryPrice : boundaryPrice = q11 := by
    rcases lt_trichotomy boundaryPrice q11 with hlt | heq | hgt
    · have hd : 55440 ∣ strictInteger boundaryPrice := by
        simpa only [maximalInteger_q11] using
          (weak_dvd_strict boundaryPrice_spec.1 hq11 hlt)
      have hbound : 55440 ≤ strictInteger boundaryPrice :=
        Nat.le_of_dvd (by
          have hpos := strictInteger_pos boundaryPrice_spec.1
          omega) hd
      have hsmall := boundaryPrice_spec.2.1
      omega
    · exact heq
    · have hd : maximalInteger boundaryPrice ∣ 5040 := by
        simpa only [strictInteger_q11] using
          (weak_dvd_strict hq11 boundaryPrice_spec.1 hgt)
      have hbound : maximalInteger boundaryPrice ≤ 5040 :=
        Nat.le_of_dvd (by norm_num) hd
      have hlarge := boundaryPrice_spec.2.2
      omega
  have hboundaryCap : boundaryCap = 55440 := by
    change maximalInteger boundaryPrice = 55440
    rw [hboundaryPrice, maximalInteger_q11]
  exact hboundaryCap

/-- Original global consumer after removing the obsolete finite premise. Coverage has
no premise. In the finite branch the actual chosen boundary is identified
locally, then the existing finite Robin theorem is consumed through the
public log-margin bridge. The finite boundary obligation is discharged by the local q11 identification;
the all-price EndpointRobinEstimates obligation remains unpaid. -/
theorem global_robin_margin_reduction
    (hEndpoint : EndpointRobinEstimates) :
    ∀ n : ℕ, 5040 < n → 0 < robinLogMargin n := by
  intro n hn
  rcases coverage_above_5040 hn with hfinite | ⟨q, hq, hB, hBn, hnU⟩
  · have hboundaryCap := boundaryCap_eq_55440
    have hn55440 : n ≤ 55440 := by
      simpa only [hboundaryCap] using hfinite
    have hfiniteRobin :=
      D5.S3.Arith.Robin.FewDistinctPrimes.robin_lt_223092870
        hn (by omega : n < 223092870)
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hsR : (0 : ℝ) < (ArithmeticFunction.sigma 1 n : ℝ) := by
      exact_mod_cast ArithmeticFunction.sigma_pos 1 n (by omega : n ≠ 0)
    have hll : 0 < Real.log (Real.log n) :=
      D5.S3.Arith.Robin.PaddingRatio.loglog_pos (by omega : 5041 ≤ n)
    have hden : 0 < Real.exp Real.eulerMascheroniConstant *
        Real.log (Real.log n) := mul_pos (Real.exp_pos _) hll
    have hratio_eq : D5.S3.Arith.Robin.PaddingRatio.robinRatio n =
        ((ArithmeticFunction.sigma 1 n : ℝ) / n) /
          (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n)) := by
      simp only [D5.S3.Arith.Robin.PaddingRatio.robinRatio,
        div_eq_mul_inv, mul_inv_rev]
      ring
    have hratio_lt : D5.S3.Arith.Robin.PaddingRatio.robinRatio n < 1 := by
      rw [hratio_eq]
      exact (div_lt_one hden).mpr hfiniteRobin
    have hratio_pos : 0 < D5.S3.Arith.Robin.PaddingRatio.robinRatio n := by
      exact div_pos hsR (mul_pos (mul_pos (Real.exp_pos _) hnR) hll)
    rw [robin_log_margin_eq_neg_log (by omega : 5041 ≤ n)]
    exact neg_pos.mpr (Real.log_neg hratio_pos hratio_lt)
  · have hm := hEndpoint q hq hB
    exact optimizer_interval_positive hq (by omega) hBn hnU (strict_is_optimal hq)
      (maximalInteger_spec hq).2.2.1 hm.1 hm.2

/-- This reduction preserves the full original margin target in both
directions. It does not smuggle any boundary or endpoint estimate into
a finiteness/cofinality/bracketing certificate. -/
theorem global_margin_iff_unpaid_estimates :
    (∀ n : ℕ, 5040 < n → 0 < robinLogMargin n) ↔
      EndpointRobinEstimates := by
  constructor
  · intro hall
    intro q hq hB
    have hBU : strictInteger q ≤ maximalInteger q :=
      Nat.le_of_dvd (by have := (maximalInteger_spec hq).1; omega) (strict_dvd_weak hq)
    exact ⟨hall _ hB, hall _ (lt_of_lt_of_le hB hBU)⟩
  · intro hEndpoint
    exact global_robin_margin_reduction hEndpoint

/-- The margin consumer implies the original sigma/n Robin inequality;
the sigma, integer and logarithmic denominator have not been changed. -/
theorem original_robin_of_margin {n : ℕ} (hn : 3 ≤ n) (hm : 0 < robinLogMargin n) :
    (ArithmeticFunction.sigma 1 n : ℝ) <
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hs0 : (0 : ℝ) < (ArithmeticFunction.sigma 1 n : ℝ) := by
    exact_mod_cast ArithmeticFunction.sigma_pos 1 n (by omega : n ≠ 0)
  have hr0 := div_pos hs0 hn0
  have hll : 0 < Real.log (Real.log n) := Real.log_pos (log_gt_one hn)
  have hlog : Real.log ((ArithmeticFunction.sigma 1 n : ℝ) / n) <
      Real.eulerMascheroniConstant + Real.log (Real.log (Real.log n)) := by
    dsimp only [robinLogMargin] at hm
    linarith
  have hr := (Real.log_lt_iff_lt_exp hr0).mp hlog
  rw [Real.exp_add, Real.exp_log hll] at hr
  have hmul := (div_lt_iff₀ hn0).mp hr
  convert hmul using 1 <;> ring

theorem global_original_robin_reduction
    (hEndpoint : EndpointRobinEstimates) :
    ∀ n : ℕ, 5040 < n → (ArithmeticFunction.sigma 1 n : ℝ) <
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  intro n hn
  exact original_robin_of_margin (by omega)
    (global_robin_margin_reduction hEndpoint n hn)

/-- Upper-price endpoint signs cover every original integer through the
actual maximal integer at that price. The existing exact 5040 boundary is
paid inside the proof. Prices below q0 cannot create a missing interior
interval: actual divisibility forces the upper endpoint q0 to equal n. -/
theorem original_robin_through_maximal
    {q0 : ℝ} (hq0 : 0 < q0)
    (hEndpoint : ∀ q : ℝ, 0 < q → q0 ≤ q →
      ∀ N : ℕ, 5040 < N →
        (N = strictInteger q ∨ N = maximalInteger q) →
        0 < robinLogMargin N)
    {n : ℕ} (hn : 5040 < n) (hcap : n ≤ maximalInteger q0) :
    (ArithmeticFunction.sigma 1 n : ℝ) <
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  rcases coverage_above_5040 hn with hfinite | ⟨q, hq, hB, hBn, hnU⟩
  · have hsmall : n < 223092870 := by
      rw [boundaryCap_eq_55440] at hfinite
      omega
    have hRobin :=
      D5.S3.Arith.Robin.FewDistinctPrimes.robin_lt_223092870 hn hsmall
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hmul := (div_lt_iff₀ hnR).mp hRobin
    convert hmul using 1 <;> ring
  · by_cases hprice : q0 ≤ q
    · have hBU : 5040 < maximalInteger q := lt_of_lt_of_le hn hnU
      have hm := optimizer_interval_positive hq (by omega) hBn hnU
        (strict_is_optimal hq) (maximalInteger_spec hq).2.2.1
        (hEndpoint q hq hprice _ hB (Or.inl rfl))
        (hEndpoint q hq hprice _ hBU (Or.inr rfl))
      exact original_robin_of_margin (by omega) hm
    · have hd : maximalInteger q0 ∣ strictInteger q :=
        weak_dvd_strict hq hq0 (lt_of_not_ge hprice)
      have hle : maximalInteger q0 ≤ strictInteger q :=
        Nat.le_of_dvd (by have := strictInteger_pos hq; omega) hd
      have heq : n = maximalInteger q0 := by omega
      have hm := hEndpoint q0 hq0 le_rfl n hn (Or.inr heq)
      exact original_robin_of_margin (by omega) hm


open Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.GoldenResourceSupremum
open D5.S3.Arith.GoldenLayerMarginalDecay
open D5.S3.Arith.Robin.ActualTwoPriceDefect

private def fpEpsilon (x : ℝ) : ℝ := 1 / (100 * Real.sqrt x * Real.log x)

private theorem fp_epsilon_antitone {u x : ℝ} (hu : 1 < u) (hux : u ≤ x) :
    fpEpsilon x ≤ fpEpsilon u := by
  have hsu := Real.sqrt_pos.2 (show 0 < u by linarith)
  have hlu := Real.log_pos hu
  apply one_div_le_one_div_of_le (mul_pos (mul_pos (by norm_num) hsu) hlu)
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hux) (by norm_num))
    (Real.log_le_log (by linarith) hux) hlu.le
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg x))

/-- Each fixed integer chooses an endpoint according to the sign of its affine
coefficient. There is no division by a price difference, even for u=v. -/
private theorem fp_cell_support {u v w B x : ℝ} (hu : 1 < u)
    (hux : u ≤ x) (hxv : x ≤ v)
    (hleft : pressure (price u) + w * price u ≤ B)
    (hright : pressure (price v) + w * price v ≤ B) :
    pressure (price x) + w * price x ≤ B := by
  have hx : 1 < x := hu.trans_le hux
  have hv : 1 < v := hx.trans_le hxv
  have hxu := price_antitone hu hux
  have hvx := price_antitone hx hxv
  have hobj (t : ℝ) (ht : 1 < t) (n : ℕ) (hn : 1 ≤ n) :
      goldenResourceObjective (price t) n ≤ pressure (price t) :=
    le_csSup (pressure_maximal_spec (price_pos ht)).1 ⟨n, hn, rfl⟩
  have hbound : pressure (price x) ≤ B - w * price x := by
    unfold pressure
    apply csSup_le
    · exact ⟨goldenResourceObjective (price x) 1, 1, le_rfl, rfl⟩
    · rintro z ⟨n, hn, rfl⟩
      by_cases hs : 0 ≤ w - Real.log n
      · have hm := mul_le_mul_of_nonneg_left hxu hs
        have he := hobj u hu n hn
        dsimp only [goldenResourceObjective] at he ⊢
        nlinarith only [hm, he, hleft]
      · have hm := mul_le_mul_of_nonpos_left hvx (le_of_lt (lt_of_not_ge hs))
        have he := hobj v hv n hn
        dsimp only [goldenResourceObjective] at he ⊢
        nlinarith only [hm, he, hright]
  linarith only [hbound]

/-- Actual endpoint-to-cell inference, preserving the full 1/100 margin.
The strict existing tangent is used at x!=w; equality is handled directly. -/
private theorem fp_cell {u v w x : ℝ} (hu : 1 < u) (hw : 1 < w)
    (hux : u ≤ x) (hxv : x ≤ v)
    (hleft : pressure (price u) + w * price u ≤
      Real.eulerMascheroniConstant + Real.log (Real.log w) - fpEpsilon u)
    (hright : pressure (price v) + w * price v ≤
      Real.eulerMascheroniConstant + Real.log (Real.log w) - fpEpsilon u) :
    pressure (price x) ≤ Real.eulerMascheroniConstant + Real.log (Real.log x) -
      1 / Real.log x - fpEpsilon x := by
  have hx : 1 < x := hu.trans_le hux
  have hs := fp_cell_support hu hux hxv hleft hright
  have ht : Real.log (Real.log w) - Real.log (Real.log x) ≤
      (w - x) * price x := by
    by_cases heq : x = w
    · subst w
      simp
    · exact (show Real.log (Real.log w) - Real.log (Real.log x) <
        (w - x) * price x from by
          simpa only [price, ActualRobinClockCovariance.g] using
            RestrictedDivisorStrictInventory.loglog_tangent hx hw heq).le
  have hid : x * price x = 1 / Real.log x := by
    dsimp only [price]
    field_simp [(show x ≠ 0 by linarith), (Real.log_pos hx).ne']
  have he := fp_epsilon_antitone hu hux
  nlinarith only [hs, ht, hid, he]

/-- B=p+...+p^a, using the same recurrence as the packet generator. -/
private def fpLayerDenom (p a : ℕ) : ℝ :=
  ∑ i ∈ range a, (p : ℝ) ^ (i + 1)

private theorem fp_layer_log {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    Real.log p * goldenLayerMarginal p a =
      Real.log (1 + 1 / fpLayerDenom p a) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := (lt_trans zero_lt_one hp1).ne'
  have hpa0 : (p : ℝ) ^ a ≠ 0 := pow_ne_zero a hp0
  have hB : 0 < fpLayerDenom p a := by
    unfold fpLayerDenom
    apply sum_pos
    · intro i hi
      exact pow_pos (by linarith) _
    · exact ⟨0, mem_range.mpr (by omega)⟩
  have hgeom : fpLayerDenom p a * ((p : ℝ) - 1) =
      (p : ℝ) * ((p : ℝ) ^ a - 1) := by
    unfold fpLayerDenom
    simp_rw [pow_succ]
    rw [← sum_mul]
    calc
      ((∑ i ∈ range a, (p : ℝ) ^ i) * p) * (p - 1) =
          p * ((∑ i ∈ range a, (p : ℝ) ^ i) * (p - 1)) := by ring
      _ = p * ((p : ℝ) ^ a - 1) := by rw [geom_sum_mul]
  have hi0 : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (by linarith)
  have hi1 : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr hp1
  have hden : 0 < 1 - (p : ℝ)⁻¹ ^ a :=
    sub_pos.mpr (pow_lt_one₀ hi0.le hi1 (by omega))
  have hr : (1 - (p : ℝ)⁻¹ ^ (a + 1)) / (1 - (p : ℝ)⁻¹ ^ a) =
      1 + 1 / fpLayerDenom p a := by
    apply (div_eq_iff hden.ne').2
    rw [show (p : ℝ)⁻¹ ^ a = 1 / (p : ℝ) ^ a by simp [one_div],
      show (p : ℝ)⁻¹ ^ (a + 1) = 1 / (p : ℝ) ^ (a + 1) by simp [one_div]]
    simp only [pow_succ]
    field_simp [hp0, hpa0, hB.ne']
    nlinarith only [hgeom]
  unfold goldenLayerMarginal
  rw [hr]
  exact mul_div_cancel₀ _ (Real.log_pos hp1).ne'

/-- A recorded power cutoff excludes every later layer. Weak exclusion is
enough, since the actual pressure support uses STRICT positive gain. -/
private theorem fp_cutoff {X x : ℝ} (hX : 1 < X) (hx : 1 < x) (hxX : x ≤ X)
    {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (hcut : X * Real.log X ≤ (p : ℝ) ^ a * Real.log p) :
    goldenLayerMarginal p a ≤ price x := by
  have hXp : 0 < X * Real.log X := mul_pos (by linarith) (Real.log_pos hX)
  calc
    goldenLayerMarginal p a ≤ (p : ℝ)⁻¹ ^ a / Real.log p :=
      golden_layer_marginal_le_inv_pow hp ha
    _ = 1 / ((p : ℝ) ^ a * Real.log p) := by
      simp only [one_div, div_eq_mul_inv, mul_inv_rev, inv_pow]
      ring
    _ ≤ price X := one_div_le_one_div_of_le hXp hcut
    _ ≤ price x := price_antitone hx hxX

private theorem fp_active_mem {X x : ℝ} (hX : 1 < X) (hx : 1 < x) (hxX : x ≤ X)
    (primes : Finset ℕ) (A : ℕ → ℕ) (T : Finset (ℕ × ℕ))
    (hcomplete : ∀ p : ℕ, p.Prime → (p : ℝ) < X → p ∈ primes)
    (hcut : ∀ p ∈ primes, X * Real.log X ≤ (p : ℝ) ^ A p * Real.log p)
    (henum : ∀ p ∈ primes, ∀ a : ℕ, 1 ≤ a → a < A p → (p, a) ∈ T)
    {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (hactive : price x < goldenLayerMarginal p a) : (p, a) ∈ T := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hlp : 0 ≤ Real.log p := (Real.log_pos (by exact_mod_cast hp.one_lt)).le
  have hpX : (p : ℝ) < X := by
    by_contra hn
    have hXp : X ≤ (p : ℝ) := le_of_not_gt hn
    have hm : X * Real.log X ≤ (p : ℝ) ^ a * Real.log p :=
      mul_le_mul (hXp.trans (le_self_pow₀ hp1 (by omega)))
        (Real.log_le_log (by linarith) hXp) (Real.log_pos hX).le
        (pow_nonneg (by linarith) a)
    exact (not_lt_of_ge (fp_cutoff hX hx hxX hp ha hm)) hactive
  have hpm := hcomplete p hp hpX
  have haA : a < A p := by
    by_contra hn
    have hm : X * Real.log X ≤ (p : ℝ) ^ a * Real.log p :=
      (hcut p hpm).trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hp1 (le_of_not_gt hn)) hlp)
    exact (not_lt_of_ge (fp_cutoff hX hx hxX hp ha hm)) hactive
  exact henum p hpm a ha haA

/-- Transport the ACTUAL unrestricted integer supremum to conservative
positive parts on a supplied complete prime-layer set. -/
private theorem fp_pressure_enclosure {x qlo : ℝ} (hx : 1 < x)
    (T : Finset (ℕ × ℕ)) (lp : ℕ → ℝ) (du : ℕ × ℕ → ℝ)
    (hcomplete : ∀ p a : ℕ, p.Prime → 1 ≤ a →
      price x < goldenLayerMarginal p a → (p, a) ∈ T)
    (hlp : ∀ pk ∈ T, 0 ≤ lp pk.1 ∧ lp pk.1 ≤ Real.log pk.1)
    (hd : ∀ pk ∈ T, pk.1.Prime → 1 ≤ pk.2 →
      Real.log (1 + 1 / fpLayerDenom pk.1 pk.2) ≤ du pk)
    (hqlo : 0 ≤ qlo) (hq : qlo ≤ price x) :
    pressure (price x) ≤ ∑ pk ∈ T, max (du pk - qlo * lp pk.1) 0 := by
  classical
  let S := (positive_part_sum_finite_support (price_pos hx)).toFinset
  have hsub : S ⊆ T := by
    intro pk hpk
    have hh : 1 ≤ pk.2 ∧ pk.1.Prime ∧ price x < goldenLayerMarginal pk.1 pk.2 := by
      simpa only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hpk
    exact hcomplete pk.1 pk.2 hh.2.1 hh.1 hh.2.2
  have hcarrier : {z : ℝ | ∃ n : ℕ, 1 ≤ n ∧ z = goldenResourceObjective (price x) n} =
      {z : ℝ | ∃ n : ℕ, 1 ≤ n ∧ goldenResourceObjective (price x) n = z} := by
    ext z
    constructor <;> rintro ⟨n, hn, he⟩ <;> exact ⟨n, hn, he.symm⟩
  unfold pressure
  rw [hcarrier, golden_resource_supremum_eq_positive_part_sum (price_pos hx)]
  change (∑ pk ∈ S, Real.log pk.1 * (goldenLayerMarginal pk.1 pk.2 - price x)) ≤ _
  calc
    _ ≤ ∑ pk ∈ S, max (du pk - qlo * lp pk.1) 0 := by
      apply sum_le_sum
      intro pk hpk
      have hh : 1 ≤ pk.2 ∧ pk.1.Prime ∧ price x < goldenLayerMarginal pk.1 pk.2 := by
        simpa only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hpk
      have hT := hsub hpk
      have hm := mul_le_mul hq (hlp pk hT).2 (hlp pk hT).1 (price_pos hx).le
      have hd' := hd pk hT hh.2.1 hh.1
      have hid := fp_layer_log hh.2.1 hh.1
      exact (show Real.log pk.1 * (goldenLayerMarginal pk.1 pk.2 - price x) ≤
          du pk - qlo * lp pk.1 by nlinarith only [hm, hd', hid]).trans (le_max_left _ _)
    _ ≤ ∑ pk ∈ T, max (du pk - qlo * lp pk.1) 0 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => le_max_right _ _)

/-- Exact prefix algebra. Sorting is not assumed to make signs correct: every
retained and omitted sign must be supplied explicitly by checked arithmetic. -/
private theorem fp_prefix (T H : Finset (ℕ × ℕ)) (du : ℕ × ℕ → ℚ)
    (lp : ℕ → ℚ) (q D L : ℚ) (hHT : H ⊆ T)
    (hon : ∀ pk ∈ H, 0 ≤ du pk - q * lp pk.1)
    (hoff : ∀ pk ∈ T, pk ∉ H → du pk - q * lp pk.1 ≤ 0)
    (hD : ∑ pk ∈ H, du pk = D) (hL : ∑ pk ∈ H, lp pk.1 = L) :
    (∑ pk ∈ T, max ((du pk : ℝ) - (q : ℝ) * (lp pk.1 : ℝ)) 0) =
      (D : ℝ) - (q : ℝ) * (L : ℝ) := by
  classical
  have hout : ∀ pk ∈ T, pk ∉ H →
      max ((du pk : ℝ) - (q : ℝ) * (lp pk.1 : ℝ)) 0 = 0 := by
    intro pk hpk hn
    exact max_eq_right (by exact_mod_cast hoff pk hpk hn)
  rw [← sum_subset hHT hout]
  have he : (∑ pk ∈ H, max ((du pk : ℝ) - (q : ℝ) * (lp pk.1 : ℝ)) 0) =
      ∑ pk ∈ H, ((du pk : ℝ) - (q : ℝ) * (lp pk.1 : ℝ)) := by
    apply sum_congr rfl
    intro pk hpk
    exact max_eq_left (by exact_mod_cast hon pk hpk)
  rw [he, sum_sub_distrib, ← mul_sum]
  have hD' : (∑ pk ∈ H, (du pk : ℝ)) = (D : ℝ) := by exact_mod_cast hD
  have hL' : (∑ pk ∈ H, (lp pk.1 : ℝ)) = (L : ℝ) := by exact_mod_cast hL
  rw [hD', hL']

private structure FPEndpoint where
  logLo : ℚ
  logHi : ℚ
  qLo : ℚ
  qHi : ℚ
  prefix : Finset (ℕ × ℕ)
  D : ℚ
  L : ℚ

private structure FPCell where
  w : ℚ
  logULo : ℚ
  sqrtULo : ℚ
  logWLo : ℚ
  loglogWLo : ℚ
  left : FPEndpoint
  right : FPEndpoint

/-- Directed log bounds imply both price bounds; no floating inverse. -/
private theorem fp_price_interval {t : ℝ} (ht : 1 < t) (e : FPEndpoint)
    (hlo : 0 < (e.logLo : ℝ)) (hloglo : (e.logLo : ℝ) ≤ Real.log t)
    (hloghi : Real.log t ≤ (e.logHi : ℝ))
    (hql : (e.qLo : ℝ) = 1 / (t * (e.logHi : ℝ)))
    (hqh : (e.qHi : ℝ) = 1 / (t * (e.logLo : ℝ))) :
    0 ≤ (e.qLo : ℝ) ∧ (e.qLo : ℝ) ≤ price t ∧ price t ≤ (e.qHi : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hhi : 0 < (e.logHi : ℝ) := (Real.log_pos ht).trans_le hloghi
  refine ⟨?_, ?_, ?_⟩
  · rw [hql]
    exact (one_div_pos.mpr (mul_pos ht0 hhi)).le
  · rw [hql]
    exact one_div_le_one_div_of_le (mul_pos ht0 (Real.log_pos ht))
      (mul_le_mul_of_nonneg_left hloghi ht0.le)
  · rw [hqh]
    exact one_div_le_one_div_of_le (mul_pos ht0 hlo)
      (mul_le_mul_of_nonneg_left hloglo ht0.le)

/-- A checked square inequality and a positive directed log lower bound pay
the entire reciprocal-root-log error term. -/
private theorem fp_epsilon_enclosure {u s l : ℝ}
    (hs : 0 < s) (hl : 0 < l) (hsq : s ^ 2 ≤ u) (hlog : l ≤ Real.log u) :
    fpEpsilon u ≤ 1 / (100 * s * l) := by
  apply one_div_le_one_div_of_le (mul_pos (mul_pos (by norm_num) hs) hl)
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le hsq) (by norm_num))
    hlog hl.le (mul_nonneg (by norm_num) (Real.sqrt_nonneg u))

private theorem fp_grid_cover (z : ℕ → ℝ) (N : ℕ) (hN : 0 < N)
    {x : ℝ} (hx0 : z 0 ≤ x) (hxN : x ≤ z N) :
    ∃ i : ℕ, i < N ∧ z i ≤ x ∧ x ≤ z (i + 1) := by
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases hx : x ≤ z N
      · by_cases hzero : N = 0
        · subst N
          exact ⟨0, by omega, hx0, hxN⟩
        · obtain ⟨i, hi, hix, hxi⟩ := ih (by omega) hx
          exact ⟨i, by omega, hix, hxi⟩
      · exact ⟨N, by omega, (le_of_lt (lt_of_not_ge hx)), hxN⟩

/- The remaining source joins the explicit primitive obligations, rather than
assuming endpoint-pressure statements or a boolean validator's soundness. -/

private theorem fp_endpoint {t u w : ℝ} (ht : 1 < t) (hw : 1 < w)
    (T : Finset (ℕ × ℕ)) (lp : ℕ → ℚ) (du : ℕ × ℕ → ℚ)
    (e : FPEndpoint) (ll eps : ℚ)
    (hcomplete : ∀ p a : ℕ, p.Prime → 1 ≤ a →
      price t < goldenLayerMarginal p a → (p, a) ∈ T)
    (hlp : ∀ pk ∈ T, 0 ≤ (lp pk.1 : ℝ) ∧ (lp pk.1 : ℝ) ≤ Real.log pk.1)
    (hd : ∀ pk ∈ T, pk.1.Prime → 1 ≤ pk.2 →
      Real.log (1 + 1 / fpLayerDenom pk.1 pk.2) ≤ (du pk : ℝ))
    (hprice : 0 ≤ (e.qLo : ℝ) ∧ (e.qLo : ℝ) ≤ price t ∧ price t ≤ (e.qHi : ℝ))
    (hHT : e.prefix ⊆ T)
    (hon : ∀ pk ∈ e.prefix, 0 ≤ du pk - e.qLo * lp pk.1)
    (hoff : ∀ pk ∈ T, pk ∉ e.prefix → du pk - e.qLo * lp pk.1 ≤ 0)
    (hD : ∑ pk ∈ e.prefix, du pk = e.D)
    (hL : ∑ pk ∈ e.prefix, lp pk.1 = e.L)
    (hll : (ll : ℝ) ≤ Real.log (Real.log w))
    (heps : fpEpsilon u ≤ (eps : ℝ))
    (hmargin : (e.D : ℝ) - (e.qLo : ℝ) * (e.L : ℝ) + w * (e.qHi : ℝ) ≤
      (5772156649 / 10 ^ 10 : ℝ) + (ll : ℝ) - (eps : ℝ)) :
    pressure (price t) + w * price t ≤
      Real.eulerMascheroniConstant + Real.log (Real.log w) - fpEpsilon u := by
  have hp := fp_pressure_enclosure ht T (fun p => (lp p : ℝ))
    (fun pk => (du pk : ℝ)) hcomplete hlp hd hprice.1 hprice.2.1
  rw [fp_prefix T e.prefix du lp e.qLo e.D e.L hHT hon hoff hD hL] at hp
  have hq := mul_le_mul_of_nonneg_left hprice.2.2 (show 0 ≤ w by linarith)
  have hg := D5.S3.Arith.GoldenResource.HarmonicGammaUpperTail.eulerMascheroni_lower_64
  linarith only [hp, hq, hmargin, hll, heps, hg]

private def fpEnd (c : FPCell) (b : Bool) : FPEndpoint :=
  if b then c.left else c.right

private def fpNode (z : ℕ → ℚ) (i : ℕ) (b : Bool) : ℚ :=
  if b then z i else z (i + 1)

/-- The full finite-root CONSUMER, conditional on explicitly displayed
primitive obligations. No instance for the packet is supplied or claimed.

`hprimeComplete`, `henum`, `hcut`, `hlogp`, `hd`, `hlogX`, `heLog`,
`hqDef`, `hsqrt`, `huLog`, `hwLog`, `hwLogLog`, `hprefixSubset`, `hon`, `hoff`,
`hD`, `hL`, `hmargin`, `hfirst`, `hlast`, and `hcell` are unpaid concrete
data obligations. In particular no assumed checker, actual-pressure bound,
or pointwise version of the conclusion occurs among the hypotheses.

The finite range and error coefficient are literal; no RH/tail conclusion
is drawn. Singleton cells, strict activation, and zero-gain ties are allowed.
-/
private theorem fp_finite_consumer
    (N : ℕ) (hN : 0 < N) (z : ℕ → ℚ) (c : ℕ → FPCell)
    (primes : Finset ℕ) (A : ℕ → ℕ) (T : Finset (ℕ × ℕ))
    (lp : ℕ → ℚ) (du : ℕ × ℕ → ℚ) (logXHi : ℚ)
    (hfirst : z 0 = 1849 / 100) (hlast : z N = 10000000)
    (hcell : ∀ i < N, (1 : ℚ) < z i ∧ z i ≤ z (i + 1) ∧
      z (i + 1) ≤ 10000000 ∧ 1 < (c i).w)
    (hprimeComplete : ∀ p : ℕ, p.Prime → (p : ℝ) < 10000000 → p ∈ primes)
    (henum : ∀ p ∈ primes, ∀ a : ℕ, 1 ≤ a → a < A p → (p, a) ∈ T)
    (hLayerPrimeRef : ∀ pk ∈ T, pk.1 ∈ primes)
    (hlogp : ∀ p ∈ primes, 0 < lp p ∧ (lp p : ℝ) ≤ Real.log p)
    (hd : ∀ pk ∈ T, pk.1.Prime → 1 ≤ pk.2 →
      Real.log (1 + 1 / fpLayerDenom pk.1 pk.2) ≤ (du pk : ℝ))
    (hlogX : Real.log (10000000 : ℝ) ≤ (logXHi : ℝ))
    (hcut : ∀ p ∈ primes, (10000000 : ℚ) * logXHi ≤ (p : ℚ) ^ A p * lp p)
    (heLog : ∀ i < N, ∀ b : Bool,
      0 < (fpEnd (c i) b).logLo ∧
      ((fpEnd (c i) b).logLo : ℝ) ≤ Real.log (fpNode z i b : ℝ) ∧
      Real.log (fpNode z i b : ℝ) ≤ ((fpEnd (c i) b).logHi : ℝ))
    (hqDef : ∀ i < N, ∀ b : Bool,
      (fpEnd (c i) b).qLo = 1 / (fpNode z i b * (fpEnd (c i) b).logHi) ∧
      (fpEnd (c i) b).qHi = 1 / (fpNode z i b * (fpEnd (c i) b).logLo))
    (hsqrt : ∀ i < N, 0 < (c i).sqrtULo ∧ (c i).sqrtULo ^ 2 ≤ z i)
    (huLog : ∀ i < N, 0 < (c i).logULo ∧
      ((c i).logULo : ℝ) ≤ Real.log (z i : ℝ))
    (hwLog : ∀ i < N, 0 < (c i).logWLo ∧
      ((c i).logWLo : ℝ) ≤ Real.log ((c i).w : ℝ))
    (hwLogLog : ∀ i < N,
      ((c i).loglogWLo : ℝ) ≤ Real.log ((c i).logWLo : ℝ))
    (hprefixSubset : ∀ i < N, ∀ b : Bool, (fpEnd (c i) b).prefix ⊆ T)
    (hon : ∀ i < N, ∀ b : Bool, ∀ pk ∈ (fpEnd (c i) b).prefix,
      0 ≤ du pk - (fpEnd (c i) b).qLo * lp pk.1)
    (hoff : ∀ i < N, ∀ b : Bool, ∀ pk ∈ T, pk ∉ (fpEnd (c i) b).prefix →
      du pk - (fpEnd (c i) b).qLo * lp pk.1 ≤ 0)
    (hD : ∀ i < N, ∀ b : Bool,
      ∑ pk ∈ (fpEnd (c i) b).prefix, du pk = (fpEnd (c i) b).D)
    (hL : ∀ i < N, ∀ b : Bool,
      ∑ pk ∈ (fpEnd (c i) b).prefix, lp pk.1 = (fpEnd (c i) b).L)
    (hmargin : ∀ i < N, ∀ b : Bool,
      (fpEnd (c i) b).D - (fpEnd (c i) b).qLo * (fpEnd (c i) b).L +
        (c i).w * (fpEnd (c i) b).qHi <
      (5772156649 / 10 ^ 10 : ℚ) + (c i).loglogWLo -
        1 / (100 * (c i).sqrtULo * (c i).logULo)) :
    ∀ x ∈ Set.Icc (1849 / 100 : ℝ) 10000000,
      pressure (price x) ≤ Real.eulerMascheroniConstant + Real.log (Real.log x) -
        1 / Real.log x - 1 / (100 * Real.sqrt x * Real.log x) := by
  have hcutReal (p : ℕ) (hp : p ∈ primes) :
      (10000000 : ℝ) * Real.log 10000000 ≤ (p : ℝ) ^ A p * Real.log p := by
    have hc : (10000000 : ℝ) * (logXHi : ℝ) ≤ (p : ℝ) ^ A p * (lp p : ℝ) := by
      exact_mod_cast hcut p hp
    exact (mul_le_mul_of_nonneg_left hlogX (by norm_num)).trans
      (hc.trans (mul_le_mul_of_nonneg_left (hlogp p hp).2 (pow_nonneg (Nat.cast_nonneg p) _)))
  have hlpReal (pk : ℕ × ℕ) (hpk : pk ∈ T) :
      0 ≤ (lp pk.1 : ℝ) ∧ (lp pk.1 : ℝ) ≤ Real.log pk.1 := by
    have hp := hlogp pk.1 (hLayerPrimeRef pk hpk)
    exact ⟨le_of_lt (by exact_mod_cast hp.1), hp.2⟩
  have hend (i : ℕ) (hi : i < N) (b : Bool) :
      pressure (price (fpNode z i b : ℝ)) + (c i).w * price (fpNode z i b : ℝ) ≤
        Real.eulerMascheroniConstant + Real.log (Real.log ((c i).w : ℝ)) -
          fpEpsilon (z i : ℝ) := by
    have hc := hcell i hi
    have hu : (1 : ℝ) < z i := by exact_mod_cast hc.1
    have huv : (z i : ℝ) ≤ z (i + 1) := by exact_mod_cast hc.2.1
    have hvX : (z (i + 1) : ℝ) ≤ 10000000 := by exact_mod_cast hc.2.2.1
    have hw : (1 : ℝ) < (c i).w := by exact_mod_cast hc.2.2.2
    have ht : (1 : ℝ) < (fpNode z i b : ℝ) := by
      cases b <;> simp only [fpNode, Bool.false_eq_true, if_false, if_true]
      · exact hu.trans_le huv
      · exact hu
    have htX : (fpNode z i b : ℝ) ≤ 10000000 := by
      cases b <;> simp only [fpNode, Bool.false_eq_true, if_false, if_true]
      · exact hvX
      · exact huv.trans hvX
    have hcomplete (p a : ℕ) (hp : p.Prime) (ha : 1 ≤ a)
        (hact : price (fpNode z i b : ℝ) < goldenLayerMarginal p a) : (p, a) ∈ T :=
      fp_active_mem (by norm_num : (1 : ℝ) < 10000000) ht htX
        primes A T hprimeComplete hcutReal henum hp ha hact
    have hpr := fp_price_interval ht (fpEnd (c i) b)
      (by exact_mod_cast (heLog i hi b).1)
      (heLog i hi b).2.1 (heLog i hi b).2.2
      (by exact_mod_cast (hqDef i hi b).1)
      (by exact_mod_cast (hqDef i hi b).2)
    have heps : fpEpsilon (z i : ℝ) ≤
        ((1 / (100 * (c i).sqrtULo * (c i).logULo) : ℚ) : ℝ) := by
      have hs : (0 : ℝ) < (c i).sqrtULo := by exact_mod_cast (hsqrt i hi).1
      have hl : (0 : ℝ) < (c i).logULo := by exact_mod_cast (huLog i hi).1
      have hsq : ((c i).sqrtULo : ℝ) ^ 2 ≤ (z i : ℝ) := by
        exact_mod_cast (hsqrt i hi).2
      exact_mod_cast fp_epsilon_enclosure hs hl hsq (huLog i hi).2
    have hll : ((c i).loglogWLo : ℝ) ≤ Real.log (Real.log ((c i).w : ℝ)) :=
      (hwLogLog i hi).trans (Real.log_le_log
        (by exact_mod_cast (hwLog i hi).1) (hwLog i hi).2)
    apply fp_endpoint ht hw T lp du (fpEnd (c i) b) (c i).loglogWLo
      (1 / (100 * (c i).sqrtULo * (c i).logULo))
      hcomplete hlpReal hd hpr
      (hprefixSubset i hi b) (hon i hi b) (hoff i hi b) (hD i hi b) (hL i hi b)
      hll heps
    exact_mod_cast (hmargin i hi b).le
  intro x hx
  have hx0 : (z 0 : ℝ) ≤ x := by rw [hfirst]; norm_num; exact hx.1
  have hxN : x ≤ (z N : ℝ) := by rw [hlast]; norm_num; exact hx.2
  obtain ⟨i, hi, hix, hxi⟩ := fp_grid_cover (fun k => (z k : ℝ)) N hN hx0 hxN
  have hu : (1 : ℝ) < z i := by exact_mod_cast (hcell i hi).1
  have hw : (1 : ℝ) < (c i).w := by exact_mod_cast (hcell i hi).2.2.2
  have hleft := hend i hi true
  have hright := hend i hi false
  simp only [fpNode, if_true, Bool.false_eq_true, if_false] at hleft hright
  exact fp_cell hu hw hix hxi hleft hright


/-
Directed-logarithm continuation in the same owning source file.

This continuation follows fp_finite_consumer and resolves its private names
in this file. It reuses the existing endpoint/cell/tangent proofs directly.
Kernel and axiom status must be read from current scoped verification receipts.

Only integer range witnesses, exact total-accessor data identities, and
rational field identities replace the logarithmic primitive hypotheses. The full table has
NOT been realized. In particular this is not a concrete finite theorem.
-/

open D5.S3.Arith.GoldenResource.DirectedLogarithmBounds

/-- Range-reduction witness and recorded data identity with the ACTUAL
total accessor at fuel 100. Totality is a theorem, not an evidence field;
there is no successful-run or real-logarithm assumption in this record. -/
private structure FPLogEvaluation (x : ℚ) where
  n : ℕ
  d : ℕ
  k : ℕ
  pair : ℕ × ℕ
  denominator : 0 < d
  range : d * 2 ^ k ≤ n ∧ n < d * 2 ^ (k + 1)
  input : x = (n : ℚ) / d
  positive : 0 < pair.1
  recorded : pair = totalLogBounds n d k

private theorem fp_log_eval_valid {x : ℚ} (e : FPLogEvaluation x) :
    0 < lower e.pair ∧ (lower e.pair : ℝ) ≤ Real.log (x : ℝ) ∧
      Real.log (x : ℝ) ≤ (upper e.pair : ℝ) := by
  have h := (encloses_iff_rat e.pair _).1
    (by
      rw [e.recorded]
      exact (totalLogBounds_correct e.n e.d e.k e.denominator e.range).2)
  have hl : 0 < lower e.pair := by
    unfold lower
    exact div_pos (by exact_mod_cast e.positive) (by norm_num [scale])
  refine ⟨hl, ?_⟩
  simpa only [e.input, Rat.cast_div, Rat.cast_natCast] using h

private def fpLog_first_u : FPLogEvaluation ((1849 : ℚ) / 100) where
  n := 1849
  d := 100
  k := 4
  pair := (2917230045399033478909702117244, 2917230045399033478909702117416)
  denominator := by norm_num
  range := by norm_num
  input := by norm_num [lower, scale]
  positive := by norm_num
  recorded := by decide

private def fpLog_first_v : FPLogEvaluation ((1867 : ℚ) / 100) where
  n := 1867
  d := 100
  k := 4
  pair := (2926917957553631246002738595450, 2926917957553631246002738595622)
  denominator := by norm_num
  range := by norm_num
  input := by norm_num [lower, scale]
  positive := by norm_num
  recorded := by decide

private def fpLog_first_w : FPLogEvaluation ((3716 : ℚ) / 200) where
  n := 3716
  d := 200
  k := 4
  pair := (2922085733385692458672045959162, 2922085733385692458672045959334)
  denominator := by norm_num
  range := by norm_num
  input := by norm_num [lower, scale]
  positive := by norm_num
  recorded := by decide

private def fpLog_first_logWLo : FPLogEvaluation (lower fpLog_first_w.pair) where
  n := 2922085733385692458672045959162
  d := 1000000000000000000000000000000
  k := 1
  pair := (1072297653550266923187835307253, 1072297653550266923187835307316)
  denominator := by norm_num
  range := by norm_num
  input := by norm_num [lower, scale, fpLog_first_w]
  positive := by norm_num
  recorded := by decide

private def fpLog_last_u : FPLogEvaluation ((995838609 : ℚ) / 100) where
  n := 995838609
  d := 100
  k := 23
  pair := (16113925577274391947387699142285, 16113925577274391947387699143198)
  denominator := by norm_num
  range := by norm_num
  input := by norm_num [lower, scale]
  positive := by norm_num
  recorded := by decide

private def fpLog_last_v : FPLogEvaluation ((1000000000 : ℚ) / 100) where
  n := 1000000000
  d := 100
  k := 23
  pair := (16118095650958319788125940182365, 16118095650958319788125940183279)
  denominator := by norm_num
  range := by norm_num
  input := by norm_num [lower, scale]
  positive := by norm_num
  recorded := by decide

private def fpLog_last_w : FPLogEvaluation ((1995838609 : ℚ) / 200) where
  n := 1995838609
  d := 200
  k := 23
  pair := (16116012787804097067940727576424, 16116012787804097067940727577338)
  denominator := by norm_num
  range := by norm_num
  input := by norm_num [lower, scale]
  positive := by norm_num
  recorded := by decide

private def fpLog_last_logWLo : FPLogEvaluation (lower fpLog_last_w.pair) where
  n := 16116012787804097067940727576424
  d := 1000000000000000000000000000000
  k := 4
  pair := (2779813360813775913593635940837, 2779813360813775913593635941001)
  denominator := by norm_num
  range := by norm_num
  input := by norm_num [lower, scale, fpLog_last_w]
  positive := by norm_num
  recorded := by decide

private def fpLog_prime2 : FPLogEvaluation ((2 : ℚ) / 1) where
  n := 2
  d := 1
  k := 1
  pair := (693147180559945309417232121440, 693147180559945309417232121479)
  denominator := by norm_num
  range := by norm_num
  input := by norm_num [lower, scale]
  positive := by norm_num
  recorded := by decide

private def fpLog_X : FPLogEvaluation ((10000000 : ℚ) / 1) where
  n := 10000000
  d := 1
  k := 23
  pair := (16118095650958319788125940182365, 16118095650958319788125940183279)
  denominator := by norm_num
  range := by norm_num
  input := by norm_num [lower, scale]
  positive := by norm_num
  recorded := by decide

private def fpLayerDenomNat (p a : ℕ) : ℕ :=
  ∑ i ∈ Finset.range a, p ^ (i + 1)

private theorem fp_layer_denom_cast (p a : ℕ) :
    (fpLayerDenomNat p a : ℝ) = fpLayerDenom p a := by
  simp [fpLayerDenomNat, fpLayerDenom]

private theorem fp_layer_denom_two {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    2 ≤ fpLayerDenomNat p a := by
  have hzero : 0 ∈ Finset.range a := Finset.mem_range.mpr (by omega)
  have hterm : p ^ (0 + 1) ≤ ∑ i ∈ Finset.range a, p ^ (i + 1) :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (p ^ (i + 1))) hzero
  exact hp.two_le.trans (by simpa [fpLayerDenomNat] using hterm)

private theorem fp_layer_eval_valid {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (pair : ℕ × ℕ) (hrecord : pair = totalLayerBounds (fpLayerDenomNat p a)) :
    Real.log (1 + 1 / fpLayerDenom p a) ≤ (upper pair : ℝ) := by
  have h := (encloses_iff_rat pair _).1
    (by
      rw [hrecord]
      exact (totalLayerBounds_correct _ (fp_layer_denom_two hp ha)).2)
  simpa only [fp_layer_denom_cast] using h.2

/-- Actual rounded layer error, including both ends of the real bracket.
No census validity is inferred from a recorded arithmetic identity. -/
private theorem fp_layer_eval_error {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a)
    (pair : ℕ × ℕ) (hrecord : pair = totalLayerBounds (fpLayerDenomNat p a)) :
    0 ≤ (upper pair : ℝ) - Real.log (1 + 1 / fpLayerDenom p a) ∧
      (upper pair : ℝ) - Real.log (1 + 1 / fpLayerDenom p a) ≤
        100 / (scale : ℝ) := by
  rw [hrecord]
  simpa only [fp_layer_denom_cast] using
    totalLayerBounds_error (fpLayerDenomNat p a) (fp_layer_denom_two hp ha)

/-- Arbitrary-length ACTUAL layer list, counted with multiplicity. This is
consumed in the finite consumer's strengthened conclusion below, so its
budget is available for prefixes as well as the complete recorded list.
No special theorem or ordinary-arithmetic instance for 665320 is added. -/
private theorem fp_layer_list_error (L : List (ℕ × ℕ))
    (pairs : ℕ × ℕ → ℕ × ℕ)
    (hvalid : ∀ pk ∈ L, pk.1.Prime ∧ 1 ≤ pk.2)
    (hrecord : ∀ pk ∈ L, pairs pk = totalLayerBounds (fpLayerDenomNat pk.1 pk.2)) :
    0 ≤ (L.map (fun pk => (upper (pairs pk) : ℝ))).sum -
        (L.map (fun pk => Real.log (1 + 1 / fpLayerDenom pk.1 pk.2))).sum ∧
      (L.map (fun pk => (upper (pairs pk) : ℝ))).sum -
        (L.map (fun pk => Real.log (1 + 1 / fpLayerDenom pk.1 pk.2))).sum ≤
        100 * (L.length : ℝ) / (scale : ℝ) := by
  revert hvalid hrecord
  induction L with
  | nil => intros; simp
  | cons pk L ih =>
    intro hvalid hrecord
    have hv := hvalid pk (by simp)
    have he := fp_layer_eval_error hv.1 hv.2 (pairs pk) (hrecord pk (by simp))
    have ht := ih (fun q hq => hvalid q (by simp [hq]))
      (fun q hq => hrecord q (by simp [hq]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one]
    constructor
    · linarith only [he.1, ht.1]
    · calc
        _ ≤ 100 / (scale : ℝ) + 100 * (L.length : ℝ) / (scale : ℝ) := by
          linarith only [he.2, ht.2]
        _ = 100 * ((L.length : ℝ) + 1) / (scale : ℝ) := by ring

/-- Full logarithm-input data for the existing finite consumer. These are
exact data identities with total algorithms, not a generic validator.
Supplying all these fields for the 1330/665320/664579 packet remains OPEN. -/
private structure FPLogInputs (N : ℕ) (z : ℕ → ℚ) (c : ℕ → FPCell)
    (primes : Finset ℕ) (T : Finset (ℕ × ℕ))
    (lp : ℕ → ℚ) (du : ℕ × ℕ → ℚ) (logXHi : ℚ) where
  prime : ∀ p ∈ primes, FPLogEvaluation (p : ℚ)
  primeLo : ∀ p (hp : p ∈ primes), lp p = lower (prime p hp).pair
  layer : ℕ × ℕ → ℕ × ℕ
  layerRecorded : ∀ pk ∈ T, layer pk = totalLayerBounds (fpLayerDenomNat pk.1 pk.2)
  layerHi : ∀ pk ∈ T, du pk = upper (layer pk)
  xHi : logXHi = upper fpLog_X.pair
  endpoint : ∀ i < N, ∀ b : Bool, FPLogEvaluation (fpNode z i b)
  endpointLo : ∀ i (hi : i < N) (b : Bool),
    (fpEnd (c i) b).logLo = lower (endpoint i hi b).pair
  endpointHi : ∀ i (hi : i < N) (b : Bool),
    (fpEnd (c i) b).logHi = upper (endpoint i hi b).pair
  uLo : ∀ i (hi : i < N), (c i).logULo = lower (endpoint i hi true).pair
  center : ∀ i < N, FPLogEvaluation (c i).w
  centerLo : ∀ i (hi : i < N), (c i).logWLo = lower (center i hi).pair
  logCenter : ∀ i (hi : i < N), FPLogEvaluation (lower (center i hi).pair)
  logCenterLo : ∀ i (hi : i < N), (c i).loglogWLo = lower (logCenter i hi).pair

/-- The total logarithm algorithms consumed on the existing finite path.
The old nonlogarithmic primitive obligations are retained literally.
This PRIVATE conclusion now also exports the actual layer-list error
budget for every list drawn from T whose entries are prime layers. -/
private theorem fp_finite_consumer_directed
    (N : ℕ) (hN : 0 < N) (z : ℕ → ℚ) (c : ℕ → FPCell)
    (primes : Finset ℕ) (A : ℕ → ℕ) (T : Finset (ℕ × ℕ))
    (lp : ℕ → ℚ) (du : ℕ × ℕ → ℚ) (logXHi : ℚ)
    (logs : FPLogInputs N z c primes T lp du logXHi)
    (hfirst : z 0 = 1849 / 100) (hlast : z N = 10000000)
    (hcell : ∀ i < N, (1 : ℚ) < z i ∧ z i ≤ z (i + 1) ∧
      z (i + 1) ≤ 10000000 ∧ 1 < (c i).w)
    (hprimeComplete : ∀ p : ℕ, p.Prime → (p : ℝ) < 10000000 → p ∈ primes)
    (henum : ∀ p ∈ primes, ∀ a : ℕ, 1 ≤ a → a < A p → (p, a) ∈ T)
    (hLayerPrimeRef : ∀ pk ∈ T, pk.1 ∈ primes)
    (hcut : ∀ p ∈ primes, (10000000 : ℚ) * logXHi ≤ (p : ℚ) ^ A p * lp p)
    (hqDef : ∀ i < N, ∀ b : Bool,
      (fpEnd (c i) b).qLo = 1 / (fpNode z i b * (fpEnd (c i) b).logHi) ∧
      (fpEnd (c i) b).qHi = 1 / (fpNode z i b * (fpEnd (c i) b).logLo))
    (hsqrt : ∀ i < N, 0 < (c i).sqrtULo ∧ (c i).sqrtULo ^ 2 ≤ z i)
    (hprefixSubset : ∀ i < N, ∀ b : Bool, (fpEnd (c i) b).prefix ⊆ T)
    (hon : ∀ i < N, ∀ b : Bool, ∀ pk ∈ (fpEnd (c i) b).prefix,
      0 ≤ du pk - (fpEnd (c i) b).qLo * lp pk.1)
    (hoff : ∀ i < N, ∀ b : Bool, ∀ pk ∈ T, pk ∉ (fpEnd (c i) b).prefix →
      du pk - (fpEnd (c i) b).qLo * lp pk.1 ≤ 0)
    (hD : ∀ i < N, ∀ b : Bool,
      ∑ pk ∈ (fpEnd (c i) b).prefix, du pk = (fpEnd (c i) b).D)
    (hL : ∀ i < N, ∀ b : Bool,
      ∑ pk ∈ (fpEnd (c i) b).prefix, lp pk.1 = (fpEnd (c i) b).L)
    (hmargin : ∀ i < N, ∀ b : Bool,
      (fpEnd (c i) b).D - (fpEnd (c i) b).qLo * (fpEnd (c i) b).L +
        (c i).w * (fpEnd (c i) b).qHi <
      (5772156649 / 10 ^ 10 : ℚ) + (c i).loglogWLo -
        1 / (100 * (c i).sqrtULo * (c i).logULo)) :
    (∀ x ∈ Set.Icc (1849 / 100 : ℝ) 10000000,
      pressure (price x) ≤ Real.eulerMascheroniConstant + Real.log (Real.log x) -
        1 / Real.log x - 1 / (100 * Real.sqrt x * Real.log x)) ∧
    (∀ L : List (ℕ × ℕ), (∀ pk ∈ L, pk ∈ T ∧ pk.1.Prime ∧ 1 ≤ pk.2) →
      0 ≤ (L.map (fun pk => (du pk : ℝ))).sum -
          (L.map (fun pk => Real.log (1 + 1 / fpLayerDenom pk.1 pk.2))).sum ∧
        (L.map (fun pk => (du pk : ℝ))).sum -
          (L.map (fun pk => Real.log (1 + 1 / fpLayerDenom pk.1 pk.2))).sum ≤
          100 * (L.length : ℝ) / (scale : ℝ)) := by
  have hbudget (L : List (ℕ × ℕ))
      (hL : ∀ pk ∈ L, pk ∈ T ∧ pk.1.Prime ∧ 1 ≤ pk.2) :
      0 ≤ (L.map (fun pk => (du pk : ℝ))).sum -
          (L.map (fun pk => Real.log (1 + 1 / fpLayerDenom pk.1 pk.2))).sum ∧
        (L.map (fun pk => (du pk : ℝ))).sum -
          (L.map (fun pk => Real.log (1 + 1 / fpLayerDenom pk.1 pk.2))).sum ≤
          100 * (L.length : ℝ) / (scale : ℝ) := by
    have he := fp_layer_list_error L logs.layer
      (fun pk hpk => (hL pk hpk).2)
      (fun pk hpk => logs.layerRecorded pk (hL pk hpk).1)
    have hid : L.map (fun pk => (du pk : ℝ)) =
        L.map (fun pk => (upper (logs.layer pk) : ℝ)) := by
      apply List.map_congr_left
      intro pk hpk
      rw [logs.layerHi pk (hL pk hpk).1]
    rw [hid]
    exact he
  have hlogp (p : ℕ) (hp : p ∈ primes) :
      0 < lp p ∧ (lp p : ℝ) ≤ Real.log p := by
    rw [logs.primeLo p hp]
    have h := fp_log_eval_valid (logs.prime p hp)
    exact ⟨h.1, by simpa using h.2.1⟩
  have hd (pk : ℕ × ℕ) (hpk : pk ∈ T) (hp : pk.1.Prime) (ha : 1 ≤ pk.2) :
      Real.log (1 + 1 / fpLayerDenom pk.1 pk.2) ≤ (du pk : ℝ) := by
    have he := (hbudget [pk] (by
      intro q hq
      have hq' : q = pk := by simpa only [List.mem_singleton] using hq
      subst q
      exact ⟨hpk, hp, ha⟩)).1
    simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, sub_nonneg] using he
  have hlogX : Real.log (10000000 : ℝ) ≤ (logXHi : ℝ) := by
    rw [logs.xHi]
    simpa using (fp_log_eval_valid fpLog_X).2.2
  have heLog (i : ℕ) (hi : i < N) (b : Bool) :
      0 < (fpEnd (c i) b).logLo ∧
      ((fpEnd (c i) b).logLo : ℝ) ≤ Real.log (fpNode z i b : ℝ) ∧
      Real.log (fpNode z i b : ℝ) ≤ ((fpEnd (c i) b).logHi : ℝ) := by
    rw [logs.endpointLo i hi b, logs.endpointHi i hi b]
    exact fp_log_eval_valid (logs.endpoint i hi b)
  have huLog (i : ℕ) (hi : i < N) :
      0 < (c i).logULo ∧ ((c i).logULo : ℝ) ≤ Real.log (z i : ℝ) := by
    rw [logs.uLo i hi]
    have h := fp_log_eval_valid (logs.endpoint i hi true)
    exact ⟨h.1, by simpa only [fpNode, if_true] using h.2.1⟩
  have hwLog (i : ℕ) (hi : i < N) :
      0 < (c i).logWLo ∧ ((c i).logWLo : ℝ) ≤ Real.log ((c i).w : ℝ) := by
    rw [logs.centerLo i hi]
    have h := fp_log_eval_valid (logs.center i hi)
    exact ⟨h.1, h.2.1⟩
  have hwLogLog (i : ℕ) (hi : i < N) :
      ((c i).loglogWLo : ℝ) ≤ Real.log ((c i).logWLo : ℝ) := by
    rw [logs.logCenterLo i hi, logs.centerLo i hi]
    exact (fp_log_eval_valid (logs.logCenter i hi)).2.1
  refine ⟨?_, hbudget⟩
  exact fp_finite_consumer N hN z c primes A T lp du logXHi
    hfirst hlast hcell hprimeComplete henum hLayerPrimeRef hlogp hd hlogX hcut
    heLog hqDef hsqrt huLog hwLog hwLogLog hprefixSubset hon hoff hD hL hmargin

/- The exact first/last-cell evaluations above use ONLY the first and last
records. Their primitive input correspondences follow. Ordinary kernel
`decide` checks the data identities when this module is compiled. -/

private structure FPBoundaryLogs (un vn : ℕ) where
  left : FPLogEvaluation ((un : ℚ) / 100)
  right : FPLogEvaluation ((vn : ℚ) / 100)
  center : FPLogEvaluation (((un + vn : ℕ) : ℚ) / 200)
  logCenter : FPLogEvaluation (lower center.pair)

private def fpFirstBoundary : FPBoundaryLogs 1849 1867 :=
  ⟨fpLog_first_u, fpLog_first_v, fpLog_first_w, fpLog_first_logWLo⟩

private def fpLastBoundary : FPBoundaryLogs 995838609 1000000000 :=
  ⟨fpLog_last_u, fpLog_last_v, fpLog_last_w, fpLog_last_logWLo⟩

/-- Exactly the finite consumer's log primitive shapes, restricted to one
boundary row and its actual stored integer bounds. The field identities
between this data and an FPCell are still required in FPLogInputs. -/
private structure FPBoundaryPrimitives (un vn : ℕ) (e : FPBoundaryLogs un vn) : Prop where
  heLog : ∀ b : Bool,
    let pair := if b then e.left.pair else e.right.pair
    0 < lower pair ∧
    (lower pair : ℝ) ≤ Real.log (if b then (un : ℝ) / 100 else (vn : ℝ) / 100) ∧
    Real.log (if b then (un : ℝ) / 100 else (vn : ℝ) / 100) ≤ (upper pair : ℝ)
  huLog : 0 < lower e.left.pair ∧
    (lower e.left.pair : ℝ) ≤ Real.log ((un : ℝ) / 100)
  hwLog : 0 < lower e.center.pair ∧
    (lower e.center.pair : ℝ) ≤ Real.log (((un + vn : ℕ) : ℝ) / 200)
  hwLogLog : (lower e.logCenter.pair : ℝ) ≤ Real.log (lower e.center.pair : ℝ)

private theorem fp_boundary_primitives (un vn : ℕ) (e : FPBoundaryLogs un vn) :
    FPBoundaryPrimitives un vn e := by
  have hl := fp_log_eval_valid e.left
  have hr := fp_log_eval_valid e.right
  have hw := fp_log_eval_valid e.center
  have hll := fp_log_eval_valid e.logCenter
  constructor
  · intro b
    cases b <;> simp only [Bool.false_eq_true, if_false, if_true]
    · simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hr
    · simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hl
  · exact ⟨hl.1, by simpa using hl.2.1⟩
  · exact ⟨hw.1, by simpa using hw.2.1⟩
  · exact hll.2.1

/-- Partial concrete suppliers: two rows only; this is not FPLogInputs for
all 1330 rows. The full packet instance is not supplied. -/
private theorem fp_first_and_last_log_primitives :
    FPBoundaryPrimitives 1849 1867 fpFirstBoundary ∧
      FPBoundaryPrimitives 995838609 1000000000 fpLastBoundary := by
  exact ⟨fp_boundary_primitives _ _ fpFirstBoundary,
    fp_boundary_primitives _ _ fpLastBoundary⟩

/-- Actual representative hlogp and hd calls. The layer B=2 is p=2,a=1;
B=3 is p=3,a=1. No claim about the unread prime/layer tables follows. -/
private theorem fp_small_prime_layer_primitives :
    (0 < lower fpLog_prime2.pair ∧
      (lower fpLog_prime2.pair : ℝ) ≤ Real.log 2) ∧
    Real.log (1 + 1 / fpLayerDenom 2 1) ≤
      (upper (405465108108164381978013115455, 405465108108164381978013115474) : ℝ) ∧
    Real.log (1 + 1 / fpLayerDenom 3 1) ≤
      (upper (287682072451780927439219005985, 287682072451780927439219006005) : ℝ) := by
  have hp := fp_log_eval_valid fpLog_prime2
  refine ⟨⟨hp.1, by simpa using hp.2.1⟩, ?_, ?_⟩
  · apply fp_layer_eval_valid (by norm_num : Nat.Prime 2) (by norm_num)
    decide
  · apply fp_layer_eval_valid (by norm_num : Nat.Prime 3) (by norm_num)
    decide

private theorem fp_concrete_logX_primitive :
    Real.log (10000000 : ℝ) ≤ (upper fpLog_X.pair : ℝ) := by
  simpa using (fp_log_eval_valid fpLog_X).2.2

end D5.S3.Arith.Robin.ActualRobinInterval
