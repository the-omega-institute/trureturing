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

end D5.S3.Arith.Robin.ActualRobinInterval
