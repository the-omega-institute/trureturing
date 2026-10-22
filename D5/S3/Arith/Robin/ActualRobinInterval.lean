/-
The original Robin margin is transferred between same-price optimizers
using the sigma/n support line, optimizer tie equality, and proved strict
concavity of gamma + log(log A). The log-log composition argument follows
the local infrastructure of ThresholdChainReduction.

EndpointRobinEstimates and BoundaryRobinEstimates are the unpaid analytic
families. The reduction retains every integer above 5040, including the
finite Icc 5041 boundaryCap region, and proves no unconditional Robin or RH.
-/

import D5.S3.Arith.Robin.ActualGlobalBracketing
import D5.S3.Arith.GoldenResource.ThresholdChainReduction

noncomputable section

namespace D5.S3.Arith.Robin.ActualRobinInterval

open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.ActualGlobalBracketing
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

/-- UNPAID ORIGINAL estimates for EVERY integer in the finite boundary
region, exactly 5041 <= n <= boundaryCap. No integer is silently dropped. -/
def BoundaryRobinEstimates : Prop :=
  ∀ n : ℕ, 5040 < n → n ≤ boundaryCap → 0 < robinLogMargin n

/-- FINAL MEANINGFUL CONSUMER. Coverage itself has no premise: it is
derived from all_integer_bracketing, including all ties and every n>5040.
Only genuine endpoint positivity and the precise finite original boundary
estimates remain hypotheses. They are NOT proved by this candidate. -/
theorem global_robin_margin_reduction
    (hEndpoint : EndpointRobinEstimates) (hBoundary : BoundaryRobinEstimates) :
    ∀ n : ℕ, 5040 < n → 0 < robinLogMargin n := by
  intro n hn
  rcases coverage_above_5040 hn with hfinite | ⟨q, hq, hB, hBn, hnU⟩
  · exact hBoundary n hn hfinite
  · have hm := hEndpoint q hq hB
    exact optimizer_interval_positive hq (by omega) hBn hnU (strict_is_optimal hq)
      (maximalInteger_spec hq).2.2.1 hm.1 hm.2

/-- This reduction preserves the full original margin target in both
directions. It does not smuggle any boundary or endpoint estimate into
a finiteness/cofinality/bracketing certificate. -/
theorem global_margin_iff_unpaid_estimates :
    (∀ n : ℕ, 5040 < n → 0 < robinLogMargin n) ↔
      EndpointRobinEstimates ∧ BoundaryRobinEstimates := by
  constructor
  · intro hall
    constructor
    · intro q hq hB
      have hBU : strictInteger q ≤ maximalInteger q :=
        Nat.le_of_dvd (by have := (maximalInteger_spec hq).1; omega) (strict_dvd_weak hq)
      exact ⟨hall _ hB, hall _ (lt_of_lt_of_le hB hBU)⟩
    · intro n hn _
      exact hall n hn
  · rintro ⟨hEndpoint, hBoundary⟩
    exact global_robin_margin_reduction hEndpoint hBoundary

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
    (hEndpoint : EndpointRobinEstimates) (hBoundary : BoundaryRobinEstimates) :
    ∀ n : ℕ, 5040 < n → (ArithmeticFunction.sigma 1 n : ℝ) <
      Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) := by
  intro n hn
  exact original_robin_of_margin (by omega)
    (global_robin_margin_reduction hEndpoint hBoundary n hn)

end D5.S3.Arith.Robin.ActualRobinInterval
