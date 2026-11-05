/- GID: D5/S3/Arith/Robin/OriginalFirstClockTransport
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/OriginalFirstClockTransport
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Original upper integer maximality excludes closed first-clock contacts. -/

import D5.S3.Arith.Robin.DelayedAtomTransport
import D5.S3.Arith.Robin.FinitePulseKernelTransport
import D5.S3.Arith.Robin.GA2ForcedPrimeSource
import D5.S3.Arith.Robin.EulerLayerPhaseSeparation
import D5.S3.Arith.Robin.ActualRobinClockCovariance
import D5.S3.Arith.Robin.OriginalFirstClockBufferEstimates
import D5.S3.Arith.Robin.MellinWeightedVariation
import D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
import D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
import D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Classical

namespace D5.S3.Arith.Robin.OriginalFirstClockTransport

open Set MeasureTheory Finset
open D5.S3.Arith.Robin.DelayedAtomTransport
open D5.S3.Arith.Robin.FinitePulseKernelTransport
open D5.S3.Arith.Robin.GA2ForcedPrimeSource
open D5.S3.Arith.Robin.PaddingRatio (robinRatio)
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResource5040EndpointComparison
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.Robin.OriginalFirstClockBufferEstimates

-- Literal source expressions; these notations create no second price producer.
local notation "λ₀" => D5.S3.Arith.Robin.ActualRobinClockCovariance.g
local notation "w₀" => D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity

/-- The original upper-integer objective, with its nonlinear logarithmic price. -/
def originalObjective (n : ℕ) : ℝ :=
  Real.log ((ArithmeticFunction.sigma 1 n : ℝ)/n) -
    Real.log (Real.log (Real.log (n : ℝ)))

/-- The full positive-integer class; no real-center or fixed-price optimality. -/
def originalMaximizes (p N : ℕ) : Prop :=
  1 ≤ N ∧ 5040*p ∣ N ∧
    ∀ n : ℕ, 1 ≤ n → 5040*p ∣ n → originalObjective n ≤ originalObjective N

/-- The least maximizer in the full class, when attained. -/
def canonicalSource (p : ℕ) : ℕ :=
  if h : ∃ N, originalMaximizes p N then Nat.find h else 0

theorem canonical_source_spec {p : ℕ} (h : ∃ N, originalMaximizes p N) :
    originalMaximizes p (canonicalSource p) ∧
      ∀ N, originalMaximizes p N → canonicalSource p ≤ N := by
  simp only [canonicalSource, dif_pos h]
  exact ⟨Nat.find_spec h, fun N hN => Nat.find_min' h hN⟩

private theorem objective_ratio {n : ℕ} (hn : 5040 < n) :
    originalObjective n = Real.log (robinRatio n)+Real.eulerMascheroniConstant := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hll := D5.S3.Arith.Robin.PaddingRatio.loglog_pos hn
  have he := (Real.exp_pos Real.eulerMascheroniConstant).ne'
  have heq : robinRatio n = ((ArithmeticFunction.sigma 1 n : ℝ)/n)/
      (Real.exp Real.eulerMascheroniConstant*Real.log (Real.log n)) := by
    unfold robinRatio
    field_simp
  have hs : (ArithmeticFunction.sigma 1 n : ℝ)/n ≠ 0 := by
    exact div_ne_zero (by exact_mod_cast (ArithmeticFunction.sigma_pos 1 n (by omega)).ne') hn0
  rw [heq, Real.log_div hs (mul_ne_zero he hll.ne'), Real.log_mul he hll.ne', Real.log_exp]
  unfold originalObjective
  ring

private theorem original_attained_of_ga2 {p a : ℕ} (hp : p.Prime)
    (hforced : 5040*p ∣ a) (hga : actualGA2 a) : ∃ N, originalMaximizes p N := by
  have hm : 3 ≤ 5040*p := by nlinarith [hp.two_le]
  obtain ⟨N, hNm, hdiv, _, _, hmax⟩ := exists_robin_maximizer_multiple_of_ga2 hm hforced hga
  have hN : 5040 < N := by nlinarith [hp.two_le]
  refine ⟨N, by omega, hdiv, ?_⟩
  intro n hn hdn
  have hn' : 5040 < n := by have := Nat.le_of_dvd (by omega : 0 < n) hdn; nlinarith [hp.two_le]
  rw [objective_ratio hn', objective_ratio hN]
  apply add_le_add _ le_rfl
  apply Real.log_le_log
  · unfold robinRatio
    have hs : (0 : ℝ) < ArithmeticFunction.sigma 1 n := by
      exact_mod_cast ArithmeticFunction.sigma_pos 1 n (by omega)
    exact div_pos hs (mul_pos (mul_pos (Real.exp_pos _) (by exact_mod_cast (by omega : 0 < n)))
      (D5.S3.Arith.Robin.PaddingRatio.loglog_pos hn'))
  · exact hmax n hn hdn

/-- Every prime in the literal original label interval, with no subsampling. -/
def originalLabelWindow (ell : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊Real.exp (2*ell)⌋₊).filter (fun p => Real.exp ell ≤ (p : ℝ))

/-- The complete literal label window, with full-domain attained sources. -/
structure OriginalWindow where
  labelStart : ℝ
  labels : Finset ℕ
  complete_labels : labels = originalLabelWindow labelStart
  prime_labels : ∀ p ∈ labels, p.Prime
  attained : ∀ p ∈ labels, ∃ N, originalMaximizes p N

/-- An actual GA2 integer supplies these canonical sources, using the existing
full-class attainment theorem. This supplies no cofinal good-edge existence. -/
def windowOfGA2 (ell : ℝ) (a : ℕ) (hga : actualGA2 a)
    (hforced : ∀ p ∈ originalLabelWindow ell, 5040*p ∣ a) : OriginalWindow where
  labelStart := ell
  labels := originalLabelWindow ell
  complete_labels := rfl
  prime_labels := fun p hp =>
    (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
  attained := fun p hp => original_attained_of_ga2
    (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2 (hforced p hp) hga

/-- Every good consecutive-label edge of the original window, with its literal
closed strict inventory and both canonical endpoint integers. Edge selection is
independent of the later integration bounds. -/
def GoodEdge (X : OriginalWindow) (p r : ℕ) : Prop :=
  p ∈ X.labels ∧ r ∈ X.labels ∧ p < r ∧
  (∀ s ∈ X.labels, ¬(p < s ∧ s < r)) ∧
  ∃ U : ℕ, 0 < U ∧ 5040 ∣ U ∧ canonicalSource p = p*U ∧ canonicalSource r = r*U ∧
    Real.log (canonicalSource p : ℕ) < Real.log (canonicalSource r : ℕ) ∧
    ∀ t ∈ Icc (Real.log (canonicalSource p : ℕ)) (Real.log (canonicalSource r : ℕ)),
      ∀ q : ℕ, U.factorization q = optimalLayerCount (λ₀ t) q

def goodEdges (X : OriginalWindow) : Finset (ℕ × ℕ) :=
  (X.labels.product X.labels).filter (fun e => GoodEdge X e.1 e.2)

/-- Bounds are required of every original good edge; they never filter edges. -/
def OriginalBounds (X : OriginalWindow) (ell R : ℝ) : Prop :=
  ∀ e ∈ goodEdges X, ell ≤ Real.log (canonicalSource e.1 : ℕ) ∧
    Real.log (canonicalSource e.2 : ℕ) ≤ R ∧ 2*R < (e.1 : ℝ) ∧ 2*R < (e.2 : ℝ)

/-- The complete union, independent of bounds, with overlaps counted once. -/
def selectedDomain (X : OriginalWindow) : Set ℝ :=
  ⋃ e ∈ goodEdges X,
    Icc (Real.log (canonicalSource e.1 : ℕ)) (Real.log (canonicalSource e.2 : ℕ))

private theorem original_curve : PriceCurve λ₀ w₀ := by
  have hwpos (x : ℝ) (hx : 1 < x) : 0 < w₀ x := by
    have hl := Real.log_pos hx
    unfold D5.S3.Arith.Robin.ActualRobinClockCovariance.activationDensity
    positivity
  refine ⟨?_, ?_, hwpos, ?_⟩
  · intro x hx
    exact D5.S3.Arith.Robin.ActualRobinClockCovariance.g_has_deriv_at hx
  · intro x hx
    change 1 < x at hx
    have hx0 : x ≠ 0 := by linarith
    have hl := (Real.log_pos hx).ne'
    exact (((Real.continuousAt_log hx0).add continuousAt_const).div
      ((continuousAt_id.pow 2).mul ((Real.continuousAt_log hx0).pow 2))
      (mul_ne_zero (pow_ne_zero 2 hx0) (pow_ne_zero 2 hl))).continuousWithinAt
  · intro x hx y hy hxy
    change 1 < x at hx
    change 1 < y at hy
    have hs := D5.S3.Arith.Robin.MellinWeightedVariation.scaleWeight_antitone
      (x := x) (y := 1) hx (by norm_num) (by linarith : 0 < x) hxy (by simp)
    rw [D5.S3.Arith.Robin.MellinWeightedVariation.scaleWeight_eq,
      D5.S3.Arith.Robin.MellinWeightedVariation.scaleWeight_eq] at hs
    simp only [mul_one] at hs
    change y * w₀ y ≤ x * w₀ x at hs
    nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (hwpos y hy).le]

private theorem first_price_bracket {q : ℕ} (hq : q.Prime) :
    λ₀ ((q : ℝ)+1) < goldenLayerMarginal q 1 ∧ goldenLayerMarginal q 1 < λ₀ q := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hq0 : (0 : ℝ) < q := by linarith
  have hl := Real.log_pos hq1
  have hz : 0 < 1+1/(q : ℝ) := by positivity
  have hz1 : 1+1/(q : ℝ) ≠ 1 := by have := one_div_pos.mpr hq0; linarith
  have hup := Real.log_lt_sub_one_of_pos hz hz1
  have hlow := Real.log_lt_sub_one_of_pos (inv_pos.mpr hz)
    (by intro h; have he := congrArg Inv.inv h; simp only [inv_inv, inv_one] at he; exact hz1 he)
  rw [Real.log_inv] at hlow
  have heq : 1-(1+1/(q : ℝ))⁻¹ = 1/((q : ℝ)+1) := by field_simp; ring
  have hlo : 1/((q : ℝ)+1) < Real.log (1+1/(q : ℝ)) := by rw [← heq]; linarith
  rw [golden_layer_marginal_one_eq_log_one_add_inv hq]
  change 1/(((q : ℝ)+1)*Real.log ((q : ℝ)+1)) < _ ∧
    _ < 1/((q : ℝ)*Real.log q)
  constructor
  · calc
      _ < (1/((q : ℝ)+1))/Real.log q := by
        rw [div_mul_eq_div_div]
        exact div_lt_div_of_pos_left (by positivity) hl
          (Real.log_lt_log hq0 (by linarith))
      _ < _ := (div_lt_div_iff_of_pos_right hl).mpr hlo
  · rw [div_mul_eq_div_div]
    apply (div_lt_div_iff_of_pos_right hl).mpr
    simpa only [add_sub_cancel_left] using hup

private theorem first_clock_exists {q : ℕ} (hq : q.Prime) :
    ∃ y : ℝ, (q : ℝ) < y ∧ y < (q : ℝ)+1 ∧ λ₀ y = goldenLayerMarginal q 1 := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hc : ContinuousOn λ₀ (Icc (q : ℝ) ((q : ℝ)+1)) := by
    intro x hx
    exact (original_curve.derivative x (hq1.trans_le hx.1)).continuousAt.continuousWithinAt
  obtain ⟨y, hy, heq⟩ := intermediate_value_Ioo' (by linarith : (q : ℝ) ≤ q+1) hc
    (first_price_bracket hq)
  exact ⟨y, hy.1, hy.2, heq⟩

/-- Canonical actual first clock; nonprimes have no atom. -/
def firstClock (q : ℕ) : ℝ :=
  if hq : q.Prime then Classical.choose (first_clock_exists hq) else 0

theorem first_clock_spec {q : ℕ} (hq : q.Prime) :
    (q : ℝ) < firstClock q ∧ firstClock q < (q : ℝ)+1 ∧
      λ₀ (firstClock q) = goldenLayerMarginal q 1 := by
  simpa only [firstClock, dif_pos hq] using Classical.choose_spec (first_clock_exists hq)

private theorem contact_density {q : ℕ} (hq : q.Prime) {t : ℝ} (ht : 243 ≤ t)
    (hc : t ∈ Icc (q : ℝ) (firstClock q)) :
    2*w₀ t < Real.log q*w₀ (t+Real.log q) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hq0 : (0 : ℝ) < q := by linarith
  have ht0 : 0 < t := by linarith
  have hlt : 1 < Real.log t := by
    apply (Real.lt_log_iff_exp_lt ht0).mpr
    exact Real.exp_one_lt_three.trans_le (by linarith)
  have hq242 : (242 : ℝ) < q := by
    have hbound := (first_clock_spec hq).2.1
    linarith [hc.2]
  have hh3 : 3 < Real.log (q : ℝ) := by
    apply (Real.lt_log_iff_exp_lt hq0).mpr
    have he : Real.exp (3 : ℝ) < 27 := by
      rw [show (3 : ℝ) = (3 : ℕ)*1 by norm_num, Real.exp_nat_mul]
      have he := pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos _).le
        (by decide : (3 : ℕ) ≠ 0)
      norm_num at he ⊢
      exact he
    linarith
  have hlog243 : Real.log (243 : ℝ) ≤ 10 := by
    rw [show (243 : ℝ) = 3^5 by norm_num, Real.log_pow]
    have hl3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num
    linarith
  have hlogt : Real.log t ≤ t/10 := by
    have hs := Real.log_le_sub_one_of_pos (div_pos ht0 (by norm_num : (0 : ℝ) < 243))
    rw [Real.log_div ht0.ne' (by norm_num)] at hs
    linarith
  have hh : Real.log (q : ℝ) ≤ t/10 :=
    (Real.log_le_log hq0 hc.1).trans hlogt
  have htlog : 0 < Real.log t := by linarith
  have hnext0 : 0 < t+Real.log q := by linarith
  have hnext : t+Real.log q ≤ (11/10)*t := by linarith
  have hlshift : Real.log (t+Real.log q) ≤ (11/10)*Real.log t := by
    have hs := Real.log_le_sub_one_of_pos (div_pos hnext0 ht0)
    rw [Real.log_div hnext0.ne' ht0.ne'] at hs
    have hdiv : (t+Real.log q)/t ≤ 11/10 := (div_le_iff₀ ht0).mpr (by linarith)
    linarith
  have hlmono : Real.log t ≤ Real.log (t+Real.log q) :=
    Real.log_le_log ht0 (by linarith)
  have hlpos : 0 < Real.log (t+Real.log q) := htlog.trans_le hlmono
  have hsqt : (t+Real.log q)^2 ≤ (11/10*t)^2 :=
    (sq_le_sq₀ hnext0.le (by positivity)).mpr hnext
  have hsql : (Real.log (t+Real.log q))^2 ≤ (11/10*Real.log t)^2 :=
    (sq_le_sq₀ hlpos.le (by positivity)).mpr hlshift
  have hden : (t+Real.log q)^2*(Real.log (t+Real.log q))^2 ≤
      (11/10)^4*(t^2*(Real.log t)^2) := by
    have hm := mul_le_mul hsqt hsql (sq_nonneg _) (sq_nonneg _)
    convert! hm using 1 <;> ring
  have hratio : (2/3)*w₀ t < w₀ (t+Real.log q) := by
    have hd0 : 0 < t^2*(Real.log t)^2 := mul_pos (sq_pos_of_pos ht0) (sq_pos_of_pos htlog)
    have hd1 : 0 < (t+Real.log q)^2*(Real.log (t+Real.log q))^2 :=
      mul_pos (sq_pos_of_pos hnext0) (sq_pos_of_pos hlpos)
    change (2/3)*((Real.log t+1)/(t^2*(Real.log t)^2)) <
      (Real.log (t+Real.log q)+1)/((t+Real.log q)^2*(Real.log (t+Real.log q))^2)
    rw [← mul_div_assoc, div_lt_div_iff₀ hd0 hd1]
    have hm := mul_le_mul_of_nonneg_left hden
      (show 0 ≤ (2/3)*(1+Real.log t) by positivity)
    have hs : (2/3)*(11/10)^4 < (1 : ℝ) := by norm_num
    nlinarith [mul_pos (sub_pos.mpr hs) (mul_pos (by linarith : 0 < 1+Real.log t) hd0)]
  have hw := original_curve.positive_weight t (by linarith)
  nlinarith

theorem first_absent {U q : ℕ} (hU : 0 < U) (hq : q.Prime) {t : ℝ}
    (ht : 1 < t) (hc : t ≤ firstClock q)
    (hstrict : ∀ q : ℕ, U.factorization q = optimalLayerCount (λ₀ t) q) : ¬q ∣ U := by
  have hy := first_clock_spec hq
  have hp : goldenLayerMarginal q 1 ≤ λ₀ t := by
    rw [← hy.2.2]
    rcases eq_or_lt_of_le hc with he | he
    · rw [he]
    · exact (D5.S3.Arith.Robin.EulerLayerPhaseSeparation.price_strictAnti ht he).le
  intro hdiv
  have hv := hq.factorization_pos_of_dvd (Nat.ne_of_gt hU) hdiv
  have hm : 1 ∈ Set.Icc 1 (optimalLayerCount (λ₀ t) q) := by rw [← hstrict]; exact ⟨le_rfl, hv⟩
  rw [← positive_layers_eq_count_interval
    (show 0 < λ₀ t from one_div_pos.mpr
      (mul_pos (by linarith) (Real.log_pos ht))) hq] at hm
  exact not_lt_of_ge hp hm.2.2

private theorem integer_insertion_comparison {p N q : ℕ}
    (hmax : originalMaximizes p N) (hq : q.Prime) (habsent : ¬q ∣ N) :
    Real.log (1+1/(q : ℝ)) ≤
      Real.log (Real.log (Real.log (N : ℝ)+Real.log q)) -
      Real.log (Real.log (Real.log (N : ℝ))) := by
  have hn : 1 ≤ N := hmax.1
  have hnq : 1 ≤ N*q := by nlinarith [hq.pos]
  have hd := golden_resource_objective_single_layer_delta 0 hn hq
  rw [golden_resource_sigma_identity 0 hmax.1,
    golden_resource_sigma_identity 0 hnq,
    Nat.factorization_eq_zero_of_not_dvd habsent, zero_add,
    golden_layer_marginal_one_eq_log_one_add_inv hq] at hd
  have hlq := Real.log_pos (by exact_mod_cast hq.one_lt : (1 : ℝ) < q)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hbound := hmax.2.2 (N*q) hnq (hmax.2.1.trans (dvd_mul_right N q))
  dsimp only [originalObjective] at hbound
  rw [Nat.cast_mul, Real.log_mul hN0 hq0] at hbound
  have hdelta : Real.log ((ArithmeticFunction.sigma 1 (N*q) : ℝ)/(N*q : ℕ)) -
      Real.log ((ArithmeticFunction.sigma 1 N : ℝ)/N) = Real.log (1+1/(q : ℝ)) := by
    simpa [hlq.ne'] using hd
  push_cast at hdelta
  linarith

/-- Original integer insertion at the upper endpoint, with the exact log price,
rules out both closed first-clock ties. -/
theorem original_upper_first_clock_exclusion {r U q : ℕ}
    (hU : 0 < U) (hr : r.Prime) (hq : q.Prime)
    (hmax : originalMaximizes r (r*U)) {t R : ℝ}
    (ht : 243 ≤ t) (htR : t ≤ R) (hrR : 2*R < (r : ℝ))
    (htC : t ≤ Real.log (r*U : ℕ))
    (hstrict : ∀ q : ℕ, U.factorization q = optimalLayerCount (λ₀ t) q) :
    t ∉ Icc (q : ℝ) (firstClock q) := by
  intro hc
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have ht1 : 1 < t := by linarith
  have hqr : q ≠ r := by intro he; subst q; linarith [hc.1]
  have hqrdiv : ¬q ∣ r := by simpa [Nat.dvd_prime hr, hq.ne_one] using hqr
  have hqU := first_absent hU hq ht1 hc.2 hstrict
  have hqN : ¬q ∣ r*U := by
    intro h
    exact (hq.dvd_mul.mp h).elim hqrdiv hqU
  have hcmp := integer_insertion_comparison hmax hq hqN
  let C := Real.log (r*U : ℕ)
  let h := Real.log (q : ℝ)
  have hC : 1 < C := ht1.trans_le htC
  have hh : 0 < h := Real.log_pos hq1
  have hcont : ContinuousOn λ₀ (Icc C (C+h)) := by
    intro x hx
    exact (original_curve.derivative x (hC.trans_le hx.1)).continuousAt.continuousWithinAt
  have hi : IntervalIntegrable λ₀ volume C (C+h) :=
    hcont.intervalIntegrable_of_Icc (by linarith)
  have hFTC : (∫ x in C..C+h, λ₀ x) = Real.log (Real.log (C+h))-Real.log (Real.log C) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ => Real.log (Real.log x)) _ hi
    intro x hx
    have hx1 : 1 < x := hC.trans_le (by rw [uIcc_of_le (by linarith : C ≤ C+h)] at hx; exact hx.1)
    have hx0 : x ≠ 0 := by linarith
    have hl := (Real.log_pos hx1).ne'
    convert! (Real.hasDerivAt_log hx0).log hl using 1
    unfold D5.S3.Arith.Robin.ActualRobinClockCovariance.g
    field_simp
    <;> ring
  have hcompat : h*λ₀ (firstClock q) ≤ ∫ x in C..C+h, λ₀ x := by
    rw [hFTC, (first_clock_spec hq).2.2,
      golden_layer_marginal_one_eq_log_one_add_inv hq]
    dsimp only [h, C] at *
    simpa only [mul_div_cancel₀ _ hh.ne'] using hcmp
  exact delayed_atom_exclusion original_curve
    (first_clock_spec hq).2.1 ht1 hh htC hcompat (contact_density hq ht hc) hc

private theorem selected_domain_bounds (X : OriginalWindow) {ell R : ℝ}
    (hbounds : OriginalBounds X ell R) : selectedDomain X ⊆ Icc ell R := by
  intro t ht
  obtain ⟨e, he, ht⟩ := mem_iUnion₂.mp ht
  have hb := hbounds e he
  exact ⟨hb.1.trans ht.1, ht.2.trans hb.2.1⟩

/-- The complete original good-edge union excludes every prime's closed first pulse. -/
theorem complete_original_first_clock_exclusion (X : OriginalWindow) {ell R : ℝ}
    (hell : 243 ≤ ell) (hbounds : OriginalBounds X ell R) :
    ∀ q : ℕ, q.Prime → Disjoint (selectedDomain X) (Icc (q : ℝ) (firstClock q)) := by
  intro q hq
  apply Set.disjoint_left.mpr
  intro t ht hc
  have htbound := selected_domain_bounds X hbounds ht
  obtain ⟨e, he, hte⟩ := mem_iUnion₂.mp ht
  have hg := (Finset.mem_filter.mp he).2
  have hb := hbounds e he
  obtain ⟨hp, hr, _, _, U, hU, _, _, hNr, _, hstrict⟩ := hg
  have hmax := (canonical_source_spec (X.attained e.2 hr)).1
  rw [hNr] at hmax
  apply original_upper_first_clock_exclusion hU (X.prime_labels e.2 hr) hq hmax
    (hell.trans htbound.1) htbound.2 hb.2.2.2 (by simpa [hNr] using hte.2) (hstrict t hte) hc

#print axioms original_upper_first_clock_exclusion
#print axioms complete_original_first_clock_exclusion

-- BEGIN good_edge_prime_buffer: original integer comparisons.
private theorem buffer_price_integrable {s t : ℝ}
    (hs : 1 < s) (hst : s ≤ t) : IntervalIntegrable λ₀ volume s t := by
  have hc : ContinuousOn λ₀ (Icc s t) := by
    intro x hx
    exact (original_curve.derivative x (hs.trans_le hx.1)).continuousAt.continuousWithinAt
  exact hc.intervalIntegrable_of_Icc hst

private theorem buffer_loglog_integral {s t : ℝ}
    (hs : 1 < s) (hst : s ≤ t) :
    (∫ x in s..t, λ₀ x) = Real.log (Real.log t)-Real.log (Real.log s) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => Real.log (Real.log x)) _
    (buffer_price_integrable hs hst)
  intro x hx
  have hx1 : 1 < x := hs.trans_le (by
    rw [uIcc_of_le hst] at hx
    exact hx.1)
  have hx0 : x ≠ 0 := by linarith
  have hl := (Real.log_pos hx1).ne'
  convert! (Real.hasDerivAt_log hx0).log hl using 1
  unfold D5.S3.Arith.Robin.ActualRobinClockCovariance.g
  field_simp
  <;> ring

private theorem buffer_average_left {x h : ℝ}
    (hx : 1 < x-h) (hh : 0 < h) :
    h*λ₀ x+h^2/2*w₀ x ≤ ∫ u in x-h..x, λ₀ u := by
  have horder : x-h ≤ x := by linarith
  have hlinear : IntervalIntegrable
      (fun u => λ₀ x+(x-u)*w₀ x) volume (x-h) x :=
    (show Continuous (fun u => λ₀ x+(x-u)*w₀ x) from by fun_prop).intervalIntegrable _ _
  have hb := intervalIntegral.integral_mono_on horder hlinear
    (buffer_price_integrable hx horder) (fun u hu => by
      have hs := (curve_slope_bounds original_curve (hx.trans_le hu.1) hu.2).1
      linarith)
  have heq : (∫ u in x-h..x, λ₀ x+(x-u)*w₀ x) =
      h*λ₀ x+h^2/2*w₀ x := by
    have hia : IntervalIntegrable (fun u : ℝ => (x-u)*w₀ x) volume (x-h) x :=
      (show Continuous (fun u : ℝ => (x-u)*w₀ x) from by fun_prop).intervalIntegrable _ _
    rw [intervalIntegral.integral_add intervalIntegrable_const hia,
      intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub (f := fun _ : ℝ => x) (g := fun u : ℝ => u)
        intervalIntegrable_const (continuous_id.intervalIntegrable _ _), integral_id]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  exact heq ▸ hb

private theorem buffer_average_right {x h : ℝ}
    (hx : 1 < x) (hh : 0 < h) :
    (∫ u in x..x+h, λ₀ u) ≤ h*λ₀ x-h^2/2*w₀ (x+h) := by
  have horder : x ≤ x+h := by linarith
  have hlinear : IntervalIntegrable
      (fun u => λ₀ x-(u-x)*w₀ (x+h)) volume x (x+h) :=
    (show Continuous (fun u => λ₀ x-(u-x)*w₀ (x+h)) from by fun_prop).intervalIntegrable _ _
  have hb := intervalIntegral.integral_mono_on horder
    (buffer_price_integrable hx horder) hlinear (fun u hu => by
      have hs := (curve_slope_bounds original_curve hx hu.1).1
      have hw := original_curve.antitone_weight (hx.trans_le hu.1)
        (hx.trans_le horder) hu.2
      have hm := mul_le_mul_of_nonneg_left hw (sub_nonneg.mpr hu.1)
      linarith)
  have heq : (∫ u in x..x+h, λ₀ x-(u-x)*w₀ (x+h)) =
      h*λ₀ x-h^2/2*w₀ (x+h) := by
    have hia : IntervalIntegrable (fun u : ℝ => (u-x)*w₀ (x+h)) volume x (x+h) :=
      (show Continuous (fun u : ℝ => (u-x)*w₀ (x+h)) from by fun_prop).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub intervalIntegrable_const hia,
      intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub (f := fun u : ℝ => u) (g := fun _ : ℝ => x)
        (continuous_id.intervalIntegrable _ _) intervalIntegrable_const, integral_id]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  exact hb.trans_eq heq

private theorem buffer_prime_not_dvd_5040 {q : ℕ} (hq : q.Prime)
    (hlarge : (16 : ℝ) < q) : ¬q ∣ 5040 := by
  intro hd
  rw [show (5040 : ℕ) = (16*9*5)*7 by norm_num] at hd
  rcases hq.dvd_mul.mp hd with hd | hd
  · rcases hq.dvd_mul.mp hd with hd | hd
    · rcases hq.dvd_mul.mp hd with hd | hd
      · have h : (q : ℝ) ≤ 16 := by exact_mod_cast Nat.le_of_dvd (by norm_num : 0 < 16) hd
        linarith
      · have h : (q : ℝ) ≤ 9 := by exact_mod_cast Nat.le_of_dvd (by norm_num : 0 < 9) hd
        linarith
    · have h : (q : ℝ) ≤ 5 := by exact_mod_cast Nat.le_of_dvd (by norm_num : 0 < 5) hd
      linarith
  · have h : (q : ℝ) ≤ 7 := by exact_mod_cast Nat.le_of_dvd (by norm_num : 0 < 7) hd
    linarith

private theorem buffer_left_prime_exclusion {p U q : ℕ}
    (hp : p.Prime) (hU : 0 < U) (h5040 : 5040 ∣ U)
    (hmax : originalMaximizes p (p*U)) {a : ℝ}
    (ha : a=Real.log (p*U : ℕ)) (ha256 : 256 ≤ a)
    (hq : q.Prime) (hql : a-2 ≤ (q : ℝ)) (hqu : (q : ℝ) < a)
    (hstrict : ∀ s : ℕ, U.factorization s=optimalLayerCount (λ₀ a) s)
    (hcontact : a ∉ Icc (q : ℝ) (firstClock q)) : False := by
  let h : ℝ := Real.log (q : ℝ)
  have hs := buffer_log_size ha256 hql (by linarith : (q : ℝ) ≤ a+1)
  change 5 < h ∧ h ≤ a/20 at hs
  have hh : 0 < h := by linarith [hs.1]
  have ha1 : 1 < a := by linarith
  have hleft1 : 1 < a-h := by linarith [hs.2]
  have hclock := first_clock_spec hq
  have htau : firstClock q < a := by
    by_contra hn
    exact hcontact ⟨hqu.le, le_of_not_gt hn⟩
  have htau1 : 1 < firstClock q := by linarith [hclock.1]
  have hactive : λ₀ a < goldenLayerMarginal q 1 := by
    rw [← hclock.2.2]
    exact D5.S3.Arith.Robin.EulerLayerPhaseSeparation.price_strictAnti htau1 htau
  have hprice : 0 < λ₀ a := by
    exact one_div_pos.mpr (mul_pos (by linarith) (Real.log_pos ha1))
  have hmemb : 1 ∈ Set.Icc 1 (optimalLayerCount (λ₀ a) q) := by
    rw [← positive_layers_eq_count_interval hprice hq]
    exact ⟨le_rfl, hq, hactive⟩
  have hfac : 0 < U.factorization q := by rw [hstrict q]; exact hmemb.2
  have hqU : q ∣ U := by
    by_contra hn
    have hz := Nat.factorization_eq_zero_of_not_dvd hn
    omega
  have hq5040 := buffer_prime_not_dvd_5040 hq (by linarith : (16 : ℝ) < q)
  obtain ⟨k, hk⟩ := h5040
  have hqk : q ∣ k := by
    rw [hk] at hqU
    exact (hq.dvd_mul.mp hqU).resolve_left hq5040
  obtain ⟨v, hv⟩ := hqk
  let V : ℕ := 5040*v
  have hVq : V*q=U := by rw [hk, hv]; dsimp [V]; ring
  have hV : 0 < V := by
    by_contra hn
    have hz : V=0 := by omega
    rw [hz, zero_mul] at hVq
    omega
  let M : ℕ := p*V
  have hM : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hp.ne_zero hV.ne')
  have hdiv : 5040*p ∣ M := by
    refine ⟨v, ?_⟩
    dsimp [M, V]
    ring
  have hMq : M*q=p*U := by dsimp [M]; rw [Nat.mul_assoc, hVq]
  have hlog : Real.log (M : ℝ)=a-h := by
    have he : a=Real.log (M : ℝ)+h := by
      rw [ha, ← hMq, Nat.cast_mul,
        Real.log_mul (by exact_mod_cast (by omega : M ≠ 0))
          (by exact_mod_cast hq.ne_zero)]
    linarith
  have hcmp := buffer_integer_removal_comparison hM hMq hq
    (by simpa only [originalObjective] using (hmax.2.2 M hM hdiv))
  rw [← ha, hlog] at hcmp
  have heq : h*λ₀ (firstClock q)=Real.log (1+1/(q : ℝ)) := by
    rw [hclock.2.2, golden_layer_marginal_one_eq_log_one_add_inv hq]
    dsimp [h]
    exact mul_div_cancel₀ _ hh.ne'
  have hcompat : (∫ u in a-h..a, λ₀ u) ≤ h*λ₀ (firstClock q) := by
    rw [buffer_loglog_integral hleft1 (by linarith), heq]
    exact hcmp
  have havg := buffer_average_left hleft1 hh
  have hlow : h/2*w₀ a ≤ λ₀ (firstClock q)-λ₀ a := by
    apply (mul_le_mul_iff_left₀ hh).mp
    nlinarith [hcompat, havg]
  have htaul : a-h ≤ firstClock q := by linarith [hs.1, hclock.1]
  have hwm := original_curve.antitone_weight hleft1 htau1 htaul
  have hwn := original_curve.positive_weight (a-h) hleft1
  have hup : λ₀ (firstClock q)-λ₀ a < 2*w₀ (a-h) := by
    calc
      _ ≤ (a-firstClock q)*w₀ (firstClock q) :=
        (curve_slope_bounds original_curve htau1 htau.le).2
      _ ≤ (a-firstClock q)*w₀ (a-h) :=
        mul_le_mul_of_nonneg_left hwm (by linarith)
      _ < 2*w₀ (a-h) := mul_lt_mul_of_pos_right (by linarith [hclock.1]) hwn
  have hdensity := buffer_density_left ha256 hh hs.2
  have hm := mul_le_mul_of_nonneg_left hdensity (show 0 ≤ h/2 by linarith)
  have hbig := mul_pos (show 0 < h/2*(81/100)-2 by linarith [hs.1]) hwn
  nlinarith

private theorem buffer_right_prime_exclusion {r U q : ℕ}
    (hr : r.Prime) (hU : 0 < U)
    (hmax : originalMaximizes r (r*U)) {b : ℝ}
    (hb : b=Real.log (r*U : ℕ)) (hb256 : 256 ≤ b)
    (hq : q.Prime) (hql : b < (q : ℝ)) (hqu : (q : ℝ) ≤ b+1)
    (hqr : q ≠ r)
    (hstrict : ∀ s : ℕ, U.factorization s=optimalLayerCount (λ₀ b) s) : False := by
  let h : ℝ := Real.log (q : ℝ)
  have hs := buffer_log_size hb256 (by linarith : b-2 ≤ (q : ℝ)) hqu
  change 5 < h ∧ h ≤ b/20 at hs
  have hh : 0 < h := by linarith [hs.1]
  have hb1 : 1 < b := by linarith
  have hclock := first_clock_spec hq
  have hbtau : b < firstClock q := by linarith [hclock.1]
  have hqU := first_absent hU hq hb1 hbtau.le hstrict
  have hqrdiv : ¬q ∣ r := by simpa [Nat.dvd_prime hr, hq.ne_one] using hqr
  have hqN : ¬q ∣ r*U := by
    intro hd
    exact (hq.dvd_mul.mp hd).elim hqrdiv hqU
  have hcmp := integer_insertion_comparison hmax hq hqN
  rw [← hb] at hcmp
  change Real.log (1+1/(q : ℝ)) ≤
    Real.log (Real.log (b+h))-Real.log (Real.log b) at hcmp
  have heq : h*λ₀ (firstClock q)=Real.log (1+1/(q : ℝ)) := by
    rw [hclock.2.2, golden_layer_marginal_one_eq_log_one_add_inv hq]
    dsimp [h]
    exact mul_div_cancel₀ _ hh.ne'
  have hcompat : h*λ₀ (firstClock q) ≤ ∫ u in b..b+h, λ₀ u := by
    rw [buffer_loglog_integral hb1 (by linarith), heq]
    exact hcmp
  have havg := buffer_average_right hb1 hh
  have hlow : h/2*w₀ (b+h) ≤ λ₀ b-λ₀ (firstClock q) := by
    apply (mul_le_mul_iff_left₀ hh).mp
    nlinarith [hcompat, havg]
  have hwb := original_curve.positive_weight b hb1
  have hup : λ₀ b-λ₀ (firstClock q) < 2*w₀ b := by
    calc
      _ ≤ (firstClock q-b)*w₀ b :=
        (curve_slope_bounds original_curve hb1 hbtau.le).2
      _ < 2*w₀ b := mul_lt_mul_of_pos_right (by linarith [hclock.2.1]) hwb
  have hdensity := buffer_density_right hb256 hh hs.2
  have hm := mul_lt_mul_of_pos_left hdensity (show 0 < h/2 by linarith)
  have hbig := mul_pos (show 0 < h/2*(81/100)-2 by linarith [hs.1]) hwb
  nlinarith

/-- Actual integer maximality at both ends of an unchanged good edge gives a
two-unit left and one-unit right prime buffer. The additional start is 256;
this theorem supplies neither source existence nor a PC cutoff identification. -/
theorem good_edge_prime_buffer
    (X : OriginalWindow) {ell R : ℝ}
    (hell : 243 ≤ ell) (hbounds : OriginalBounds X ell R)
    {p r : ℕ} (hgood : GoodEdge X p r)
    (ha256 : 256 ≤ Real.log (canonicalSource p : ℕ)) :
    ∀ q : ℕ, q.Prime →
      (q : ℝ) ∉ Icc (Real.log (canonicalSource p : ℕ)-2)
        (Real.log (canonicalSource r : ℕ)+1) := by
  let a : ℝ := Real.log (canonicalSource p : ℕ)
  let b : ℝ := Real.log (canonicalSource r : ℕ)
  have heMem : (p,r) ∈ goodEdges X := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hgood.1, hgood.2.1⟩, hgood⟩
  have hbnd := hbounds (p,r) heMem
  obtain ⟨hp, hr, _, _, U, hU, h5040, hpU, hrU, hab, hstrict⟩ := hgood
  have hpa := X.prime_labels p hp
  have hra := X.prime_labels r hr
  have hmaxp := (canonical_source_spec (X.attained p hp)).1
  have hmaxr := (canonical_source_spec (X.attained r hr)).1
  rw [hpU] at hmaxp
  rw [hrU] at hmaxr
  have ha : a=Real.log (p*U : ℕ) := by dsimp [a]; rw [hpU]
  have hb : b=Real.log (r*U : ℕ) := by dsimp [b]; rw [hrU]
  change a < b at hab
  change 256 ≤ a at ha256
  have hb256 : 256 ≤ b := by linarith
  have hstricta : ∀ s : ℕ, U.factorization s=optimalLayerCount (λ₀ a) s :=
    hstrict a (show a ∈ Icc a b from ⟨le_rfl, hab.le⟩)
  have hstrictb : ∀ s : ℕ, U.factorization s=optimalLayerCount (λ₀ b) s :=
    hstrict b (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)
  have hamem : a ∈ selectedDomain X := by
    exact mem_iUnion₂.mpr ⟨(p,r), heMem, ⟨le_rfl, hab.le⟩⟩
  intro q hq hqI
  change (q : ℝ) ∈ Icc (a-2) (b+1) at hqI
  have hex := complete_original_first_clock_exclusion X hell hbounds q hq
  by_cases hqa : (q : ℝ) < a
  · have hcontact : a ∉ Icc (q : ℝ) (firstClock q) := by
      intro hc
      exact Set.disjoint_left.mp hex hamem hc
    exact buffer_left_prime_exclusion hpa hU h5040 hmaxp ha ha256 hq hqI.1 hqa
      hstricta hcontact
  · have haq : a ≤ (q : ℝ) := le_of_not_gt hqa
    by_cases hqb : (q : ℝ) ≤ b
    · have hqmem : (q : ℝ) ∈ selectedDomain X :=
        mem_iUnion₂.mpr ⟨(p,r), heMem, ⟨haq, hqb⟩⟩
      exact Set.disjoint_left.mp hex hqmem ⟨le_rfl, (first_clock_spec hq).1.le⟩
    · have hbq : b < (q : ℝ) := lt_of_not_ge hqb
      have hqr : q ≠ r := by
        intro heq
        have hcast : (q : ℝ)=(r : ℝ) := by exact_mod_cast heq
        change ell ≤ a ∧ b ≤ R ∧ 2*R < (p : ℝ) ∧ 2*R < (r : ℝ) at hbnd
        linarith [hqI.2, hbnd.2.1, hbnd.2.2.2]
      exact buffer_right_prime_exclusion hra hU hmaxr hb hb256 hq hbq hqI.2 hqr hstrictb
#print axioms good_edge_prime_buffer
-- END good_edge_prime_buffer.

local notation "B₀" => (fun t : ℝ => t+t^(4/5 : ℝ))
local notation "D₀" => (fun t : ℝ => w₀ t*t^(11/10 : ℝ))

private theorem forward_endpoint {t : ℝ} (ht : 1 ≤ t) : t ≤ B₀ t ∧ B₀ t ≤ 2*t := by
  have hh0 := Real.rpow_nonneg (by linarith : 0 ≤ t) (4/5 : ℝ)
  have hh : t^(4/5 : ℝ) ≤ t := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le ht
      (show (4/5 : ℝ) ≤ 1 by norm_num)
  constructor <;> dsimp only <;> linarith

private theorem first_pulse_envelope (I : Finset ℕ) (hI : ∀ q ∈ I, q.Prime)
    {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ (∑ q ∈ I, (Icc (q : ℝ) (firstClock q)).indicator (fun _ => Real.log q) x) ∧
      (∑ q ∈ I, (Icc (q : ℝ) (firstClock q)).indicator (fun _ => Real.log q) x) ≤ Real.log x := by
  have hx0 : 0 ≤ x := by linarith
  have hqfloor (q : ℕ) (hq : q ∈ I) (hc : x ∈ Icc (q : ℝ) (firstClock q)) : q = ⌊x⌋₊ := by
    apply le_antisymm
    · exact (Nat.le_floor_iff hx0).mpr hc.1
    · have hlt : x < (q : ℝ)+1 := hc.2.trans_lt (first_clock_spec (hI q hq)).2.1
      have hn : ⌊x⌋₊ < q+1 := (Nat.floor_lt hx0).mpr (by exact_mod_cast hlt)
      omega
  constructor
  · apply Finset.sum_nonneg
    intro q hq
    by_cases hc : x ∈ Icc (q : ℝ) (firstClock q) <;>
      simp [hc, Real.log_natCast_nonneg]
  · calc
      _ ≤ ∑ q ∈ ({⌊x⌋₊} : Finset ℕ), Real.log q := by
        have he : (∑ q ∈ I, (Icc (q : ℝ) (firstClock q)).indicator (fun _ => Real.log q) x) =
            ∑ q ∈ I.filter (fun q : ℕ => x ∈ Icc (q : ℝ) (firstClock q)), Real.log q := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro q _
          simp [indicator]
        rw [he]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro q hq
          have h := Finset.mem_filter.mp hq
          simpa using hqfloor q h.1 h.2
        · intro q _ _
          exact Real.log_natCast_nonneg q
      _ = Real.log (⌊x⌋₊ : ℝ) := by simp
      _ ≤ Real.log x := Real.log_le_log
        (by exact_mod_cast (Nat.floor_pos.mpr hx)) (Nat.floor_le hx0)

/-- The exact uniform first-layer error. -/
def firstError (t : ℝ) : ℝ := t^(-3/10 : ℝ)*Real.log (2*t)

private theorem local_error {t : ℝ} (ht : 243 ≤ t) :
    0 < D₀ t ∧ 0 ≤ (λ₀ t-λ₀ (B₀ t))/D₀ t ∧
      (λ₀ t-λ₀ (B₀ t))/D₀ t*Real.log (B₀ t) ≤ firstError t := by
  have ht0 : 0 < t := by linarith
  have ht1 : 1 < t := by linarith
  have hb := forward_endpoint (by linarith : 1 ≤ t)
  have hw := original_curve.positive_weight t ht1
  have hp := Real.rpow_pos_of_pos ht0 (11/10 : ℝ)
  have hD : 0 < D₀ t := mul_pos hw hp
  have hs := curve_slope_bounds original_curve ht1 hb.1
  have hn : 0 ≤ λ₀ t-λ₀ (B₀ t) := by
    have hwB := original_curve.positive_weight (B₀ t) (ht1.trans_le hb.1)
    nlinarith [hs.1]
  have hratio : (λ₀ t-λ₀ (B₀ t))/D₀ t ≤ t^(-3/10 : ℝ) := by
    apply (div_le_iff₀ hD).mpr
    have hr : t^(-3/10 : ℝ)*t^(11/10 : ℝ) = t^(4/5 : ℝ) := by
      rw [← Real.rpow_add ht0]
      norm_num
    dsimp only at *
    calc
      _ ≤ (t+t^(4/5 : ℝ)-t)*w₀ t := hs.2
      _ = t^(-3/10 : ℝ)*(w₀ t*t^(11/10 : ℝ)) := by rw [mul_left_comm, hr]; ring
  refine ⟨hD, div_nonneg hn hD.le, ?_⟩
  have hlog := Real.log_le_log (by linarith [hb.1] : 0 < B₀ t) hb.2
  exact mul_le_mul hratio hlog (Real.log_nonneg (by linarith [hb.1]))
    (Real.rpow_nonneg ht0.le _)

private theorem local_first_response {ell R t : ℝ} (X : OriginalWindow)
    (hell : 243 ≤ ell) (hbounds : OriginalBounds X ell R) (ht : t ∈ selectedDomain X) :
    -firstError t ≤
      (∑ q ∈ Nat.primesLE ⌊2*R⌋₊,
        Real.log q*(actualKernel λ₀ t (B₀ t) (D₀ t) (firstClock q)-
          referenceKernel λ₀ t (B₀ t) (D₀ t) q)) ∧
      (∑ q ∈ Nat.primesLE ⌊2*R⌋₊,
        Real.log q*(actualKernel λ₀ t (B₀ t) (D₀ t) (firstClock q)-
          referenceKernel λ₀ t (B₀ t) (D₀ t) q)) ≤ 0 := by
  have hb := selected_domain_bounds X hbounds ht
  have ht243 := hell.trans hb.1
  have hforward := forward_endpoint (by linarith : 1 ≤ t)
  have hprime : ∀ q ∈ Nat.primesLE ⌊2*R⌋₊, q.Prime := fun q hq => (Nat.mem_primesLE.mp hq).2
  have he := complete_original_first_clock_exclusion X hell hbounds
  have hlocal := finite_pulse_bounds (Nat.primesLE ⌊2*R⌋₊) original_curve
    (fun q => (q : ℝ)) firstClock (fun q => Real.log q)
    (fun q hq => (first_clock_spec (hprime q hq)).1)
    (fun q _ => Real.log_natCast_nonneg q) (by linarith : 1 < t) hforward.1
    (local_error ht243).1
    (fun q hq => fun hc => (Set.disjoint_left.mp (he q (hprime q hq))) ht hc)
    (fun x hx => (first_pulse_envelope _ hprime (by linarith [hx.1] : 1 ≤ x)).2.trans
      (Real.log_le_log (by linarith [hx.1] : 0 < x) hx.2))
  refine ⟨?_, hlocal.2⟩
  have hbound := (local_error ht243).2.2
  exact (neg_le_neg hbound).trans (by simpa only [neg_mul, neg_div] using hlocal.1)

#print axioms local_first_response

private theorem error_derivative {t : ℝ} (ht : 0 < t) :
    HasDerivAt firstError
      (t^(-13/10 : ℝ)*(1-(3/10)*Real.log (2*t))) t := by
  have hr := (hasDerivAt_id t).rpow_const
    (Or.inl ht.ne' : t ≠ 0 ∨ 1 ≤ (-3/10 : ℝ))
  have hl := ((hasDerivAt_id t).const_mul 2).log (by positivity : 2*t ≠ 0)
  have hd := hr.mul hl
  convert! hd using 1
  simp only [id_eq, one_mul]
  have he : t^(-3/10 : ℝ) = t^(-13/10 : ℝ)*t := by
    calc
      _ = t^((-13/10 : ℝ)+1) := by norm_num
      _ = _ := by rw [Real.rpow_add ht, Real.rpow_one]
  rw [he]
  norm_num
  field_simp
  <;> ring
/-- The literal error decreases at every original start and tends to zero. -/
theorem first_error_decay : StrictAntiOn firstError (Ici 243) ∧
    Filter.Tendsto firstError Filter.atTop (nhds 0) := by
  have hlog243 : (10/3 : ℝ) < Real.log (2*243 : ℝ) := by
    have he : Real.exp (4 : ℝ) < 81 := by
      have hh := pow_lt_pow_left₀ Real.exp_one_lt_three (Real.exp_pos _).le
        (by decide : (4 : ℕ) ≠ 0)
      rw [← Real.exp_nat_mul] at hh
      norm_num at hh ⊢
      exact hh
    have h4 : 4 < Real.log (2*243 : ℝ) :=
      (Real.lt_log_iff_exp_lt (by norm_num)).mpr (he.trans_le (by norm_num))
    norm_num at h4 ⊢
    linarith
  constructor
  · apply strictAntiOn_of_deriv_neg (convex_Ici 243)
    · intro t ht
      exact (error_derivative (by change 243 ≤ t at ht; linarith)).continuousAt.continuousWithinAt
    · intro t ht
      have ht243 : 243 ≤ t := interior_subset ht
      have ht0 : 0 < t := by linarith
      rw [(error_derivative ht0).deriv]
      have hl : (10/3 : ℝ) < Real.log (2*t) := hlog243.trans_le
        (Real.log_le_log (by norm_num) (by linarith))
      exact mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos ht0 _) (by linarith)
  · have hlog := (isLittleO_log_rpow_atTop (r := (3/10 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
    have hpow := tendsto_inv_atTop_zero.comp
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3/10))
    have hh := hlog.add (hpow.const_mul (Real.log 2))
    simp only [mul_zero, zero_add] at hh
    apply hh.congr'
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    unfold firstError
    rw [show (-3/10 : ℝ) = -(3/10) by ring,
      Real.rpow_neg ht.le, Real.log_mul (by norm_num) ht.ne']
    simp only [Function.comp_apply]
    ring

private theorem domain_compact (X : OriginalWindow) :
    IsCompact (selectedDomain X) :=
  (goodEdges X).isCompact_biUnion (fun _ _ => isCompact_Icc)

private theorem window_continuous {ell R : ℝ} (hell : 243 ≤ ell) :
    ContinuousOn B₀ (Icc ell R) ∧ ContinuousOn D₀ (Icc ell R) := by
  have hb : Continuous B₀ :=
    continuous_id.add (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 4/5))
  refine ⟨hb.continuousOn, ?_⟩
  intro t ht
  have ht1 : 1 < t := by linarith [ht.1]
  have hw := original_curve.continuous_weight t ht1
  exact hw.mono (fun x (hx : x ∈ Icc ell R) => (show 1 < ell by linarith).trans_le hx.1) |>.mul
    ((Real.continuousAt_rpow_const t (11/10 : ℝ) (Or.inl (by linarith : t ≠ 0))).continuousWithinAt)

private theorem original_kernel_integrable (X : OriginalWindow) {ell R : ℝ}
    (hell : 243 ≤ ell) (hbounds : OriginalBounds X ell R) (z : ℝ) :
    IntegrableOn (fun t => referenceKernel λ₀ t (B₀ t) (D₀ t) z) (selectedDomain X) := by
  let S := selectedDomain X
  have hcS := domain_compact X
  have hB := (window_continuous (R := R) hell).1
  have hD := (window_continuous (R := R) hell).2
  have hsub := selected_domain_bounds X hbounds
  have hp : ContinuousOn λ₀ (Ioi 1) := fun x hx =>
    (original_curve.derivative x hx).continuousAt.continuousWithinAt
  have hpB : ContinuousOn (fun t => λ₀ (B₀ t)) (Icc ell R) := hp.comp hB (by
    intro t ht
    exact (show 1 < t by linarith [ht.1]).trans_le (forward_endpoint (by linarith [ht.1])).1)
  have ha : ContinuousOn (fun t => (λ₀ z-λ₀ (B₀ t))/D₀ t) S := by
    apply (continuousOn_const.sub (hpB.mono hsub)).div (hD.mono hsub)
    intro t ht
    exact (local_error (hell.trans (hsub ht).1)).1.ne'
  have hi : IntegrableOn (fun t => (λ₀ z-λ₀ (B₀ t))/D₀ t) S volume :=
    ha.integrableOn_compact hcS
  have hm : MeasurableSet {t : ℝ | t < z ∧ z ≤ B₀ t} := by
    apply MeasurableSet.inter measurableSet_Iio
    have hBc : Continuous B₀ :=
      continuous_id.add (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 4/5))
    exact measurableSet_le (measurable_const : Measurable (fun _ : ℝ => z)) hBc.measurable
  have he : (fun t => referenceKernel λ₀ t (B₀ t) (D₀ t) z) =
      {t : ℝ | t < z ∧ z ≤ B₀ t}.indicator (fun t => (λ₀ z-λ₀ (B₀ t))/D₀ t) := by
    funext t
    simp only [referenceKernel, indicator, mem_ofPred_eq]
  rw [he]
  exact hi.indicator hm

private theorem actual_eq_reference_on_domain (X : OriginalWindow) {ell R : ℝ}
    (hell : 243 ≤ ell) (hbounds : OriginalBounds X ell R) {q : ℕ} (hq : q.Prime) {t : ℝ}
    (ht : t ∈ selectedDomain X) :
    actualKernel λ₀ t (B₀ t) (D₀ t) (firstClock q) =
      referenceKernel λ₀ t (B₀ t) (D₀ t) (firstClock q) := by
  have he : t ≠ firstClock q := by
    intro he
    have hc : t ∈ Icc (q : ℝ) (firstClock q) := by
      rw [he]
      exact ⟨(first_clock_spec hq).1.le, le_rfl⟩
    exact Set.disjoint_left.mp (complete_original_first_clock_exclusion X hell hbounds q hq) ht hc
  have hh : (t ≤ firstClock q) ↔ (t < firstClock q) :=
    ⟨fun h => lt_of_le_of_ne h he, le_of_lt⟩
  simp only [actualKernel, referenceKernel, hh]

private theorem original_kernel_tail (X : OriginalWindow) {ell R : ℝ} (hell : 243 ≤ ell)
    (hbounds : OriginalBounds X ell R)
    {q : ℕ} (hq : q.Prime) (hlarge : 2*R < (q : ℝ)) :
    (∫ t in selectedDomain X, referenceKernel λ₀ t (B₀ t) (D₀ t) q) = 0 ∧
      (∫ t in selectedDomain X, referenceKernel λ₀ t (B₀ t) (D₀ t) (firstClock q)) = 0 := by
  have hzero (z : ℝ) (hz : (q : ℝ) ≤ z) :
      ∀ t ∈ selectedDomain X, referenceKernel λ₀ t (B₀ t) (D₀ t) z = 0 := by
    intro t ht
    have hb := selected_domain_bounds X hbounds ht
    have hf := (forward_endpoint (by have := hell.trans hb.1; linarith : 1 ≤ t)).2
    have hBz : ¬z ≤ B₀ t := by linarith [hb.2]
    simp [referenceKernel, hBz]
  constructor
  · apply setIntegral_eq_zero_of_forall_eq_zero
    exact hzero q le_rfl
  · apply setIntegral_eq_zero_of_forall_eq_zero
    exact hzero (firstClock q) (first_clock_spec hq).1.le

/-- Complete source-faithful first-clock transport. The only sum is over the
single finite prime set q<=2R; all remaining prime contributions vanish. -/
theorem complete_original_first_clock_transport (X : OriginalWindow) {ell R : ℝ}
    (hell : 243 ≤ ell) (hbounds : OriginalBounds X ell R) :
    (∀ q : ℕ, q.Prime → Disjoint (selectedDomain X) (Icc (q : ℝ) (firstClock q))) ∧
    (-firstError ell*volume.real (selectedDomain X) ≤
      ∑ q ∈ Nat.primesLE ⌊2*R⌋₊, Real.log q*
        ((∫ t in selectedDomain X, referenceKernel λ₀ t (B₀ t) (D₀ t) (firstClock q)) -
          (∫ t in selectedDomain X, referenceKernel λ₀ t (B₀ t) (D₀ t) q))) ∧
    (∑ q ∈ Nat.primesLE ⌊2*R⌋₊, Real.log q*
        ((∫ t in selectedDomain X, referenceKernel λ₀ t (B₀ t) (D₀ t) (firstClock q)) -
          (∫ t in selectedDomain X, referenceKernel λ₀ t (B₀ t) (D₀ t) q))) ≤ 0 ∧
    (∀ q : ℕ, q.Prime → 2*R < (q : ℝ) →
      (∫ t in selectedDomain X, referenceKernel λ₀ t (B₀ t) (D₀ t) q) = 0 ∧
        (∫ t in selectedDomain X,
          referenceKernel λ₀ t (B₀ t) (D₀ t) (firstClock q)) = 0) := by
  classical
  let S := selectedDomain X
  let I := Nat.primesLE ⌊2*R⌋₊
  let p := fun t => ∑ q ∈ I, Real.log q*
    (referenceKernel λ₀ t (B₀ t) (D₀ t) (firstClock q)-referenceKernel λ₀ t (B₀ t) (D₀ t) q)
  have hiq (q : ℕ) : IntegrableOn (fun t => Real.log q*
      (referenceKernel λ₀ t (B₀ t) (D₀ t) (firstClock q)-referenceKernel λ₀ t (B₀ t) (D₀ t) q)) S :=
    ((original_kernel_integrable X hell hbounds (firstClock q)).sub
      (original_kernel_integrable X hell hbounds q)).const_mul _
  have hip : IntegrableOn p S := by
    exact integrable_finsetSum I (fun q _ => hiq q)
  have hpid : (∫ t in S, p t) = ∑ q ∈ I, Real.log q*
      ((∫ t in S, referenceKernel λ₀ t (B₀ t) (D₀ t) (firstClock q)) -
        (∫ t in S, referenceKernel λ₀ t (B₀ t) (D₀ t) q)) := by
    rw [integral_finsetSum I (fun q _ => hiq q)]
    apply Finset.sum_congr rfl
    intro q _
    rw [integral_const_mul, integral_sub (original_kernel_integrable X hell hbounds (firstClock q))
      (original_kernel_integrable X hell hbounds q)]
  have hbnd (t : ℝ) (ht : t ∈ S) : -firstError ell ≤ p t ∧ p t ≤ 0 := by
    have hlocal := local_first_response X hell hbounds ht
    have he : (∑ q ∈ I, Real.log q*
        (actualKernel λ₀ t (B₀ t) (D₀ t) (firstClock q)-
          referenceKernel λ₀ t (B₀ t) (D₀ t) q)) = p t := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [actual_eq_reference_on_domain X hell hbounds (Nat.mem_primesLE.mp hq).2 ht]
    rw [he] at hlocal
    have hmono := first_error_decay.1.antitoneOn (show ell ∈ Set.Ici (243 : ℝ) from hell)
      (show t ∈ Set.Ici (243 : ℝ) from hell.trans (selected_domain_bounds X hbounds ht).1)
      (selected_domain_bounds X hbounds ht).1
    exact ⟨by linarith [hlocal.1], hlocal.2⟩
  have hS := (domain_compact X).measurableSet
  have hfinite : volume S ≠ ⊤ := (domain_compact X).measure_lt_top.ne
  have hic : IntegrableOn (fun _ : ℝ => -firstError ell) S := integrableOn_const hfinite
  have hlo := setIntegral_mono_on hic hip hS (fun t ht => (hbnd t ht).1)
  have hup := setIntegral_nonpos (μ := volume) hS (fun t ht => (hbnd t ht).2)
  rw [setIntegral_const, smul_eq_mul, mul_comm, hpid] at hlo
  rw [hpid] at hup
  exact ⟨complete_original_first_clock_exclusion X hell hbounds, hlo, hup,
    fun q hq hqR => original_kernel_tail X hell hbounds hq hqR⟩

#print axioms first_error_decay
#print axioms complete_original_first_clock_transport

end D5.S3.Arith.Robin.OriginalFirstClockTransport
