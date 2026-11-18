/- GID: D5/S3/Arith/Robin/Analytic/RobinExceptionCount
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/RobinExceptionCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp exponential upper counts for Robin and real-power Robin exceptions. -/

import D5.S3.Arith.Robin.Analytic.ExceptionCount.CountingTransfer
import D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionArithmetic
import D5.S3.Arith.Robin.Analytic.ExceptionCount.MertensGap
import D5.S3.Arith.Robin.Analytic.ExceptionCount.ZetaTail

/-! Strict prime-product gaps and local exclusion transfer to both exceptional sets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable
open Real Filter Finset
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.RobinExceptionCount
open OmegaTailUpper OmegaTail ExceptionCount
open LcmPowerEndpointExpansion

private lemma omega_eq_card (n : ℕ) : ArithmeticFunction.cardDistinctFactors n = n.primeFactors.card := by
  simp only [ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]

private lemma cutoff_card {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ,
      (ArithmeticFunction.cardDistinctFactors n : ℝ) ≤ threshold (-eta) x →
        n.primeFactors.card ≤ Nat.primeCounting ⌊PrimeCutoff.cutoff (log (log x))⌋₊ := by
  filter_upwards [(tendsto_log_atTop.comp tendsto_log_atTop).eventually
    PrimeCutoff.enough_primes,
    eventually_gt_atTop (exp 1)] with x hx hx1 n hn
  have hL : 1 < log x := (lt_log_iff_exp_lt ((exp_pos _).trans hx1)).mpr hx1
  have hth : threshold (-eta) x ≤ scale x := by
    dsimp only [threshold]
    have hs := (scale_pos hx1).le
    have hl : 0 < log (log x) := log_pos hL
    have : (-eta) * scale x / log (log x) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith) hs) hl.le
    linarith
  have he : exp (log (log x)) / log (log x) = scale x := by rw [exp_log (by linarith)]; rfl
  dsimp only [Function.comp_apply] at hx
  rw [he] at hx
  dsimp only [PriceRecord.QuantitativePrimeAbel.primeCount] at hx
  rw [omega_eq_card] at hn
  exact_mod_cast (hn.trans hth).trans hx

private lemma robin_local_exclusion (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, x / 2 < n → (n : ℝ) ≤ x →
      (5040 < n ∧ exp eulerMascheroniConstant * n * log (log n) ≤
        (ArithmeticFunction.sigma 1 n : ℝ)) →
      threshold (-eta) x < (ArithmeticFunction.cardDistinctFactors n : ℝ) := by
  have htop := PrimeCutoff.cutoff_top.comp (tendsto_log_atTop.comp tendsto_log_atTop)
  filter_upwards [cutoff_card heta, MertensGap.upper_half_product_gap (by norm_num : (0 : ℝ) < 1) 0,
    htop.eventually_gt_atTop 1, eventually_gt_atTop (4 : ℝ)] with x hc hg hP hx n hnlo _ hn
  by_contra! hsmall
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hpref := ReductionArithmetic.robin_product_upper hP hn0 (hc n hsmall)
  simp only [zero_mul, exp_zero, mul_one] at hg
  have hll : log (log (x / 2)) ≤ log (log (n : ℝ)) := by
    apply log_le_log (log_pos (by linarith : 1 < x / 2))
    exact log_le_log (by linarith : 0 < x / 2) hnlo.le
  have hratio : (ArithmeticFunction.sigma 1 n : ℝ) / n <
      exp eulerMascheroniConstant * log (log (n : ℝ)) :=
    hpref.trans_lt (hg.trans_le (mul_le_mul_of_nonneg_left hll (exp_pos _).le))
  have he := (div_lt_iff₀ hnpos).mp hratio
  nlinarith [hn.2]

private lemma kappa_local_exclusion {delta : ℝ} (hdelta : 0 < delta)
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, x / 2 < n → (n : ℝ) ≤ x →
      (2162160 < n ∧ ∃ κ : ℝ, 1 + delta ≤ κ ∧
        (exp eulerMascheroniConstant * n * log (log n)) ^ κ ≤
          (riemannZeta (κ : ℂ)).re * sigmaKappa κ n) →
      threshold (-eta) x < (ArithmeticFunction.cardDistinctFactors n : ℝ) := by
  obtain ⟨C, hC, hupper⟩ := ReductionArithmetic.kappa_product_tail_upper hdelta
  have htop := PrimeCutoff.cutoff_top.comp (tendsto_log_atTop.comp tendsto_log_atTop)
  filter_upwards [cutoff_card heta,
    MertensGap.upper_half_product_gap (show 0 < delta / 2 by positivity) C,
    htop.eventually_ge_atTop 2, eventually_gt_atTop (4 : ℝ)]
    with x hc hg hP hx n hnlo _ hn
  by_contra! hsmall
  obtain ⟨hnlarge, κ, hκ, hbad⟩ := hn
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hκ0 : 0 < κ := by linarith
  have hpref := hupper κ (PrimeCutoff.cutoff (log (log x))) n hκ hP hn0 (hc n hsmall)
  have hll : log (log (x / 2)) ≤ log (log (n : ℝ)) := by
    apply log_le_log (log_pos (by linarith : 1 < x / 2))
    exact log_le_log (by linarith : 0 < x / 2) hnlo.le
  have hgap : MertensGap.product (PrimeCutoff.cutoff (log (log x))) *
      exp (C * (PrimeCutoff.cutoff (log (log x))) ^ (-(delta / 2))) <
        exp eulerMascheroniConstant * log (log (n : ℝ)) :=
    hg.trans_le (mul_le_mul_of_nonneg_left hll (exp_pos _).le)
  have hM : 0 ≤ MertensGap.product (PrimeCutoff.cutoff (log (log x))) := by
    unfold MertensGap.product
    apply Finset.prod_nonneg
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (mem_filter.mp hp).2.one_lt
    apply inv_nonneg.mpr
    have : 1 / (p : ℝ) < 1 := (div_lt_one (by linarith : (0 : ℝ) < p)).mpr hp1
    linarith
  have hpow := Real.rpow_lt_rpow (mul_nonneg hM (exp_pos _).le) hgap hκ0
  have hstrict := hpref.trans_lt hpow
  have hdiv := (div_lt_iff₀ (Real.rpow_pos_of_pos hnpos κ)).mp hstrict
  have heq : (exp eulerMascheroniConstant * log (log (n : ℝ))) ^ κ * (n : ℝ) ^ κ =
      (exp eulerMascheroniConstant * n * log (log n)) ^ κ := by
    rw [← Real.mul_rpow]
    · congr 1
      ring
    · exact (lt_of_le_of_lt (mul_nonneg hM (exp_pos _).le) hgap).le
    · exact hnpos.le
  rw [heq] at hdiv
  exact (not_lt_of_ge hbad) hdiv

/-- The real-power Robin exceptions, uniformly above every fixed parameter gap,
have the sharp distinct-prime-tail upper exponent. -/
theorem kappa_exception_count {delta epsilon : ℝ} (hdelta : 0 < delta)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop,
      (((Icc 1 ⌊x⌋₊).filter (fun n : ℕ => 2162160 < n ∧
        ∃ κ : ℝ, 1 + delta ≤ κ ∧
          (exp eulerMascheroniConstant * n * log (log n)) ^ κ ≤
            (riemannZeta (κ : ℂ)).re * sigmaKappa κ n)).card : ℝ) ≤
        exp ((C0 + epsilon) * scale x) := by
  classical
  exact CountingTransfer.count_from_local_exclusion _
    (kappa_local_exclusion hdelta) hepsilon

/-- The number of ordinary Robin exceptions has the sharp distinct-prime-tail upper exponent. -/
theorem robin_exception_count {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ x : ℝ in atTop,
      (((Icc 1 ⌊x⌋₊).filter (fun n : ℕ => 5040 < n ∧
        exp eulerMascheroniConstant * n * log (log n) ≤
          (ArithmeticFunction.sigma 1 n : ℝ))).card : ℝ) ≤
        exp ((C0 + epsilon) * scale x) := by
  classical
  exact CountingTransfer.count_from_local_exclusion _ robin_local_exclusion hepsilon

end D5.S3.Arith.Robin.Analytic.RobinExceptionCount
