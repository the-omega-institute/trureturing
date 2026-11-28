/- GID: D5/S3/Weil/Analytic/NymanCenteredPrimeDirichlet
   generality: I
   mirror-B: none(waiver:nyman-centered-prime-analysis)
   mirror-E: none(waiver:nyman-centered-prime-analysis)
   anchors: []
   utility: none
   digest: The centered prime coefficient convolved with Möbius has zero Abel limit. -/

import D5.S3.Weil.Analytic.NymanPrimeDilations
import D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
import Mathlib.NumberTheory.LSeries.SumCoeff

/-! The arithmetic Dirichlet series entering the centered Nyman moment. -/

set_option autoImplicit false

noncomputable section

open ArithmeticFunction Asymptotics Filter Finset
open scoped ArithmeticFunction.Moebius Topology

namespace NymanCenteredPrimeDirichlet

open NymanPrimeDilations (centeredPrimeCoefficient)
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel (theta_error_log_power)

/-- The complex cast of the prime coefficient centered by counting integers. -/
def centeredPrimeCoefficientComplex : ArithmeticFunction ℂ :=
  ⟨fun n => (centeredPrimeCoefficient n : ℂ), by simp [centeredPrimeCoefficient]⟩

private theorem prime_log_sum_Icc (N : ℕ) :
    (∑ n ∈ Icc 1 N, if n.Prime then Real.log (n : ℝ) else 0) =
      Chebyshev.theta (N : ℝ) := by
  rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast, Finset.sum_filter,
    ← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le N)]
  have h : Ioc 0 N = Icc 1 N := rfl
  simp [h]

private theorem centeredPrimeCoefficient_sum {N : ℕ} (hN : 1 ≤ N) :
    (∑ n ∈ Icc 1 N, centeredPrimeCoefficient n) =
      Chebyshev.theta (N : ℝ) - (N : ℝ) + 1 := by
  have hunit : centeredPrimeCoefficient 1 = 0 := by simp [centeredPrimeCoefficient]
  have hprime : (∑ n ∈ Ioc 1 N, if n.Prime then Real.log (n : ℝ) else 0) =
      Chebyshev.theta (N : ℝ) := by
    rw [← prime_log_sum_Icc N, ← Finset.add_sum_Ioc_eq_sum_Icc hN]
    simp [Nat.not_prime_one]
  rw [← Finset.add_sum_Ioc_eq_sum_Icc hN, hunit, zero_add]
  calc
    _ = ∑ n ∈ Ioc 1 N, ((if n.Prime then Real.log (n : ℝ) else 0) - 1) := by
      apply Finset.sum_congr rfl
      intro n hn
      simp [centeredPrimeCoefficient, (mem_Ioc.mp hn).1]
    _ = _ := by
      rw [Finset.sum_sub_distrib, hprime, Finset.sum_const, nsmul_eq_mul,
        Nat.card_Ioc, mul_one, Nat.cast_sub hN, Nat.cast_one]
      ring

private theorem norm_centeredPrimeCoefficient_le (n : ℕ) :
    ‖centeredPrimeCoefficientComplex n‖ ≤
      (if n.Prime then Real.log (n : ℝ) else 0) + 1 := by
  have hp : 0 ≤ (if n.Prime then Real.log (n : ℝ) else 0) := by
    split_ifs with h
    · exact Real.log_nonneg (by exact_mod_cast h.one_le)
    · exact le_rfl
  change ‖((centeredPrimeCoefficient n : ℝ) : ℂ)‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs]
  by_cases hn : 1 < n
  · simp only [centeredPrimeCoefficient, ArithmeticFunction.coe_mk, ite_eq_left hn]
    simpa only [abs_of_nonneg hp, abs_one] using
      abs_sub (if n.Prime then Real.log (n : ℝ) else 0) (1 : ℝ)
  · simp only [centeredPrimeCoefficient, ArithmeticFunction.coe_mk, ite_eq_right hn, abs_zero]
    linarith only [hp]

private theorem norm_centeredPrimePrefix_le (N : ℕ) :
    (∑ n ∈ Icc 1 N, ‖centeredPrimeCoefficientComplex n‖) ≤
      (Real.log 4 + 1) * (N : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Icc 1 N, ((if n.Prime then Real.log (n : ℝ) else 0) + 1) :=
      Finset.sum_le_sum fun n _ => norm_centeredPrimeCoefficient_le n
    _ = Chebyshev.theta (N : ℝ) + (N : ℝ) := by
      rw [Finset.sum_add_distrib, prime_log_sum_Icc, Finset.sum_const, nsmul_eq_mul,
        Nat.card_Icc, Nat.add_sub_cancel, mul_one]
    _ ≤ (Real.log 4 + 1) * (N : ℝ) := by
      have h := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N)
      linarith only [h]

/-- Absolute convergence to the right of one follows from the Chebyshev bound. -/
theorem centeredPrimeCoefficient_lSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable centeredPrimeCoefficientComplex s := by
  refine LSeriesSummable_of_sum_norm_bigO (r := (1 : ℝ)) ?_ zero_le_one hs
  refine IsBigO.of_bound (Real.log 4 + 1) (Eventually.of_forall fun N => ?_)
  have hnonneg : 0 ≤ ∑ n ∈ Icc 1 N, ‖centeredPrimeCoefficientComplex n‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  simpa only [Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg hnonneg,
    abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N)] using
    norm_centeredPrimePrefix_le N

private theorem tendsto_centeredPrimePrefix_div :
    Tendsto (fun n : ℕ => (∑ k ∈ Icc 1 n, centeredPrimeCoefficientComplex k) / n)
      atTop (𝓝 (0 : ℂ)) := by
  have hNat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hθ : Tendsto (fun n : ℕ => (Chebyshev.theta (n : ℝ) - (n : ℝ)) / (n : ℝ))
      atTop (𝓝 0) := by
    simpa only [pow_zero, div_one, Function.comp_def] using
      ((theta_error_log_power 0).tendsto_div_nhds_zero.comp hNat)
  have hOne := hNat.const_div_atTop (1 : ℝ)
  have hReal :
      Tendsto (fun n : ℕ => (∑ k ∈ Icc 1 n, centeredPrimeCoefficient k) / (n : ℝ))
        atTop (𝓝 0) := by
    have hsum := hθ.add hOne
    rw [add_zero] at hsum
    apply hsum.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    rw [centeredPrimeCoefficient_sum hn, add_div]
  simpa only [Complex.ofReal_zero, Complex.ofReal_div, Complex.ofReal_sum,
    Complex.ofReal_natCast, centeredPrimeCoefficientComplex, ArithmeticFunction.coe_mk]
    using hReal.ofReal

private theorem tendsto_centeredPrimeCoefficient_normalized :
    Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * LSeries centeredPrimeCoefficientComplex (σ : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℂ)) :=
  LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div
    (f := fun n => centeredPrimeCoefficientComplex n) tendsto_centeredPrimePrefix_div
    (fun σ hσ => centeredPrimeCoefficient_lSeriesSummable (by simpa using hσ))

private theorem tendsto_zeta_normalized :
    Tendsto (fun σ : ℝ => ((σ : ℂ) - 1) * riemannZeta (σ : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
  have hmap : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    refine Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin ?_
    intro σ hσ
    change (σ : ℂ) ≠ 1
    intro he
    have h : σ = 1 := by simpa using congrArg Complex.re he
    exact (Set.mem_Ioi.mp hσ).ne' h
  exact riemannZeta_residue_one.comp hmap

private theorem centeredPrimeConvolution_lSeries_eq_div {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (centeredPrimeCoefficientComplex * (μ : ArithmeticFunction ℂ)) n) s =
      LSeries centeredPrimeCoefficientComplex s / riemannZeta s := by
  have hvsum : LSeriesSummable centeredPrimeCoefficientComplex s :=
    centeredPrimeCoefficient_lSeriesSummable hs
  have hμsum : LSeriesSummable (μ : ArithmeticFunction ℂ) s :=
    LSeriesSummable_moebius_iff.mpr hs
  have hprod := @ArithmeticFunction.LSeries_mul' centeredPrimeCoefficientComplex
    (μ : ArithmeticFunction ℂ) s hvsum hμsum
  have hμ := LSeries_zeta_mul_Lseries_moebius hs
  rw [LSeries_zeta_eq_riemannZeta hs] at hμ
  have hμInv : LSeries (μ : ArithmeticFunction ℂ) s = 1 / riemannZeta s := by
    apply (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs)).2
    rw [mul_comm]
    exact hμ
  calc
    LSeries (fun n => (centeredPrimeCoefficientComplex * (μ : ArithmeticFunction ℂ)) n) s =
      LSeries centeredPrimeCoefficientComplex s * LSeries (μ : ArithmeticFunction ℂ) s := hprod
    _ = LSeries centeredPrimeCoefficientComplex s / riemannZeta s := by
      rw [hμInv, mul_one_div]

/-- The Abel limit of the Dirichlet series of the centered prime coefficient
convolved with Möbius is zero. -/
theorem tendsto_centeredPrimeConvolution_lSeries :
    Tendsto (fun σ : ℝ =>
      LSeries (fun n => (centeredPrimeCoefficientComplex * (μ : ArithmeticFunction ℂ)) n) (σ : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  have hquot :
      Tendsto (fun σ : ℝ =>
        (((σ : ℂ) - 1) * LSeries centeredPrimeCoefficientComplex (σ : ℂ)) /
          (((σ : ℂ) - 1) * riemannZeta (σ : ℂ)))
        (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℂ)) := by
    have h := tendsto_centeredPrimeCoefficient_normalized.div tendsto_zeta_normalized
      (one_ne_zero : (1 : ℂ) ≠ 0)
    change Tendsto (fun σ : ℝ =>
      (((σ : ℂ) - 1) * LSeries centeredPrimeCoefficientComplex (σ : ℂ)) /
        (((σ : ℂ) - 1) * riemannZeta (σ : ℂ))) (𝓝[>] (1 : ℝ)) (𝓝 ((0 : ℂ) / 1)) at h
    rwa [zero_div] at h
  apply hquot.congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hσ' : 1 < (σ : ℂ).re := by simpa using Set.mem_Ioi.mp hσ
  have hσone : (σ : ℂ) ≠ 1 := by
    intro he
    simp [he] at hσ'
  change (((σ : ℂ) - 1) * LSeries centeredPrimeCoefficientComplex (σ : ℂ)) /
        (((σ : ℂ) - 1) * riemannZeta (σ : ℂ)) =
    LSeries (fun n => (centeredPrimeCoefficientComplex * (μ : ArithmeticFunction ℂ)) n) (σ : ℂ)
  rw [mul_div_mul_left _ _ (sub_ne_zero.mpr hσone),
    centeredPrimeConvolution_lSeries_eq_div hσ']

end NymanCenteredPrimeDirichlet
