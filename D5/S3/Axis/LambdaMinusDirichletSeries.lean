/- GID: D5/S3/Axis/LambdaMinusDirichletSeries
   generality: I
   mirror-B: D5/B/S3/Axis/LambdaMinusDirichletSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The contraction-face Dirichlet series splits into zeta times its prime-axis series. -/

import D5.S1.Deficit.LambdaMinusAdditive
import D5.S1.Deficit.Displacement.GoldenContractionRadicalBound
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.PrimesInAP

/- Library-search audit trail (2026-08-17):
   * No repository or pinned-Mathlib theorem packages this Dirichlet identity.
   * `lambdaMinus_coprime_add` and
     `abs_lambdaMinus_le_goldenRatio_inv_log_primeRadical` are exact repository
     component hits and are applied below.
   * `ArithmeticFunction.LSeries_mul'`,
     `ArithmeticFunction.LSeries_zeta_eq_riemannZeta`, and
     `tsum_eq_tsum_primes_of_support_subset_prime_powers` are exact Mathlib
     component hits and are applied below. -/

open scoped ArithmeticFunction LSeries
open D5.S1.Deficit
open D5.S1.Deficit.AlmostAdditivity
open D5.S1.Deficit.LambdaMinusAdditive
open GoldenContractionRadicalBound

namespace D5.S3.Axis.LambdaMinusDirichletSeries

noncomputable section

private theorem beta_contraction_zero : betaContraction 0 = 0 := by
  simp [betaContraction, betaGolden, betaDigits,
    D5.S1.Digit.Z, D5.S1.Digit.toRaw,
    D5.S0.Conventions.wEncoding, Nat.zeckendorfEquiv,
    D5.S1.Digit.rawOfZeckendorf]

private theorem lambda_minus_prime_pow {p e : ℕ} (hp : p.Prime) :
    lambdaMinus (p ^ e) = betaContraction e * Real.log p := by
  rw [lambdaMinus, hp.factorization_pow]
  exact Finsupp.sum_single_index (by simp [beta_contraction_zero])

/-- The existing contraction reading, bundled as a complex arithmetic function. -/
private noncomputable def lambdaArithmetic : ArithmeticFunction ℂ :=
  ⟨fun n => (lambdaMinus n : ℂ), by simp [lambdaMinus]⟩

/-- The prime-power coefficient obtained by taking one exponent difference. -/
private noncomputable def axisArithmetic : ArithmeticFunction ℂ :=
  ⟨fun n => if IsPrimePow n then
      ((betaContraction (n.factorization n.minFac) -
          betaContraction (n.factorization n.minFac - 1)) * Real.log n.minFac : ℂ)
    else 0,
    by simp⟩

private theorem axis_arithmetic_prime_pow {p k : ℕ} (hp : p.Prime) :
    axisArithmetic (p ^ (k + 1)) =
      ((betaContraction (k + 1) - betaContraction k) * Real.log p : ℂ) := by
  have his : IsPrimePow (p ^ (k + 1)) :=
    (isPrimePow_pow_iff (Nat.succ_ne_zero k)).mpr hp.prime.isPrimePow
  rw [axisArithmetic]
  simp [his, hp.pow_minFac, Nat.Prime.factorization_self hp]

private theorem axis_sum_prime_pow {p k : ℕ} (hp : p.Prime) :
    ∑ d ∈ (p ^ k).divisors, axisArithmetic d = lambdaArithmetic (p ^ k) := by
  induction k with
  | zero => simp [axisArithmetic, lambdaArithmetic, lambdaMinus, beta_contraction_zero]
  | succ k ih =>
      rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ]
      rw [← Nat.sum_divisors_prime_pow hp, ih, axis_arithmetic_prime_pow hp,
        show lambdaArithmetic (p ^ k) = (lambdaMinus (p ^ k) : ℂ) from rfl,
        show lambdaArithmetic (p ^ (k + 1)) =
          (lambdaMinus (p ^ (k + 1)) : ℂ) from rfl,
        lambda_minus_prime_pow hp, lambda_minus_prime_pow hp]
      push_cast
      ring

private theorem axis_sum (n : ℕ) :
    ∑ d ∈ n.divisors, axisArithmetic d = lambdaArithmetic n := by
  refine Nat.recOnPrimeCoprime ?_ ?_ ?_ n
  · simp [axisArithmetic, lambdaArithmetic, lambdaMinus]
  · exact fun p k hp => axis_sum_prime_pow hp
  · intro a b ha hb hab hia hib
    simp only [axisArithmetic, ArithmeticFunction.coe_mk, ← Finset.sum_filter] at hia hib ⊢
    rw [Nat.mul_divisors_filter_prime_pow hab, Finset.filter_union,
      Finset.sum_union (Nat.disjoint_divisors_filter_isPrimePow hab), hia, hib]
    simp only [lambdaArithmetic, ArithmeticFunction.coe_mk]
    rw [lambdaMinus_coprime_add hab]
    push_cast
    rfl

private theorem axis_mul_zeta :
    axisArithmetic * (ArithmeticFunction.zeta : ArithmeticFunction ℂ) = lambdaArithmetic := by
  ext n
  rw [ArithmeticFunction.coe_mul_zeta_apply, axis_sum]

private theorem beta_contraction_abs_lt_one (v : ℕ) : |betaContraction v| < 1 := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [beta_contraction_zero]
  · have hpow : 2 ^ v ≠ 0 := pow_ne_zero _ (by norm_num)
    have hrad : primeRadical (2 ^ v) = 2 := by
      rw [primeRadical, Nat.primeFactors_prime_pow hv Nat.prime_two]
      simp
    have hbound :=
      abs_lambdaMinus_le_goldenRatio_inv_log_primeRadical hpow
    rw [lambda_minus_prime_pow Nat.prime_two, hrad, abs_mul] at hbound
    have hlog : 0 < Real.log ((2 : ℕ) : ℝ) := Real.log_pos (by norm_num)
    rw [abs_of_pos hlog] at hbound
    have hbeta : |betaContraction v| ≤ Real.goldenRatio⁻¹ :=
      le_of_mul_le_mul_right hbound hlog
    exact hbeta.trans_lt (inv_lt_one_of_one_lt₀ Real.one_lt_goldenRatio)

private theorem axis_norm_le_two_von_mangoldt (n : ℕ) :
    ‖axisArithmetic n‖ ≤
      ‖(2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ)‖ := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [axis_arithmetic_prime_pow hp]
    rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero k),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_two]
    have hlog : 0 ≤ Real.log (p : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hp.one_le)
    rw [abs_of_nonneg hlog]
    apply mul_le_mul_of_nonneg_right _ hlog
    calc
      ‖(betaContraction (k + 1) : ℂ) - (betaContraction k : ℂ)‖ =
          |betaContraction (k + 1) - betaContraction k| := by
            rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |betaContraction (k + 1)| + |betaContraction k| := abs_sub _ _
      _ ≤ 2 := by
        linarith [beta_contraction_abs_lt_one (k + 1),
          beta_contraction_abs_lt_one k]
  · rw [axisArithmetic]
    simp only [ArithmeticFunction.coe_mk, if_neg hn, norm_zero]
    exact norm_nonneg _

private theorem axis_lseries_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (axisArithmetic ·) s := by
  have hmajor : LSeriesSummable
      ((2 : ℂ) • fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).smul 2
  rw [LSeriesSummable, ← summable_norm_iff] at hmajor ⊢
  refine hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
  exact LSeries.norm_term_le s (by simpa using axis_norm_le_two_von_mangoldt n)

private theorem norm_prime_cpow_neg_lt_one (s : ℂ) (hs : 1 < s.re)
    (p : Nat.Primes) : ‖(p : ℂ) ^ (-s)‖ < 1 := by
  rw [Complex.norm_natCast_cpow_of_pos p.prop.pos]
  exact Real.rpow_lt_one_of_one_lt_of_neg
    (by exact_mod_cast p.prop.one_lt) (by simp; linarith)

private theorem beta_geometric_summable {q : ℂ} (hq : ‖q‖ < 1) :
    Summable (fun k : ℕ => (betaContraction k : ℂ) * q ^ k) := by
  apply Summable.of_norm
  refine (summable_geometric_of_norm_lt_one hq).norm.of_nonneg_of_le
    (fun _ => norm_nonneg _) (fun k => ?_)
  rw [norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  simpa only [Complex.norm_real, Real.norm_eq_abs] using
    (beta_contraction_abs_lt_one k).le

private theorem beta_difference_tsum {q : ℂ} (hq : ‖q‖ < 1) :
    (∑' k : ℕ, ((betaContraction (k + 1) - betaContraction k : ℝ) : ℂ) * q ^ (k + 1)) =
      (1 - q) * ∑' k : ℕ, (betaContraction (k + 1) : ℂ) * q ^ (k + 1) := by
  let f : ℕ → ℂ := fun k => (betaContraction k : ℂ) * q ^ k
  have hf : Summable f := beta_geometric_summable hq
  have htail : Summable (fun k => f (k + 1)) :=
    (summable_nat_add_iff 1).mpr hf
  have hqf : Summable (fun k => q * f k) := hf.mul_left q
  calc
    (∑' k : ℕ, ((betaContraction (k + 1) - betaContraction k : ℝ) : ℂ) *
        q ^ (k + 1)) = ∑' k : ℕ, (f (k + 1) - q * f k) := by
          apply tsum_congr
          intro k
          simp only [f, pow_succ']
          push_cast
          ring
    _ = (∑' k : ℕ, f (k + 1)) - ∑' k : ℕ, q * f k :=
      htail.tsum_sub hqf
    _ = (∑' k : ℕ, f (k + 1)) - q * ∑' k : ℕ, f k := by
      rw [hf.tsum_mul_left]
    _ = (∑' k : ℕ, f (k + 1)) - q * ∑' k : ℕ, f (k + 1) := by
      rw [hf.tsum_eq_zero_add]
      simp [f, beta_contraction_zero]
    _ = (1 - q) * ∑' k : ℕ, (betaContraction (k + 1) : ℂ) * q ^ (k + 1) := by
      simp only [f]
      ring

/-- The prime-axis factor in the contraction-face Dirichlet decomposition. -/
noncomputable def lambdaMinusAxisSeries (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes,
    (Real.log (p : ℕ) : ℂ) * (1 - (p : ℂ) ^ (-s)) *
      ∑' k : ℕ, (betaContraction (k + 1) : ℂ) *
        ((p : ℂ) ^ (-s)) ^ (k + 1)

private theorem axis_term_prime_pow (s : ℂ) (p : Nat.Primes) (k : ℕ) :
    LSeries.term (axisArithmetic ·) s ((p : ℕ) ^ (k + 1)) =
      (Real.log (p : ℕ) : ℂ) *
        ((betaContraction (k + 1) - betaContraction k : ℝ) : ℂ) *
          ((p : ℂ) ^ (-s)) ^ (k + 1) := by
  let pn : ℕ := p
  change LSeries.term (axisArithmetic ·) s (pn ^ (k + 1)) = _
  rw [LSeries.term_of_ne_zero (pow_ne_zero _ p.prop.ne_zero),
    axis_arithmetic_prime_pow p.prop, div_eq_mul_inv, ← Complex.cpow_neg]
  change ((betaContraction (k + 1) - betaContraction k) * Real.log pn : ℂ) *
      ((pn ^ (k + 1) : ℕ) : ℂ) ^ (-s) = _
  have hpow : (((pn ^ (k + 1) : ℕ) : ℂ) ^ (-s)) =
      ((pn : ℂ) ^ (-s)) ^ (k + 1) := by
    rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul pn (k + 1) (-s),
      Complex.cpow_nat_mul]
  rw [hpow]
  dsimp only [pn]
  push_cast
  ring

private theorem axis_lseries_eq_axis_series {s : ℂ} (hs : 1 < s.re) :
    LSeries (axisArithmetic ·) s = lambdaMinusAxisSeries s := by
  have hsum := axis_lseries_summable hs
  have hsupport : Function.support (LSeries.term (axisArithmetic ·) s) ⊆
      {n : ℕ | IsPrimePow n} := by
    intro n hn
    by_contra hprime
    have hprime' : ¬IsPrimePow n := by simpa using hprime
    exact hn (by simp [LSeries.term, axisArithmetic, hprime'])
  rw [LSeries, tsum_eq_tsum_primes_of_support_subset_prime_powers hsum hsupport,
    lambdaMinusAxisSeries]
  apply tsum_congr
  intro p
  simp_rw [axis_term_prime_pow s p]
  calc
    (∑' k : ℕ, (Real.log (p : ℕ) : ℂ) *
        ((betaContraction (k + 1) - betaContraction k : ℝ) : ℂ) *
          ((p : ℂ) ^ (-s)) ^ (k + 1)) =
        (Real.log (p : ℕ) : ℂ) *
          ∑' k : ℕ, ((betaContraction (k + 1) - betaContraction k : ℝ) : ℂ) *
            ((p : ℂ) ^ (-s)) ^ (k + 1) := by
              rw [← tsum_mul_left]
              apply tsum_congr
              intro k
              ring
    _ = (Real.log (p : ℕ) : ℂ) * (1 - (p : ℂ) ^ (-s)) *
          ∑' k : ℕ, (betaContraction (k + 1) : ℂ) *
            ((p : ℂ) ^ (-s)) ^ (k + 1) := by
              rw [beta_difference_tsum (norm_prime_cpow_neg_lt_one s hs p)]
              ring

/-- For `re s > 1`, the contraction-face Dirichlet series is zeta times its
prime-axis series, and every contraction exponent lies in the unit window. -/
theorem lambda_minus_dirichlet_series (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n : ℕ => (lambdaMinus n : ℂ)) s =
        riemannZeta s * lambdaMinusAxisSeries s ∧
      ∀ v : ℕ, |betaContraction v| < 1 := by
  change LSeries (lambdaArithmetic ·) s =
      riemannZeta s * lambdaMinusAxisSeries s ∧
    ∀ v : ℕ, |betaContraction v| < 1
  constructor
  · calc
      LSeries (lambdaArithmetic ·) s =
          LSeries ((axisArithmetic *
            (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) ·) s := by
            rw [axis_mul_zeta]
      _ = LSeries (axisArithmetic ·) s *
          LSeries ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) ·) s :=
        ArithmeticFunction.LSeries_mul' (axis_lseries_summable hs)
          (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs)
      _ = riemannZeta s * lambdaMinusAxisSeries s := by
        have hzeta : LSeries
            ((ArithmeticFunction.zeta : ArithmeticFunction ℂ) ·) s = riemannZeta s := by
          simpa only [ArithmeticFunction.natCoe_apply] using
            ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
        rw [hzeta, axis_lseries_eq_axis_series hs]
        ring
  · exact beta_contraction_abs_lt_one

#print axioms lambda_minus_dirichlet_series

end

end D5.S3.Axis.LambdaMinusDirichletSeries
