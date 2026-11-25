/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/ShortGapSeries
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact polynomial and Taylor tail lower bounds for the scalar short-gap test. -/

import D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.NumberTheory.Bernoulli

/-! # From Bernstein lower bounds to the scalar curvature test -/

open Finset Polynomial
open scoped Polynomial

namespace RefinedBMV.PositiveCenter

open D5.S3.Analytic.SeriesInequalities.LorentzLowDegreeCoefficientRemainder

/-- The moment of the equally spaced grid, as an exact polynomial in its spacing.
The extra endpoint term uses the grid from zero through the degree inclusive. -/
def shortGapGridMoment (n : ℕ) (h : ℚ) : ℚ :=
  (∑ i ∈ range (n+1),
    bernoulli i * ((n+1).choose i : ℚ) * (3 : ℚ)^(n+1-i) * h^i / (n+1)) +
    h*(3 : ℚ)^n

theorem shortGapGridMoment_eq {p : ℕ} (hp : 0 < p) (n : ℕ) :
    shortGapGridMoment n (3/(p : ℚ)) =
      (3/(p : ℚ)) * ∑ l ∈ range (p+1), ((3/(p : ℚ))*(l : ℚ))^n := by
  let h : ℚ := 3/(p : ℚ)
  have hpQ : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne'
  have hh : h*(p : ℚ) = 3 := div_mul_cancel₀ 3 hpQ
  change shortGapGridMoment n h = _
  symm
  calc
    _ = h^(n+1) * ∑ l ∈ range (p+1), (l : ℚ)^n := by
      simp_rw [mul_pow, ← mul_sum, pow_succ]
      ring
    _ = _ := by
      rw [sum_range_succ, sum_range_pow, mul_add, mul_sum]
      unfold shortGapGridMoment
      congr 1
      · apply sum_congr rfl
        intro i hi
        have hindex : i ≤ n+1 := (mem_range.mp hi).le
        have hpow : h^(n+1)*(p : ℚ)^(n+1-i) = h^i*3^(n+1-i) := by
          rw [← hh, mul_pow, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hindex]
        calc
          _ = bernoulli i * ((n+1).choose i : ℚ) *
              (h^(n+1)*(p : ℚ)^(n+1-i)) / (n+1) := by ring
          _ = _ := by rw [hpow]; ring
      · rw [pow_succ, mul_right_comm, ← mul_pow, hh, mul_comm]

private theorem bernstein_weight_eq (n i : ℕ) (x : ℝ) :
    (bernsteinPolynomial ℂ n i).eval (x : ℂ) =
      ((n.choose i : ℝ) * x^i * (1-x)^(n-i) : ℝ) := by
  simp [bernsteinPolynomial]

/-- Lower bounds on the ordinary Bernstein coefficients apply on the whole
real unit interval. -/
theorem bernstein_eval_re_lower {P : ℂ[X]} {n : ℕ} (hdegree : P.natDegree ≤ n)
    {x lower : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1)
    (hcoeff : ∀ i ≤ n, lower ≤ (bernsteinCoefficient n i P).re) :
    lower ≤ (P.eval (x : ℂ)).re := by
  let b (i : ℕ) := (n.choose i : ℝ) * x^i * (1-x)^(n-i)
  have hb (i : ℕ) : 0 ≤ b i := by
    unfold b
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx₀ _))
      (pow_nonneg (sub_nonneg.mpr hx₁) _)
  have hweights : ∑ i ∈ range (n+1), b i = 1 := by
    have hs := congrArg (Polynomial.eval x) (bernsteinPolynomial.sum ℝ n)
    simpa [b, eval_finsetSum, bernsteinPolynomial] using hs
  have heval : (P.eval (x : ℂ)).re =
      ∑ i ∈ range (n+1), (bernsteinCoefficient n i P).re * b i := by
    have he := congrArg (fun Q : ℂ[X] ↦ (Q.eval (x : ℂ)).re)
      (bernstein_reconstruction P n hdegree)
    simpa only [eval_finsetSum, eval_mul, eval_C, Complex.re_sum, bernstein_weight_eq,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, b] using he.symm
  rw [heval]
  calc
    lower = lower * ∑ i ∈ range (n+1), b i := by rw [hweights, mul_one]
    _ = ∑ i ∈ range (n+1), lower * b i := by rw [mul_sum]
    _ ≤ _ := sum_le_sum fun i hi ↦
      mul_le_mul_of_nonneg_right (hcoeff i (Nat.lt_succ_iff.mp (mem_range.mp hi))) (hb i)

/-- Bernstein lower bounds for a real polynomial presented as a finite power sum. -/
theorem bernstein_eval_power_lower (a : ℕ → ℝ) (n : ℕ) {x lower : ℝ}
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1)
    (ha : ∀ i ≤ n, lower ≤
      ∑ k ∈ range (n + 1), a k * (i.choose k : ℝ) / (n.choose k : ℝ)) :
    lower ≤ ∑ k ∈ range (n + 1), a k * x ^ k := by
  let P : ℂ[X] := ∑ k ∈ range (n + 1), monomial k (a k : ℂ)
  have hdegree : P.natDegree ≤ n := by
    apply natDegree_sum_le_of_forall_le
    exact fun k hk ↦ (natDegree_monomial_le _).trans (Nat.lt_succ_iff.mp (mem_range.mp hk))
  have hcoeff (k : ℕ) (hk : k ∈ range (n + 1)) : P.coeff k = (a k : ℂ) := by
    simp only [P, finsetSum_coeff, coeff_monomial]
    rw [sum_eq_single_of_mem k hk]
    · simp
    · intro j _ hj
      simp [Ne.symm hj, hj]
  have hbound (i : ℕ) (hi : i ≤ n) : lower ≤ (bernsteinCoefficient n i P).re := by
    unfold bernsteinCoefficient
    rw [Complex.re_sum]
    convert ha i hi using 1
    refine sum_congr rfl fun k hk ↦ ?_
    rw [hcoeff k hk]
    push_cast
    simp
  have h := bernstein_eval_re_lower hdegree hx₀ hx₁ hbound
  simpa only [P, eval_finsetSum, eval_monomial, Complex.re_sum, ← Complex.ofReal_pow,
    ← Complex.ofReal_mul, Complex.ofReal_re] using h

private theorem finite_abel (a : ℕ → ℝ) (x : ℝ) (n : ℕ) :
    (∑ i ∈ range (n+1), a i*x^i) =
      (1-x)*(∑ i ∈ range n, (∑ j ∈ range (i+1), a j)*x^i) +
      (∑ i ∈ range (n+1), a i)*x^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ (fun i ↦ a i*x^i) (n+1), ih,
      sum_range_succ (fun i ↦ (∑ j ∈ range (i+1), a j)*x^i) n,
      sum_range_succ a (n+1), pow_succ]
    ring

/-- The lower bound on every ordinary partial sum also bounds the
exponentially weighted partial sum on the unit interval. -/
theorem partial_sums_lower {a : ℕ → ℝ} {lower x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1)
    (n : ℕ) (ha : ∀ i ≤ n, lower ≤ ∑ j ∈ range (i+1), a j) :
    lower ≤ ∑ i ∈ range (n+1), a i*x^i := by
  rw [finite_abel]
  have hsum : (∑ i ∈ range n, lower*x^i) ≤
      ∑ i ∈ range n, (∑ j ∈ range (i+1), a j)*x^i :=
    sum_le_sum fun i hi ↦
      mul_le_mul_of_nonneg_right (ha i (mem_range.mp hi).le) (pow_nonneg hx₀ _)
  calc
    lower = (1-x)*(∑ i ∈ range n, lower*x^i) + lower*x^n := by
      rw [← mul_sum]
      have hgeom := geom_sum_mul_neg x n
      linear_combination -lower * hgeom
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hx₁))
      (mul_le_mul_of_nonneg_right (ha n le_rfl) (pow_nonneg hx₀ _))

/-- The cumulative Bernstein bound and the tail budget yield the required
strict discriminant sign on the entire interval. -/
theorem shortGap_discriminant_pos_of_series {discriminant x : ℝ} {a : ℕ → ℝ}
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1)
    (hpartial : ∀ i ≤ 88, (31 : ℝ) ≤ ∑ j ∈ range (i+1), a j)
    (htail : |discriminant - ∑ i ∈ range 89, a i*x^i| ≤ 1/100) :
    0 < discriminant := by
  have hp := partial_sums_lower hx₀ hx₁ 88 hpartial
  have ht := (abs_le.mp htail).1
  linarith

/-- Bound the tail after order 18 by comparing successive factorial terms
with the geometric ratio attained at the first omitted index. -/
theorem shortGap_factorial_tail {a : ℕ → ℝ} {x value K R : ℝ}
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (hK : 0 ≤ K) (hR : 0 ≤ R) (hRmax : R < 20)
    (ha : HasSum (fun n ↦ a n * x ^ n) value)
    (hbound : ∀ n ≥ 19, |a n| ≤ K * R ^ n / (n.factorial : ℝ)) :
    |value - ∑ n ∈ range 19, a n * x ^ n| ≤
      (K * R ^ 19 / ((19 : ℕ).factorial : ℝ) / (1 - R / 20)) * x ^ 19 := by
  let base := R ^ 19 / ((19 : ℕ).factorial : ℝ)
  let ratio := R / 20
  have hratio₀ : 0 ≤ ratio := by positivity
  have hratio₁ : ratio < 1 := by dsimp [ratio]; linarith
  have hf (n : ℕ) :
      R ^ (n + 19) / ((n + 19).factorial : ℝ) ≤ base * ratio ^ n := by
    induction n with
    | zero => simp [base]
    | succ n ih =>
      have hn : (20 : ℝ) ≤ ((n + 19 : ℕ) : ℝ) + 1 := by
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) n]
      rw [show n.succ + 19 = (n + 19) + 1 by omega, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_succ, pow_succ R (n + 19), pow_succ ratio n]
      calc
        _ = (R ^ (n + 19) / ((n + 19).factorial : ℝ)) *
            (R / (((n + 19 : ℕ) : ℝ) + 1)) := by
          rw [div_mul_div_comm, mul_comm ((n + 19).factorial : ℝ)]
        _ ≤ (base * ratio ^ n) * ratio := mul_le_mul ih
          (div_le_div_of_nonneg_left hR (by norm_num) hn) (by positivity) (by positivity)
        _ = _ := by ring
  have hgeom := (hasSum_geometric_of_lt_one hratio₀ hratio₁).mul_left (K * base * x ^ 19)
  have htail := (hasSum_nat_add_iff' 19).2 ha
  have hnorm := htail.norm_le_of_bounded hgeom (fun n ↦ by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx₀ _)]
    calc
      _ ≤ (K * (R ^ (n + 19) / ((n + 19).factorial : ℝ))) * x ^ (n + 19) := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hx₀ _)
        simpa only [mul_div_assoc] using hbound (n + 19) (by omega)
      _ ≤ (K * (base * ratio ^ n)) * x ^ 19 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (hf n) hK) _ (by positivity) (by positivity)
        rw [pow_add]
        exact mul_le_of_le_one_left (pow_nonneg hx₀ _) (pow_le_one₀ hx₀ hx₁)
      _ = _ := by ring)
  rw [Real.norm_eq_abs] at hnorm
  exact hnorm.trans_eq (by dsimp [base, ratio]; ring)

/-- Evaluate a coefficient majorant at three to control the terms from
degree 89 onward on the unit interval. -/
theorem shortGap_real_tail_of_majorant {a M : ℕ → ℝ} {x value budget : ℝ}
    (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1) (ha : HasSum (fun n ↦ a n * x^n) value)
    (hM : HasSum M budget) (hM₀ : ∀ n, 0 ≤ M n)
    (hbudget : budget ≤ 3_000_000 * Real.exp 76)
    (hbound : ∀ n, |a n| * 3^n ≤ M n) :
    |value - ∑ n ∈ range 89, a n*x^n| ≤ 1/100 := by
  have htail := (hasSum_nat_add_iff' 89).2 ha
  have htailM := ((hasSum_nat_add_iff' 89).2 hM).div_const ((3 : ℝ)^89)
  have hnorm := htail.norm_le_of_bounded htailM (fun n ↦ by
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hx₀ _)]
    apply (le_div_iff₀ (by positivity : 0 < (3 : ℝ)^89)).2
    calc
      _ ≤ |a (n+89)| * 1 * 3^89 := by
        have hp : x^(n+89) ≤ 1 := pow_le_one₀ hx₀ hx₁
        gcongr
      _ ≤ |a (n+89)| * 3^(n+89) := by
        rw [mul_one, pow_add]
        have hp : (1 : ℝ) ≤ 3^n := one_le_pow₀ (by norm_num)
        exact mul_le_mul_of_nonneg_left
          (le_mul_of_one_le_left (by positivity) hp) (abs_nonneg _)
      _ ≤ _ := hbound (n+89))
  rw [Real.norm_eq_abs] at hnorm
  have hsum : 0 ≤ ∑ n ∈ range 89, M n := sum_nonneg fun n _ ↦ hM₀ n
  have hexp : Real.exp 76 ≤ (11/4 : ℝ)^76 := by
    rw [show (76 : ℝ) = (76 : ℕ) * (1 : ℝ) by norm_num, Real.exp_nat_mul]
    gcongr
    exact Real.exp_one_lt_d9.le.trans (by norm_num : (2.7182818286 : ℝ) ≤ 11/4)
  calc
    _ ≤ (budget - ∑ n ∈ range 89, M n) / (3 : ℝ)^89 := hnorm
    _ ≤ (3_000_000 * (11/4 : ℝ)^76) / (3 : ℝ)^89 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith only [hexp, hsum, hbudget]
    _ ≤ _ := by norm_num

/-- A coefficient convolution represents multiplication of absolutely
summable series in the same chart coordinate. -/
theorem shortGap_hasSum_product {a b : ℕ → ℝ} {x A B : ℝ}
    (ha : HasSum (fun n ↦ a n*x^n) A) (hb : HasSum (fun n ↦ b n*x^n) B)
    (ha' : Summable (fun n ↦ |a n*x^n|)) (hb' : Summable (fun n ↦ |b n*x^n|)) :
    HasSum (fun n ↦ (∑ k ∈ range (n+1), a k*b (n-k))*x^n) (A*B) := by
  have hs := hasSum_sum_range_mul_of_summable_norm
    (f := fun n ↦ a n*x^n) (g := fun n ↦ b n*x^n)
    (by simpa only [Real.norm_eq_abs] using ha') (by simpa only [Real.norm_eq_abs] using hb')
  rw [ha.tsum_eq, hb.tsum_eq] at hs
  refine hs.congr_fun fun n ↦ ?_
  rw [sum_mul]
  refine sum_congr rfl fun k hk ↦ ?_
  rw [show (a k*x^k)*(b (n-k)*x^(n-k)) = (a k*b (n-k))*(x^k*x^(n-k)) by ring,
    ← pow_add, Nat.add_sub_of_le (Nat.lt_succ_iff.mp (mem_range.mp hk))]

/-- Multiplication by the physical gap shifts the coordinate series by
one degree and multiplies the coefficient by two. -/
theorem shortGap_hasSum_times_gap {a : ℕ → ℝ} {x A : ℝ}
    (ha : HasSum (fun n ↦ a n*x^n) A) :
    HasSum (fun n ↦ (match n with | 0 => 0 | k+1 => 2*a k)*x^n) (2*x*A) := by
  apply (hasSum_nat_add_iff' 1).1
  simpa only [sum_range_one, Nat.zero_add, zero_mul, sub_zero, pow_succ] using
    ((ha.mul_left (2*x)).congr_fun fun n ↦ show 2*a n*(x^n*x) = (2*x)*(a n*x^n) by ring)

/-- The coefficient majorant for the discriminant, evaluated at gap six. -/
theorem shortGap_discriminant_majorant_budget :
    let U := 3*Real.exp 18
    let U₁ := 9*Real.exp 18
    let U₂ := 27*Real.exp 18
    let T₂ := 11*Real.exp (54/5)
    16*U^3*T₂^2 + (4*U*U₁ + 6*(2*U*U₂+U₁^2))^2 ≤ 3_000_000*Real.exp 76 := by
  dsimp only
  have h₁ : Real.exp 18 ^ 3 * Real.exp (54/5) ^ 2 = Real.exp (378/5) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    norm_num
  have h₂ : Real.exp 18 ^ 4 = Real.exp 72 := by
    rw [← Real.exp_nat_mul]
    norm_num
  calc
    _ = 52272*(Real.exp 18^3 * Real.exp (54/5)^2) + 2452356*Real.exp 18^4 := by ring
    _ ≤ _ := by
      rw [h₁, h₂]
      have ha := Real.exp_le_exp.mpr (by norm_num : (378/5 : ℝ) ≤ 76)
      have hb := Real.exp_le_exp.mpr (by norm_num : (72 : ℝ) ≤ 76)
      linarith only [ha, hb, Real.exp_pos (76 : ℝ)]

/-- The endpoint slope certificate has the same tail budget. -/
theorem shortGap_slope_majorant_budget :
    let U := 3*Real.exp 18
    let U₁ := 9*Real.exp 18
    let T₁ := 6*Real.exp (54/5)
    (2*U+6*U₁)^2+4*U*T₁^2 ≤ 3_000_000*Real.exp 76 := by
  dsimp only
  have h₁ : Real.exp 18 ^ 2 = Real.exp 36 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h₂ : Real.exp 18 * Real.exp (54/5)^2 = Real.exp (198/5) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    norm_num
  calc
    _ = 3600*Real.exp 18^2+432*(Real.exp 18*Real.exp (54/5)^2) := by ring
    _ ≤ _ := by
      rw [h₁, h₂]
      have ha := Real.exp_le_exp.mpr (by norm_num : (36 : ℝ) ≤ 76)
      have hb := Real.exp_le_exp.mpr (by norm_num : (198/5 : ℝ) ≤ 76)
      linarith only [ha, hb, Real.exp_pos (76 : ℝ)]

#print axioms bernstein_eval_re_lower
#print axioms shortGap_discriminant_pos_of_series
#print axioms shortGapGridMoment_eq
#print axioms shortGap_real_tail_of_majorant

end RefinedBMV.PositiveCenter
