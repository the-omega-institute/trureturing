/- GID: D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/CompactMarginalQuadrature
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact closed-mesh and signed quadrature formulas for the regularized marginal. -/

import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactPositiveMomentTails
import D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactRegularizedRadical
import D5.S3.FluidDynamics.Fourier.PeriodicAllenCahnDecay
import D5.S3.Weil.ZetaPntBase.EulerMaclaurinSixth
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-! Signed quadrature remainders for the regularized refined BMV marginal. -/

open scoped BigOperators

noncomputable section

namespace RefinedBMV.PositiveCenter

open DimThree (gaps gaps_length_eq_choose)
open D5.S3.Weil.ZetaPntBase.EulerMaclaurinSixth
  (abs_meshRemainder_le meshRemainder meshRemainder_nonneg mesh_sum_eq)
open SmallCorner

open private gridPoint gridAverage gaps_length_pos gridAverage_eq_marginal
  gridAverage_const_mul gridAverage_sub gridAverage_pow_eq centered_variance_eq from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactPositiveMomentTails
open private compositionMoment_marginal_sum from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.ShortGapNormalization

/-- The mass normalization for the closed marginal mesh of spacing `h`. -/
def compactMarginalMeshDenominator (h : ℝ) : ℝ := (3 + h) * (3 + 2 * h)

/-- The regularized exponential remainder multiplied by the affine marginal weight. -/
def regularizedMarginalIntegrand (h t x : ℝ) : ℝ :=
  (2 + h - x) * regularizedMarginalRemainder t x

/-- The pointwise regularized remainder and all its parameter derivatives have one
integral representation, including at a zero parameter. -/
theorem iteratedDeriv_regularizedMarginalRemainder_parameter (j : ℕ) (x t : ℝ) :
    iteratedDeriv j (fun r ↦ regularizedMarginalRemainder r x) t =
      x ^ 2 * (∫ s in (0 : ℝ)..1, (1 - s) * (x * s) ^ j * Real.exp (t * (x * s))) := by
  have hzero (r : ℝ) : regularizedMarginalRemainder r x =
      x ^ 2 * (∫ s in (0 : ℝ)..1, (1 - s) * Real.exp (r * (x * s))) := by
    by_cases hr : r = 0
    · subst r
      have h : (∫ s in (0 : ℝ)..1, 1 - s) = (1 : ℝ) / 2 := by
        rw [intervalIntegral.integral_sub (f := fun _ : ℝ ↦ (1 : ℝ)) (g := fun s : ℝ ↦ s)
          (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _)]
        norm_num [intervalIntegral.integral_const, integral_id, smul_eq_mul]
      simp only [regularizedMarginalRemainder, ite_true, zero_mul, Real.exp_zero, mul_one, h]
      ring
    · rw [regularizedMarginalRemainder, ite_eq_right hr, exp_quadratic_remainder_eq_integral]
      apply (div_eq_iff (pow_ne_zero _ hr)).2
      simp only [mul_assoc r, mul_pow]
      ring
  induction j generalizing t with
  | zero => simpa only [iteratedDeriv_zero, pow_zero, mul_one] using hzero t
  | succ j ih =>
      rw [iteratedDeriv_succ, show iteratedDeriv j (fun r ↦ regularizedMarginalRemainder r x) =
        fun t ↦ x ^ 2 * (∫ s in (0 : ℝ)..1, (1 - s) * (x * s) ^ j * Real.exp (t * (x * s)))
        from funext ih]
      exact ((hasDerivAt_exponential_moment_integral x j t).const_mul (x ^ 2)).deriv

/-- The shifted exponential series gives the exact pointwise coefficients used for
the first two parameter derivatives and the regularized value itself. -/
theorem iteratedDeriv_regularizedMarginalRemainder_eq_tsum (j : ℕ) (x t : ℝ) :
    iteratedDeriv j (fun r ↦ regularizedMarginalRemainder r x) t =
      ∑' n : ℕ, (1 / ((((j + n : ℕ) : ℝ) + 1) * (((j + n : ℕ) : ℝ) + 2))) *
        (t ^ n / n.factorial) * x ^ (j + n + 2) := by
  let f (n : ℕ) : C(ℝ, ℝ) := ⟨fun s ↦ (1 - s) * (x * s) ^ j *
    ((t * (x * s)) ^ n / n.factorial), by fun_prop⟩
  let majorant (n : ℕ) := |x| ^ j * (|t * x| ^ n / n.factorial)
  have hmaj : Summable majorant := (Real.summable_pow_div_factorial |t * x|).mul_left _
  have hnorm : Summable fun n ↦
      ‖(f n).restrict (⟨Set.uIcc (0 : ℝ) 1, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ := by
    apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) _ hmaj
    intro n
    refine (ContinuousMap.norm_le _ (show 0 ≤ majorant n by unfold majorant; positivity)).mpr ?_
    intro s
    let y : ℝ := s
    have hs : y ∈ Set.uIcc (0 : ℝ) 1 := s.property
    have hy : y ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le zero_le_one] using hs
    have hb : |x * y| ≤ |x| := by
      rw [abs_mul, abs_of_nonneg hy.1]
      exact mul_le_of_le_one_right (abs_nonneg x) hy.2
    have ht : |t * (x * y)| ≤ |t * x| := by
      rw [← mul_assoc, abs_mul, abs_of_nonneg hy.1]
      exact mul_le_of_le_one_right (abs_nonneg _) hy.2
    have hw : |1 - y| ≤ 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hy.2)]; linarith [hy.1]
    change |(1 - y) * (x * y) ^ j * ((t * (x * y)) ^ n / n.factorial)| ≤ majorant n
    rw [abs_mul, abs_mul, abs_pow, abs_div, abs_pow,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n.factorial)]
    calc
      _ ≤ 1 * |x| ^ j * (|t * x| ^ n / n.factorial) :=
        mul_le_mul (mul_le_mul hw (pow_le_pow_left₀ (abs_nonneg _) hb j) (by positivity) zero_le_one)
          (div_le_div_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) ht n) (Nat.cast_nonneg _))
          (by positivity) (by positivity)
      _ = _ := by simp [majorant]
  have hint := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
    (a := (0 : ℝ)) (b := 1) hnorm
  rw [iteratedDeriv_regularizedMarginalRemainder_parameter]
  calc
    _ = x ^ 2 * (∫ s in (0 : ℝ)..1, ∑' n, f n s) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s _
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
      change (1 - s) * (x * s) ^ j * ((∑' n : ℕ, (t * (x * s)) ^ n / n.factorial)) = _
      rw [← tsum_mul_left]
      rfl
    _ = x ^ 2 * (∑' n : ℕ, ∫ s in (0 : ℝ)..1, f n s) := by rw [← hint]
    _ = _ := by
      rw [← tsum_mul_left]
      refine tsum_congr fun n ↦ ?_
      have hf (s : ℝ) : f n s =
          (x ^ (j + n) * (t ^ n / n.factorial)) * ((1 - s) * s ^ (j + n)) := by
        simp only [f, ContinuousMap.coe_mk, mul_pow, pow_add]
        ring
      simp_rw [hf]
      rw [intervalIntegral.integral_const_mul, unit_weight_moment, pow_add x (j + n) 2]
      ring

private theorem compactKappa_mul_compactZ_eq_gridAverage {p : ℕ} (hp : 0 < p) (t : ℝ) :
    compactKappa p * compactZ p t = gridAverage p (regularizedMarginalRemainder t) := by
  by_cases ht : t = 0
  · subst t
    have hvariance : gridAverage p (fun x ↦ x ^ 2) = (1 + 3 / (p : ℝ)) / 2 := by
      rw [gridAverage_eq_marginal]
      exact centered_variance_eq hp
    rw [regularizedMarginalRemainder, ite_eq_left (rfl : (0 : ℝ) = 0)]
    simp only [compactZ_zero hp, mul_one, div_eq_inv_mul, gridAverage_const_mul, hvariance,
      compactKappa]
    ring
  · have hone : gridAverage p (fun _ ↦ 1) = 1 := by
      simpa only [pow_zero, compactCenteredMomentPolynomial] using gridAverage_pow_eq hp 0
    have hmean : gridAverage p (fun x ↦ x) = 0 := by
      simpa only [pow_one, compactCenteredMomentPolynomial] using gridAverage_pow_eq hp 1
    have hlinear : gridAverage p (fun x ↦ t * x) = 0 := by
      rw [gridAverage_const_mul, hmean, mul_zero]
    have hexp : compositionMoment p 0 t = gridAverage p (fun x ↦ Real.exp (t * x)) - 1 := by
      rw [compositionMoment_marginal_sum, gridAverage]
      apply congrArg (· - 1)
      apply congrArg (· / ((gaps p).length : ℝ))
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [mul_comm t]
      rfl
    have hQ : compactKappa p * compactZ p t = compositionMoment p 0 t / t ^ 2 := by
      apply (eq_div_iff (pow_ne_zero _ ht)).2
      rw [compositionMoment_eq_compactZ hp]
      ring
    rw [hQ, hexp, regularizedMarginalRemainder, ite_eq_right ht]
    simp only [div_eq_inv_mul, gridAverage_const_mul, gridAverage_sub, hone, hlinear, sub_zero]

private theorem mul_marginal_step {p : ℕ} (hp : 0 < p) :
    (p : ℝ) * (3 / (p : ℝ)) = 3 := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp [hpR]

/-- The exact marginal is a weighted closed sum over all `p + 1` nodes, including at `t = 0`. -/
theorem compactKappa_mul_compactZ_eq_mesh_sum {p : ℕ} (hp : 0 < p) (t : ℝ) :
    let h : ℝ := 3 / (p : ℝ)
    compactKappa p * compactZ p t = 2 * h / compactMarginalMeshDenominator h *
      ∑ i ∈ Finset.range (p + 1), regularizedMarginalIntegrand h t (-1 + (i : ℝ) * h) := by
  let h : ℝ := 3 / (p : ℝ)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 < h := div_pos (by norm_num) hpR
  have hph : (p : ℝ) * h = 3 := mul_marginal_step hp
  have hmass : ((gaps p).length : ℝ) * h ^ 2 = compactMarginalMeshDenominator h / 2 := by
    rw [gaps_length_eq_choose]
    exact tail_choose_scale hp
  have hweight (i : ℕ) (hi : i ∈ Finset.range (p + 1)) :
      ((p + 1 - i : ℕ) : ℝ) * h = 2 + h - (-1 + (i : ℝ) * h) := by
    rw [Nat.cast_sub (Finset.mem_range.mp hi).le, Nat.cast_add, Nat.cast_one]
    linear_combination hph
  have hsum :
      h * (∑ i ∈ Finset.range (p + 1),
        ((p + 1 - i : ℕ) : ℝ) * regularizedMarginalRemainder t (gridPoint p i)) =
      ∑ i ∈ Finset.range (p + 1), regularizedMarginalIntegrand h t (-1 + (i : ℝ) * h) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hnode : gridPoint p i = -1 + (i : ℝ) * h := by
      unfold gridPoint h
      ring
    rw [hnode, regularizedMarginalIntegrand, ← hweight i hi]
    ring
  change compactKappa p * compactZ p t = 2 * h / compactMarginalMeshDenominator h *
    ∑ i ∈ Finset.range (p + 1), regularizedMarginalIntegrand h t (-1 + (i : ℝ) * h)
  rw [compactKappa_mul_compactZ_eq_gridAverage hp, gridAverage, ← hsum]
  rw [show compactMarginalMeshDenominator h = 2 * ((gaps p).length : ℝ) * h ^ 2 by
    linear_combination -2 * hmass]
  field_simp [hh.ne', (gaps_length_pos p).ne']

/-- The Euler–Maclaurin quadrature through order four for the closed mesh on [-1, 2]. -/
def compactClosedQuadrature (h : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ x in (-1 : ℝ)..2, f x) + h / 2 * (f (-1) + f 2) +
    h ^ 2 / 12 * (iteratedDeriv 1 f 2 - iteratedDeriv 1 f (-1)) -
    h ^ 4 / 720 * (iteratedDeriv 3 f 2 - iteratedDeriv 3 f (-1))

/-- The rational coefficients of h⁰ through h⁴ returned by the short-gap checker's
quadrature_monomial for x^k. -/
def compactQuadratureMonomialCoefficients (k : ℕ) : Fin 5 → ℚ :=
  ![((2 : ℚ) ^ (k + 1) - (-1 : ℚ) ^ (k + 1)) / (k + 1),
    ((2 : ℚ) ^ k + (-1 : ℚ) ^ k) / 2,
    if 1 ≤ k then (k : ℚ) * ((2 : ℚ) ^ (k - 1) - (-1 : ℚ) ^ (k - 1)) / 12 else 0,
    0,
    if 3 ≤ k then
      -((k.factorial / (k - 3).factorial : ℕ) : ℚ) *
        ((2 : ℚ) ^ (k - 3) - (-1 : ℚ) ^ (k - 3)) / 720
    else 0]

private theorem monomial_endpoint_deriv_sub (k j : ℕ) :
    iteratedDeriv j (fun x : ℝ ↦ x ^ k) 2 - iteratedDeriv j (fun x : ℝ ↦ x ^ k) (-1) =
      (k.descFactorial j : ℝ) * (2 ^ (k - j) - (-1) ^ (k - j)) := by
  simp only [iteratedDeriv_pow, mul_sub]

/-- Evaluating the rational monomial row at any real spacing gives the closed quadrature. -/
theorem compactClosedQuadrature_monomial (h : ℝ) (k : ℕ) :
    compactClosedQuadrature h (fun x ↦ x ^ k) =
      ∑ i : Fin 5, (compactQuadratureMonomialCoefficients k i : ℝ) * h ^ (i : ℕ) := by
  have hfirst :
      iteratedDeriv 1 (fun x : ℝ ↦ x ^ k) 2 - iteratedDeriv 1 (fun x : ℝ ↦ x ^ k) (-1) =
        if 1 ≤ k then (k : ℝ) * (2 ^ (k - 1) - (-1) ^ (k - 1)) else 0 := by
    rw [monomial_endpoint_deriv_sub, Nat.descFactorial_one]
    by_cases hk : 1 ≤ k
    · rw [ite_eq_left hk]
    · have hk0 : k = 0 := by omega
      simp [hk0]
  have hthird :
      iteratedDeriv 3 (fun x : ℝ ↦ x ^ k) 2 - iteratedDeriv 3 (fun x : ℝ ↦ x ^ k) (-1) =
        if 3 ≤ k then
          ((k.factorial / (k - 3).factorial : ℕ) : ℝ) *
            (2 ^ (k - 3) - (-1) ^ (k - 3))
        else 0 := by
    rw [monomial_endpoint_deriv_sub]
    by_cases hk : 3 ≤ k
    · rw [ite_eq_left hk, Nat.descFactorial_eq_div hk]
    · rw [ite_eq_right hk, Nat.descFactorial_of_lt (Nat.lt_of_not_ge hk), Nat.cast_zero, zero_mul]
  unfold compactClosedQuadrature
  rw [integral_pow, hfirst, hthird]
  simp only [compactQuadratureMonomialCoefficients, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ]
  split_ifs <;> push_cast <;> ring

/-- A finite Taylor polynomial is evaluated by taking the same linear combination of
the exact quadrature rows. -/
theorem compactClosedQuadrature_polynomial (h : ℝ) (n : ℕ) (c : ℕ → ℝ) :
    compactClosedQuadrature h (fun x ↦ ∑ k ∈ Finset.range n, c k * x ^ k) =
      ∑ k ∈ Finset.range n,
        c k * (∑ i : Fin 5, (compactQuadratureMonomialCoefficients k i : ℝ) * h ^ (i : ℕ)) := by
  let f (k : ℕ) (x : ℝ) := c k * x ^ k
  have hf (k : ℕ) : ContDiff ℝ ⊤ (f k) := by
    unfold f
    fun_prop
  have hint : (∫ x in (-1 : ℝ)..2, ∑ k ∈ Finset.range n, f k x) =
      ∑ k ∈ Finset.range n, ∫ x in (-1 : ℝ)..2, f k x :=
    intervalIntegral.integral_finsetSum fun k _ ↦ (hf k).continuous.intervalIntegrable _ _
  have hd (j : ℕ) (x : ℝ) : iteratedDeriv j (fun y ↦ ∑ k ∈ Finset.range n, f k y) x =
      ∑ k ∈ Finset.range n, iteratedDeriv j (f k) x :=
    iteratedDeriv_fun_sum fun k _ ↦ ((hf k).of_le le_top).contDiffAt
  change compactClosedQuadrature h (fun x ↦ ∑ k ∈ Finset.range n, f k x) = _
  calc
    _ = ∑ k ∈ Finset.range n, compactClosedQuadrature h (f k) := by
      unfold compactClosedQuadrature
      rw [hint, hd 1 2, hd 1 (-1), hd 3 2, hd 3 (-1)]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub, Finset.mul_sum]
    _ = _ := Finset.sum_congr rfl fun k _ ↦ by
      rw [← compactClosedQuadrature_monomial]
      unfold compactClosedQuadrature f
      simp only [intervalIntegral.integral_const_mul, iteratedDeriv_const_mul_field]
      ring

/-- Closed quadrature commutes with a factorially weighted series of monomials. -/
theorem compactClosedQuadrature_tsum {C : ℝ} (h t : ℝ) (offset : ℕ) (weight : ℕ → ℝ)
    (hw : ∀ n, |weight n| ≤ C) :
    compactClosedQuadrature h (fun x ↦ ∑' n : ℕ, weight n * t ^ n / n.factorial *
      x ^ (n + offset)) =
      ∑' n : ℕ, weight n * t ^ n / n.factorial *
        compactClosedQuadrature h (fun x ↦ x ^ (n + offset)) := by
  let c (n : ℕ) : ℝ := weight n * t ^ n / n.factorial
  let f (n : ℕ) (x : ℝ) := c n * x ^ (n + offset)
  let F (x : ℝ) := ∑' n, f n x
  let s := Set.Ioo (-3 : ℝ) 3
  have hs : IsOpen s := isOpen_Ioo
  have hC : 0 ≤ C := (abs_nonneg _).trans (hw 0)
  have hwithin (j n : ℕ) {x : ℝ} (hx : x ∈ s) :
      iteratedDerivWithin j (f n) s x =
        c n * ((n + offset).descFactorial j * x ^ (n + offset - j)) := by
    rw [iteratedDerivWithin_of_isOpen hs hx]
    simp only [f, iteratedDeriv_const_mul_field, iteratedDeriv_pow]
  let bound (j n : ℕ) : ℝ :=
    (C * j.factorial * 6 ^ offset) * ((6 * |t|) ^ n / n.factorial)
  have hboundSum (j : ℕ) : Summable (bound j) :=
    (Real.summable_pow_div_factorial _).mul_left _
  have hbound (j n : ℕ) (x : ℝ) (hx : x ∈ s) :
      ‖iteratedDerivWithin j (f n) s x‖ ≤ bound j n := by
    have hx3 : |x| ≤ 3 := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
    have hp : |x| ^ (n + offset - j) ≤ (3 : ℝ) ^ (n + offset) :=
      (pow_le_pow_left₀ (abs_nonneg _) hx3 _).trans
        (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _))
    have hd : ((n + offset).descFactorial j : ℝ) ≤
        (j.factorial : ℝ) * 2 ^ (n + offset) := by
      exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose (n + offset) j).le.trans
        (Nat.mul_le_mul_left _ (Nat.choose_le_two_pow (n + offset) j))
    rw [hwithin j n hx]
    simp only [Real.norm_eq_abs, abs_mul, abs_pow, c, abs_div,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
    calc
      _ ≤ C * |t| ^ n / n.factorial *
          ((j.factorial : ℝ) * 2 ^ (n + offset) * 3 ^ (n + offset)) := by
        gcongr
        exact hw n
      _ = bound j n := by
        simp only [bound, show (6 : ℝ) = 2 * 3 by norm_num, mul_pow, pow_add]
        ring
  have huniform (j : ℕ) :
      HasSumUniformlyOn (fun n ↦ iteratedDerivWithin j (f n) s)
        (fun x ↦ ∑' n, iteratedDerivWithin j (f n) s x) s :=
    HasSumUniformlyOn.of_norm_le_summable (hboundSum j) (hbound j)
  have hvalue {x : ℝ} (hx : x ∈ s) : HasSum (fun n ↦ f n x) (F x) := by
    simpa only [iteratedDerivWithin_zero, F] using (huniform 0).hasSum hx
  have hderiv (j : ℕ) {x : ℝ} (hx : x ∈ s) :
      HasSum (fun n ↦ iteratedDeriv j (f n) x) (iteratedDeriv j F x) := by
    rw [← iteratedDerivWithin_of_isOpen hs hx]
    have heq := iteratedDerivWithin_tsum (f := f) j hs hx
      (fun _ hy ↦ (hvalue hy).summable)
      (fun k _ _ ↦ (huniform k).hasSumLocallyUniformlyOn.summableLocallyUniformlyOn) (by
        intro n k y _ hy
        have hevent := (hs.eventually_mem hy).mono (fun z hz ↦ hwithin k n hz)
        exact (show DifferentiableAt ℝ
          (fun z : ℝ ↦ c n * ((n + offset).descFactorial k * z ^ (n + offset - k))) y by
            fun_prop).congr_of_eventuallyEq hevent)
    rw [show iteratedDerivWithin j F s x = _ from heq]
    simpa only [iteratedDerivWithin_of_isOpen hs hx] using (huniform j).hasSum hx
  let g (n : ℕ) : C(ℝ, ℝ) := ⟨f n, by dsimp [f]; fun_prop⟩
  let K : TopologicalSpace.Compacts ℝ := ⟨Set.uIcc (-1 : ℝ) 2, isCompact_uIcc⟩
  have hnorm : Summable (fun n ↦ ‖(g n).restrict K‖) := by
    refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) (hboundSum 0)
    apply (ContinuousMap.norm_le _ (by dsimp [bound]; positivity)).2
    intro x
    have hx : (x : ℝ) ∈ Set.Icc (-1 : ℝ) 2 := by
      simpa only [K, TopologicalSpace.Compacts.coe_mk, Set.uIcc_of_le
        (by norm_num : (-1 : ℝ) ≤ 2)] using x.property
    have hxs : (x : ℝ) ∈ s :=
      ⟨(by norm_num : (-3 : ℝ) < -1).trans_le hx.1, hx.2.trans_lt (by norm_num)⟩
    simpa only [ContinuousMap.restrict_apply, g, ContinuousMap.coe_mk, iteratedDerivWithin_zero]
      using hbound 0 n (x : ℝ) hxs
  have hint : HasSum (fun n ↦ ∫ x in (-1 : ℝ)..2, f n x) (∫ x in (-1 : ℝ)..2, F x) :=
    intervalIntegral.hasSum_intervalIntegral_of_summable_norm (f := g) hnorm
  have hleft : (-1 : ℝ) ∈ s := by norm_num [s, Set.mem_Ioo]
  have hright : (2 : ℝ) ∈ s := by norm_num [s, Set.mem_Ioo]
  have hsum : HasSum (fun n ↦ compactClosedQuadrature h (f n)) (compactClosedQuadrature h F) := by
    unfold compactClosedQuadrature
    exact ((hint.add (((hvalue hleft).add (hvalue hright)).mul_left (h / 2))).add
      (((hderiv 1 hright).sub (hderiv 1 hleft)).mul_left (h ^ 2 / 12))).sub
      (((hderiv 3 hright).sub (hderiv 3 hleft)).mul_left (h ^ 4 / 720))
  change compactClosedQuadrature h F = ∑' n, c n *
    compactClosedQuadrature h (fun x ↦ x ^ (n + offset))
  rw [← hsum.tsum_eq]
  congr 1
  funext n
  unfold compactClosedQuadrature f
  simp only [intervalIntegral.integral_const_mul, iteratedDeriv_const_mul_field]
  ring

/-- The monomial majorant used in the geometric tail of the quadrature expansion. -/
theorem compactClosedQuadrature_monomial_abs_le {h : ℝ} (hh : 0 ≤ h) (k : ℕ) :
    |compactClosedQuadrature h (fun x ↦ x ^ k)| ≤
      (3 + h) * 2 ^ k + h ^ 2 / 6 * (k : ℝ) * 2 ^ (k - 1) +
        h ^ 4 / 360 * (k.descFactorial 3 : ℝ) * 2 ^ (k - 3) := by
  have hmono (m : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 2) : |x ^ m| ≤ 2 ^ m := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg x) (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩) m
  have hab : (-1 : ℝ) ≤ 2 := by norm_num
  have hI : |∫ x in (-1 : ℝ)..2, x ^ k| ≤ 3 * 2 ^ k := by
    have hc : Continuous (fun x : ℝ ↦ |x ^ k|) := by fun_prop
    calc
      _ ≤ ∫ x in (-1 : ℝ)..2, |x ^ k| := intervalIntegral.abs_integral_le_integral_abs hab
      _ ≤ ∫ _ in (-1 : ℝ)..2, (2 : ℝ) ^ k :=
        intervalIntegral.integral_mono_on hab (hc.intervalIntegrable _ _)
          (continuous_const.intervalIntegrable _ _) fun _ hx ↦ hmono k hx
      _ = _ := by norm_num [intervalIntegral.integral_const, smul_eq_mul]
  have hleft : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 2 := ⟨le_rfl, hab⟩
  have hright : (2 : ℝ) ∈ Set.Icc (-1 : ℝ) 2 := ⟨hab, le_rfl⟩
  have hE : |(-1 : ℝ) ^ k + 2 ^ k| ≤ 2 * 2 ^ k := by
    exact (abs_add_le ..).trans (by linarith [hmono k hleft, hmono k hright])
  have hD (j : ℕ) :
      |iteratedDeriv j (fun x : ℝ ↦ x ^ k) 2 - iteratedDeriv j (fun x : ℝ ↦ x ^ k) (-1)| ≤
        (k.descFactorial j : ℝ) * (2 * 2 ^ (k - j)) := by
    rw [monomial_endpoint_deriv_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    rw [sub_eq_add_neg]
    refine (abs_add_le ..).trans ?_
    rw [abs_neg]
    linarith [hmono (k - j) hleft, hmono (k - j) hright]
  let I := ∫ x in (-1 : ℝ)..2, x ^ k
  let E := (-1 : ℝ) ^ k + 2 ^ k
  let D (j : ℕ) := iteratedDeriv j (fun x : ℝ ↦ x ^ k) 2 - iteratedDeriv j (fun x : ℝ ↦ x ^ k) (-1)
  have hT : |I + h / 2 * E + h ^ 2 / 12 * D 1 - h ^ 4 / 720 * D 3| ≤
      |I| + |h / 2 * E| + |h ^ 2 / 12 * D 1| + |h ^ 4 / 720 * D 3| := by
    rw [sub_eq_add_neg]
    calc
      _ ≤ |I + h / 2 * E + h ^ 2 / 12 * D 1| + |-(h ^ 4 / 720 * D 3)| := abs_add_le ..
      _ ≤ (|I + h / 2 * E| + |h ^ 2 / 12 * D 1|) + |-(h ^ 4 / 720 * D 3)| :=
        add_le_add (abs_add_le ..) le_rfl
      _ ≤ _ := by rw [abs_neg]; gcongr; exact abs_add_le ..
  refine hT.trans ?_
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (show 0 ≤ h / 2 by positivity),
    abs_of_nonneg (show 0 ≤ h ^ 2 / 12 by positivity),
    abs_of_nonneg (show 0 ≤ h ^ 4 / 720 by positivity)]
  calc
    _ ≤ 3 * 2 ^ k + h / 2 * (2 * 2 ^ k) +
        h ^ 2 / 12 * ((k.descFactorial 1 : ℝ) * (2 * 2 ^ (k - 1))) +
        h ^ 4 / 720 * ((k.descFactorial 3 : ℝ) * (2 * 2 ^ (k - 3))) :=
      add_le_add (add_le_add (add_le_add hI (mul_le_mul_of_nonneg_left hE (by positivity)))
        (mul_le_mul_of_nonneg_left (hD 1) (by positivity)))
        (mul_le_mul_of_nonneg_left (hD 3) (by positivity))
    _ = _ := by rw [Nat.descFactorial_one]; ring

private def quadratureTailTerm (offset order : ℕ) (radius : ℝ) (n : ℕ) : ℝ :=
  ((n + offset).descFactorial order : ℝ) * 2 ^ (n + offset - order) * radius ^ n / n.factorial

private theorem quadratureTailTerm_succ_le {offset order N n : ℕ} {R : ℝ}
    (hR : 0 ≤ R) (horder : order ≤ 3) (hN : 3 ≤ N) (hn : N ≤ n) :
    quadratureTailTerm offset order R (n + 1) ≤
      (2 * R / ((N : ℝ) - 2)) * quadratureTailTerm offset order R n := by
  have hle' : order ≤ n + offset + 1 := by omega
  have hpow : n + 1 + offset - order = (n + offset - order) + 1 := by omega
  have hfactor : ((n + offset : ℕ) : ℝ) + 1 - order = (↑(n + offset + 1 - order) : ℝ) := by
    push_cast [Nat.cast_sub hle']
    rfl
  have hdesc : ((n + offset : ℕ).descFactorial order : ℝ) * ((n : ℝ) + offset + 1) =
      ((n + 1 + offset : ℕ).descFactorial order : ℝ) * ((n : ℝ) + offset + 1 - order) := by
    have hr := congrArg (fun m : ℕ ↦ (m : ℝ)) (Nat.succ_descFactorial (n + offset) order)
    rw [Nat.cast_mul, Nat.cast_mul, ← hfactor, Nat.cast_add n offset,
      Nat.cast_add (n + offset) 1, Nat.cast_add n offset, Nat.cast_one,
      show n + offset + 1 = n + 1 + offset by omega] at hr
    linarith only [hr]
  have hleft : 0 < (N : ℝ) - 2 := sub_pos.mpr (by exact_mod_cast (show 2 < N by omega))
  have hc : 0 < (n : ℝ) + offset + 1 - order := by
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hN.trans hn
    have ho' : (order : ℝ) ≤ 3 := by exact_mod_cast horder
    linarith [Nat.cast_nonneg (α := ℝ) offset]
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have ho' : (order : ℝ) ≤ 3 := by exact_mod_cast horder
  have hcross : ((N : ℝ) - 2) * ((n : ℝ) + offset + 1) ≤
      ((n : ℝ) + 1) * ((n : ℝ) + offset + 1 - order) := by
    have hs : (N : ℝ) - 2 ≤ (n : ℝ) + 1 - order := by linarith
    have hb := mul_le_mul_of_nonneg_right hs (show 0 ≤ (n : ℝ) + offset + 1 by positivity)
    have hd := mul_nonneg (Nat.cast_nonneg (α := ℝ) offset) (Nat.cast_nonneg (α := ℝ) order)
    nlinarith only [hb, hd]
  have hstep : quadratureTailTerm offset order R (n + 1) =
      (2 * R) * (((n : ℝ) + offset + 1) /
        (((n : ℝ) + 1) * ((n : ℝ) + offset + 1 - order))) * quadratureTailTerm offset order R n := by
    have hd : ((n + 1 + offset : ℕ).descFactorial order : ℝ) =
        ((n + offset : ℕ).descFactorial order : ℝ) * ((n : ℝ) + offset + 1) /
          ((n : ℝ) + offset + 1 - order) := (eq_div_iff hc.ne').mpr hdesc.symm
    unfold quadratureTailTerm
    rw [hpow, pow_succ (2 : ℝ), pow_succ R, Nat.factorial_succ, hd]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hratio : ((n : ℝ) + offset + 1) /
        (((n : ℝ) + 1) * ((n : ℝ) + offset + 1 - order)) ≤ 1 / ((N : ℝ) - 2) := by
    apply (div_le_div_iff₀ (mul_pos (by positivity) hc) hleft).2
    simpa only [one_mul, mul_comm ((N : ℝ) - 2)] using hcross
  rw [hstep]
  apply mul_le_mul_of_nonneg_right _ (by unfold quadratureTailTerm; positivity)
  calc
    _ ≤ (2 * R) * (1 / ((N : ℝ) - 2)) :=
      mul_le_mul_of_nonneg_left hratio (mul_nonneg (by norm_num) hR)
    _ = _ := by ring

/-- A common geometric tail for the value, first-endpoint, and third-endpoint
monomial terms. A shift in the monomial degree does not worsen the ratio. -/
theorem quadratureTailTerm_tsum_le {offset order N : ℕ} {R : ℝ}
    (hR : 0 ≤ R) (horder : order ≤ 3) (hN : 3 ≤ N) (hr : 2 * R < (N : ℝ) - 2) :
    Summable (fun n : ℕ ↦ quadratureTailTerm offset order R (n + N)) ∧
      (∑' n : ℕ, quadratureTailTerm offset order R (n + N)) ≤
        quadratureTailTerm offset order R N / (1 - 2 * R / ((N : ℝ) - 2)) := by
  let a (n : ℕ) := quadratureTailTerm offset order R (n + N)
  let ρ := 2 * R / ((N : ℝ) - 2)
  have hden : 0 < (N : ℝ) - 2 := sub_pos.mpr (by exact_mod_cast (show 2 < N by omega))
  have hρ : 0 ≤ ρ := div_nonneg (mul_nonneg (by norm_num) hR) hden.le
  have hρ' : ρ < 1 := (div_lt_one hden).mpr hr
  have ha (n : ℕ) : 0 ≤ a n := by unfold a quadratureTailTerm; positivity
  have hbound (n : ℕ) : a n ≤ a 0 * ρ ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        a (n + 1) = quadratureTailTerm offset order R (n + N + 1) := by
          dsimp only [a]
          rw [show n + 1 + N = n + N + 1 by omega]
        _ ≤ ρ * a n := quadratureTailTerm_succ_le hR horder hN (by omega)
        _ ≤ ρ * (a 0 * ρ ^ n) := mul_le_mul_of_nonneg_left ih hρ
        _ = a 0 * ρ ^ (n + 1) := by rw [pow_succ]; ring
  have hsum := (summable_geometric_of_lt_one hρ hρ').mul_left (a 0)
  have has := Summable.of_nonneg_of_le ha hbound hsum
  have htsum := has.tsum_le_tsum hbound hsum
  rw [tsum_mul_left, tsum_geometric_of_lt_one hρ hρ'] at htsum
  exact ⟨has, by simpa only [a, ρ, zero_add, div_eq_mul_inv] using htsum⟩

/-- A single majorant covers each shifted monomial density. For the regularized exponential,
the inverse quadratic coefficient can be bounded at the first omitted index. -/
theorem compactClosedQuadrature_series_tail_le {h C t R : ℝ} {offset N : ℕ}
    (hh : 0 ≤ h) (hC : 0 ≤ C) (ht : |t| ≤ R) (hN : 3 ≤ N)
    (hr : 2 * R < (N : ℝ) - 2) {weight : ℕ → ℝ}
    (hw : ∀ n ≥ N, |weight n| ≤ C) :
    let term (n : ℕ) := |weight (n + N) * (t ^ (n + N) / (n + N).factorial) *
      compactClosedQuadrature h (fun x ↦ x ^ (n + N + offset))|
    Summable term ∧ (∑' n : ℕ, term n) ≤
      C * ((3 + h) * quadratureTailTerm offset 0 R N +
        h ^ 2 / 6 * quadratureTailTerm offset 1 R N +
        h ^ 4 / 360 * quadratureTailTerm offset 3 R N) / (1 - 2 * R / ((N : ℝ) - 2)) := by
  let term (n : ℕ) := |weight (n + N) * (t ^ (n + N) / (n + N).factorial) *
    compactClosedQuadrature h (fun x ↦ x ^ (n + N + offset))|
  let A (j n : ℕ) := quadratureTailTerm offset j R (n + N)
  let B (n : ℕ) := (3 + h) * A 0 n + h ^ 2 / 6 * A 1 n + h ^ 4 / 360 * A 3 n
  let den := 1 - 2 * R / ((N : ℝ) - 2)
  have hR : 0 ≤ R := (abs_nonneg t).trans ht
  have hdom (n : ℕ) : term n ≤ C * B n := by
    let k := n + N + offset
    let M := (3 + h) * 2 ^ k + h ^ 2 / 6 * (k : ℝ) * 2 ^ (k - 1) +
      h ^ 4 / 360 * (k.descFactorial 3 : ℝ) * 2 ^ (k - 3)
    have hp : |t| ^ (n + N) ≤ R ^ (n + N) := pow_le_pow_left₀ (abs_nonneg t) ht _
    have hw' : |weight (n + N)| ≤ C := hw _ (by omega)
    unfold term
    simp only [abs_mul, abs_div, abs_pow,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n + N).factorial)]
    calc
      _ ≤ C * (R ^ (n + N) / (n + N).factorial) * M :=
        mul_le_mul (mul_le_mul hw' (div_le_div_of_nonneg_right hp (Nat.cast_nonneg _))
          (by positivity) hC) (compactClosedQuadrature_monomial_abs_le hh k)
          (abs_nonneg _) (by positivity)
      _ = _ := by
        dsimp only [B, A, M, k, quadratureTailTerm]
        simp only [Nat.descFactorial_zero, Nat.descFactorial_one, Nat.cast_one, Nat.sub_zero]
        ring
  have h0 := quadratureTailTerm_tsum_le (offset := offset) (order := 0) hR (by decide) hN hr
  have h1 := quadratureTailTerm_tsum_le (offset := offset) (order := 1) hR (by decide) hN hr
  have h3 := quadratureTailTerm_tsum_le (offset := offset) (order := 3) hR (by decide) hN hr
  have s0 : Summable (fun n ↦ (3 + h) * A 0 n) := h0.1.mul_left _
  have s1 : Summable (fun n ↦ h ^ 2 / 6 * A 1 n) := h1.1.mul_left _
  have s3 : Summable (fun n ↦ h ^ 4 / 360 * A 3 n) := h3.1.mul_left _
  have sB : Summable B := (s0.add s1).add s3
  have has : Summable term := Summable.of_nonneg_of_le (fun _ ↦ abs_nonneg _) hdom (sB.mul_left _)
  refine ⟨has, (has.tsum_le_tsum hdom (sB.mul_left _)).trans ?_⟩
  rw [tsum_mul_left]
  have hB : (∑' n : ℕ, B n) = (3 + h) * (∑' n : ℕ, A 0 n) +
      h ^ 2 / 6 * (∑' n : ℕ, A 1 n) + h ^ 4 / 360 * (∑' n : ℕ, A 3 n) := by
    unfold B
    rw [(s0.add s1).tsum_add s3, s0.tsum_add s1, tsum_mul_left, tsum_mul_left, tsum_mul_left]
  rw [hB]
  calc
    _ ≤ C * ((3 + h) * (quadratureTailTerm offset 0 R N / den) +
        h ^ 2 / 6 * (quadratureTailTerm offset 1 R N / den) +
        h ^ 4 / 360 * (quadratureTailTerm offset 3 R N / den)) := by
      gcongr
      · exact h0.2
      · exact h1.2
      · exact h3.2
    _ = _ := by dsimp only [den]; ring

/-- Verified truncation of a closed-quadrature expansion. The right-hand side
uses only the first omitted monomial majorants and a geometric ratio. -/
theorem compactClosedQuadrature_taylor_error_le {h C t R : ℝ} {offset N : ℕ}
    (hh : 0 ≤ h) (ht : |t| ≤ R) (hN : 3 ≤ N) (hr : 2 * R < (N : ℝ) - 2)
    {weight : ℕ → ℝ} (hw : ∀ n, |weight n| ≤ C) :
    let c (n : ℕ) := weight n * (t ^ n / n.factorial)
    |compactClosedQuadrature h (fun x ↦ ∑' n : ℕ, c n * x ^ (n + offset)) -
      ∑ n ∈ Finset.range N, c n * compactClosedQuadrature h (fun x ↦ x ^ (n + offset))| ≤
      C * ((3 + h) * quadratureTailTerm offset 0 R N +
        h ^ 2 / 6 * quadratureTailTerm offset 1 R N +
        h ^ 4 / 360 * quadratureTailTerm offset 3 R N) / (1 - 2 * R / ((N : ℝ) - 2)) := by
  let c (n : ℕ) := weight n * (t ^ n / n.factorial)
  let a (n : ℕ) := c n * compactClosedQuadrature h (fun x ↦ x ^ (n + offset))
  have hC : 0 ≤ C := (abs_nonneg _).trans (hw 0)
  have htail := compactClosedQuadrature_series_tail_le (offset := offset) hh hC ht hN hr
    (fun n _ ↦ hw n)
  have hs : Summable (fun n : ℕ ↦ ‖a (n + N)‖) := by
    simpa only [a, c, Real.norm_eq_abs] using htail.1
  have hsum : Summable a := (summable_nat_add_iff N).mp hs.of_norm
  have heq : compactClosedQuadrature h (fun x ↦ ∑' n : ℕ, c n * x ^ (n + offset)) = ∑' n, a n := by
    simpa only [c, a, mul_div_assoc] using compactClosedQuadrature_tsum h t offset weight hw
  change |compactClosedQuadrature h (fun x ↦ ∑' n : ℕ, c n * x ^ (n + offset)) -
    ∑ n ∈ Finset.range N, a n| ≤ _
  rw [heq, ← hsum.sum_add_tsum_nat_add N, add_sub_cancel_left]
  exact (norm_tsum_le_tsum_norm hs).trans (by simpa only [a, c, Real.norm_eq_abs] using htail.2)

/-- The normalized Euler–Maclaurin quadrature with endpoint corrections through order four. -/
def compactMarginalQuadrature (h t : ℝ) : ℝ :=
  2 / compactMarginalMeshDenominator h *
    compactClosedQuadrature h (regularizedMarginalIntegrand h t)

private def marginalQuadratureWeight (k : ℕ) : ℝ :=
  1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))

private theorem marginalQuadratureWeight_abs_le (k : ℕ) :
    |marginalQuadratureWeight k| ≤ 1 := by
  unfold marginalQuadratureWeight
  rw [abs_of_nonneg (by positivity)]
  exact (div_le_one (by positivity)).mpr <| by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]

private theorem contDiff_factorial_series {w : ℕ → ℝ} {C : ℝ}
    (hw : ∀ n, |w n| ≤ C) (t : ℝ) :
    ContDiff ℝ ⊤ (fun x : ℝ ↦ ∑' n : ℕ, w n * t ^ n / n.factorial * x ^ n) := by
  let c (n : ℕ) := w n * t ^ n / n.factorial
  let p := FormalMultilinearSeries.ofScalars ℝ c
  have hr : p.radius = ⊤ := by
    refine p.radius_eq_top_of_summable_norm fun r ↦ ?_
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_)
      ((Real.summable_pow_div_factorial (|t| * (r : ℝ))).mul_left C)
    simp only [p, FormalMultilinearSeries.ofScalars_norm, c, Real.norm_eq_abs, abs_div, abs_mul,
      abs_pow, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), mul_pow]
    calc
      _ ≤ C * |t| ^ n / n.factorial * (r : ℝ) ^ n := by gcongr; exact hw n
      _ = _ := by ring
  have ha : AnalyticOnNhd ℝ p.sum Set.univ := by
    simpa only [hr, Metric.eball_top] using p.analyticOnNhd
  have hc : ContDiff ℝ ⊤ (FormalMultilinearSeries.ofScalarsSum (E := ℝ) c) := ha.contDiff
  simpa only [FormalMultilinearSeries.ofScalarsSum_eq_tsum, smul_eq_mul, c] using hc

private theorem compactClosedQuadrature_const_mul_sub (h c : ℝ) {f g : ℝ → ℝ}
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) :
    compactClosedQuadrature h (fun x ↦ c * f x - g x) =
      c * compactClosedQuadrature h f - compactClosedQuadrature h g := by
  have hderiv (k : ℕ) (x : ℝ) :
      iteratedDeriv k (fun y ↦ c * f y - g y) x =
        c * iteratedDeriv k f x - iteratedDeriv k g x := by
    rw [iteratedDeriv_fun_sub, iteratedDeriv_const_mul_field]
    · exact (((contDiff_const (c := c)).mul hf).of_le le_top).contDiffAt
    · exact (hg.of_le le_top).contDiffAt
  unfold compactClosedQuadrature
  rw [intervalIntegral.integral_sub
    ((hf.continuous.const_mul c).intervalIntegrable _ _) (hg.continuous.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, hderiv, hderiv, hderiv, hderiv]
  ring

private theorem compactClosedQuadrature_monomial_abs_le_geometric {h : ℝ} (hh : 0 ≤ h)
    (k : ℕ) :
    |compactClosedQuadrature h (fun x ↦ x ^ k)| ≤
      (3 + h + h ^ 2 / 6 + h ^ 4 / 60) * 4 ^ k := by
  have hd (j : ℕ) : (k.descFactorial j : ℝ) ≤ (j.factorial : ℝ) * 2 ^ k := by
    exact_mod_cast (Nat.descFactorial_eq_factorial_mul_choose k j).le.trans
      (Nat.mul_le_mul_left _ (Nat.choose_le_two_pow k j))
  have h1 : (k : ℝ) ≤ 2 ^ k := by simpa using hd 1
  have hfac : (3 : ℕ).factorial = 6 := by decide
  have h3 : (k.descFactorial 3 : ℝ) ≤ 6 * 2 ^ k := by
    simpa only [hfac, Nat.cast_ofNat] using hd 3
  refine (compactClosedQuadrature_monomial_abs_le hh k).trans ?_
  calc
    _ ≤ (3 + h) * 2 ^ k +
        h ^ 2 / 6 * 2 ^ k * 2 ^ k + h ^ 4 / 360 * (6 * 2 ^ k) * 2 ^ k := by
      gcongr <;> norm_num
    _ ≤ (3 + h) * (2 ^ k * 2 ^ k) +
        h ^ 2 / 6 * 2 ^ k * 2 ^ k + h ^ 4 / 360 * (6 * 2 ^ k) * 2 ^ k := by
      have hone : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      gcongr
      exact le_mul_of_one_le_right (by positivity) hone
    _ = _ := by rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]; ring

private theorem summable_factorial_quadrature_series {a : ℕ → ℝ} {C : ℝ}
    (ha : ∀ n, |a n| ≤ C * 4 ^ n) (t : ℝ) :
    Summable fun n : ℕ ↦ a n * t ^ n / n.factorial := by
  refine Summable.of_norm_bounded ((Real.summable_pow_div_factorial (4 * |t|)).mul_left C)
    fun n ↦ ?_
  simp only [Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), mul_pow]
  calc
    _ ≤ (C * 4 ^ n) * |t| ^ n / n.factorial := by gcongr; exact ha n
    _ = _ := by ring

private def marginalQuadratureCoefficient (h : ℝ) (k : ℕ) : ℝ :=
  marginalQuadratureWeight k *
    ((2 + h) * compactClosedQuadrature h (fun x ↦ x ^ (k + 2)) -
      compactClosedQuadrature h (fun x ↦ x ^ (k + 3)))

private theorem marginalQuadratureCoefficient_abs_le {h : ℝ} (hh : 0 ≤ h) (k : ℕ) :
    |marginalQuadratureCoefficient h k| ≤
      (16 * (6 + h) * (3 + h + h ^ 2 / 6 + h ^ 4 / 60)) * 4 ^ k := by
  let C := 3 + h + h ^ 2 / 6 + h ^ 4 / 60
  let Q (m : ℕ) := compactClosedQuadrature h (fun x ↦ x ^ m)
  have h23 : 0 ≤ 2 + h := by positivity
  have hdiff : |(2 + h) * Q (k + 2) - Q (k + 3)| ≤
      (2 + h) * (C * 4 ^ (k + 2)) + C * 4 ^ (k + 3) := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg h23]
    exact add_le_add
      (mul_le_mul_of_nonneg_left (compactClosedQuadrature_monomial_abs_le_geometric hh _) h23)
      (compactClosedQuadrature_monomial_abs_le_geometric hh _)
  change |marginalQuadratureWeight k * ((2 + h) * Q (k + 2) - Q (k + 3))| ≤ _
  rw [abs_mul]
  calc
    _ ≤ 1 * ((2 + h) * (C * 4 ^ (k + 2)) + C * 4 ^ (k + 3)) :=
      mul_le_mul (marginalQuadratureWeight_abs_le k) hdiff (abs_nonneg _) zero_le_one
    _ = _ := by dsimp only [C]; rw [pow_add, pow_add]; ring

private theorem compactClosedQuadrature_parameter_series {h : ℝ} (hh : 0 ≤ h)
    (j : ℕ) (t : ℝ) :
    compactClosedQuadrature h
      (fun x ↦ iteratedDeriv j (fun s ↦ regularizedMarginalIntegrand h s x) t) =
      ∑' n : ℕ, marginalQuadratureCoefficient h (j + n) * t ^ n / n.factorial := by
  let w (n : ℕ) := marginalQuadratureWeight (j + n)
  let f (k : ℕ) (x : ℝ) := ∑' n : ℕ, w n * t ^ n / n.factorial * x ^ (n + k)
  have hsmooth (k : ℕ) : ContDiff ℝ ⊤ (f k) := by
    have hf : f k = fun x ↦ (∑' n : ℕ, w n * t ^ n / n.factorial * x ^ n) * x ^ k := by
      funext x
      rw [← tsum_mul_right]
      exact tsum_congr fun n ↦ by simp only [pow_add, mul_assoc]
    rw [hf]
    exact (contDiff_factorial_series (fun n ↦ marginalQuadratureWeight_abs_le (j + n)) t).mul
      (by fun_prop)
  have hpoint :
      (fun x ↦ iteratedDeriv j (fun s ↦ regularizedMarginalIntegrand h s x) t) =
        fun x ↦ (2 + h) * f (j + 2) x - f (j + 3) x := by
    funext x
    unfold regularizedMarginalIntegrand
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_regularizedMarginalRemainder_eq_tsum]
    have hbase : (∑' n : ℕ, (1 / ((((j + n : ℕ) : ℝ) + 1) *
        (((j + n : ℕ) : ℝ) + 2))) * (t ^ n / n.factorial) * x ^ (j + n + 2)) =
        f (j + 2) x := by
      refine tsum_congr fun n ↦ ?_
      rw [show j + n + 2 = n + (j + 2) by omega]
      simp only [w, marginalQuadratureWeight, mul_div_assoc]
    rw [hbase, sub_mul]
    congr 1
    dsimp only [f]
    rw [← tsum_mul_left]
    exact tsum_congr fun n ↦ by
      rw [show n + (j + 3) = (n + (j + 2)) + 1 by omega, pow_succ]
      ring
  have hQ (k : ℕ) := compactClosedQuadrature_tsum h t k w
    (fun n ↦ marginalQuadratureWeight_abs_le (j + n))
  let A (k n : ℕ) := w n * t ^ n / n.factorial *
    compactClosedQuadrature h (fun x ↦ x ^ (n + k))
  have hsum (k : ℕ) : Summable (A k) := by
    let a (n : ℕ) := w n * compactClosedQuadrature h (fun x ↦ x ^ (n + k))
    have ha (n : ℕ) : |a n| ≤ ((3 + h + h ^ 2 / 6 + h ^ 4 / 60) * 4 ^ k) * 4 ^ n := by
      rw [abs_mul]
      calc
        _ ≤ 1 * ((3 + h + h ^ 2 / 6 + h ^ 4 / 60) * 4 ^ (n + k)) :=
          mul_le_mul (marginalQuadratureWeight_abs_le (j + n))
            (compactClosedQuadrature_monomial_abs_le_geometric hh _) (abs_nonneg _) zero_le_one
        _ = _ := by rw [pow_add]; ring
    have hterm (n : ℕ) : A k n = a n * t ^ n / n.factorial := by dsimp only [A, a]; ring
    rw [show A k = _ from funext hterm]
    exact summable_factorial_quadrature_series ha t
  rw [hpoint, compactClosedQuadrature_const_mul_sub h (2 + h) (hsmooth _) (hsmooth _),
    hQ, hQ]
  change (2 + h) * (∑' n, A (j + 2) n) - (∑' n, A (j + 3) n) = _
  rw [← tsum_mul_left, ← ((hsum (j + 2)).mul_left (2 + h)).tsum_sub (hsum (j + 3))]
  refine tsum_congr fun n ↦ ?_
  simp only [A, marginalQuadratureCoefficient, w,
    show n + (j + 2) = j + n + 2 by omega, show n + (j + 3) = j + n + 3 by omega]
  ring

private theorem hasDerivAt_factorial_quadrature_series {a : ℕ → ℝ} {C : ℝ}
    (ha : ∀ n, |a n| ≤ C * 4 ^ n) (j : ℕ) (t : ℝ) :
    HasDerivAt (fun s ↦ ∑' n : ℕ, a (j + n) * s ^ n / n.factorial)
      (∑' n : ℕ, a (j + 1 + n) * t ^ n / n.factorial) t := by
  have hshift (k n : ℕ) : |a (k + n)| ≤ (C * 4 ^ k) * 4 ^ n := by
    simpa only [pow_add, mul_assoc] using ha (k + n)
  let g (n : ℕ) (s : ℝ) := a (j + n) * s ^ n / n.factorial
  let g' (n : ℕ) (s : ℝ) := match n with
    | 0 => 0
    | n + 1 => a (j + 1 + n) * s ^ n / n.factorial
  have hg (n : ℕ) (s : ℝ) : HasDerivAt (g n) (g' n s) s := by
    cases n with
    | zero => simpa [g, g'] using hasDerivAt_const s (a j)
    | succ n =>
      apply (((hasDerivAt_pow (n + 1) s).const_mul (a (j + (n + 1)))).div_const
        ((n + 1).factorial : ℝ)).congr_deriv
      simp only [g', Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
      rw [show j + (n + 1) = j + 1 + n by omega]
      have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [hn]
  let R := |t| + 1
  let u (n : ℕ) : ℝ := match n with
    | 0 => 0
    | n + 1 => (C * 4 ^ (j + 1)) * ((4 * R) ^ n / n.factorial)
  have hu : Summable u := (summable_nat_add_iff 1).mp
    ((Real.summable_pow_div_factorial (4 * R)).mul_left _)
  have hC : 0 ≤ C := by simpa using (abs_nonneg (a 0)).trans (ha 0)
  have hdom (n : ℕ) (s : ℝ) (hs : s ∈ Set.Ioo (-R) R) : ‖g' n s‖ ≤ u n := by
    cases n with
    | zero => simp [g', u]
    | succ n =>
      have habs := abs_le.mpr ⟨hs.1.le, hs.2.le⟩
      have hR : 0 ≤ R := by positivity
      simp only [g', u, Real.norm_eq_abs, abs_div, abs_mul, abs_pow,
        abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _), mul_pow]
      calc
        _ ≤ (C * 4 ^ (j + 1) * 4 ^ n) * R ^ n / n.factorial := by
          gcongr
          exact hshift _ _
        _ = _ := by ring
  have ht : t ∈ Set.Ioo (-R) R := by
    exact abs_lt.mp (lt_add_one |t|)
  have hbase : Summable (fun n ↦ g n t) := summable_factorial_quadrature_series (hshift j) t
  have h := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    (fun n s _ ↦ hg n s) hdom ht hbase ht
  have hs : Summable (fun n ↦ g' n t) := Summable.of_norm_bounded hu (fun n ↦ hdom n t ht)
  rw [hs.tsum_eq_zero_add, show g' 0 t = 0 by rfl, zero_add] at h
  exact h

private theorem hasDerivAt_compactClosedQuadrature_parameter {h : ℝ} (hh : 0 ≤ h)
    (j : ℕ) (t : ℝ) :
    HasDerivAt
      (fun s ↦ compactClosedQuadrature h
        (fun x ↦ iteratedDeriv j (fun r ↦ regularizedMarginalIntegrand h r x) s))
      (compactClosedQuadrature h
        (fun x ↦ iteratedDeriv (j + 1) (fun r ↦ regularizedMarginalIntegrand h r x) t)) t := by
  rw [funext (compactClosedQuadrature_parameter_series hh j),
    compactClosedQuadrature_parameter_series hh (j + 1)]
  exact hasDerivAt_factorial_quadrature_series (marginalQuadratureCoefficient_abs_le hh) j t

/-- Parameter differentiation commutes with the closed quadrature, including all
endpoint corrections and the regularized value at zero parameter. -/
theorem iteratedDeriv_compactMarginalQuadrature_eq_closed {h : ℝ} (hh : 0 ≤ h)
    (j : ℕ) (t : ℝ) :
    iteratedDeriv j (compactMarginalQuadrature h) t =
      (2 / compactMarginalMeshDenominator h) * compactClosedQuadrature h
        (fun x ↦ iteratedDeriv j (fun s ↦ regularizedMarginalIntegrand h s x) t) := by
  induction j generalizing t with
  | zero => simp only [iteratedDeriv_zero, compactMarginalQuadrature]
  | succ j ih =>
    rw [iteratedDeriv_succ, funext ih]
    exact ((hasDerivAt_compactClosedQuadrature_parameter hh j t).const_mul _).deriv

/-- The signed error in Pro equation (20), expressed as a sum of cell integrals.
The scaled kernel in `meshRemainder` includes the factor `h ^ 6`. -/
theorem compactKappa_mul_compactZ_sub_quadrature {p : ℕ} (hp : 0 < p) (t : ℝ) :
    let h : ℝ := 3 / (p : ℝ)
    compactKappa p * compactZ p t - compactMarginalQuadrature h t =
      2 / compactMarginalMeshDenominator h *
        meshRemainder (-1) h p
          (fun x ↦ t ^ 3 * Real.exp (t * x) * (t * (2 + h - x) - 6)) := by
  let h : ℝ := 3 / (p : ℝ)
  let f := regularizedMarginalIntegrand h t
  have hb : -1 + (p : ℝ) * h = 2 := by
    have hph : (p : ℝ) * h = 3 := mul_marginal_step hp
    rw [hph]
    norm_num
  have hsmooth : ContDiff ℝ ⊤ f := contDiff_regularizedMarginalIntegrand h t
  have hderiv (k : ℕ) (x : ℝ) :
      HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f x) x := by
    rw [iteratedDeriv_succ]
    exact (hsmooth.differentiable_iteratedDeriv k (by simp)).differentiableAt.hasDerivAt
  have hsix : iteratedDeriv 6 f =
      (fun x ↦ t ^ 3 * Real.exp (t * x) * (t * (2 + h - x) - 6)) :=
    funext (iteratedDeriv_six_regularizedMarginalIntegrand h t)
  have hmesh := mesh_sum_eq (a := -1) (h := h) (n := p)
    (f0 := f) (f1 := iteratedDeriv 1 f) (f2 := iteratedDeriv 2 f)
    (f3 := iteratedDeriv 3 f) (f4 := iteratedDeriv 4 f) (f5 := iteratedDeriv 5 f)
    (f6 := iteratedDeriv 6 f) (by simpa only [iteratedDeriv_zero] using hderiv 0)
    (hderiv 1) (hderiv 2) (hderiv 3) (hderiv 4) (hderiv 5)
    (hsmooth.continuous_iteratedDeriv 6 le_top)
  rw [hb, hsix] at hmesh
  rw [compactKappa_mul_compactZ_eq_mesh_sum hp t]
  change 2 * h / compactMarginalMeshDenominator h *
      (∑ i ∈ Finset.range (p + 1), f (-1 + (i : ℝ) * h)) -
      compactMarginalQuadrature h t = _
  rw [mul_div_right_comm (2 : ℝ) h, mul_assoc, hmesh]
  unfold compactMarginalQuadrature compactClosedQuadrature
  ring

private theorem hasDerivAt_meshRemainder {a h t : ℝ} {n : ℕ} (hh : 0 ≤ h)
    {F F' : ℝ → ℝ → ℝ} (hF : Continuous (fun z : ℝ × ℝ ↦ F z.1 z.2))
    (hF' : Continuous (fun z : ℝ × ℝ ↦ F' z.1 z.2))
    (hderiv : ∀ s x, HasDerivAt (fun r ↦ F r x) (F' s x) s) :
    HasDerivAt (fun s ↦ meshRemainder a h n (F s)) (meshRemainder a h n (F' t)) t := by
  unfold meshRemainder
  refine HasDerivAt.fun_sum fun i _ ↦ ?_
  let w (x : ℝ) := D5.S3.Weil.ZetaPntBase.EulerMaclaurinSixth.kernel h (x - (a + (i : ℝ) * h))
  have hw : Continuous w := by
    unfold w D5.S3.Weil.ZetaPntBase.EulerMaclaurinSixth.kernel
    fun_prop
  have hab : a + (i : ℝ) * h ≤ a + ((i + 1 : ℕ) : ℝ) * h := by
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    linarith
  exact D5.S3.FluidDynamics.Fourier.PeriodicAllenCahnDecay.deriv_integral_compact
    (F := fun s x ↦ w x * F s x) (H := fun s x ↦ w x * F' s x) (δ := 1)
    hab one_pos ((hw.comp continuous_snd).mul hF).continuousOn
    ((hw.comp continuous_snd).mul hF').continuousOn
    (fun s _ x _ ↦ (hderiv s x).const_mul (w x))

/-- The density in the first parameter derivative of the signed marginal remainder. -/
def compactMarginalRemainderFirst (h t x : ℝ) : ℝ :=
  let w := 2 + h - x
  Real.exp (t * x) * (4 * t ^ 3 * w - 18 * t ^ 2 + x * (t ^ 4 * w - 6 * t ^ 3))

/-- The density in the second parameter derivative of the signed marginal remainder. -/
def compactMarginalRemainderSecond (h t x : ℝ) : ℝ :=
  let w := 2 + h - x
  Real.exp (t * x) * (12 * t ^ 2 * w - 36 * t +
    2 * x * (4 * t ^ 3 * w - 18 * t ^ 2) + x ^ 2 * (t ^ 4 * w - 6 * t ^ 3))

/-- Both parameter derivatives retain the signed mesh remainder, with the differentiated
densities integrated against the same kernel. -/
theorem compactMarginalQuadrature_error_derivatives {p : ℕ} (hp : 0 < p) (t : ℝ) :
    let h : ℝ := 3 / (p : ℝ)
    let error (s : ℝ) := compactKappa p * compactZ p s - compactMarginalQuadrature h s
    deriv error t = 2 / compactMarginalMeshDenominator h *
      meshRemainder (-1) h p (compactMarginalRemainderFirst h t) ∧
    iteratedDeriv 2 error t = 2 / compactMarginalMeshDenominator h *
      meshRemainder (-1) h p (compactMarginalRemainderSecond h t) := by
  let h : ℝ := 3 / (p : ℝ)
  let error (s : ℝ) := compactKappa p * compactZ p s - compactMarginalQuadrature h s
  let density (s x : ℝ) := s ^ 3 * Real.exp (s * x) * (s * (2 + h - x) - 6)
  have hh : 0 ≤ h := by
    have hpR : (0 : ℝ) < p := by exact_mod_cast hp
    exact div_nonneg (by norm_num) hpR.le
  have herror : error = fun s ↦ 2 / compactMarginalMeshDenominator h *
      meshRemainder (-1) h p (density s) :=
    funext (compactKappa_mul_compactZ_sub_quadrature hp)
  have hfirst (s x : ℝ) :
      HasDerivAt (fun r ↦ density r x) (compactMarginalRemainderFirst h s x) s := by
    have hid := hasDerivAt_id' s
    have hexp := (hid.mul_const x).exp
    have hlinear := (hid.mul_const (2 + h - x)).sub_const 6
    apply (((hid.pow 3).mul hexp).mul hlinear).congr_deriv
    dsimp [compactMarginalRemainderFirst]
    ring
  have hsecond (s x : ℝ) :
      HasDerivAt (fun r ↦ compactMarginalRemainderFirst h r x)
        (compactMarginalRemainderSecond h s x) s := by
    let w := 2 + h - x
    have hid := hasDerivAt_id' s
    have hexp := (hid.mul_const x).exp
    have hpoly := (((hid.pow 3).const_mul 4).mul_const w).sub ((hid.pow 2).const_mul 18)
    have hhigh := ((hid.pow 4).mul_const w).sub ((hid.pow 3).const_mul 6)
    apply (hexp.mul (hpoly.add (hhigh.const_mul x))).congr_deriv
    dsimp [compactMarginalRemainderSecond, w]
    ring
  have hcont : Continuous (fun z : ℝ × ℝ ↦ density z.1 z.2) := by
    unfold density
    fun_prop
  have hcfirst : Continuous (fun z : ℝ × ℝ ↦ compactMarginalRemainderFirst h z.1 z.2) := by
    unfold compactMarginalRemainderFirst
    fun_prop
  have hcsecond : Continuous (fun z : ℝ × ℝ ↦ compactMarginalRemainderSecond h z.1 z.2) := by
    unfold compactMarginalRemainderSecond
    fun_prop
  have hderiv : deriv error = fun s ↦ 2 / compactMarginalMeshDenominator h *
      meshRemainder (-1) h p (compactMarginalRemainderFirst h s) := by
    funext s
    rw [herror]
    exact ((hasDerivAt_meshRemainder (t := s) hh hcont hcfirst hfirst).const_mul _).deriv
  change deriv error t = _ ∧ iteratedDeriv 2 error t = _
  refine ⟨congrFun hderiv t, ?_⟩
  change iteratedDeriv (1 + 1) error t = _
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv]
  exact ((hasDerivAt_meshRemainder (t := t) hh hcfirst hcsecond hsecond).const_mul _).deriv

open private hasDerivAt_compactZ_family from
  D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter.CompactRegularizedRadical

/-- The three scaled marginal inputs in the short negative score equal their
closed quadratures plus the corresponding signed mesh remainders. -/
theorem compactScaledMarginal_eq_closed_add_remainder {p : ℕ} (hp : 0 < p) (t : ℝ) :
    let h : ℝ := 3 / (p : ℝ)
    let J := (3 + h) * (3 + 2 * h) / 2
    let q (s : ℝ) := (J * compactKappa p) * compactZ p s
    let Q (j : ℕ) := compactClosedQuadrature h
      (fun x ↦ iteratedDeriv j (fun s ↦ regularizedMarginalIntegrand h s x) t)
    q t = Q 0 + meshRemainder (-1) h p
      (fun x ↦ t ^ 3 * Real.exp (t * x) * (t * (2 + h - x) - 6)) ∧
    deriv q t = Q 1 + meshRemainder (-1) h p (compactMarginalRemainderFirst h t) ∧
    iteratedDeriv 2 q t = Q 2 + meshRemainder (-1) h p (compactMarginalRemainderSecond h t) := by
  let h : ℝ := 3 / (p : ℝ)
  let J := (3 + h) * (3 + 2 * h) / 2
  let q (s : ℝ) := (J * compactKappa p) * compactZ p s
  let Q (j : ℕ) := compactClosedQuadrature h
    (fun x ↦ iteratedDeriv j (fun s ↦ regularizedMarginalIntegrand h s x) t)
  let base (s : ℝ) := compactKappa p * compactZ p s
  let error (s : ℝ) := base s - compactMarginalQuadrature h s
  have hh : 0 ≤ h := by dsimp only [h]; positivity
  have hbase (k : ℕ) : ContDiff ℝ (k : ℕ) base := by
    rw [← WithTop.coe_natCast]
    apply contDiff_of_differentiable_iteratedDeriv
    intro j _
    have heq : iteratedDeriv j base =
        fun s ↦ compactKappa p * integralMarginalDerivative p (compactKappa p) j s := by
      funext s
      change iteratedDeriv j (fun r ↦ compactKappa p * compactZ p r) s = _
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_compactZ_eq_integral hp]
    rw [heq]
    exact fun s ↦ ((hasDerivAt_compactZ_family hp j s).const_mul _).differentiableAt
  have hquad (k : ℕ) : ContDiff ℝ (k : ℕ) (compactMarginalQuadrature h) := by
    rw [← WithTop.coe_natCast]
    apply contDiff_of_differentiable_iteratedDeriv
    intro j _
    rw [funext (iteratedDeriv_compactMarginalQuadrature_eq_closed hh j)]
    exact fun s ↦ ((hasDerivAt_compactClosedQuadrature_parameter hh j s).const_mul _).differentiableAt
  have hcancel (y : ℝ) : J * (2 / compactMarginalMeshDenominator h * y) = y := by
    have hden : compactMarginalMeshDenominator h ≠ 0 := by
      unfold compactMarginalMeshDenominator
      positivity
    rw [show J = compactMarginalMeshDenominator h / 2 by rfl]
    field_simp
  have hscaled (j : ℕ) : iteratedDeriv j q t = Q j + J * iteratedDeriv j error t := by
    have heq : q = fun s ↦ J * base s := by
      funext s
      exact mul_assoc J (compactKappa p) (compactZ p s)
    have hsub : iteratedDeriv j error t =
        iteratedDeriv j base t - iteratedDeriv j (compactMarginalQuadrature h) t :=
      iteratedDeriv_fun_sub (hbase j).contDiffAt (hquad j).contDiffAt
    rw [heq, iteratedDeriv_const_mul_field, hsub, iteratedDeriv_compactMarginalQuadrature_eq_closed hh,
      mul_sub, hcancel]
    dsimp only [Q]
    ring
  have h0 : error t = 2 / compactMarginalMeshDenominator h *
      meshRemainder (-1) h p (fun x ↦ t ^ 3 * Real.exp (t * x) * (t * (2 + h - x) - 6)) :=
    compactKappa_mul_compactZ_sub_quadrature hp t
  have h1 : deriv error t = 2 / compactMarginalMeshDenominator h *
      meshRemainder (-1) h p (compactMarginalRemainderFirst h t) :=
    (compactMarginalQuadrature_error_derivatives hp t).1
  have h2 : iteratedDeriv 2 error t = 2 / compactMarginalMeshDenominator h *
      meshRemainder (-1) h p (compactMarginalRemainderSecond h t) :=
    (compactMarginalQuadrature_error_derivatives hp t).2
  refine ⟨?_, ?_, ?_⟩
  · simpa only [iteratedDeriv_zero, h0, hcancel, Q] using hscaled 0
  · simpa only [iteratedDeriv_one, h1, hcancel, Q] using hscaled 1
  · simpa only [h2, hcancel] using hscaled 2

private theorem abs_scaled_marginal_meshRemainder_le {p : ℕ} (hp : 0 < p)
    {f : ℝ → ℝ} (hf : Continuous f) :
    let h : ℝ := 3 / (p : ℝ)
    |2 / compactMarginalMeshDenominator h * meshRemainder (-1) h p f| ≤
      (2 / compactMarginalMeshDenominator h) * (h ^ 6 / 15360) *
        (∫ x in (-1 : ℝ)..2, |f x|) := by
  let h : ℝ := 3 / (p : ℝ)
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hh : 0 ≤ h := div_nonneg (by norm_num) hpR.le
  have hscale : 0 ≤ 2 / compactMarginalMeshDenominator h := by
    unfold compactMarginalMeshDenominator
    positivity
  have hspan : (-1 : ℝ) + (p : ℝ) * h = 2 := by
    change (-1 : ℝ) + (p : ℝ) * (3 / (p : ℝ)) = 2
    rw [mul_div_cancel₀ 3 hpR.ne']
    norm_num
  dsimp only
  rw [abs_mul, abs_of_nonneg hscale, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hscale
  simpa only [hspan] using abs_meshRemainder_le (a := -1) (n := p) hh hf

/-- The common sixth-order bound on the marginal error and its first two parameter derivatives. -/
theorem compactMarginalQuadrature_errors_le {p : ℕ} (hp : 0 < p) (t : ℝ) :
    let h : ℝ := 3 / (p : ℝ)
    let error (s : ℝ) := compactKappa p * compactZ p s - compactMarginalQuadrature h s
    let bound (f : ℝ → ℝ) := (2 / compactMarginalMeshDenominator h) * (h ^ 6 / 15360) *
      (∫ x in (-1 : ℝ)..2, |f x|)
    |error t| ≤ bound (fun x ↦ t ^ 3 * Real.exp (t * x) * (t * (2 + h - x) - 6)) ∧
    |deriv error t| ≤ bound (compactMarginalRemainderFirst h t) ∧
    |iteratedDeriv 2 error t| ≤ bound (compactMarginalRemainderSecond h t) := by
  dsimp only
  have hd := compactMarginalQuadrature_error_derivatives hp t
  refine ⟨?_, ?_, ?_⟩
  · rw [compactKappa_mul_compactZ_sub_quadrature hp t]
    exact abs_scaled_marginal_meshRemainder_le hp (by fun_prop)
  · rw [hd.1]
    exact abs_scaled_marginal_meshRemainder_le hp (by
      unfold compactMarginalRemainderFirst
      fun_prop)
  · rw [hd.2]
    exact abs_scaled_marginal_meshRemainder_le hp (by
      unfold compactMarginalRemainderSecond
      fun_prop)

/-- The one-sided errors used when enclosing the marginal on the short-gap strip. -/
theorem compactMarginalQuadrature_error_signs {p : ℕ} (hp : 11 ≤ p) (t : ℝ) :
    let h : ℝ := 3 / (p : ℝ)
    let error (s : ℝ) := compactKappa p * compactZ p s - compactMarginalQuadrature h s
    (t ≤ 0 → 0 ≤ error t) ∧ (0 ≤ t → t * (3 + h) ≤ 6 → error t ≤ 0) ∧
      (0 ≤ t → t ≤ 1 → deriv error t ≤ 0) := by
  let h : ℝ := 3 / (p : ℝ)
  let w (x : ℝ) := 2 + h - x
  let density (x : ℝ) := t ^ 3 * Real.exp (t * x) * (t * w x - 6)
  have hp₀ : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp₀
  have hh : 0 ≤ h := div_nonneg (by norm_num) hpR.le
  have hh' : h ≤ 3 / 11 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hp)
  have hspan : (-1 : ℝ) + (p : ℝ) * h = 2 := by
    change (-1 : ℝ) + (p : ℝ) * (3 / (p : ℝ)) = 2
    rw [mul_div_cancel₀ 3 hpR.ne']
    norm_num
  have hscale : 0 ≤ 2 / compactMarginalMeshDenominator h := by
    unfold compactMarginalMeshDenominator
    positivity
  have hw {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 2) : 0 ≤ w x ∧ w x ≤ 3 + h := by
    dsimp only [w]
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hnonneg {f : ℝ → ℝ} (hf : ∀ x ∈ Set.Icc (-1 : ℝ) 2, 0 ≤ f x) :
      0 ≤ meshRemainder (-1) h p f :=
    meshRemainder_nonneg hh (by simpa only [hspan] using hf)
  have hnonpos {f : ℝ → ℝ} (hf : ∀ x ∈ Set.Icc (-1 : ℝ) 2, f x ≤ 0) :
      meshRemainder (-1) h p f ≤ 0 := by
    have hneg := hnonneg (f := fun x ↦ -f x) fun x hx ↦ neg_nonneg.mpr (hf x hx)
    simpa only [meshRemainder, mul_neg, intervalIntegral.integral_neg,
      Finset.sum_neg_distrib, neg_nonneg] using hneg
  dsimp only
  rw [compactKappa_mul_compactZ_sub_quadrature hp₀ t,
    (compactMarginalQuadrature_error_derivatives hp₀ t).1]
  refine ⟨?_, ?_, ?_⟩
  · intro ht
    refine mul_nonneg hscale (hnonneg (f := density) fun x hx ↦ ?_)
    have hcube : t ^ 3 ≤ 0 := by nlinarith [mul_nonpos_of_nonneg_of_nonpos (sq_nonneg t) ht]
    have hz : t * w x - 6 ≤ 0 := by linarith [mul_nonpos_of_nonpos_of_nonneg ht (hw hx).1]
    exact mul_nonneg_of_nonpos_of_nonpos
      (mul_nonpos_of_nonpos_of_nonneg hcube (Real.exp_pos _).le) hz
  · intro ht ht'
    refine mul_nonpos_of_nonneg_of_nonpos hscale (hnonpos (f := density) fun x hx ↦ ?_)
    have hz : t * w x - 6 ≤ 0 := sub_nonpos.mpr
      ((mul_le_mul_of_nonneg_left (hw hx).2 ht).trans ht')
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (pow_nonneg ht _) (Real.exp_pos _).le) hz
  · intro ht ht'
    refine mul_nonpos_of_nonneg_of_nonpos hscale (hnonpos fun x hx ↦ ?_)
    have htW : t * w x ≤ 3 + h := by
      calc
        t * w x ≤ 1 * w x := mul_le_mul_of_nonneg_right ht' (hw hx).1
        _ = w x := one_mul _
        _ ≤ 3 + h := (hw hx).2
    have hz : t * w x - 6 ≤ 0 := by linarith
    have hx₀ : -t ≤ t * x := by
      simpa only [mul_neg, mul_one] using mul_le_mul_of_nonneg_left hx.1 ht
    have hxz := mul_le_mul_of_nonpos_right hx₀ hz
    have hquad : (4 - t) * t ≤ 3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ht') (show 0 ≤ 3 - t by linarith)]
    have hbracket : 4 * t * w x - 18 + t * x * (t * w x - 6) ≤ 0 := by
      have hprod := (mul_le_mul_of_nonneg_right hquad (hw hx).1).trans
        (mul_le_mul_of_nonneg_left (hw hx).2 (by norm_num : (0 : ℝ) ≤ 3))
      nlinarith only [hxz, hprod, ht', hh']
    have hfactor : compactMarginalRemainderFirst h t x =
        Real.exp (t * x) * t ^ 2 * (4 * t * w x - 18 + t * x * (t * w x - 6)) := by
      dsimp [compactMarginalRemainderFirst, w]
      ring
    rw [hfactor]
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (Real.exp_pos _).le (sq_nonneg t)) hbracket

end RefinedBMV.PositiveCenter
