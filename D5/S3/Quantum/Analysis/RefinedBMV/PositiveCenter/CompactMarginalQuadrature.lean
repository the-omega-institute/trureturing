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
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Fin.VecNotation

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

/-- The normalized Euler–Maclaurin quadrature with endpoint corrections through order four. -/
def compactMarginalQuadrature (h t : ℝ) : ℝ :=
  2 / compactMarginalMeshDenominator h *
    compactClosedQuadrature h (regularizedMarginalIntegrand h t)

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
