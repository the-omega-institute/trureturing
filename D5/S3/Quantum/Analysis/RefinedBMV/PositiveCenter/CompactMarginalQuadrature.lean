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
    _ ≤ 3 * 2 ^ k + h / 2 * (2 * 2 ^ k) + h ^ 2 / 12 * ((k.descFactorial 1 : ℝ) * (2 * 2 ^ (k - 1))) +
        h ^ 4 / 720 * ((k.descFactorial 3 : ℝ) * (2 * 2 ^ (k - 3))) :=
      add_le_add (add_le_add (add_le_add hI (mul_le_mul_of_nonneg_left hE (by positivity)))
        (mul_le_mul_of_nonneg_left (hD 1) (by positivity)))
        (mul_le_mul_of_nonneg_left (hD 3) (by positivity))
    _ = _ := by rw [Nat.descFactorial_one]; ring

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
