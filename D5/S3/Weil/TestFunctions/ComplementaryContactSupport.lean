/- GID: D5/S3/Weil/TestFunctions/ComplementaryContactSupport
   generality: I
   mirror-B: D5/B/S3/Weil/TestFunctions/ComplementaryContactSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Localize residual support on finite-type entire contact zeros. -/

import D5.S3.Fourier.FourierLaplaceEntire
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge
import Mathlib.MeasureTheory.Measure.Support

/- Library-search audit trail (2026-08-30):
   * D5 has no whole complementary-contact theorem. The active finite-contact
     completion uses the same entire expression but assumes support inclusion.
   * The canonical Fourier-Laplace transform, its real-axis theorem, and its
     entire theorem are imported instead of redeclared.
   * Pinned Mathlib has no packaged finite-exponential-type predicate. The
     explicit bound below uses the canonical compact-support Fourier estimate,
     `integral_eq_zero_iff_of_nonneg`, and `Measure.support_subset_of_isClosed`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ComplexConjugate
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula

namespace D5.S3.Weil.TestFunctions.ComplementaryContactSupport

private example :
    exists (a theta : Real) (phi : WeilTestFunction) (mu : Measure Real),
      0 < a /\ 0 <= theta /\
      (forall x, conj (phi x) = phi x) /\
      (forall xi : Real,
        0 <= (fourierLaplace phi xi).re + theta / (xi ^ 2 + a ^ 2)) /\
      Integrable
        (fun xi : Real => (fourierLaplace phi xi).re + theta / (xi ^ 2 + a ^ 2)) mu /\
      (∫ xi : Real, (fourierLaplace phi xi).re +
        theta / (xi ^ 2 + a ^ 2) ∂mu) = 0 := by
  let phi : WeilTestFunction :=
    { toFun := fun _ => 0
      contDiff' := contDiff_const
      hasCompactSupport' := HasCompactSupport.zero
      even' := by simp }
  have phiZero (x : Real) : phi x = 0 := rfl
  refine ⟨1, 0, phi, 0, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [phiZero]
    simp
  · intro xi
    have transformZero : fourierLaplace phi xi = 0 := by
      rw [fourierLaplace]
      apply integral_eq_zero_of_ae
      filter_upwards with u
      simp [phiZero]
    simp [transformZero]
  · exact integrable_zero_measure
  · exact integral_zero_measure _

/-- A nonnegative Fourier contact gap with zero residual integral vanishes on
the residual support. Clearing its positive denominator gives an entire
function of finite exponential type with the same support localization. -/
theorem complementary_contact_support
    (a theta : Real) (ha : 0 < a) (htheta : 0 <= theta)
    (phi : WeilTestFunction) (hreal : forall x, conj (phi x) = phi x)
    (mu : Measure Real)
    (contactNonnegative : forall xi : Real,
      0 <= (fourierLaplace phi xi).re + theta / (xi ^ 2 + a ^ 2))
    (contactIntegrable : Integrable
      (fun xi : Real => (fourierLaplace phi xi).re + theta / (xi ^ 2 + a ^ 2)) mu)
    (complementarity :
      (∫ xi : Real, (fourierLaplace phi xi).re +
        theta / (xi ^ 2 + a ^ 2) ∂mu) = 0) :
    let contact : Real -> Real := fun xi =>
      (fourierLaplace phi xi).re + theta / (xi ^ 2 + a ^ 2)
    let contactEntire : Complex -> Complex := fun z =>
      (z ^ 2 + (a : Complex) ^ 2) * fourierLaplace phi z + theta
    mu.support <= {xi | contact xi = 0} /\
      Differentiable Complex contactEntire /\
      (exists C tau : Real, 0 <= C /\ 0 <= tau /\
        forall z : Complex, norm (contactEntire z) <= C * Real.exp (tau * norm z)) /\
      mu.support <= {xi : Real | contactEntire xi = 0} := by
  dsimp only
  have fourierContinuous : Continuous (fourierLaplace phi) :=
    (fourierLaplace_entire phi).continuous
  have denominatorPositive (xi : Real) : 0 < xi ^ 2 + a ^ 2 := by positivity
  have contactContinuous : Continuous (fun xi : Real =>
      (fourierLaplace phi xi).re + theta / (xi ^ 2 + a ^ 2)) := by
    have transformRealContinuous :
        Continuous (fun xi : Real => (fourierLaplace phi xi).re) := by
      fun_prop
    have denominatorContinuous : Continuous (fun xi : Real => xi ^ 2 + a ^ 2) := by
      fun_prop
    exact transformRealContinuous.add
      (continuous_const.div denominatorContinuous fun xi => (denominatorPositive xi).ne')
  have contactZeroAlmostEverywhere :
      (fun xi : Real =>
        (fourierLaplace phi xi).re + theta / (xi ^ 2 + a ^ 2)) =ᵐ[mu] 0 :=
    (integral_eq_zero_iff_of_nonneg contactNonnegative contactIntegrable).mp complementarity
  have supportOnContactZeros : mu.support <= {xi : Real |
      (fourierLaplace phi xi).re + theta / (xi ^ 2 + a ^ 2) = 0} :=
    Measure.support_subset_of_isClosed
      (isClosed_eq contactContinuous continuous_const) contactZeroAlmostEverywhere
  have contactEntireDifferentiable : Differentiable Complex (fun z : Complex =>
      (z ^ 2 + (a : Complex) ^ 2) * fourierLaplace phi z + theta) := by
    exact (((differentiable_id.pow 2).add (differentiable_const (c := (a : Complex) ^ 2))).mul
      (fourierLaplace_entire phi)).add (differentiable_const (c := (theta : Complex)))
  obtain ⟨Lambda, supportBound⟩ :=
    Zeta23.EF.exists_abs_le_of_hasCompactSupport phi.hasCompactSupport
  let radius : Real := max Lambda 0
  have radiusNonnegative : 0 <= radius := le_max_right Lambda 0
  have supportBound' : forall u, phi u ≠ 0 -> abs u <= radius := by
    intro u hu
    exact (supportBound u hu).trans (le_max_left Lambda 0)
  let mass : Real := ∫ u : Real, norm (phi u)
  have massNonnegative : 0 <= mass := integral_nonneg fun _ => norm_nonneg _
  have transformBound (z : Complex) :
      norm (fourierLaplace phi z) <=
        Real.exp (radius * norm z) * mass := by
    have paperBound := Zeta23.norm_paperFT_le phi.integrable supportBound' z
    rw [paperFT_eq_fourierLaplace] at paperBound
    calc
      norm (fourierLaplace phi z) <=
          Real.exp (abs z.im * radius) * mass := paperBound
      _ <= Real.exp (radius * norm z) * mass := by
        apply mul_le_mul_of_nonneg_right _ massNonnegative
        apply Real.exp_le_exp.mpr
        rw [mul_comm (abs z.im) radius]
        exact mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm z) radiusNonnegative
  have exponentialPolynomialBound (z : Complex) :
      norm (z ^ 2 + (a : Complex) ^ 2) <=
        2 * (1 + a ^ 2) * Real.exp (2 * norm z) := by
    have normLeExp : norm z <= Real.exp (norm z) :=
      (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp (norm z))
    have squareLeExp : norm z ^ 2 <= Real.exp (2 * norm z) := by
      have productNonnegative :
          0 <= (Real.exp (norm z) - norm z) * (Real.exp (norm z) + norm z) :=
        mul_nonneg (sub_nonneg.mpr normLeExp)
          (add_nonneg (Real.exp_pos _).le (norm_nonneg _))
      rw [show Real.exp (2 * norm z) = Real.exp (norm z) * Real.exp (norm z) by
        rw [← Real.exp_add]
        congr 1
        ring]
      nlinarith
    have oneLeExp : 1 <= Real.exp (2 * norm z) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by positivity)
    calc
      norm (z ^ 2 + (a : Complex) ^ 2) <=
          norm (z ^ 2) + norm ((a : Complex) ^ 2) := norm_add_le _ _
      _ = norm z ^ 2 + a ^ 2 := by simp [norm_pow, Real.norm_eq_abs, abs_of_pos ha]
      _ <= (1 + a ^ 2) * (1 + norm z ^ 2) := by
        nlinarith [sq_nonneg a, sq_nonneg (norm z)]
      _ <= (1 + a ^ 2) * (2 * Real.exp (2 * norm z)) := by
        gcongr
        nlinarith
      _ = 2 * (1 + a ^ 2) * Real.exp (2 * norm z) := by ring
  let coefficient : Real := 2 * (1 + a ^ 2) * mass + theta
  let rate : Real := radius + 2
  have coefficientNonnegative : 0 <= coefficient := by
    dsimp [coefficient]
    positivity
  have rateNonnegative : 0 <= rate := by
    dsimp [rate]
    positivity
  have finiteExponentialType (z : Complex) :
      norm ((z ^ 2 + (a : Complex) ^ 2) * fourierLaplace phi z + theta) <=
        coefficient * Real.exp (rate * norm z) := by
    have exponentialAtLeastOne : 1 <= Real.exp (rate * norm z) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonneg rateNonnegative (norm_nonneg z))
    have thetaBound : theta <= theta * Real.exp (rate * norm z) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left exponentialAtLeastOne htheta
    have exponentialProduct :
        Real.exp (2 * norm z) * Real.exp (radius * norm z) =
          Real.exp (rate * norm z) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [rate]
      ring
    calc
      norm ((z ^ 2 + (a : Complex) ^ 2) * fourierLaplace phi z + theta) <=
          norm ((z ^ 2 + (a : Complex) ^ 2) * fourierLaplace phi z) +
            norm (theta : Complex) :=
        norm_add_le ((z ^ 2 + (a : Complex) ^ 2) * fourierLaplace phi z)
          (theta : Complex)
      _ = norm (z ^ 2 + (a : Complex) ^ 2) * norm (fourierLaplace phi z) + theta := by
        rw [norm_mul]
        simp [abs_of_nonneg htheta]
      _ <= (2 * (1 + a ^ 2) * Real.exp (2 * norm z)) *
            (Real.exp (radius * norm z) * mass) + theta := by
        gcongr
        · exact exponentialPolynomialBound z
        · exact transformBound z
      _ = 2 * (1 + a ^ 2) * mass *
            (Real.exp (2 * norm z) * Real.exp (radius * norm z)) + theta := by ring
      _ = 2 * (1 + a ^ 2) * mass * Real.exp (rate * norm z) + theta := by
        rw [exponentialProduct]
      _ <= 2 * (1 + a ^ 2) * mass * Real.exp (rate * norm z) +
            theta * Real.exp (rate * norm z) := by
        let mainTerm := 2 * (1 + a ^ 2) * mass * Real.exp (rate * norm z)
        calc
          mainTerm + theta = theta + mainTerm := add_comm _ _
          _ <= theta * Real.exp (rate * norm z) + mainTerm :=
            add_le_add_left thetaBound mainTerm
          _ = mainTerm + theta * Real.exp (rate * norm z) := add_comm _ _
      _ = coefficient * Real.exp (rate * norm z) := by
        dsimp [coefficient]
        ring
  have supportOnEntireRealZeros : mu.support <= {xi : Real |
      ((xi : Complex) ^ 2 + (a : Complex) ^ 2) * fourierLaplace phi xi + theta = 0} := by
    intro xi hxi
    have contactZero := supportOnContactZeros hxi
    have transformImaginaryPart : (fourierLaplace phi (xi : Complex)).im = 0 :=
      Complex.conj_eq_iff_im.mp (fourierLaplace_real_axis phi hreal xi)
    have transformReal : fourierLaplace phi (xi : Complex) =
        ((fourierLaplace phi (xi : Complex)).re : Complex) := by
      apply Complex.ext
      · simp
      · simpa using transformImaginaryPart
    have denominatorNonzero : xi ^ 2 + a ^ 2 ≠ 0 :=
      ne_of_gt (denominatorPositive xi)
    have clearedContact :
        (xi ^ 2 + a ^ 2) * (fourierLaplace phi (xi : Complex)).re + theta = 0 := by
      field_simp [denominatorNonzero] at contactZero
      simpa [mul_comm] using contactZero
    change ((xi : Complex) ^ 2 + (a : Complex) ^ 2) *
      fourierLaplace phi xi + theta = 0
    rw [transformReal]
    exact_mod_cast clearedContact
  exact ⟨supportOnContactZeros, contactEntireDifferentiable,
    ⟨coefficient, rate, coefficientNonnegative, rateNonnegative, finiteExponentialType⟩,
    supportOnEntireRealZeros⟩

end D5.S3.Weil.TestFunctions.ComplementaryContactSupport
