/- GID: D5/S3/Weil/Budget/CayleyMomentTransport
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/CayleyMomentTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Cayley moments admit a derivative jet and geometric scale-transport tail bound. -/

import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
Library-search audit trail (2026-08-29):
* D5 searches for scale-parametrized Cayley coordinates, resolvent moments,
  shifted Chebyshev jets, and geometric budget transport found no exact owner.
  `Analytic.LiCausalTrichotomy.cayley` is fixed at scale one half and is not the
  scale-parametrized source object used here.
* Pinned Mathlib supplies `Polynomial.Chebyshev.T`, `iteratedDeriv`,
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le`, and
  `integral_finsetSum`.  No exact theorem combines these into the public
  statement below.
* Pinned Mathlib contains no generalized Laguerre polynomial API or the
  Laguerre transform needed for the adjacent time-domain theorem.
-/

open MeasureTheory
open scoped ComplexConjugate

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Budget.CayleyMomentTransport

private theorem norm_scale_cayley (a xi : Real) (ha : a ≠ 0) :
    norm (((xi : Complex) + Complex.I * a) /
      ((xi : Complex) - Complex.I * a)) = 1 := by
  have denominatorNonzero : (xi : Complex) - Complex.I * a ≠ 0 := by
    intro h
    have imaginaryPart := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.ofReal_im, mul_zero, Complex.I_im, Complex.ofReal_re, one_mul,
      zero_sub, Complex.zero_im] at imaginaryPart
    exact ha (by linarith)
  rw [norm_div]
  have equalNorms :
      norm ((xi : Complex) + Complex.I * a) =
        norm ((xi : Complex) - Complex.I * a) := by
    rw [Complex.norm_def, Complex.norm_def]
    congr 1
    simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, zero_mul, Complex.I_im,
      Complex.ofReal_im, mul_zero, sub_zero, Complex.add_im,
      Complex.sub_re, Complex.sub_im, zero_sub]
    ring
  rw [equalNorms, div_self (norm_ne_zero_iff.mpr denominatorNonzero)]

private theorem real_pow_eq_chebyshev
    (z : Complex) (n : Nat) (hz : norm z = 1) :
    (z ^ n).re = (Polynomial.Chebyshev.T Real (n : Int)).eval z.re := by
  rcases (Complex.norm_eq_one_iff z).mp hz with ⟨theta, htheta⟩
  have realPart : Real.cos theta = z.re := by
    simpa only [Complex.exp_ofReal_mul_I_re] using congrArg Complex.re htheta
  calc
    (z ^ n).re = (Complex.exp (theta * Complex.I) ^ n).re := by rw [htheta]
    _ = (Complex.exp ((n : Complex) * (theta * Complex.I))).re := by
      rw [Complex.exp_nat_mul]
    _ = Real.cos ((n : Real) * theta) := by
      rw [show (n : Complex) * (theta * Complex.I) =
          (((n : Real) * theta : Real) : Complex) * Complex.I by push_cast; ring]
      exact Complex.exp_ofReal_mul_I_re _
    _ = (Polynomial.Chebyshev.T Real (n : Int)).eval (Real.cos theta) := by
      rw [Polynomial.Chebyshev.T_real_cos]
      norm_num
    _ = (Polynomial.Chebyshev.T Real (n : Int)).eval z.re := by rw [realPart]

private theorem cayley_real_power
    (xi a : Real) (n : Nat) (ha : 0 < a) :
    ((((xi : Complex) + Complex.I * a) /
      ((xi : Complex) - Complex.I * a)) ^ n).re =
      (Polynomial.Chebyshev.T Real (n : Int)).eval
        (1 - 2 * (a ^ 2 / (xi ^ 2 + a ^ 2))) := by
  let z : Complex := ((xi : Complex) + Complex.I * a) /
    ((xi : Complex) - Complex.I * a)
  have hzNorm : norm z = 1 := norm_scale_cayley a xi ha.ne'
  rw [real_pow_eq_chebyshev z n hzNorm]
  congr 1
  dsimp only [z]
  have denominatorNonzero : (xi : Complex) - Complex.I * a ≠ 0 := by
    intro h
    have imaginaryPart := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.ofReal_im, mul_zero, Complex.I_im, Complex.ofReal_re, one_mul,
      zero_sub, Complex.zero_im] at imaginaryPart
    linarith
  rw [Complex.div_re]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.mul_im, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.add_im, Complex.sub_re, Complex.sub_im, zero_sub,
    Complex.normSq_apply]
  have realDenominatorNonzero : xi ^ 2 + a ^ 2 ≠ 0 := by positivity
  field_simp [realDenominatorNonzero]
  ring

private theorem scale_poisson_kernel_identity
    (xi a b : Real) (ha : 0 < a) (hb : 0 < b) :
    let r := (a - b) / (a + b)
    let z : Complex := ((xi : Complex) + Complex.I * a) /
      ((xi : Complex) - Complex.I * a)
    (a / b) * ((1 - r ^ 2) / Complex.normSq (1 + (r : Complex) * z)) *
      (1 / (xi ^ 2 + a ^ 2)) = 1 / (xi ^ 2 + b ^ 2) := by
  dsimp only
  have scaleSumNonzero : a + b ≠ 0 := by positivity
  have complexDenominatorNonzero : (xi : Complex) - Complex.I * a ≠ 0 := by
    intro h
    have imaginaryPart := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      mul_zero, Complex.I_im, Complex.ofReal_re, one_mul, zero_sub,
      Complex.zero_im] at imaginaryPart
    linarith
  have realADenominatorNonzero : xi ^ 2 + a ^ 2 ≠ 0 := by positivity
  have realBDenominatorNonzero : xi ^ 2 + b ^ 2 ≠ 0 := by positivity
  have normIdentity :
      Complex.normSq (1 + ((((a - b) / (a + b) : Real)) : Complex) *
        (((xi : Complex) + Complex.I * a) /
          ((xi : Complex) - Complex.I * a))) =
        4 * a ^ 2 * (xi ^ 2 + b ^ 2) /
          ((a + b) ^ 2 * (xi ^ 2 + a ^ 2)) := by
    rw [show 1 + (((a - b) / (a + b) : Real) : Complex) *
          (((xi : Complex) + Complex.I * a) /
            ((xi : Complex) - Complex.I * a)) =
        (((xi : Complex) - Complex.I * a) +
            (((a - b) / (a + b) : Real) : Complex) *
              ((xi : Complex) + Complex.I * a)) /
          ((xi : Complex) - Complex.I * a) by
        field_simp [complexDenominatorNonzero]]
    rw [Complex.normSq_div]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re,
      Complex.ofReal_re, Complex.mul_re, Complex.mul_im, Complex.I_re, zero_mul,
      Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, Complex.add_im,
      Complex.sub_im, zero_sub, one_mul, add_zero]
    field_simp [scaleSumNonzero, realADenominatorNonzero]
    ring
  rw [normIdentity]
  field_simp [scaleSumNonzero, ha.ne', hb.ne', realADenominatorNonzero,
    realBDenominatorNonzero]
  ring

private theorem cayley_moment_integrable
    (nu : Measure Real) (a : Real) (k : Nat) (ha : 0 < a)
    (baseIntegrable : Integrable (fun xi : Real => 1 / (xi ^ 2 + a ^ 2)) nu) :
    Integrable (fun xi : Real =>
      (((((xi : Complex) + Complex.I * a) /
        ((xi : Complex) - Complex.I * a)) ^ k).re) / (xi ^ 2 + a ^ 2)) nu := by
  have complexDenominatorNonzero :
      forall xi : Real, (xi : Complex) - Complex.I * a ≠ 0 := by
    intro xi h
    have imaginaryPart := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      mul_zero, Complex.I_im, Complex.ofReal_re, one_mul, zero_sub,
      Complex.zero_im] at imaginaryPart
    exact ha.ne' (by linarith)
  refine baseIntegrable.mono' ?_ (ae_of_all _ fun xi => ?_)
  · have cayleyContinuous : Continuous (fun xi : Real =>
        ((xi : Complex) + Complex.I * a) /
          ((xi : Complex) - Complex.I * a)) :=
      (Complex.continuous_ofReal.add continuous_const).div
        (Complex.continuous_ofReal.sub continuous_const)
        complexDenominatorNonzero
    exact ((Complex.continuous_re.comp (cayleyContinuous.pow k)).div
      (by fun_prop) (fun xi => by positivity)).aestronglyMeasurable
  · have numeratorBound :
        abs (((((xi : Complex) + Complex.I * a) /
          ((xi : Complex) - Complex.I * a)) ^ k).re) <= 1 := by
      calc
        abs (((((xi : Complex) + Complex.I * a) /
          ((xi : Complex) - Complex.I * a)) ^ k).re) <=
            norm ((((xi : Complex) + Complex.I * a) /
              ((xi : Complex) - Complex.I * a)) ^ k) :=
          Complex.abs_re_le_norm _
        _ = 1 := by
          rw [norm_pow, norm_scale_cayley a xi ha.ne', one_pow]
    have denominatorPositive : 0 < xi ^ 2 + a ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos denominatorPositive]
    exact (div_le_div_iff_of_pos_right denominatorPositive).2 numeratorBound

private theorem poisson_kernel_truncation
    (z : Complex) (r : Real) (M : Nat) (hz : norm z = 1) (hr : abs r < 1) :
    abs ((1 - r ^ 2) / Complex.normSq (1 + (r : Complex) * z) -
      (1 + 2 * Finset.sum (Finset.range M) (fun k : Nat =>
        (-r) ^ (k + 1) * (z ^ (k + 1)).re))) <=
      2 * abs r ^ (M + 1) / (1 - abs r) := by
  let x : Complex := -(r : Complex) * z
  have xNorm : norm x = abs r := by
    dsimp only [x]
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, hz, mul_one]
  have xNormLtOne : norm x < 1 := by rwa [xNorm]
  have xNeOne : x ≠ 1 := by
    intro h
    rw [h, norm_one] at xNormLtOne
    linarith
  have denominatorNonzero : 1 - x ≠ 0 := sub_ne_zero.mpr xNeOne.symm
  have finiteRemainder :
      (1 + x) / (1 - x) -
          (1 + 2 * Finset.sum (Finset.range M) (fun k : Nat => x ^ (k + 1))) =
        2 * x ^ (M + 1) / (1 - x) := by
    have shiftedSum : Finset.sum (Finset.range M) (fun k : Nat => x ^ (k + 1)) =
        x * Finset.sum (Finset.range M) (fun k : Nat => x ^ k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [pow_succ']
    rw [shiftedSum]
    field_simp [denominatorNonzero]
    have geometricIdentity := geom_sum_mul_neg x M
    calc
      1 + x - (1 - x) *
          (1 + x * 2 * Finset.sum (Finset.range M) (fun k : Nat => x ^ k)) =
        2 * x * (1 - Finset.sum (Finset.range M) (fun k : Nat => x ^ k) *
          (1 - x)) := by ring
      _ = 2 * x * x ^ M := by rw [geometricIdentity]; ring
      _ = 2 * x ^ (M + 1) := by rw [pow_succ']; ring
  have poissonRealPart :
      ((1 + x) / (1 - x)).re =
        (1 - r ^ 2) / Complex.normSq (1 + (r : Complex) * z) := by
    have kernelIdentity := congrFun (poissonKernel_eq_re_herglotzRieszKernel
      (c := (0 : Complex)) (w := x)) (1 : Complex)
    rw [Function.comp_apply, poissonKernel_def, herglotzRieszKernel_def] at kernelIdentity
    have xSquare : norm x ^ 2 = r ^ 2 := by
      rw [xNorm, sq_abs]
    have denominatorIdentity : norm ((1 : Complex) - x) ^ 2 =
        Complex.normSq (1 + (r : Complex) * z) := by
      rw [Complex.normSq_eq_norm_sq]
      congr 2
      dsimp only [x]
      ring
    simpa [xSquare, denominatorIdentity] using kernelIdentity.symm
  have finiteRealPart :
      (1 + 2 * Finset.sum (Finset.range M) (fun k : Nat => x ^ (k + 1))).re =
        1 + 2 * Finset.sum (Finset.range M) (fun k : Nat =>
          (-r) ^ (k + 1) * (z ^ (k + 1)).re) := by
    rw [Complex.add_re, Complex.one_re, Complex.mul_re]
    norm_num [map_sum Complex.reCLM]
    apply Finset.sum_congr rfl
    intro k _
    dsimp only [x]
    rw [mul_pow]
    have realPower : (-(r : Complex)) ^ (k + 1) =
        (((-r) ^ (k + 1) : Real) : Complex) := by
      push_cast
      rfl
    rw [realPower, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  rw [← poissonRealPart, ← finiteRealPart, ← Complex.sub_re]
  calc
    abs (((1 + x) / (1 - x) -
        (1 + 2 * Finset.sum (Finset.range M) (fun k : Nat => x ^ (k + 1)))).re) <=
        norm ((1 + x) / (1 - x) -
          (1 + 2 * Finset.sum (Finset.range M) (fun k : Nat => x ^ (k + 1)))) :=
      Complex.abs_re_le_norm _
    _ = norm (2 * x ^ (M + 1) / (1 - x)) := by rw [finiteRemainder]
    _ = 2 * abs r ^ (M + 1) / norm (1 - x) := by
      rw [norm_div, norm_mul, Complex.norm_ofNat, norm_pow, xNorm]
    _ <= 2 * abs r ^ (M + 1) / (1 - abs r) := by
      have denominatorLower : 1 - abs r <= norm (1 - x) := by
        rw [← xNorm]
        simpa using norm_sub_norm_le (1 : Complex) x
      exact div_le_div_of_nonneg_left (by positivity) (by linarith)
        denominatorLower

private theorem kernel_power_integrable
    (nu : Measure Real) (v : Real) (m : Nat) (hv : 0 < v)
    (baseIntegrable : Integrable (fun xi : Real => 1 / (xi ^ 2 + v)) nu) :
    Integrable (fun xi : Real => 1 / (xi ^ 2 + v) ^ (m + 1)) nu := by
  have scaledIntegrable := baseIntegrable.const_mul ((1 / v) ^ m)
  refine scaledIntegrable.mono' (by
    exact (continuous_const.div (by fun_prop) (fun xi => by positivity) :
      Continuous (fun xi : Real => 1 / (xi ^ 2 + v) ^ (m + 1))).aestronglyMeasurable)
      (ae_of_all _ fun xi => ?_)
  have denominatorPositive : 0 < xi ^ 2 + v := by positivity
  have denominatorLower : v ≤ xi ^ 2 + v := by nlinarith [sq_nonneg xi]
  have inverseBound : 1 / (xi ^ 2 + v) ≤ 1 / v := by
    exact one_div_le_one_div_of_le hv denominatorLower
  rw [Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (xi ^ 2 + v) ^ (m + 1))]
  rw [show 1 / (xi ^ 2 + v) ^ (m + 1) =
      (1 / (xi ^ 2 + v)) ^ m * (1 / (xi ^ 2 + v)) by
    rw [← one_div_pow, pow_succ]]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) inverseBound m) (by positivity)

private theorem resolvent_integrable_at_positive_scale
    (nu : Measure Real) (u v : Real) (uPositive : 0 < u) (vPositive : 0 < v)
    (budgetIntegrable : Integrable (fun xi : Real => 1 / (xi ^ 2 + u)) nu) :
    Integrable (fun xi : Real => 1 / (xi ^ 2 + v)) nu := by
  let comparison : Real := u / v + 1
  have comparisonPositive : 0 < comparison := by
    dsimp only [comparison]
    positivity
  have scaledIntegrable := budgetIntegrable.const_mul comparison
  refine scaledIntegrable.mono' (by
    exact (continuous_const.div (by fun_prop) (fun xi => by positivity) :
      Continuous (fun xi : Real => 1 / (xi ^ 2 + v))).aestronglyMeasurable)
      (ae_of_all _ fun xi => ?_)
  have uDenominatorPositive : 0 < xi ^ 2 + u := by positivity
  have vDenominatorPositive : 0 < xi ^ 2 + v := by positivity
  rw [Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 1 / (xi ^ 2 + v))]
  have denominatorComparison :
      xi ^ 2 + u <= comparison * (xi ^ 2 + v) := by
    have ratioNonnegative : 0 <= u / v := by positivity
    have ratioMul : (u / v) * v = u := by field_simp
    have squareNonnegative : 0 <= xi ^ 2 := sq_nonneg xi
    dsimp only [comparison]
    nlinarith [mul_nonneg ratioNonnegative squareNonnegative]
  calc
    1 / (xi ^ 2 + v) <= comparison / (xi ^ 2 + u) :=
      (div_le_div_iff₀ vDenominatorPositive uDenominatorPositive).2
        (by simpa using denominatorComparison)
    _ = comparison * (1 / (xi ^ 2 + u)) := by ring

private theorem hasDerivAt_kernel_integral
    (nu : Measure Real)
    (resolventIntegrable : forall v : Real, 0 < v ->
      Integrable (fun xi : Real => 1 / (xi ^ 2 + v)) nu)
    (m : Nat) (v : Real) (hv : 0 < v) :
    HasDerivAt
      (fun w : Real => integral nu (fun xi : Real =>
        1 / (xi ^ 2 + w) ^ (m + 1)))
      (-((m + 1 : Nat) : Real) * integral nu (fun xi : Real =>
        1 / (xi ^ 2 + v) ^ (m + 2))) v := by
  let s : Set Real := Set.Ioi (v / 2)
  let bound : Real -> Real := fun xi =>
    ((m + 1 : Nat) : Real) * (1 / (xi ^ 2 + v / 2) ^ (m + 2))
  have halfPositive : 0 < v / 2 := by positivity
  have sMem : s ∈ nhds v := by
    apply Ioi_mem_nhds
    linarith
  have integrandIntegrable := kernel_power_integrable nu v m hv
    (resolventIntegrable v hv)
  have boundIntegrable : Integrable bound nu := by
    exact (kernel_power_integrable nu (v / 2) (m + 1) halfPositive
      (resolventIntegrable (v / 2) halfPositive)).const_mul ((m + 1 : Nat) : Real)
  have derivativeMeasurable : AEStronglyMeasurable
      (fun xi : Real => -((m + 1 : Nat) : Real) *
        (1 / (xi ^ 2 + v) ^ (m + 2))) nu := by
    exact (continuous_const.mul
      (continuous_const.div (by fun_prop) (fun xi => by positivity)) :
        Continuous (fun xi : Real => -((m + 1 : Nat) : Real) *
          (1 / (xi ^ 2 + v) ^ (m + 2)))).aestronglyMeasurable
  have derivativeBound : forall xi : Real, forall w : Real, w ∈ s ->
      norm (-((m + 1 : Nat) : Real) *
        (1 / (xi ^ 2 + w) ^ (m + 2))) <= bound xi := by
    intro xi w hw
    change v / 2 < w at hw
    have wPositive : 0 < w := halfPositive.trans hw
    have denominatorPositive : 0 < xi ^ 2 + w := by
      positivity
    have lowerDenominator : xi ^ 2 + v / 2 ≤ xi ^ 2 + w := by
      linarith
    have inverseBound : 1 / (xi ^ 2 + w) ≤ 1 / (xi ^ 2 + v / 2) := by
      exact one_div_le_one_div_of_le (by positivity) lowerDenominator
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (by positivity),
      abs_of_pos (by positivity : 0 < 1 / (xi ^ 2 + w) ^ (m + 2))]
    dsimp only [bound]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [one_div_pow] using
        pow_le_pow_left₀ (by positivity) inverseBound (m + 2)) (by positivity)
  have pointwiseDerivative : forall xi : Real, forall w : Real, w ∈ s ->
      HasDerivAt
        (fun y : Real => 1 / (xi ^ 2 + y) ^ (m + 1))
        (-((m + 1 : Nat) : Real) *
          (1 / (xi ^ 2 + w) ^ (m + 2))) w := by
    intro xi w hw
    change v / 2 < w at hw
    have wPositive : 0 < w := halfPositive.trans hw
    have denominatorNonzero : xi ^ 2 + w ≠ 0 := by
      positivity
    have derivative := (hasDerivAt_zpow (-((m + 1 : Nat) : Int))
      (xi ^ 2 + w) (Or.inl denominatorNonzero)).comp w
        ((hasDerivAt_id w).const_add (xi ^ 2))
    have exponentIdentity :
        -((m + 1 : Nat) : Int) - 1 = -((m + 2 : Nat) : Int) := by omega
    rw [exponentIdentity] at derivative
    simp only [zpow_neg, zpow_natCast] at derivative
    simpa [Function.comp_def, one_div] using derivative
  have integrandMeasurable : ∀ᶠ w in nhds v,
      AEStronglyMeasurable
        (fun xi : Real => 1 / (xi ^ 2 + w) ^ (m + 1)) nu := by
    filter_upwards [sMem] with w hw
    change v / 2 < w at hw
    have wPositive : 0 < w := halfPositive.trans hw
    exact (continuous_const.div (by fun_prop) (fun xi => by positivity) :
      Continuous (fun xi : Real =>
        1 / (xi ^ 2 + w) ^ (m + 1))).aestronglyMeasurable
  have integralDerivative := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w xi : Real => 1 / (xi ^ 2 + w) ^ (m + 1))
    (F' := fun w xi : Real => -((m + 1 : Nat) : Real) *
      (1 / (xi ^ 2 + w) ^ (m + 2)))
    (bound := bound) sMem integrandMeasurable integrandIntegrable
    derivativeMeasurable (ae_of_all _ derivativeBound) boundIntegrable
    (ae_of_all _ pointwiseDerivative)).2
  rw [integral_const_mul] at integralDerivative
  exact integralDerivative

private theorem iteratedDeriv_resolvent_budget
    (nu : Measure Real)
    (resolventIntegrable : forall v : Real, 0 < v ->
      Integrable (fun xi : Real => 1 / (xi ^ 2 + v)) nu)
    (k : Nat) (u : Real) (uPositive : 0 < u) :
    iteratedDeriv k
        (fun v : Real => integral nu (fun xi : Real => 1 / (xi ^ 2 + v))) u =
      (-1 : Real) ^ k * (k.factorial : Real) *
        integral nu (fun xi : Real => 1 / (xi ^ 2 + u) ^ (k + 1)) := by
  induction k generalizing u with
  | zero => simp [iteratedDeriv_zero]
  | succ k inductionHypothesis =>
      rw [iteratedDeriv_succ]
      have eventualIdentity :
          (fun v : Real => iteratedDeriv k
            (fun w : Real => integral nu (fun xi : Real => 1 / (xi ^ 2 + w))) v) =ᶠ[nhds u]
          (fun v : Real => (-1 : Real) ^ k * (k.factorial : Real) *
            integral nu (fun xi : Real => 1 / (xi ^ 2 + v) ^ (k + 1))) := by
        filter_upwards [Ioi_mem_nhds uPositive] with v hv
        exact inductionHypothesis v hv
      rw [eventualIdentity.deriv_eq]
      have integralDerivative :=
        hasDerivAt_kernel_integral nu resolventIntegrable k u uPositive
      rw [(integralDerivative.const_mul
        ((-1 : Real) ^ k * (k.factorial : Real))).deriv]
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      ring

/-- Expanding the shifted Chebyshev polynomial inside the resolvent integral
and substituting the genuine iterated derivatives of the Stieltjes budget
produces the finite scale jet. -/
theorem chebyshev_stieltjes_jet
    (nu : Measure Real) (n : Nat) (u : Real) (p : Fin (n + 1) -> Real)
    (uPositive : 0 < u)
    (coefficientExpansion : forall x : Real,
      (Polynomial.Chebyshev.T Real (n : Int)).eval (1 - 2 * x) =
        Finset.univ.sum (fun k => p k * x ^ (k : Nat)))
    (budgetIntegrable : Integrable (fun xi : Real => 1 / (xi ^ 2 + u)) nu) :
    integral nu (fun xi : Real =>
      (((((xi : Complex) + Complex.I * Real.sqrt u) /
        ((xi : Complex) - Complex.I * Real.sqrt u)) ^ n).re) /
          (xi ^ 2 + u)) =
      Finset.univ.sum (fun k : Fin (n + 1) =>
        p k * u ^ (k : Nat) *
          ((-1 : Real) ^ (k : Nat) / ((k : Nat).factorial : Real)) *
            iteratedDeriv (k : Nat)
              (fun v : Real =>
                integral nu (fun xi : Real => 1 / (xi ^ 2 + v))) u) := by
  have sqrtPositive : 0 < Real.sqrt u := Real.sqrt_pos.2 uPositive
  have momentExpansion (xi : Real) :
      (((((xi : Complex) + Complex.I * Real.sqrt u) /
        ((xi : Complex) - Complex.I * Real.sqrt u)) ^ n).re) /
          (xi ^ 2 + u) =
      (Polynomial.Chebyshev.T Real (n : Int)).eval
          (1 - 2 * (u / (xi ^ 2 + u))) /
        (xi ^ 2 + u) := by
    rw [cayley_real_power xi (Real.sqrt u) n sqrtPositive, Real.sq_sqrt uPositive.le]
  rw [integral_congr_ae (ae_of_all _ momentExpansion)]
  have resolventIntegrable : forall v : Real, 0 < v ->
      Integrable (fun xi : Real => 1 / (xi ^ 2 + v)) nu := by
    intro v vPositive
    exact resolvent_integrable_at_positive_scale nu u v uPositive vPositive
      budgetIntegrable
  have denominatorNonzero (xi : Real) : xi ^ 2 + u ≠ 0 := by positivity
  have pointwiseExpansion (xi : Real) :
      (Polynomial.Chebyshev.T Real (n : Int)).eval
          (1 - 2 * (u / (xi ^ 2 + u))) /
        (xi ^ 2 + u) =
      Finset.univ.sum (fun k : Fin (n + 1) =>
        (p k * u ^ (k : Nat)) *
          (1 / (xi ^ 2 + u) ^ ((k : Nat) + 1))) := by
    rw [coefficientExpansion]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    rw [div_pow]
    field_simp [denominatorNonzero xi]
    rw [pow_succ]
    ring
  rw [integral_congr_ae (ae_of_all _ pointwiseExpansion)]
  rw [integral_finsetSum Finset.univ (fun (k : Fin (n + 1)) _ =>
    (kernel_power_integrable nu u (k : Nat) uPositive
      (resolventIntegrable u uPositive)).const_mul (p k * u ^ (k : Nat)))]
  simp_rw [integral_const_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [iteratedDeriv_resolvent_budget nu resolventIntegrable (k : Nat) u uPositive]
  have factorialNonzero : ((k : Nat).factorial : Real) ≠ 0 := by positivity
  field_simp [factorialNonzero]
  have signSquare : ((-1 : Real) ^ (k : Nat)) ^ 2 = 1 := by
    rw [sq, ← pow_add]
    simp
  rw [signSquare, mul_one]

/-- Truncating the Poisson expansion that transports the resolvent budget
between two positive Cayley scales has the source's strict geometric tail
bound.  Every budget and moment is expanded directly from the measure. -/
theorem budget_transport_error
    (nu : Measure Real) (a b : Real) (M : Nat)
    (aPositive : 0 < a) (bPositive : 0 < b)
    (budgetIntegrable :
      Integrable (fun xi : Real => 1 / (xi ^ 2 + a ^ 2)) nu) :
    abs (integral nu (fun xi : Real => 1 / (xi ^ 2 + b ^ 2)) -
      (a / b) *
        (integral nu (fun xi : Real => 1 / (xi ^ 2 + a ^ 2)) +
          2 * Finset.sum (Finset.range M) (fun k : Nat =>
            (-((a - b) / (a + b))) ^ (k + 1) *
              integral nu (fun xi : Real =>
                (((((xi : Complex) + Complex.I * a) /
                  ((xi : Complex) - Complex.I * a)) ^ (k + 1)).re) /
                    (xi ^ 2 + a ^ 2))))) <=
      (2 * a / b) * integral nu (fun xi : Real => 1 / (xi ^ 2 + a ^ 2)) *
        (abs ((a - b) / (a + b)) ^ (M + 1) /
          (1 - abs ((a - b) / (a + b)))) := by
  let r : Real := (a - b) / (a + b)
  have scaleSumPositive : 0 < a + b := by positivity
  have rAbsLtOne : abs r < 1 := by
    dsimp only [r]
    rw [abs_div, abs_of_pos scaleSumPositive,
      div_lt_one scaleSumPositive]
    exact abs_lt.2 ⟨by linarith, by linarith⟩
  have ratioPositive : 0 < a / b := div_pos aPositive bPositive
  have bBudgetIntegrable :
      Integrable (fun xi : Real => 1 / (xi ^ 2 + b ^ 2)) nu := by
    exact resolvent_integrable_at_positive_scale nu (a ^ 2) (b ^ 2)
      (sq_pos_of_pos aPositive) (sq_pos_of_pos bPositive) budgetIntegrable
  have momentTermIntegrable : forall k : Nat, k ∈ Finset.range M ->
      Integrable (fun xi : Real =>
        (-r) ^ (k + 1) *
          (((((xi : Complex) + Complex.I * a) /
            ((xi : Complex) - Complex.I * a)) ^ (k + 1)).re) /
              (xi ^ 2 + a ^ 2)) nu := by
    intro k _
    simpa only [mul_div_assoc] using
      (cayley_moment_integrable nu a (k + 1) aPositive
        budgetIntegrable).const_mul ((-r) ^ (k + 1))
  have momentSumIntegrable : Integrable (fun xi : Real =>
      Finset.sum (Finset.range M) (fun k : Nat =>
        (-r) ^ (k + 1) *
          (((((xi : Complex) + Complex.I * a) /
            ((xi : Complex) - Complex.I * a)) ^ (k + 1)).re) /
              (xi ^ 2 + a ^ 2))) nu :=
    integrable_finsetSum (Finset.range M) momentTermIntegrable
  have truncatedIntegrable : Integrable (fun xi : Real =>
      (a / b) * (1 / (xi ^ 2 + a ^ 2) +
        2 * Finset.sum (Finset.range M) (fun k : Nat =>
          (-r) ^ (k + 1) *
            (((((xi : Complex) + Complex.I * a) /
              ((xi : Complex) - Complex.I * a)) ^ (k + 1)).re) /
                (xi ^ 2 + a ^ 2)))) nu := by
    exact (budgetIntegrable.add (momentSumIntegrable.const_mul 2)).const_mul (a / b)
  have errorAsIntegral :
      integral nu (fun xi : Real => 1 / (xi ^ 2 + b ^ 2)) -
        (a / b) *
          (integral nu (fun xi : Real => 1 / (xi ^ 2 + a ^ 2)) +
            2 * Finset.sum (Finset.range M) (fun k : Nat =>
              (-r) ^ (k + 1) *
                integral nu (fun xi : Real =>
                  (((((xi : Complex) + Complex.I * a) /
                    ((xi : Complex) - Complex.I * a)) ^ (k + 1)).re) /
                      (xi ^ 2 + a ^ 2)))) =
        integral nu (fun xi : Real =>
          1 / (xi ^ 2 + b ^ 2) -
            (a / b) * (1 / (xi ^ 2 + a ^ 2) +
              2 * Finset.sum (Finset.range M) (fun k : Nat =>
                (-r) ^ (k + 1) *
                  (((((xi : Complex) + Complex.I * a) /
                    ((xi : Complex) - Complex.I * a)) ^ (k + 1)).re) /
                      (xi ^ 2 + a ^ 2)))) := by
    rw [integral_sub bBudgetIntegrable truncatedIntegrable,
      integral_const_mul]
    rw [integral_add budgetIntegrable (momentSumIntegrable.const_mul 2),
      integral_const_mul]
    rw [integral_finsetSum (Finset.range M) momentTermIntegrable]
    have momentIntegralIdentity (k : Nat) :
        integral nu (fun xi : Real =>
          (-r) ^ (k + 1) *
            (((((xi : Complex) + Complex.I * a) /
              ((xi : Complex) - Complex.I * a)) ^ (k + 1)).re) /
                (xi ^ 2 + a ^ 2)) =
          (-r) ^ (k + 1) * integral nu (fun xi : Real =>
            (((((xi : Complex) + Complex.I * a) /
              ((xi : Complex) - Complex.I * a)) ^ (k + 1)).re) /
                (xi ^ 2 + a ^ 2)) := by
      rw [show (fun xi : Real =>
          (-r) ^ (k + 1) *
            (((((xi : Complex) + Complex.I * a) /
              ((xi : Complex) - Complex.I * a)) ^ (k + 1)).re) /
                (xi ^ 2 + a ^ 2)) =
          fun xi : Real => (-r) ^ (k + 1) *
            (((((xi : Complex) + Complex.I * a) /
              ((xi : Complex) - Complex.I * a)) ^ (k + 1)).re /
                (xi ^ 2 + a ^ 2)) by
        funext xi
        ring]
      exact integral_const_mul _ _
    simp_rw [momentIntegralIdentity]
  rw [show (a - b) / (a + b) = r by rfl]
  rw [errorAsIntegral]
  rw [← Real.norm_eq_abs]
  calc
    norm (integral nu (fun xi : Real =>
        1 / (xi ^ 2 + b ^ 2) -
          (a / b) * (1 / (xi ^ 2 + a ^ 2) +
            2 * Finset.sum (Finset.range M) (fun k : Nat =>
              (-r) ^ (k + 1) *
                (((((xi : Complex) + Complex.I * a) /
                  ((xi : Complex) - Complex.I * a)) ^ (k + 1)).re) /
                    (xi ^ 2 + a ^ 2))))) <=
      integral nu (fun xi : Real =>
        ((2 * a / b) * (abs r ^ (M + 1) / (1 - abs r))) *
          (1 / (xi ^ 2 + a ^ 2))) := by
      apply norm_integral_le_of_norm_le
        (budgetIntegrable.const_mul
          ((2 * a / b) * (abs r ^ (M + 1) / (1 - abs r))))
      exact ae_of_all _ fun xi => by
        let z : Complex := ((xi : Complex) + Complex.I * a) /
          ((xi : Complex) - Complex.I * a)
        have zNorm : norm z = 1 := norm_scale_cayley a xi aPositive.ne'
        have kernelBound := poisson_kernel_truncation z r M zNorm rAbsLtOne
        have scaleIdentity := scale_poisson_kernel_identity xi a b
          aPositive bPositive
        have momentSumIdentity :
            Finset.sum (Finset.range M) (fun k : Nat =>
              (-r) ^ (k + 1) *
                (((((xi : Complex) + Complex.I * a) /
                  ((xi : Complex) - Complex.I * a)) ^ (k + 1)).re) /
                    (xi ^ 2 + a ^ 2)) =
              (1 / (xi ^ 2 + a ^ 2)) *
                Finset.sum (Finset.range M) (fun k : Nat =>
                  (-r) ^ (k + 1) * (z ^ (k + 1)).re) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          dsimp only [z]
          ring
        have pointwiseAlgebra :
            1 / (xi ^ 2 + b ^ 2) -
                (a / b) * (1 / (xi ^ 2 + a ^ 2) +
                  2 * Finset.sum (Finset.range M) (fun k : Nat =>
                    (-r) ^ (k + 1) *
                      (((((xi : Complex) + Complex.I * a) /
                        ((xi : Complex) - Complex.I * a)) ^ (k + 1)).re) /
                          (xi ^ 2 + a ^ 2))) =
              (a / b) * (1 / (xi ^ 2 + a ^ 2)) *
                ((1 - r ^ 2) / Complex.normSq (1 + (r : Complex) * z) -
                  (1 + 2 * Finset.sum (Finset.range M) (fun k : Nat =>
                    (-r) ^ (k + 1) * (z ^ (k + 1)).re))) := by
          rw [momentSumIdentity]
          rw [← scaleIdentity]
          ring
        have basePositive : 0 < 1 / (xi ^ 2 + a ^ 2) := by positivity
        rw [pointwiseAlgebra, Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_pos ratioPositive, abs_of_pos basePositive]
        calc
          a / b * (1 / (xi ^ 2 + a ^ 2)) *
              abs ((1 - r ^ 2) / Complex.normSq (1 + (r : Complex) * z) -
                (1 + 2 * Finset.sum (Finset.range M) (fun k : Nat =>
                  (-r) ^ (k + 1) * (z ^ (k + 1)).re))) <=
            a / b * (1 / (xi ^ 2 + a ^ 2)) *
              (2 * abs r ^ (M + 1) / (1 - abs r)) :=
            mul_le_mul_of_nonneg_left kernelBound (by positivity)
          _ = ((2 * a / b) * (abs r ^ (M + 1) / (1 - abs r))) *
              (1 / (xi ^ 2 + a ^ 2)) := by ring
    _ = (2 * a / b) * integral nu
          (fun xi : Real => 1 / (xi ^ 2 + a ^ 2)) *
        (abs r ^ (M + 1) / (1 - abs r)) := by
      rw [integral_const_mul]
      ring

end D5.S3.Weil.Budget.CayleyMomentTransport
