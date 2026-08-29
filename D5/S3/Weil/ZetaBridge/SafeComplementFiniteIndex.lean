/- GID: D5/S3/Weil/ZetaBridge/SafeComplementFiniteIndex
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/SafeComplementFiniteIndex
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A safe spectral complement has a positive gap and finite negative index. -/

import D5.S3.Weil.ZetaBridge.FixedScaleWeilQuadraticForm
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import D5.S3.Weil.ZetaLinear.ExactStickyReduction
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.LinearAlgebra.Projection

/-!
# Safe complementary gap and negative index

The first theorem works on the canonical even compactly supported Weil tests,
the angular Fourier-Laplace transform, and the fixed-scale multiplier.  Its
local proof supplies the band/complement integration bridge.

The second theorem is the finite-codimension linear-algebra consequence: a
strictly positive complementary subspace contains no negative direction, so
projection of every finite negative subspace into the retained block is
injective.
-/

noncomputable section

namespace D5.S3.Weil.ZetaBridge.SafeComplementFiniteIndex

open MeasureTheory Set
open D5.S3.Weil.Convention
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
open D5.S3.Weil.PrimePoleTerms
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.WeilIdentity
open D5.S3.Weil.ZetaBridge.FixedScaleWeilQuadraticForm
open D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
open D5.S3.Weil.ZetaLinear.ExactStickyReduction
open scoped ComplexConjugate FourierTransform

private theorem spectral_normSq_integrable (f : WeilTestFunction) :
    Integrable (fun xi : ℝ => Complex.normSq (fourierLaplace f xi)) := by
  let sf : SchwartzMap ℝ ℂ := f.hasCompactSupport.toSchwartzMap f.contDiff
  have hFourier : Integrable (fun w : ℝ => ‖𝓕 sf w‖ ^ 2) :=
    ((𝓕 sf).memLp 2).integrable_norm_pow (by norm_num)
  have hScaled := hFourier.comp_div (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
  refine hScaled.congr ?_
  filter_upwards with xi
  have hLaplace : fourierLaplace f xi = 𝓕 sf (xi / (2 * Real.pi)) := by
    rw [fourierLaplace_real_eq_fourier]
    rfl
  rw [hLaplace, Complex.normSq_eq_norm_sq]

private theorem angular_plancherel (f : WeilTestFunction) :
    (1 / (2 * Real.pi)) *
        ∫ xi : ℝ, Complex.normSq (fourierLaplace f xi) = l2Mass f := by
  let sf : SchwartzMap ℝ ℂ := f.hasCompactSupport.toSchwartzMap f.contDiff
  have hFourierPoint (xi : ℝ) :
      Complex.normSq (fourierLaplace f xi) =
        ‖𝓕 sf (xi / (2 * Real.pi))‖ ^ 2 := by
    have hLaplace : fourierLaplace f xi = 𝓕 sf (xi / (2 * Real.pi)) := by
      rw [fourierLaplace_real_eq_fourier]
      rfl
    rw [hLaplace, Complex.normSq_eq_norm_sq]
  have hScale :
      (∫ xi : ℝ, ‖𝓕 sf (xi / (2 * Real.pi))‖ ^ 2) =
        |2 * Real.pi| * ∫ w : ℝ, ‖𝓕 sf w‖ ^ 2 := by
    simpa only [smul_eq_mul] using Measure.integral_comp_div
      (fun w : ℝ => ‖𝓕 sf w‖ ^ 2) (2 * Real.pi)
  have hPlancherel := SchwartzMap.integral_norm_sq_fourier sf
  calc
    (1 / (2 * Real.pi)) *
          ∫ xi : ℝ, Complex.normSq (fourierLaplace f xi) =
        (1 / (2 * Real.pi)) *
          ∫ xi : ℝ, ‖𝓕 sf (xi / (2 * Real.pi))‖ ^ 2 := by
            congr 1
            apply integral_congr_ae
            filter_upwards with xi
            exact hFourierPoint xi
    _ = (1 / (2 * Real.pi)) *
          (|2 * Real.pi| * ∫ w : ℝ, ‖𝓕 sf w‖ ^ 2) := by rw [hScale]
    _ = ∫ x : ℝ, ‖sf x‖ ^ 2 := by
      rw [abs_of_pos (by positivity : 0 < 2 * Real.pi), hPlancherel]
      field_simp [Real.pi_ne_zero]
    _ = l2Mass f := by
      unfold l2Mass
      apply integral_congr_ae
      filter_upwards with x
      exact (Complex.normSq_eq_norm_sq (f x)).symm

private theorem complex_weighted_integral_re
    (m e : ℝ -> ℝ) (h : Integrable (fun xi => m xi * e xi)) :
    ((∫ xi : ℝ, (m xi : ℂ) * (e xi : ℂ))).re = ∫ xi : ℝ, m xi * e xi := by
  have hComplex : Integrable (fun xi : ℝ => ((m xi * e xi : ℝ) : ℂ)) :=
    h.ofReal
  rw [show (fun xi : ℝ => (m xi : ℂ) * (e xi : ℂ)) =
      fun xi : ℝ => ((m xi * e xi : ℝ) : ℂ) by
    funext xi
    exact (Complex.ofReal_mul _ _).symm]
  rw [integral_complex_ofReal]
  simp

/-- A safe spectral complement has the explicit gap
`a - (a + b) * eta`, where `b` is the depth of the canonical dangerous
multiplier band.  The conclusion is stated on the frozen zero-side Weil form. -/
theorem safe_complement_gap
    (Z : ZeroData) (L a eta : ℝ) (Q : WeilTestFunction -> Prop)
    (f : WeilTestFunction) (hfQ : Q f)
    (hSupport : tsupport (f : ℝ -> ℂ) ⊆ Icc (-L) L)
    (hZero : SymmetricConvergent Z (convolutionSquare f))
    (hArch : ArchimedeanConvergent (convolutionSquare f))
    (hMultiplierIntegrable : Integrable (fun xi : ℝ =>
      fixedScaleMultiplier L xi * Complex.normSq (fourierLaplace f xi)))
    (hDangerousMeasurable :
      MeasurableSet {xi : ℝ | fixedScaleMultiplier L xi < a})
    (hDepthBounded : BddBelow
      (fixedScaleMultiplier L '' {xi : ℝ | fixedScaleMultiplier L xi < a}))
    (ha : 0 < a)
    (hEta :
      0 < eta /\
        eta < a / (a + max 0 (-sInf
          (fixedScaleMultiplier L '' {xi : ℝ | fixedScaleMultiplier L xi < a}))))
    (hConcentration : forall g, Q g ->
      (1 / (2 * Real.pi)) *
          ∫ xi : ℝ in {xi | fixedScaleMultiplier L xi < a},
            Complex.normSq (fourierLaplace g xi) <= eta * l2Mass g)
    (hPoleOrthogonal : forall g, Q g ->
      (∫ x : ℝ, ((Real.cosh (x / 2) : ℝ) : ℂ) * g x) = 0) :
    let dangerous := {xi : ℝ | fixedScaleMultiplier L xi < a}
    let depth := max 0 (-sInf (fixedScaleMultiplier L '' dangerous))
    let delta := a - (a + depth) * eta
    0 < delta /\
      delta * l2Mass f <= (zeroSum Z (convolutionSquare f) hZero).re := by
  dsimp only
  let dangerous : Set ℝ := {xi | fixedScaleMultiplier L xi < a}
  let depth : ℝ := max 0 (-sInf (fixedScaleMultiplier L '' dangerous))
  let delta : ℝ := a - (a + depth) * eta
  let energy : ℝ -> ℝ := fun xi => Complex.normSq (fourierLaplace f xi)
  let multiplier : ℝ -> ℝ := fixedScaleMultiplier L
  let factor : ℝ := 1 / (2 * Real.pi)
  have hDangerousMeasurable' : MeasurableSet dangerous := by
    simpa only [dangerous] using hDangerousMeasurable
  have hEnergyIntegrable : Integrable energy := by
    exact spectral_normSq_integrable f
  have hEnergyNonnegative (xi : ℝ) : 0 <= energy xi :=
    Complex.normSq_nonneg _
  have hDepthNonnegative : 0 <= depth := le_max_left _ _
  have hInside (xi : ℝ) (hxi : xi ∈ dangerous) : -depth <= multiplier xi := by
    have hinf : sInf (multiplier '' dangerous) <= multiplier xi :=
      csInf_le hDepthBounded ⟨xi, hxi, rfl⟩
    have hNeg : -depth <= sInf (multiplier '' dangerous) := by
      simpa only [depth, neg_neg] using
        neg_le_neg (le_max_right 0 (-sInf (multiplier '' dangerous)))
    exact hNeg.trans hinf
  have hOutside (xi : ℝ) (hxi : xi ∈ dangerousᶜ) : a <= multiplier xi := by
    exact not_lt.mp hxi
  have hBandMultiplier :
      (-depth) * (∫ xi : ℝ in dangerous, energy xi) <=
        ∫ xi : ℝ in dangerous, multiplier xi * energy xi := by
    rw [← integral_const_mul]
    apply integral_mono_ae
    · exact (hEnergyIntegrable.const_mul (-depth)).integrableOn
    · exact hMultiplierIntegrable.integrableOn
    · filter_upwards [self_mem_ae_restrict hDangerousMeasurable'] with xi hxi
      exact mul_le_mul_of_nonneg_right (hInside xi hxi) (hEnergyNonnegative xi)
  have hOutsideMultiplier :
      a * (∫ xi : ℝ in dangerousᶜ, energy xi) <=
        ∫ xi : ℝ in dangerousᶜ, multiplier xi * energy xi := by
    rw [← integral_const_mul]
    apply integral_mono_ae
    · exact (hEnergyIntegrable.const_mul a).integrableOn
    · exact hMultiplierIntegrable.integrableOn
    · filter_upwards [self_mem_ae_restrict hDangerousMeasurable'.compl] with xi hxi
      exact mul_le_mul_of_nonneg_right (hOutside xi hxi) (hEnergyNonnegative xi)
  have hFactorPositive : 0 < factor := by
    unfold factor
    positivity
  have hBandMultiplier' :
      -depth * (factor * ∫ xi : ℝ in dangerous, energy xi) <=
        factor * ∫ xi : ℝ in dangerous, multiplier xi * energy xi := by
    nlinarith [mul_le_mul_of_nonneg_left hBandMultiplier hFactorPositive.le]
  have hOutsideMultiplier' :
      a * (factor * ∫ xi : ℝ in dangerousᶜ, energy xi) <=
        factor * ∫ xi : ℝ in dangerousᶜ, multiplier xi * energy xi := by
    nlinarith [mul_le_mul_of_nonneg_left hOutsideMultiplier hFactorPositive.le]
  have hEnergySplit :
      factor * (∫ xi : ℝ in dangerous, energy xi) +
          factor * (∫ xi : ℝ in dangerousᶜ, energy xi) = l2Mass f := by
    rw [← mul_add, integral_add_compl hDangerousMeasurable' hEnergyIntegrable]
    exact angular_plancherel f
  have hMultiplierSplit :
      factor * (∫ xi : ℝ in dangerous, multiplier xi * energy xi) +
          factor * (∫ xi : ℝ in dangerousᶜ, multiplier xi * energy xi) =
        factor * ∫ xi : ℝ, multiplier xi * energy xi := by
    rw [← mul_add, integral_add_compl hDangerousMeasurable' hMultiplierIntegrable]
  have hConcentrationF :
      factor * (∫ xi : ℝ in dangerous, energy xi) <= eta * l2Mass f := by
    simpa only [factor, energy, dangerous] using hConcentration f hfQ
  have hCoefficientNonnegative : 0 <= a + depth := add_nonneg ha.le hDepthNonnegative
  have hConcentrationScaled :
      (a + depth) * (factor * ∫ xi : ℝ in dangerous, energy xi) <=
        (a + depth) * (eta * l2Mass f) :=
    mul_le_mul_of_nonneg_left hConcentrationF hCoefficientNonnegative
  have hMultiplierLower :
      delta * l2Mass f <= factor * ∫ xi : ℝ, multiplier xi * energy xi := by
    rw [← hMultiplierSplit]
    unfold delta
    nlinarith [hBandMultiplier', hOutsideMultiplier', hEnergySplit,
      hConcentrationScaled]
  have hDenominatorPositive : 0 < a + depth := add_pos_of_pos_of_nonneg ha hDepthNonnegative
  have hDeltaPositive : 0 < delta := by
    have hScaledEta : (a + depth) * eta < a :=
      by
        have h := (lt_div_iff₀ hDenominatorPositive).mp
          (by simpa [depth] using hEta.2)
        simpa only [mul_comm] using h
    unfold delta
    linarith
  have hPole :
      (∫ x : ℝ, ((Real.cosh (x / 2) : ℝ) : ℂ) * f x) = 0 :=
    hPoleOrthogonal f hfQ
  have hFormula :=
    (fixed_scale_weil_quadratic_form Z f L hSupport hZero hArch).1
  have hComplexReal :
      ((∫ xi : ℝ, (multiplier xi : ℂ) * (energy xi : ℂ))).re =
        ∫ xi : ℝ, multiplier xi * energy xi :=
    complex_weighted_integral_re multiplier energy hMultiplierIntegrable
  have hZeroSide :
      (zeroSum Z (convolutionSquare f) hZero).re =
        factor * ∫ xi : ℝ, multiplier xi * energy xi := by
    rw [hFormula, hPole]
    simp only [Complex.normSq_zero, Complex.ofReal_zero, mul_zero, zero_add]
    change
      (((((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ xi : ℝ, (multiplier xi : ℂ) * (energy xi : ℂ)) : ℂ)).re = _
    rw [Complex.mul_re, hComplexReal]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rfl
  refine ⟨hDeltaPositive, ?_⟩
  rw [hZeroSide]
  exact hMultiplierLower

/-- A strictly positive complementary subspace bounds the negative inertia by
the dimension of the retained subspace. -/
theorem finite_negative_index_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (energy : H -> ℝ) (P Q : Submodule ℝ H) [FiniteDimensional ℝ P]
    (hCompl : IsCompl P Q) (delta : ℝ) (hDelta : 0 < delta)
    (hSafe : ∀ q, q ∈ Q -> delta * ‖q‖ ^ 2 <= energy q) :
    negativeIndex energy <= (Module.finrank ℝ P : WithTop ℕ) := by
  unfold negativeIndex
  apply csSup_le'
  rintro _ ⟨n, hn, rfl⟩
  rcases hn with ⟨T, hTInjective, hTNegative⟩
  let TP : (Fin n -> ℝ) →ₗ[ℝ] P := (P.projectionOnto Q hCompl).comp T
  have hTPInjective : Function.Injective TP := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    have hTxQ : T x ∈ Q := by
      apply (Submodule.projectionOnto_apply_eq_zero_iff hCompl).mp
      exact hx
    by_contra hx0
    have hNegative := hTNegative x hx0
    have hNonnegative : 0 <= energy (T x) :=
      (mul_nonneg hDelta.le (sq_nonneg ‖T x‖)).trans (hSafe (T x) hTxQ)
    exact (not_lt_of_ge hNonnegative) hNegative
  exact WithTop.coe_le_coe.2 (by
    simpa using LinearMap.finrank_le_finrank_of_injective hTPInjective)

end D5.S3.Weil.ZetaBridge.SafeComplementFiniteIndex
