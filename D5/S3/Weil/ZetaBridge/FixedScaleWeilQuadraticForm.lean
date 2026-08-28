/- GID: D5/S3/Weil/ZetaBridge/FixedScaleWeilQuadraticForm
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/FixedScaleWeilQuadraticForm
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Decompose the fixed-scale Weil quadratic form and identify its positivity test. -/

import D5.S3.Weil.WeilIdentity
import D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
import D5.S3.Weil.ZetaBridge.PoleRankOneDecomposition
import D5.S3.Weil.ZetaCore.ExplicitFormulaBridge

namespace D5.S3.Weil.ZetaBridge.FixedScaleWeilQuadraticForm

open Filter MeasureTheory Set
open D5.S3.Weil.Convention
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.PrimePoleTerms
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.WeilIdentity
open D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
open D5.S3.Weil.ZetaBridge.PoleRankOneDecomposition
open scoped ArithmeticFunction ComplexConjugate FourierTransform

noncomputable section

/-- The completed fixed-scale multiplier, constructed from the canonical
Archimedean and finite prime-power multipliers. -/
def fixedScaleMultiplier (L xi : ℝ) : ℝ :=
  2 * Real.pi * (Zeta23.mu xi + Zeta23.PX (Real.exp (2 * L)) xi)

private theorem convolutionSquare_eq_weilTest (f : WeilTestFunction) :
    ((convolutionSquare f : WeilTestFunction) : ℝ → ℂ) =
      Zeta23.EF.weilTest (f : ℝ → ℂ) (f : ℝ → ℂ) := by
  rfl

private theorem boundary_readout_eq_cosh (f : WeilTestFunction) :
    (∫ x : ℝ, Complex.exp ((x : ℂ) / 2) * f x) =
      ∫ x : ℝ, ((Real.cosh (x / 2) : ℝ) : ℂ) * f x := by
  have hPlus : Integrable (fun x : ℝ => Complex.exp ((x : ℂ) / 2) * f x) :=
    ((by fun_prop : Continuous fun x : ℝ => Complex.exp ((x : ℂ) / 2)).mul
      f.continuous).integrable_of_hasCompactSupport f.hasCompactSupport.mul_left
  have hMinus : Integrable (fun x : ℝ => Complex.exp (-(x : ℂ) / 2) * f x) :=
    ((by fun_prop : Continuous fun x : ℝ => Complex.exp (-(x : ℂ) / 2)).mul
      f.continuous).integrable_of_hasCompactSupport f.hasCompactSupport.mul_left
  have hReflect :
      (∫ x : ℝ, Complex.exp (-(x : ℂ) / 2) * f x) =
        ∫ x : ℝ, Complex.exp ((x : ℂ) / 2) * f x := by
    rw [← MeasureTheory.integral_neg_eq_self
      (fun x : ℝ => Complex.exp ((x : ℂ) / 2) * f x) volume]
    apply integral_congr_ae
    filter_upwards with x
    rw [f.even]
    push_cast
    congr 2
  rw [show (fun x : ℝ => ((Real.cosh (x / 2) : ℝ) : ℂ) * f x) =
      fun x : ℝ => (1 / 2 : ℂ) *
        (Complex.exp ((x : ℂ) / 2) * f x +
          Complex.exp (-(x : ℂ) / 2) * f x) by
    funext x
    rw [Real.cosh_eq]
    push_cast
    ring]
  rw [integral_const_mul, integral_add hPlus hMinus, hReflect]
  ring

private theorem fixed_scale_weil_formula
    (Z : ZeroData) (f : WeilTestFunction) (L : ℝ)
    (hSupport : tsupport (f : ℝ → ℂ) ⊆ Icc (-L) L)
    (hZero : SymmetricConvergent Z (convolutionSquare f))
    (hArch : ArchimedeanConvergent (convolutionSquare f)) :
    zeroSum Z (convolutionSquare f) hZero =
      2 * (Complex.normSq
        (∫ x : ℝ, ((Real.cosh (x / 2) : ℝ) : ℂ) * f x) : ℂ) +
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ xi : ℝ, (fixedScaleMultiplier L xi : ℂ) *
          (Complex.normSq (fourierLaplace f xi) : ℂ)) := by
  let k : WeilTestFunction := convolutionSquare f
  have hkSupport : tsupport (k : ℝ → ℂ) ⊆ Icc (-(2 * L)) (2 * L) := by
    have h := Zeta23.EF.tsupport_weilTest_subset
      (L := 2 * L) (f := (f : ℝ → ℂ)) (g := (f : ℝ → ℂ))
      (by simpa only [show -(2 * L) / 2 = -L by ring,
          show 2 * L / 2 = L by ring] using hSupport)
      (by simpa only [show -(2 * L) / 2 = -L by ring,
          show 2 * L / 2 = L by ring] using hSupport)
    simpa only [k, convolutionSquare_eq_weilTest] using h
  have hkFourier : Integrable (𝓕 (k : ℝ → ℂ)) :=
    Zeta23.EF.integrable_fourier_of_contDiff_two
      (k.contDiff.of_le (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr le_top))
      k.hasCompactSupport
  have hPrimeRaw := Zeta23.EF.prime_term k.continuous hkSupport hkFourier
  have hPrimeSeries :
      (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n))) = primeTerm k := by
    unfold primeTerm primeSummand
    apply tsum_congr
    intro n
    rw [vonMangoldt_div_sqrt]
    push_cast
    ring
  have hPrime :
      -primeTerm k =
        ∫ xi : ℝ, (Complex.normSq (fourierLaplace f xi) : ℂ) *
          (Zeta23.PX (Real.exp (2 * L)) xi : ℂ) := by
    rw [hPrimeSeries] at hPrimeRaw
    rw [hPrimeRaw]
    apply integral_congr_ae
    filter_upwards with xi
    rw [paperFT_eq_fourierLaplace]
    rw [show k = convolutionSquare f by rfl,
      fourierLaplace_convolutionSquare_real]
  have hMuIntegrable : Integrable
      (fun xi : ℝ => Zeta23.paperFT (k : ℝ → ℂ) xi * (Zeta23.mu xi : ℂ)) := by
    have hScaled := hArch.const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ))
    refine hScaled.congr ?_
    filter_upwards with xi
    rw [paperFT_eq_fourierLaplace]
    unfold archimedeanIntegrand Zeta23.mu
    push_cast
    ring
  have hArchEq : archimedeanTerm k hArch =
      ∫ xi : ℝ, (Complex.normSq (fourierLaplace f xi) : ℂ) * (Zeta23.mu xi : ℂ) := by
    have hGamma := Zeta23.EF.gamma_term (k : ℝ → ℂ)
    rw [show archimedeanTerm k hArch =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ xi : ℝ, Zeta23.paperFT (k : ℝ → ℂ) xi *
            (Zeta23.EF.gammaBracket xi : ℂ) by
      unfold archimedeanTerm archimedeanIntegrand Zeta23.EF.gammaBracket
      congr 1
      apply integral_congr_ae
      filter_upwards with xi
      rw [paperFT_eq_fourierLaplace]
      ring]
    have hCoeff : (((1 / (2 * Real.pi) : ℝ) : ℂ)) =
        (1 / (2 * (Real.pi : ℂ)) : ℂ) := by
      push_cast
      rfl
    rw [hCoeff, hGamma]
    apply integral_congr_ae
    filter_upwards with xi
    rw [paperFT_eq_fourierLaplace]
    rw [show k = convolutionSquare f by rfl,
      fourierLaplace_convolutionSquare_real]
  have hPrimeIntegrable : Integrable
      (fun xi : ℝ => (Complex.normSq (fourierLaplace f xi) : ℂ) *
        (Zeta23.PX (Real.exp (2 * L)) xi : ℂ)) := by
    have h := Zeta23.EF.integrable_paperFT_mul_PX (k := (k : ℝ → ℂ)) (2 * L) hkFourier
    refine h.congr ?_
    filter_upwards with xi
    rw [paperFT_eq_fourierLaplace]
    rw [show k = convolutionSquare f by rfl,
      fourierLaplace_convolutionSquare_real]
  have hMuIntegrable' : Integrable
      (fun xi : ℝ => (Complex.normSq (fourierLaplace f xi) : ℂ) *
        (Zeta23.mu xi : ℂ)) := by
    refine hMuIntegrable.congr ?_
    filter_upwards with xi
    rw [paperFT_eq_fourierLaplace]
    rw [show k = convolutionSquare f by rfl,
      fourierLaplace_convolutionSquare_real]
  have hPole : poleTerm k =
      2 * (Complex.normSq
        (∫ x : ℝ, ((Real.cosh (x / 2) : ℝ) : ℂ) * f x) : ℂ) := by
    rw [← boundary_readout_eq_cosh]
    simpa only [k] using pole_rank_one_decomposition f
  rw [D5.S3.Weil.WeilIdentity.weil_explicit_formula Z k hZero hArch]
  rw [hPole, sub_eq_add_neg, hPrime, hArchEq]
  conv_lhs =>
    rw [add_assoc, ← integral_add hPrimeIntegrable hMuIntegrable']
  rw [← integral_const_mul]
  apply congrArg (fun z : ℂ =>
    2 * (Complex.normSq
      (∫ x : ℝ, ((Real.cosh (x / 2) : ℝ) : ℂ) * f x) : ℂ) + z)
  apply integral_congr_ae
  filter_upwards with xi
  unfold fixedScaleMultiplier
  push_cast
  field_simp [Real.pi_ne_zero]
  all_goals ring

/-- The frozen explicit formula is the fixed-scale rank-one pole energy plus the completed
Fourier multiplier form; consequently their real-part nonnegativity tests are equivalent. -/
theorem fixed_scale_weil_quadratic_form
    (Z : ZeroData) (f : WeilTestFunction) (L : ℝ)
    (hSupport : tsupport (f : ℝ → ℂ) ⊆ Icc (-L) L)
    (hZero : SymmetricConvergent Z (convolutionSquare f))
    (hArch : ArchimedeanConvergent (convolutionSquare f)) :
    (zeroSum Z (convolutionSquare f) hZero =
      2 * (Complex.normSq
        (∫ x : ℝ, ((Real.cosh (x / 2) : ℝ) : ℂ) * f x) : ℂ) +
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ xi : ℝ, (fixedScaleMultiplier L xi : ℂ) *
          (Complex.normSq (fourierLaplace f xi) : ℂ))) ∧
    (0 ≤ (zeroSum Z (convolutionSquare f) hZero).re ↔
      0 ≤ (2 * (Complex.normSq
        (∫ x : ℝ, ((Real.cosh (x / 2) : ℝ) : ℂ) * f x) : ℂ) +
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ xi : ℝ, (fixedScaleMultiplier L xi : ℂ) *
          (Complex.normSq (fourierLaplace f xi) : ℂ))).re) := by
  have hFormula := fixed_scale_weil_formula Z f L hSupport hZero hArch
  exact ⟨hFormula, by rw [hFormula]⟩

#print axioms fixed_scale_weil_quadratic_form

end

end D5.S3.Weil.ZetaBridge.FixedScaleWeilQuadraticForm
