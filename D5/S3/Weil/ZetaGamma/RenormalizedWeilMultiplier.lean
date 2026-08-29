/- GID: D5/S3/Weil/ZetaGamma/RenormalizedWeilMultiplier
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/RenormalizedWeilMultiplier
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Express the fixed-support Weil form through the shifted discrepancy multiplier. -/

import D5.S3.Weil.ZetaBridge.FixedScaleWeilQuadraticForm
import D5.S3.Weil.ZetaGamma.PoleContinuumCompletion

/-!
# Renormalized Weil multiplier

Library-search audit trail (2026-08-29):

* Searches for a renormalized Weil multiplier, prime-discrepancy transform,
  and the body shapes `PX (Real.exp (2 * L))`, `EL (2 * L)`, and the shifted
  digamma found no exact frozen owner.
* The construction uses the canonical `Zeta23.PX` atomic prime multiplier and
  `Zeta23.EF.EL` continuous reference weight rather than redeclaring either.
* `literatureRHS_eq_integral_nu`, `paperFT_eq_fourierLaplace`,
  `fourierLaplace_convolutionSquare_real`, and
  `archimedean_shift_completion` supply the exact existing analytic steps.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaGamma.RenormalizedWeilMultiplier

open MeasureTheory Set
open D5.S3.Weil.FourierLaplace
open D5.S3.Weil.PrimePoleTerms
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.TestFunctions.ConvolutionSquarePositivity
open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula
open D5.S3.Weil.ZetaGamma.PoleContinuumCompletion
open scoped ComplexConjugate FourierTransform

noncomputable section

/-- On a positive support scale, the classical zero-side Weil form is the
single multiplier form obtained by subtracting the finite prime-continuum
discrepancy transform from the shifted Archimedean baseline. -/
theorem renormalized_weil_multiplier
    (Z : ZeroData) (f : WeilTestFunction) (L : ℝ)
    (hL : 0 < L)
    (hSupport : tsupport (f : ℝ → ℂ) ⊆ Icc (-L) L)
    (hZero : SymmetricConvergent Z (convolutionSquare f))
    (hArch : ArchimedeanConvergent (convolutionSquare f)) :
    let bInf : ℝ → ℝ := fun xi =>
      (Complex.digamma ((1 / 4 : ℂ) + Complex.I * (xi : ℂ) / 2)).re -
          Real.log Real.pi +
        1 / (xi ^ 2 + 1 / 4)
    let rL : ℝ → ℝ := fun xi =>
      -2 * Real.pi * Zeta23.PX (Real.exp (2 * L)) xi -
        (∫ u : ℝ, Zeta23.EF.EL (2 * L) u *
          Complex.exp (-Complex.I * (xi : ℂ) * (u : ℂ))).re
    zeroSum Z (convolutionSquare f) hZero =
      (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        ∫ xi : ℝ, ((bInf xi - rL xi : ℝ) : ℂ) *
          (Complex.normSq (fourierLaplace f xi) : ℂ) := by
  dsimp only
  let k : WeilTestFunction := convolutionSquare f
  have hkSupport : tsupport (k : ℝ → ℂ) ⊆ Icc (-(2 * L)) (2 * L) := by
    have h := Zeta23.EF.tsupport_weilTest_subset
      (L := 2 * L) (f := (f : ℝ → ℂ)) (g := (f : ℝ → ℂ))
      (by simpa only [show -(2 * L) / 2 = -L by ring,
          show 2 * L / 2 = L by ring] using hSupport)
      (by simpa only [show -(2 * L) / 2 = -L by ring,
          show 2 * L / 2 = L by ring] using hSupport)
    change tsupport (Zeta23.EF.weilTest (f : ℝ → ℂ) (f : ℝ → ℂ)) ⊆
      Icc (-(2 * L)) (2 * L)
    exact h
  have hkFourier : Integrable (𝓕 (k : ℝ → ℂ)) :=
    Zeta23.EF.integrable_fourier_of_contDiff_two
      (k.contDiff.of_le (show (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr le_top))
      k.hasCompactSupport
  have hMu : Integrable
      (fun xi : ℝ => Zeta23.paperFT (k : ℝ → ℂ) xi * (Zeta23.mu xi : ℂ)) := by
    have hScaled := hArch.const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ))
    refine hScaled.congr ?_
    filter_upwards with xi
    rw [paperFT_eq_fourierLaplace]
    unfold archimedeanIntegrand Zeta23.mu
    push_cast
    ring
  have hZeroNu :
      zeroSum Z (convolutionSquare f) hZero =
        ∫ xi : ℝ, Zeta23.paperFT (k : ℝ → ℂ) xi *
          (Zeta23.nuX (Real.exp (2 * L)) xi : ℂ) := by
    rw [weil_explicit_formula Z (convolutionSquare f) hZero hArch,
      ← literatureRHS_eq (convolutionSquare f) hArch]
    exact Zeta23.EF.literatureRHS_eq_integral_nu
      (L := 2 * L) (by linarith) k.continuous hkSupport hkFourier hMu
  have hMultiplier (xi : ℝ) :
      Zeta23.nuX (Real.exp (2 * L)) xi =
        (1 / (2 * Real.pi)) *
          ((Complex.digamma ((1 / 4 : ℂ) + Complex.I * (xi : ℂ) / 2)).re -
            Real.log Real.pi + 1 / (xi ^ 2 + 1 / 4) -
            (-2 * Real.pi * Zeta23.PX (Real.exp (2 * L)) xi -
              (∫ u : ℝ, Zeta23.EF.EL (2 * L) u *
                Complex.exp (-Complex.I * (xi : ℂ) * (u : ℂ))).re)) := by
    have hEL := Zeta23.EF.integral_EL_mul xi (L := 2 * L) (by linarith)
    have hELRe := congrArg Complex.re hEL
    unfold Zeta23.nuX Zeta23.mu Zeta23.PiX
    dsimp only
    simp only [Complex.ofReal_re] at hELRe
    rw [hELRe]
    field_simp [Real.pi_ne_zero]
    ring
  rw [hZeroNu, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with xi
  rw [paperFT_eq_fourierLaplace, show k = convolutionSquare f by rfl,
    fourierLaplace_convolutionSquare_real, hMultiplier]
  push_cast
  ring

#print axioms renormalized_weil_multiplier

end

end D5.S3.Weil.ZetaGamma.RenormalizedWeilMultiplier
