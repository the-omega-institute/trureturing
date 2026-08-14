/- GID: D5/S3/Analytic/Dilation/MellinDilationFlow
   generality: G
   mirror-B: D5/B/S3/Analytic/Dilation/MellinDilationFlow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Mellin is Fourier in logarithmic time along the dilation flow. -/

import Mathlib.Analysis.MellinInversion

open Real Complex MeasureTheory
open scoped FourierTransform

namespace D5.S3.Analytic.Dilation.MellinDilationFlow

/-- After the logarithmic change of variables `x = exp t`, the Mellin
transform has real weight `exp (s.re * t)` and Fourier phase
`exp (i * s.im * t)` along the dilation flow. Mathlib's Bochner integrals are
totalized, so this change-of-variables identity needs no convergence
hypothesis; `MellinConvergent` records when the transform is integrable. -/
theorem mellin_eq_fourier_on_dilation_flow (f : ℝ → ℂ) (s : ℂ) :
    mellin f s =
      ∫ t : ℝ,
        Complex.exp (((s.im * t : ℝ) : ℂ) * Complex.I) •
          (Real.exp (s.re * t) • f (Real.exp t)) := by
  rw [mellin_eq_fourier]
  let g : ℝ → ℂ := fun t ↦ Real.exp (s.re * t) • f (Real.exp t)
  have hreflect :
      (fun u : ℝ ↦ Real.exp (-s.re * u) • f (Real.exp (-u))) =
        fun u ↦ g (-u) := by
    funext u
    simp [g]
  rw [hreflect, ← congrFun (fourierInv_eq_fourier_comp_neg g) (s.im / (2 * Real.pi)),
    fourierInv_eq']
  simp only [g]
  congr 1
  funext t
  congr 1
  congr 1
  simp only [Real.inner_apply]
  norm_cast
  field_simp

/-- The compact nonzero window makes the Mellin convergence predicate
inhabited at `s = 1`. -/
example :
    MellinConvergent
      (Set.indicator (Set.Icc (1 : ℝ) 2) (fun _ ↦ (1 : ℂ))) 1 := by
  rw [MellinConvergent]
  simp only [sub_self, Complex.cpow_zero, one_smul]
  exact
    ((integrableOn_const
      (C := (1 : ℂ)) measure_Icc_lt_top.ne).integrable_indicator
        measurableSet_Icc).integrableOn

/-- The transformed compact-window integrand is genuinely nonzero at
logarithmic time zero. -/
example :
    let f := Set.indicator (Set.Icc (1 : ℝ) 2) (fun _ ↦ (1 : ℂ))
    Complex.exp (((((1 : ℂ).im * 0 : ℝ) : ℂ) * Complex.I)) •
        (Real.exp ((1 : ℂ).re * 0) • f (Real.exp 0)) = 1 := by
  simp

end D5.S3.Analytic.Dilation.MellinDilationFlow
