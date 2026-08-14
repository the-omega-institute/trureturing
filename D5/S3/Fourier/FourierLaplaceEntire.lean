/- GID: D5/S3/Fourier/FourierLaplaceEntire
   generality: I
   mirror-B: none(waiver:formal-analysis-foundation-only)
   mirror-E: none(waiver:formal-analysis-foundation-without-numerical-dependency)
   anchors: []
   digest: Extend the concrete Fourier-Laplace transform to an entire function via Paley-Wiener. -/

import D5.S3.Weil.FourierLaplace
import D5.S3.Fourier.PaleyWiener

namespace D5.S3.Weil.FourierLaplace

open MeasureTheory
open D5.S3.Weil.TestFunctions
open D5.S3.Fourier

/-
D5-T0018-C (discharged): the transform is concrete, and its entire-extension
proof is now native in `D5/S3/Fourier/PaleyWiener`, no longer a classical
tail carried by AxiomDebt.lean.
-/

/-- A smooth compactly supported Weil test has an entire Fourier-Laplace transform. -/
theorem fourierLaplace_entire (g : WeilTestFunction) :
    Differentiable ℂ (fourierLaplace g) := by
  change Differentiable ℂ fun z : ℂ =>
    ∫ x : ℝ, Complex.exp (-Complex.I * z * (x : ℂ)) * g x
  exact PaleyWiener.fourier_laplace_entire_classic (g : ℝ → ℂ)
    g.contDiff g.hasCompactSupport

end D5.S3.Weil.FourierLaplace
