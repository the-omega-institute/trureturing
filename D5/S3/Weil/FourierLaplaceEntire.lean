/- GID: D5/S3/Weil/FourierLaplaceEntire
   generality: I
   mirror-B: none(waiver:formal-analysis-foundation-only)
   mirror-E: none(waiver:classical-analysis-tail-without-numerical-dependency)
   anchors: [PZG-v170-26.4, paleywiener1934fourier]
   digest: Extend the concrete Fourier-Laplace transform to an entire function via Paley-Wiener. -/

import D5.S3.Weil.FourierLaplace
import D5.X_Assumptions.AxiomDebt

namespace D5.S3.Weil.FourierLaplace

open MeasureTheory
open D5.S3.Weil.TestFunctions
open D5.X_Assumptions

/-
TAIL D5-T0018-C: the transform is concrete, while its entire-extension proof
is the single registered classical-analysis debt in AxiomDebt.lean.
-/

/-- A smooth compactly supported Weil test has an entire Fourier-Laplace transform. -/
theorem fourierLaplace_entire (g : WeilTestFunction) :
    Differentiable ℂ (fourierLaplace g) := by
  change Differentiable ℂ fun z : ℂ =>
    ∫ x : ℝ, Complex.exp (-Complex.I * z * (x : ℂ)) * g x
  exact AxiomDebt.fourier_laplace_entire_classic (g : ℝ → ℂ)
    g.contDiff g.hasCompactSupport

end D5.S3.Weil.FourierLaplace
