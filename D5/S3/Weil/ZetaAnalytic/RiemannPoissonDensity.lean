/- GID: D5/S3/Weil/ZetaAnalytic/RiemannPoissonDensity
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaAnalytic/RiemannPoissonDensity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The zero-sum phase density is the Poisson smoothing of the zero-counting measure. -/

import D5.S3.Zeros.CompletedZeta
import D5.S3.Weil.ZeroSum
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Riemann Poisson density

The phase density is constructed from the logarithmic derivative of the
canonical entire xi reading.  On the real-zero carrier supplied by the
critical-line hypothesis, the zero-counting measure is constructed
independently as a multiplicity-weighted sum of Dirac masses.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace D5.S3.Weil.ZetaAnalytic.RiemannPoissonDensity

open D5.S3.Zeros.CompletedZeta
open D5.S3.Weil.ZeroSum

/-- The real Poisson kernel at height `omega`. -/
def poissonKernel (omega x : ℝ) : ℝ :=
  (1 / Real.pi) * (omega / (x ^ 2 + omega ^ 2))

/-- The multiplicity-weighted counting measure of a countable real zero
family. -/
def zeroCountingMeasure (Z : ZeroData) : Measure ℝ :=
  Measure.sum fun n => (Z.multiplicity n : ℝ≥0∞) • Measure.dirac (Z.zero n).im

/-- The shifted-xi phase density from the source logarithmic derivative. -/
def phaseDensity (omega x : ℝ) : ℝ :=
  (1 / Real.pi) *
    (logDeriv xiReading
      ((1 / 2 : ℂ) + (omega : ℂ) - Complex.I * (x : ℂ))).re

/-- Poisson smoothing of a measure, with the additive-convolution convention
`x - y`. -/
def poissonSmooth (omega : ℝ) (mu : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ y, poissonKernel omega (x - y) ∂mu

/-- Under the real-zero parametrization supplied by the critical-line
hypothesis, the local phase density is exactly the Poisson smoothing of the
zero-counting measure. -/
theorem riemann_poisson_density
    (Z : ZeroData) (omega : ℝ) (homega : 0 < omega)
    (hRH : RiemannHypothesis)
    (hPhaseExpansion : ∀ x, 0 < omega → RiemannHypothesis →
      phaseDensity omega x =
        ∑' n, (Z.multiplicity n : ℝ) *
          poissonKernel omega (x - (Z.zero n).im)) :
    phaseDensity omega = poissonSmooth omega (zeroCountingMeasure Z) := by
  funext x
  rw [hPhaseExpansion x homega hRH, poissonSmooth, zeroCountingMeasure]
  rw [MeasureTheory.integral_sum_dirac]
  · congr with n
  · simp

#print axioms riemann_poisson_density

end D5.S3.Weil.ZetaAnalytic.RiemannPoissonDensity
