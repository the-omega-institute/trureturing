/- GID: D5/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Defs
   generality: G
   mirror-B: D5/B/S3/Analytic/MixedNorm/DmitrovicPointEvaluation/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Measure.Lebesgue.Basic, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.NNReal, mathlib/module/Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv]
   utility: none
   digest: Circle means, mixed norms, and the constant-one point-evaluation conjecture. -/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! The source definitions of the mixed norm and point evaluation. -/

open MeasureTheory
open scoped ENNReal

namespace D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Defs

/-- Integral mean of order p on the circle of radius r (p = ∞: angular supremum). -/
noncomputable def circleMean (p : ℝ≥0∞) (f : ℂ → ℂ) (r : ℝ) : ℝ≥0∞ :=
  if p = ∞ then ⨆ θ : ℝ, (‖f (r * Complex.exp (θ * Complex.I))‖₊ : ℝ≥0∞)
  else ((∫⁻ θ in Set.Ioc (0 : ℝ) (2 * Real.pi),
          (‖f (r * Complex.exp (θ * Complex.I))‖₊ : ℝ≥0∞) ^ p.toReal) /
        ENNReal.ofReal (2 * Real.pi)) ^ (1 / p.toReal)

/-- The mixed norm ‖f‖_{p,q,α} of Dmitrović (and Flett). -/
noncomputable def mixedNorm (p q : ℝ≥0∞) (α : ℝ) (f : ℂ → ℂ) : ℝ≥0∞ :=
  if q = ∞ then ⨆ r ∈ Set.Ioo (0 : ℝ) 1,
    ENNReal.ofReal ((1 - r ^ 2) ^ α) * circleMean p f r
  else (ENNReal.ofReal (2 * α * q.toReal) *
        ∫⁻ r in Set.Ioo (0 : ℝ) 1,
          ENNReal.ofReal (r * (1 - r ^ 2) ^ (α * q.toReal - 1)) *
            circleMean p f r ^ q.toReal) ^ (1 / q.toReal)

/-- Dmitrović's conjecture (Oper. Matrices 18 (2024), p. 705), in multiplied-out form;
for p = ∞, `1 / p.toReal = 0`. -/
def claim : Prop :=
  ∀ (p q : ℝ≥0∞) (α : ℝ), 0 < p → 0 < q → 0 < α →
    ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball 0 1) → mixedNorm p q α f < ∞ →
    ∀ z : ℂ, ‖z‖ < 1 →
      ENNReal.ofReal ‖f z‖ * ENNReal.ofReal ((1 - ‖z‖ ^ 2) ^ (α + 1 / p.toReal)) ≤
        mixedNorm p q α f

end D5.S3.Analytic.MixedNorm.DmitrovicPointEvaluation.Defs
