/- GID: D5/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper
   generality: G
   mirror-B: D5/B/S3/Analytic/OptimalRecovery/PointwiseMinimaxUpper
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pointwise deterministic recovery of the ground energy of finite atomic laws. -/

import D5.S3.Analytic.Interpolation.UniformCoefficientBudget
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open Set Finset MeasureTheory
open D5.S3.Analytic.Interpolation.UniformCoefficientBudget
namespace D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper

/-- Finite Borel probability laws; only the ground atom has a prescribed mass. -/
def AtomicLaw (Elo Ehi η : ℝ) (d : ℕ) (μ : Measure ℝ) (g : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ ENNReal.ofReal η ≤ μ {g} ∧
    ∃ s : Finset ℝ, s.card ≤ d ∧ g ∈ s ∧
      (∀ x ∈ s, x ∈ Icc Elo Ehi ∧ g ≤ x) ∧ μ ((s : Set ℝ)ᶜ) = 0

/-- The original measure-valued Laplace observation. -/
def measureCurve (μ : Measure ℝ) (t : ℝ) : ℝ := ∫ x, Real.exp (-t * x) ∂μ

/-- The all-time dimension--precision rate. -/
def rateAll (d : ℕ) (ε : ℝ) : ℝ :=
  sSup ((fun m : ℕ => Real.rpow ε (((2 * m - 1 : ℕ) : ℝ)⁻¹) / (m : ℝ)^2) ''
    (Icc 1 d : Set ℕ))

/-- The finite-window rate, including saturation at the geometric bound. -/
def rateWindow (d : ℕ) (ε U : ℝ) : ℝ :=
  sSup ((fun m : ℕ => min (1 : ℝ)
    (Real.rpow ε (((2 * m - 1 : ℕ) : ℝ)⁻¹) * max 1 (((2 * m - 1 : ℕ) : ℝ) / U)) /
      (m : ℝ)^2) '' (Icc 1 d : Set ℕ))

/-- Complete-lattice minimax risk; observations are arbitrary pointwise functions. -/
def minimaxRisk (Elo Ehi η : ℝ) (d : ℕ) (D : Set ℝ) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ G : (D → ℝ) → ℝ, ⨆ μ : Measure ℝ, ⨆ g : ℝ,
    ⨆ (_ : AtomicLaw Elo Ehi η d μ g), ⨆ Y : D → ℝ,
      ⨆ (_ : ∀ t : D, |Y t - measureCurve μ t| ≤ ε), ENNReal.ofReal |G Y - g|

end D5.S3.Analytic.OptimalRecovery.PointwiseMinimaxUpper
