/- GID: D5/S3/Analytic/HypergeometricShiftTuran/Defs
   generality: G
   mirror-B: D5/B/S3/Analytic/HypergeometricShiftTuran/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.Basic, mathlib/module/Mathlib.RingTheory.MvPolynomial.Symmetric.Defs]
   utility: none
   digest: Gamma product ratios, their shifted Turanian coefficients, and the coefficient nonnegativity assertion. -/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

noncomputable section
open scoped BigOperators

namespace D5.S3.Analytic.HypergeometricShiftTuran.Defs

/-- The Gamma product ratio, with empty parameter products equal to one. -/
def coeff {p q : ℕ} (a : Fin p → ℝ) (b : Fin q → ℝ) (t : ℝ) : ℝ :=
  (∏ i, Real.Gamma (a i + t)) / ∏ j, Real.Gamma (b j + t)

/-- The coefficient of degree `m` in the shifted Turanian, including factorial weights. -/
def turanCoeff {p q : ℕ} (a : Fin p → ℝ) (b : Fin q → ℝ)
    (μ α β : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    (coeff a b (μ + α + k) * coeff a b (μ + β + ((m - k : ℕ) : ℝ)) -
      coeff a b (μ + k) * coeff a b (μ + α + β + ((m - k : ℕ) : ℝ))) /
      ((k.factorial : ℝ) * ((m - k).factorial : ℝ))

/-- The elementary symmetric function of the entries, retaining multiplicities. -/
def esymm {p : ℕ} (a : Fin p → ℝ) (k : ℕ) : ℝ :=
  ((Finset.univ : Finset (Fin p)).val.map a).esymm k

/-- Consecutive inequalities in the elementary symmetric ratio chain. -/
def cond13 {p q : ℕ} (a : Fin p → ℝ) (b : Fin q → ℝ) : Prop :=
  ∀ j : ℕ, j < p →
    esymm b (q - j) / esymm a (p - j) ≤
      esymm b (q - j - 1) / esymm a (p - j - 1)

/-- The coefficient assertion for the branch with no more numerator parameters
than denominator parameters. -/
def claim : Prop :=
  ∀ (p q : ℕ) (a : Fin p → ℝ) (b : Fin q → ℝ),
    p ≤ q → (∀ i, 0 < a i) → (∀ j, 0 < b j) → cond13 a b →
      ∀ μ α β : ℝ, 1 ≤ μ → 0 ≤ α → 0 ≤ β → α ≤ β + 1 →
        ∀ m : ℕ, 0 ≤ turanCoeff a b μ α β m

end D5.S3.Analytic.HypergeometricShiftTuran.Defs
