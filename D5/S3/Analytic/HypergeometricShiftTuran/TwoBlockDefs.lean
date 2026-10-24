/- GID: D5/S3/Analytic/HypergeometricShiftTuran/TwoBlockDefs
   generality: G
   mirror-B: D5/B/S3/Analytic/HypergeometricShiftTuran/TwoBlockDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.Pochhammer]
   utility: none
   digest: Two parameter blocks and the coefficient assertion of the second hypergeometric conjecture. -/

import D5.S3.Analytic.HypergeometricShiftTuran.Defs
import Mathlib.RingTheory.Polynomial.Pochhammer

noncomputable section
open scoped BigOperators

namespace D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockDefs

/-- The ratio of rising factorial products for the unshifted parameter block. -/
def pochRatio {p₁ q₁ : ℕ} (a₁ : Fin p₁ → ℝ) (b₁ : Fin q₁ → ℝ) (n : ℕ) : ℝ :=
  (∏ i, (ascPochhammer ℝ n).eval (a₁ i)) /
    ∏ j, (ascPochhammer ℝ n).eval (b₁ j)

/-- The degree `n` Taylor coefficient in equation (3), including its factorial. -/
def seriesCoeff {p₁ q₁ p₂ q₂ : ℕ}
    (a₁ : Fin p₁ → ℝ) (b₁ : Fin q₁ → ℝ)
    (a₂ : Fin p₂ → ℝ) (b₂ : Fin q₂ → ℝ) (μ : ℝ) (n : ℕ) : ℝ :=
  pochRatio a₁ b₁ n * Defs.coeff a₂ b₂ (μ + n) / (n.factorial : ℝ)

/-- The finite Cauchy coefficient of the generalized Turanian for two blocks. -/
def twoBlockTuranCoeff {p₁ q₁ p₂ q₂ : ℕ}
    (a₁ : Fin p₁ → ℝ) (b₁ : Fin q₁ → ℝ)
    (a₂ : Fin p₂ → ℝ) (b₂ : Fin q₂ → ℝ) (μ α β : ℝ) (m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    (seriesCoeff a₁ b₁ a₂ b₂ (μ + α) k *
        seriesCoeff a₁ b₁ a₂ b₂ (μ + β) (m - k) -
      seriesCoeff a₁ b₁ a₂ b₂ μ k *
        seriesCoeff a₁ b₁ a₂ b₂ (μ + α + β) (m - k))

/-- The coefficient clause of Conjecture 2, with a nonempty shifted numerator. -/
def claim : Prop :=
  ∀ (p₁ q₁ p₂ q₂ : ℕ)
    (a₁ : Fin p₁ → ℝ) (b₁ : Fin q₁ → ℝ)
    (a₂ : Fin p₂ → ℝ) (b₂ : Fin q₂ → ℝ),
    p₁ ≤ q₁ → 1 ≤ p₂ → p₂ ≤ q₂ →
      (∀ i, 0 < a₁ i) → (∀ j, 0 < b₁ j) →
      (∀ i, 0 < a₂ i) → (∀ j, 0 < b₂ j) →
      Defs.cond13 a₁ b₁ → Defs.cond13 a₂ b₂ →
      ∀ μ α β : ℝ, 1 ≤ μ → 0 ≤ α → 0 ≤ β →
        ∀ m : ℕ, 0 ≤ twoBlockTuranCoeff a₁ b₁ a₂ b₂ μ α β m

end D5.S3.Analytic.HypergeometricShiftTuran.TwoBlockDefs
