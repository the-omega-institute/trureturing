/- GID: D5/S3/Analytic/MeijerZeroCount/Defs
   generality: G
   mirror-B: D5/B/S3/Analytic/MeijerZeroCount/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.MellinInversion, mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.Basic, mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: Gamma quotients, inverse Mellin transforms, and the zero-count conjecture. -/

import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Set.Card

namespace D5.S3.Analytic.MeijerZeroCount.Defs

/-- The Gamma quotient Π Γ(aᵢ+s)/Π Γ(bᵢ+s). -/
noncomputable def gammaQuot {p : ℕ} (a b : Fin p → ℝ) (s : ℂ) : ℂ :=
  (∏ i, Complex.Gamma (a i + s)) / ∏ i, Complex.Gamma (b i + s)

/-- Meijer's G as the inverse Mellin transform along Re s = 1, with normalization
1/(2π) times the real integral. On the stated parameter range this is the
vertical contour integral to the right of the numerator poles. -/
noncomputable def meijerG {p : ℕ} (a b : Fin p → ℝ) (x : ℝ) : ℂ :=
  mellinInv 1 (gammaQuot a b) x

/-- The control function v(t) = Σ (t^{aₖ} − t^{bₖ}). -/
noncomputable def control {p : ℕ} (a b : Fin p → ℝ) (t : ℝ) : ℝ :=
  ∑ k, (t ^ (a k) - t ^ (b k))

/-- Conjecture 1 restricted to ψ > 1. Infinite zero sets have cardinality ⊤. -/
def claim : Prop :=
  ∀ (p : ℕ) (a b : Fin p → ℝ), (∀ i, 0 ≤ a i) → 1 < ∑ i, (b i - a i) →
    {x : ℝ | x ∈ Set.Ioo 0 1 ∧ meijerG a b x = 0}.encard ≤
      {t : ℝ | t ∈ Set.Ioo 0 1 ∧ control a b t = 0}.encard

end D5.S3.Analytic.MeijerZeroCount.Defs
