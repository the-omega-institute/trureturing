/- GID: D5/S3/Analytic/KummerRatio/Defs
   generality: G
   mirror-B: D5/B/S3/Analytic/KummerRatio/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.Pochhammer, mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.Basic]
   utility: none
   digest: Kummer series, upper parameter ratios, and their monotonicity and range statement. -/

import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

namespace D5.S3.Analytic.KummerRatio.Defs

/-- Coefficient (s)_n / ((c)_n n!). -/
noncomputable def kummerCoeff (s c : ℝ) (n : ℕ) : ℝ :=
  (ascPochhammer ℝ n).eval s / ((ascPochhammer ℝ n).eval c * (n.factorial : ℝ))

/-- Kummer's function M(s;c;x) = ₁F₁(s;c;x). -/
noncomputable def kummer (s c x : ℝ) : ℝ := ∑' n : ℕ, kummerCoeff s c n * x ^ n

/-- The ratio in the middle of (10) and (11). -/
noncomputable def ratio (a b c δ x : ℝ) : ℝ :=
  kummer (b + δ) c x * kummer a c x / (kummer (a + δ) c x * kummer b c x)

/-- The Karp–Sitnik conjecture, both clauses. -/
def claim : Prop :=
  ∀ a b c δ : ℝ, 0 < c → 0 < δ →
    ((0 < a → a < b →
        StrictAntiOn (ratio a b c δ) (Set.Ioi 0) ∧
        ratio a b c δ '' Set.Ioi 0 =
          Set.Ioo (Real.Gamma (a + δ) * Real.Gamma b / (Real.Gamma (b + δ) * Real.Gamma a)) 1) ∧
     (a < b → b < c - δ →
        StrictMonoOn (ratio a b c δ) (Set.Iio 0) ∧
        ratio a b c δ '' Set.Iio 0 =
          Set.Ioo (Real.Gamma (c - a - δ) * Real.Gamma (c - b) / (Real.Gamma (c - b - δ) * Real.Gamma (c - a))) 1))

end D5.S3.Analytic.KummerRatio.Defs
