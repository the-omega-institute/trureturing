/- GID: D5/S3/Analytic/GaussZeroBalanced/Defs
   generality: G
   mirror-B: D5/B/S3/Analytic/GaussZeroBalanced/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric, mathlib/module/Mathlib.Analysis.Calculus.Deriv.Basic, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real]
   utility: none
   digest: The zero-balanced Gauss quotient and its two parameter classifications. -/

import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace D5.S3.Analytic.GaussZeroBalanced.Defs

/-- The Gauss hypergeometric function over the real numbers. -/
noncomputable def gauss (a b c x : ℝ) : ℝ :=
  ordinaryHypergeometric (𝔸 := ℝ) a b c x

/-- The quotient in the first classification. -/
noncomputable def quot (a b x : ℝ) : ℝ :=
  gauss (a + 1) (b + 1) (a + b + 1) x / gauss a b (a + b) x

/-- The contiguous quotient used in the Riccati equation. -/
noncomputable def f (a b x : ℝ) : ℝ :=
  gauss a b (a + b + 1) x / gauss a b (a + b) x

/-- The comparison in the second classification. -/
def ineq17 (a r : ℝ) : Prop :=
  gauss (a + 1) (2 - a) 2 r / gauss a (1 - a) 1 r >
    gauss (a + 1) (5 / 2 - a) (5 / 2) r / gauss a (3 / 2 - a) (3 / 2) r

/-- The two clauses of the zero-balanced quotient conjecture. -/
def claim : Prop :=
  (∀ a b : ℝ, 0 < a → 0 < b →
    ((∀ x ∈ Set.Ioo (0 : ℝ) 1, deriv (fun β => quot a β x) b < 0) ↔
      b ≤ Real.sqrt (a * (a + 1)))) ∧
  (∀ a : ℝ, 0 < a → a < 1 →
    ((∀ r ∈ Set.Ioo (0 : ℝ) 1, ineq17 a r) ↔ 3 / 7 ≤ a))

end D5.S3.Analytic.GaussZeroBalanced.Defs
