/- GID: D5/S3/Analytic/EllipticTailExponent/Defs
   generality: G
   mirror-B: D5/B/S3/Analytic/EllipticTailExponent/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv, mathlib/module/Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic, mathlib/module/Mathlib.Data.Nat.Factorial.Basic]
   utility: none
   digest: Polynomial truncations and the parameter exponent of the elliptic remainder. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Factorial.Basic

open scoped BigOperators

namespace D5.S3.Analytic.EllipticTailExponent.Defs

/-- The coefficient polynomial a (a)_k (1-a)_k. -/
noncomputable def g6 (k : ℕ) (a : ℝ) : ℝ :=
  a * (∏ j ∈ Finset.range k, (a + j)) * (∏ j ∈ Finset.range k, (1 - a + j))

/-- The finite polynomial truncation through index n. -/
noncomputable def S (n : ℕ) (a : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), g6 k a / ((k + 1 : ℝ) * (Nat.factorial k : ℝ) ^ 2)

/-- The parameter exponent of the elliptic remainder. -/
noncomputable def lambda10 (n : ℕ) (a : ℝ) : ℝ :=
  a / (1 - a) *
    ((Real.sin (Real.pi * a) + Real.pi * (1 - a) * Real.cos (Real.pi * a) -
        Real.pi * (1 - a) ^ 2 * deriv (S n) a) /
      (Real.sin (Real.pi * a) - Real.pi * (1 - a) * S n a))

/-- Every truncation has parameter-exponent supremum two on (0,1/2]. -/
def claim : Prop :=
  ∀ n : ℕ, IsLUB (lambda10 n '' Set.Ioc 0 (1 / 2)) 2

end D5.S3.Analytic.EllipticTailExponent.Defs
