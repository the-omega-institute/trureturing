/- GID: D5/S3/Analytic/BesselRedheffer/Defs
   generality: G
   mirror-B: D5/B/S3/Analytic/BesselRedheffer/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.Pochhammer, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Real]
   utility: none
   digest: Normalized Bessel series, its first positive zero, and the Redheffer lower bound. -/

import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace D5.S3.Analytic.BesselRedheffer.Defs

/-- The normalized Bessel function 𝒥_ν(x) = Σ (−x²/4)^k / (k! (ν+1)_k). -/
noncomputable def nbessel (ν x : ℝ) : ℝ :=
  ∑' k : ℕ, (-(x ^ 2) / 4) ^ k / ((k.factorial : ℝ) * (ascPochhammer ℝ k).eval (ν + 1))

/-- The first positive zero j_{ν,1} of 𝒥_ν. -/
noncomputable def firstZero (ν : ℝ) : ℝ := sInf {x : ℝ | 0 < x ∧ nbessel ν x = 0}

/-- Conjecture 1, left-hand side of (3.2). -/
def claim : Prop :=
  ∀ ν : ℝ, -1 < ν → ∀ x : ℝ, |x| < firstZero ν →
    (firstZero ν ^ 2 / (firstZero ν ^ 2 - x ^ 2)) ^ (firstZero ν ^ 2 / (4 * (ν + 1) * (ν + 2)))
      ≤ nbessel (ν + 1) x / nbessel ν x

end D5.S3.Analytic.BesselRedheffer.Defs
