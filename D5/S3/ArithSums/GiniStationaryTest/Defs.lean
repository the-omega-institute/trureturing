/- GID: D5/S3/ArithSums/GiniStationaryTest/Defs
   generality: I
   mirror-B: D5/B/S3/ArithSums/GiniStationaryTest/Defs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.Deriv.Basic]
   utility: none
   digest: Gini comparisons and their normalized stationary test on positive intervals. -/

import D5.S3.ArithSums.GiniMeanEndpointComparison
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Gini comparison and normalized characteristic derivatives. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.ArithSums.GiniStationaryTest.Defs

/-- The full Gini mean, using the existing unequal-parameter mean. -/
def giniMean {n : ℕ} (p q : ℝ) (x : Fin n → ℝ) : ℝ :=
  if p = q then Real.exp ((∑ i, x i ^ p * Real.log (x i)) / (∑ i, x i ^ p))
  else GiniMeanEndpointComparison.giniMean p q x

/-- The characteristic function of the Gini parameters. -/
def chi (p q t : ℝ) : ℝ :=
  if p = q then t ^ p * Real.log t else (t ^ p - t ^ q) / (p - q)

/-- The derivative of the characteristic function. -/
def chiDeriv (p q t : ℝ) : ℝ := deriv (chi p q) t

/-- Parameter pairs whose Gini means are ordered on every tuple in the interval. -/
def Gamma (n : ℕ) (I : Set ℝ) : Set ((ℝ × ℝ) × (ℝ × ℝ)) :=
  {P | ∀ x : Fin n → ℝ, (∀ i, x i ∈ I) →
    giniMean P.1.1 P.1.2 x ≤ giniMean P.2.1 P.2.2 x}

/-- The normalized stationary test for a pair of Gini means. -/
def stationaryTest (n : ℕ) (r s p q : ℝ) : Prop :=
  ∀ u : Fin n → ℝ, (∀ i, 0 < u i) → giniMean r s u = 1 →
    (∃ ρ : ℝ, ∀ k, chiDeriv p q (u k) + ρ * chiDeriv r s (u k) = 0) →
    1 ≤ giniMean p q u

/-- The proposed characterization by the normalized stationary test. -/
def claim : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ (I : Set ℝ), I ⊆ Set.Ioi 0 → I.OrdConnected →
    I.Nonempty → sInf ((fun z : ℝ × ℝ => z.1 / z.2) '' (I ×ˢ I)) = 0 →
    ∀ r s p q : ℝ,
      (((r, s), (p, q)) ∈ Gamma n I ↔ stationaryTest n r s p q)

end D5.S3.ArithSums.GiniStationaryTest.Defs
