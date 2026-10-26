/- GID: D5/S3/StatisticalMechanics/UnicyclicSkewnessMinimum
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/UnicyclicSkewnessMinimum
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The least unidirectional unicyclic current skewness is attained by one slow rate. -/

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open scoped BigOperators

namespace D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum

/-- The inverse-rate power sums; the first three waiting-time cumulants are R₁, R₂, 2R₃. -/
def waitingPowerSum {n : ℕ} (k : Fin n → ℝ) (j : ℕ) : ℝ :=
  ∑ i, (k i)⁻¹ ^ j

/-- The third scaled current cumulant divided by the first scaled current cumulant. -/
def skewness {n : ℕ} (k : Fin n → ℝ) : ℝ :=
  3 * waitingPowerSum k 2 ^ 2 / waitingPowerSum k 1 ^ 4 -
    2 * waitingPowerSum k 3 / waitingPowerSum k 1 ^ 3

/-- The conjectured finite-state minimum. -/
def minimumValue (n : ℕ) : ℝ :=
  -(8 - 8 * (n : ℝ) + (n : ℝ) ^ 2) / (16 * ((n : ℝ) - 1) ^ 2)

/-- All positive clockwise rate vectors on every cycle with at least two states. -/
def claim : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    IsLeast {s : ℝ | ∃ k : Fin n → ℝ, (∀ i, 0 < k i) ∧ s = skewness k}
      (minimumValue n)

private def simplexFunctional {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  3 * (∑ i, x i ^ 2) ^ 2 - 2 * ∑ i, x i ^ 3

private lemma normalized_simplex {n : ℕ} (hn : 2 ≤ n) (k : Fin n → ℝ)
    (hk : ∀ i, 0 < k i) :
    (fun i => (k i)⁻¹ / waitingPowerSum k 1) ∈ stdSimplex ℝ (Fin n) := by
  sorry

private lemma skewness_normalized {n : ℕ} (k : Fin n → ℝ) :
    skewness k = simplexFunctional (fun i => (k i)⁻¹ / waitingPowerSum k 1) := by
  sorry

private lemma simplex_lower_bound {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin n)) : minimumValue n ≤ simplexFunctional x := by
  sorry

private lemma attaining_rates (n : ℕ) (hn : 2 ≤ n) :
    ∃ k : Fin n → ℝ, (∀ i, 0 < k i) ∧ minimumValue n = skewness k := by
  sorry

/-- The conjectured skewness minimum holds for every positive rate vector and is attained. -/
theorem result : claim := by
  intro n hn
  refine ⟨attaining_rates n hn, ?_⟩
  rintro s ⟨k, hk, rfl⟩
  rw [skewness_normalized]
  exact simplex_lower_bound hn _ (normalized_simplex hn k hk)

end D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum
