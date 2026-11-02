/- GID: D5/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/UnicyclicKurtosisLowerBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The sharp unicyclic current kurtosis lower bound is approached by one slow rate. -/

import D5.S3.Quantum.Transport.StrongAbsorption.Foundations
import Mathlib.Analysis.SpecificLimits.Basic

/-! The fourth-to-second current cumulant ratio for positive unidirectional cycle rates.
The finite-cycle inequality is strict; the optimal constant is an asymptotic value. -/

noncomputable section

open scoped BigOperators
open Filter
open D5.S3.Quantum.Transport.StrongAbsorption.Foundations (powerSum)

namespace D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound

/-- The fourth scaled current cumulant divided by the second scaled current cumulant. -/
def kurtosis {n : ℕ} (k : Fin n → ℝ) : ℝ :=
  15 * powerSum n 2 (fun i => (k i)⁻¹) ^ 2 /
      powerSum n 1 (fun i => (k i)⁻¹) ^ 4 -
    20 * powerSum n 3 (fun i => (k i)⁻¹) /
      powerSum n 1 (fun i => (k i)⁻¹) ^ 3 +
    6 * powerSum n 4 (fun i => (k i)⁻¹) /
      (powerSum n 1 (fun i => (k i)⁻¹) ^ 2 * powerSum n 2 (fun i => (k i)⁻¹))

/-- The sharp lower bound, approached as the number of states tends to infinity. -/
def lowerBound : ℝ := -(1 + Real.sqrt 5) / 10

/-- Strict finite-cycle lower bound and greatest lower bound over all positive cycles. -/
def claim : Prop :=
  (∀ n : ℕ, 2 ≤ n → ∀ k : Fin n → ℝ, (∀ i, 0 < k i) →
    lowerBound < kurtosis k) ∧
  IsGLB {s : ℝ | ∃ n : ℕ, 2 ≤ n ∧ ∃ k : Fin n → ℝ,
    (∀ i, 0 < k i) ∧ s = kurtosis k} lowerBound

private lemma normalized {n : ℕ} (k : Fin n → ℝ) :
    kurtosis k =
      15 * powerSum n 2 (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹)) ^ 2 -
      20 * powerSum n 3 (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹)) +
      6 * powerSum n 4 (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹)) /
        powerSum n 2 (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹)) := by
  sorry

private lemma moments {n : ℕ} (hn : 2 ≤ n) (x : Fin n → ℝ)
    (hx : ∀ i, 0 < x i) :
    0 < powerSum n 2 x ∧ 0 ≤ powerSum n 3 x ∧
      powerSum n 3 x ^ 2 ≤ powerSum n 2 x * powerSum n 4 x ∧
      powerSum n 4 x < powerSum n 2 x ^ 2 := by
  sorry

private lemma polynomial_lower_bound (u : ℝ) (hu : 0 ≤ u) :
    lowerBound ≤ 15 * u ^ 4 - 20 * u ^ 3 + 6 * u ^ 2 := by
  sorry

private lemma moment_lower_bound (a b c : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hbc : b ^ 2 ≤ a * c) (hc : c < a ^ 2) :
    lowerBound < 15 * a ^ 2 - 20 * b + 6 * c / a := by
  sorry

private lemma strict_lower_bound (n : ℕ) (hn : 2 ≤ n) (k : Fin n → ℝ)
    (hk : ∀ i, 0 < k i) : lowerBound < kurtosis k := by
  have hs : 0 < powerSum n 1 (fun i => (k i)⁻¹) := by
    sorry
  rw [normalized]
  obtain ⟨ha, hb, hbc, hc⟩ := moments hn
    (fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹))
    (fun i => div_pos (inv_pos.mpr (hk i)) hs)
  exact moment_lower_bound _ _ _ ha hb hbc hc

private def sourceParameter : ℝ := (3 - Real.sqrt 5) / 2

private def sourceRates (m : ℕ) : Fin (m + 2) → ℝ :=
  fun i => if i = 0 then sourceParameter / (m + 2 : ℕ) else 1

private lemma source_rates_positive (m : ℕ) : ∀ i, 0 < sourceRates m i := by
  sorry

private def approximation (a t : ℝ) : ℝ :=
  15 * (1 + a ^ 2 * (t - t ^ 2)) ^ 2 / (1 + a - a * t) ^ 4 -
    20 * (1 + a ^ 3 * (t ^ 2 - t ^ 3)) / (1 + a - a * t) ^ 3 +
    6 * (1 + a ^ 4 * (t ^ 3 - t ^ 4)) /
      ((1 + a - a * t) ^ 2 * (1 + a ^ 2 * (t - t ^ 2)))

private lemma source_kurtosis (m : ℕ) :
    kurtosis (sourceRates m) = approximation sourceParameter (1 / (m + 2 : ℕ)) := by
  sorry

private lemma source_limit :
    Tendsto (fun m : ℕ => kurtosis (sourceRates m)) atTop (nhds lowerBound) := by
  sorry

private lemma greatest_lower_bound :
    IsGLB {s : ℝ | ∃ n : ℕ, 2 ≤ n ∧ ∃ k : Fin n → ℝ,
      (∀ i, 0 < k i) ∧ s = kurtosis k} lowerBound := by
  sorry

/-- Ptaszyński's sharp lower bound, with strictness for every finite positive cycle. -/
theorem result : claim := ⟨strict_lower_bound, greatest_lower_bound⟩

end D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound
