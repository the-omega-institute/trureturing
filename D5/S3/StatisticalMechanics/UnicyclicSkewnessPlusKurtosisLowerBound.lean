/- GID: D5/S3/StatisticalMechanics/UnicyclicSkewnessPlusKurtosisLowerBound
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/UnicyclicSkewnessPlusKurtosisLowerBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Ptaszyński's sharp finite-cycle lower bound for skewness plus kurtosis. -/

import D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum
import D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound

noncomputable section

open scoped BigOperators
open Filter
open D5.S3.Quantum.Transport.StrongAbsorption.Foundations (powerSum)

namespace D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound

open D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum (skewness)
open D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound (kurtosis)

def lowerBound : ℝ := -8 / 27

def claim : Prop :=
  (∀ n : ℕ, 2 ≤ n → ∀ k : Fin n → ℝ, (∀ i, 0 < k i) →
    lowerBound < skewness k + kurtosis k) ∧
  IsGLB {s : ℝ | ∃ n : ℕ, 2 ≤ n ∧ ∃ k : Fin n → ℝ,
    (∀ i, 0 < k i) ∧ s = skewness k + kurtosis k} lowerBound

private def normalizedRates {n : ℕ} (k : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹)

private def p {n : ℕ} (k : Fin n → ℝ) : ℝ := powerSum n 2 (normalizedRates k)

private def q {n : ℕ} (k : Fin n → ℝ) : ℝ := powerSum n 3 (normalizedRates k)

private def r {n : ℕ} (k : Fin n → ℝ) : ℝ := powerSum n 4 (normalizedRates k)

private lemma normalized_sum {n : ℕ} (k : Fin n → ℝ) :
    skewness k + kurtosis k = 18 * p k ^ 2 - 22 * q k + 6 * r k / p k := by sorry

private lemma normalized_moments {n : ℕ} (hn : 2 ≤ n) (k : Fin n → ℝ)
    (hk : ∀ i, 0 < k i) :
    0 < p k ∧ 0 ≤ q k ∧ q k ^ 2 ≤ p k * r k ∧ r k < p k ^ 2 := by sorry

private lemma reduced_form (p q r t e : ℝ) (hp : p ≠ 0)
    (hqt : q = p * t) (hre : r = p * (t ^ 2 + e)) :
    18 * p ^ 2 - 22 * q + 6 * r / p + 8 / 27 =
      18 * p ^ 2 - 22 * p * t + 6 * t ^ 2 + 6 * e + 8 / 27 := by sorry

private lemma low_certificate_identity (p t e : ℝ) :
    18 * p ^ 2 - 22 * p * t + 6 * t ^ 2 + 6 * e + 8 / 27 =
      6 * e + 18 * (p - (11 / 18 : ℝ) * t) ^ 2 +
        13 / 18 * ((11 / 18 : ℝ) ^ 2 - t ^ 2) + 155 / 5832 := by sorry

private lemma high_certificate_identity (p t e d : ℝ) (hd : d = p - t ^ 2) :
    18 * p ^ 2 - 22 * p * t + 6 * t ^ 2 + 6 * e + 8 / 27 =
      6 * e + d * (18 * d + 36 * t ^ 2 - 22 * t) +
        (t - 2 / 3) ^ 2 * (18 * t ^ 2 + 2 * t + 2 / 3) := by sorry

private lemma low_certificate (p t e : ℝ) (he : 0 ≤ e)
    (ht0 : 0 ≤ t) (ht : t ≤ 11 / 18) :
    0 < 6 * e + 18 * (p - (11 / 18 : ℝ) * t) ^ 2 +
      13 / 18 * ((11 / 18 : ℝ) ^ 2 - t ^ 2) + 155 / 5832 := by sorry

private lemma high_certificate (t e d : ℝ) (he : 0 ≤ e) (hd : 0 < d)
    (ht : 11 / 18 ≤ t) :
    0 < 6 * e + d * (18 * d + 36 * t ^ 2 - 22 * t) +
      (t - 2 / 3) ^ 2 * (18 * t ^ 2 + 2 * t + 2 / 3) := by sorry

private lemma strict_lower_bound (n : ℕ) (hn : 2 ≤ n) (k : Fin n → ℝ)
    (hk : ∀ i, 0 < k i) : lowerBound < skewness k + kurtosis k := by sorry

private def sourceRates (m : ℕ) : Fin (m + 1) → ℝ :=
  fun i => if i = 0 then (2 * (m : ℝ))⁻¹ else 1

private lemma source_rates_positive (m : ℕ) (hm : 1 ≤ m) :
    ∀ i, 0 < sourceRates m i := by sorry

private lemma source_power_sum (m j : ℕ) (hm : 1 ≤ m) :
    powerSum (m + 1) j (fun i => (sourceRates m i)⁻¹) =
      (2 * (m : ℝ)) ^ j + m := by sorry

private lemma source_value (m : ℕ) (hm : 1 ≤ m) :
    skewness (sourceRates m) + kurtosis (sourceRates m) + 8 / 27 =
      2 * (60 * (m : ℝ) ^ 2 - 8 * m + 1) /
        (27 * (m : ℝ) ^ 2 * (4 * m + 1)) := by sorry

private lemma source_limit :
    Tendsto (fun m : ℕ => skewness (sourceRates (m + 1)) +
      kurtosis (sourceRates (m + 1))) atTop (nhds lowerBound) := by sorry

private lemma greatest_lower_bound :
    IsGLB {s : ℝ | ∃ n : ℕ, 2 ≤ n ∧ ∃ k : Fin n → ℝ,
      (∀ i, 0 < k i) ∧ s = skewness k + kurtosis k} lowerBound := by sorry

theorem result : claim := by
  exact ⟨strict_lower_bound, greatest_lower_bound⟩

end D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound
