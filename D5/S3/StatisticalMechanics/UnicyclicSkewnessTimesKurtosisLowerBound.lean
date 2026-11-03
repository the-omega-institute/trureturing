/- GID: D5/S3/StatisticalMechanics/UnicyclicSkewnessTimesKurtosisLowerBound
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/UnicyclicSkewnessTimesKurtosisLowerBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Ptaszynski's sharp lower bound for unidirectional unicyclic S times K. -/

import D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound

/-! Ptaszyński's sharp lower bound for the product of unicyclic skewness and kurtosis. -/

noncomputable section

open scoped BigOperators
open Filter
open D5.S3.Quantum.Transport.StrongAbsorption.Foundations (powerSum)

namespace D5.S3.StatisticalMechanics.UnicyclicSkewnessTimesKurtosisLowerBound

open D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum (skewness)
open D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound (kurtosis)
open D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound
  (normalizedRates p q r normalized_moments)

def lowerBound : ℝ :=
  sInf ((fun A : ℝ => (1 - 10 * A + 22 * A ^ 2 - 12 * A ^ 3) / (1 + A) ^ 8) ''
    Set.Ioi 0)

def claim : Prop :=
  (∀ n : ℕ, 2 ≤ n → ∀ k : Fin n → ℝ, (∀ i, 0 < k i) →
    lowerBound < skewness k * kurtosis k) ∧
  IsGLB {s : ℝ | ∃ n : ℕ, 2 ≤ n ∧ ∃ k : Fin n → ℝ,
    (∀ i, 0 < k i) ∧ s = skewness k * kurtosis k} lowerBound

private def f (u : ℝ) : ℝ := u ^ 5 * (3 * u - 2) * (15 * u ^ 2 - 20 * u + 6)

private def sourceExpression (A : ℝ) : ℝ :=
  (1 - 10 * A + 22 * A ^ 2 - 12 * A ^ 3) / (1 + A) ^ 8

private lemma source_bddBelow :
    BddBelow (sourceExpression '' Set.Ioi (0 : ℝ)) := by
  refine ⟨-100, ?_⟩
  rintro y ⟨A, hA, rfl⟩
  have hA0 : 0 < A := hA
  have h1 : 0 < 1 + A := by linarith
  have hden : 0 < (1 + A) ^ 8 := by positivity
  apply (le_div_iff₀ hden).2
  have hpoly : 0 ≤ 100 * (1 + A) ^ 8 +
      (1 - 10 * A + 22 * A ^ 2 - 12 * A ^ 3) := by
    have hA0 : 0 ≤ A := le_of_lt hA0
    ring_nf
    positivity
  nlinarith

private lemma source_le_lower_bound (A : ℝ) (hA : 0 < A) :
    lowerBound ≤ sourceExpression A := by
  dsimp [lowerBound]
  exact csInf_le source_bddBelow ⟨A, hA, rfl⟩

private lemma source_expression_eq_f (u : ℝ) (hu : 0 < u) (hu1 : u < 1) :
    sourceExpression ((1 - u) / u) = f u := by
  dsimp [sourceExpression, f]
  field_simp
  ring

private lemma f_lower_bound (u : ℝ) (hu : 0 < u) (hu1 : u < 1) :
    lowerBound ≤ f u := by
  rw [← source_expression_eq_f u hu hu1]
  apply source_le_lower_bound
  apply div_pos
  · linarith
  · exact hu

private lemma lowerBound_negative : lowerBound < 0 := by
  have h := source_le_lower_bound (1 / 3) (by norm_num)
  dsimp [sourceExpression] at h
  norm_num at h ⊢
  linarith

private lemma f_strict_scale (t z : ℝ) (ht : 0 < t) (htz : t < z)
    (hz : 0 < z) (hneg : z * (3 * z - 2) * (15 * z ^ 2 - 20 * z + 6) < 0) :
    t ^ 4 * (z * (3 * z - 2) * (15 * z ^ 2 - 20 * z + 6)) > f z := by sorry

private lemma normalized_product {n : ℕ} (k : Fin n → ℝ)
    (hk : ∀ i, 0 < k i) :
    skewness k * kurtosis k =
      (3 * p k ^ 2 - 2 * q k) * (15 * p k ^ 2 - 20 * q k + 6 * r k / p k) := by sorry

private lemma product_nonnegative (p q r : ℝ) (hp : 0 < p)
    (hprod : 0 ≤ (3 * p ^ 2 - 2 * q) * (15 * p ^ 2 - 20 * q + 6 * r / p)) :
    lowerBound < (3 * p ^ 2 - 2 * q) * (15 * p ^ 2 - 20 * q + 6 * r / p) := by sorry

private lemma product_skew_negative (p q r : ℝ) (hp : 0 < p) (hq : 0 ≤ q)
    (hqr : q ^ 2 ≤ p * r) (hr : r < p ^ 2)
    (hskew : 3 * p ^ 2 - 2 * q < 0)
    (hkurt : 0 < 15 * p ^ 2 - 20 * q + 6 * r / p) :
    lowerBound < (3 * p ^ 2 - 2 * q) * (15 * p ^ 2 - 20 * q + 6 * r / p) := by sorry

private lemma product_kurtosis_negative (p q r : ℝ) (hp : 0 < p) (hq : 0 ≤ q)
    (hqr : q ^ 2 ≤ p * r) (hr : r < p ^ 2)
    (hskew : 0 < 3 * p ^ 2 - 2 * q)
    (hkurt : 15 * p ^ 2 - 20 * q + 6 * r / p < 0) :
    lowerBound < (3 * p ^ 2 - 2 * q) * (15 * p ^ 2 - 20 * q + 6 * r / p) := by sorry

private lemma strict_lower_bound (n : ℕ) (hn : 2 ≤ n) (k : Fin n → ℝ)
    (hk : ∀ i, 0 < k i) : lowerBound < skewness k * kurtosis k := by sorry

private def sourceRates (u : ℝ) (m : ℕ) : Fin (m + 1) → ℝ :=
  fun i => if i = 0 then (1 - u) / (m * u) else 1

private lemma source_rates_positive (u : ℝ) (m : ℕ) (hu : 0 < u) (hu1 : u < 1)
    (hm : 1 ≤ m) : ∀ i, 0 < sourceRates u m i := by sorry

private def sourceApproximation (u : ℝ) : ℝ := f u

private lemma source_value (u : ℝ) (m : ℕ) (hu : 0 < u) (hu1 : u < 1)
    (hm : 1 ≤ m) :
    skewness (sourceRates u m) * kurtosis (sourceRates u m) =
      sourceApproximation u + (1 / (m : ℝ)) *
        (1 / (m : ℝ) * (2 * u ^ 5 - 3 * u ^ 4 + u ^ 3)) := by sorry

private lemma source_limit (u : ℝ) (hu : 0 < u) (hu1 : u < 1)
    (hmin : f u = lowerBound) :
    Tendsto (fun m : ℕ => skewness (sourceRates u (m + 1)) *
      kurtosis (sourceRates u (m + 1))) atTop (nhds lowerBound) := by sorry

private lemma greatest_lower_bound :
    IsGLB {s : ℝ | ∃ n : ℕ, 2 ≤ n ∧ ∃ k : Fin n → ℝ,
      (∀ i, 0 < k i) ∧ s = skewness k * kurtosis k} lowerBound := by sorry

theorem result : claim := by
  exact ⟨strict_lower_bound, greatest_lower_bound⟩

end D5.S3.StatisticalMechanics.UnicyclicSkewnessTimesKurtosisLowerBound
