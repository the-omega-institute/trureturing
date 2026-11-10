/- GID: D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisUpperBound
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisUpperBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The exact sharp upper endpoint of unicyclic current skewness minus kurtosis. -/

import D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound

/-! The all-positive-rate upper bound and its supremum over unbounded finite cycles.
The source's detailed display concerns S − K; its introductory summary reverses the sign. -/

noncomputable section

open scoped BigOperators
open Filter
open D5.S3.Quantum.Transport.StrongAbsorption.Foundations (powerSum)

namespace D5.S3.StatisticalMechanics.UnicyclicSkewnessMinusKurtosisUpperBound

open D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum (skewness)
open D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound (kurtosis)
open D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound
  (normalizedRates p q r normalized_moments)

/-- The upper endpoint in the detailed S − K display of the primary source. -/
def upperBound : ℝ := 3 * (107 + 51 * Real.sqrt 17) / 2048

/-- Universal bound and least upper bound of exactly the actual positive-rate values. -/
def claim : Prop :=
  (∀ n : ℕ, 2 ≤ n → ∀ k : Fin n → ℝ, (∀ i, 0 < k i) →
    skewness k - kurtosis k ≤ upperBound) ∧
  IsLUB {s : ℝ | ∃ n : ℕ, 2 ≤ n ∧ ∃ k : Fin n → ℝ,
    (∀ i, 0 < k i) ∧ s = skewness k - kurtosis k} upperBound

lemma normalized_difference {n : ℕ} (k : Fin n → ℝ) :
    skewness k - kurtosis k = -12 * p k ^ 2 + 18 * q k - 6 * r k / p k := by
  rw [D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness_normalized,
    D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.normalized]
  delta D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.simplexFunctional
    p q r normalizedRates
  ring

private lemma polynomial_upper_bound (t : ℝ) (ht : 0 ≤ t) :
    -12 * t ^ 4 + 18 * t ^ 3 - 6 * t ^ 2 ≤ upperBound := by
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hs3 : Real.sqrt 17 ^ 3 = 17 * Real.sqrt 17 := by rw [pow_succ, hs]
  have h3 : 3 ≤ Real.sqrt 17 := Real.le_sqrt_of_sq_le (by norm_num)
  have hid : upperBound - (-12 * t ^ 4 + 18 * t ^ 3 - 6 * t ^ 2) =
      (t - (9 + Real.sqrt 17) / 16) ^ 2 *
        (12 * t ^ 2 + (3 * Real.sqrt 17 - 9) / 2 * t +
          (9 * Real.sqrt 17 - 15) / 32) := by
    dsimp [upperBound]
    ring_nf
    simp only [hs, hs3]
    ring
  have hc : 0 ≤ (3 * Real.sqrt 17 - 9) / 2 := by linarith
  have hd : 0 ≤ (9 * Real.sqrt 17 - 15) / 32 := by linarith
  have hn : 0 ≤ (t - (9 + Real.sqrt 17) / 16) ^ 2 *
      (12 * t ^ 2 + (3 * Real.sqrt 17 - 9) / 2 * t +
        (9 * Real.sqrt 17 - 15) / 32) := by positivity
  linarith

private lemma moment_upper_bound (a b c : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (hbc : b ^ 2 ≤ a * c) (hc : c < a ^ 2) :
    -12 * a ^ 2 + 18 * b - 6 * c / a ≤ upperBound := by
  let t := b / a
  have hat : a * t = b := mul_div_cancel₀ b ha.ne'
  have hat2 : a ^ 2 * t ^ 2 = b ^ 2 := by rw [← mul_pow, hat]
  have ht : 0 ≤ t := div_nonneg hb ha.le
  have hts : t ^ 2 < a := by
    have h := mul_lt_mul_of_pos_left hc ha
    apply (mul_lt_mul_iff_left₀ (sq_pos_of_pos ha)).mp
    nlinarith [hbc]
  have hcs : a * t ^ 2 ≤ c := by
    apply (mul_le_mul_iff_left₀ ha).mp
    nlinarith [hbc]
  have hdiv : t ^ 2 ≤ c / a := (le_div_iff₀ ha).mpr (by nlinarith [hcs])
  have he : -12 * a ^ 2 + 18 * b - 6 * c / a ≤
      -12 * a ^ 2 + 18 * a * t - 6 * t ^ 2 := by
    rw [mul_div_assoc]
    nlinarith
  by_cases ht34 : t ≤ 3 / 4
  · have ht2 : t ^ 2 ≤ 9 / 16 := by
      nlinarith [mul_nonneg ht (by linarith : 0 ≤ 3 / 4 - t)]
    have hsmall : -12 * a ^ 2 + 18 * a * t - 6 * t ^ 2 ≤ 27 / 64 := by
      nlinarith [sq_nonneg (a - 3 / 4 * t)]
    have hbnd : (27 / 64 : ℝ) ≤ upperBound := by
      dsimp [upperBound]
      have h4 : 4 ≤ Real.sqrt 17 := Real.le_sqrt_of_sq_le (by norm_num)
      linarith
    exact he.trans (hsmall.trans hbnd)
  · have hcoef : 0 ≤ 12 * (a + t ^ 2) - 18 * t := by
      have htcoef : 0 ≤ t * (4 * t - 3) := mul_nonneg ht (by linarith)
      nlinarith
    have hprod := mul_nonneg (sub_nonneg.mpr hts.le) hcoef
    have hf := polynomial_upper_bound t ht
    nlinarith

private lemma universal_upper_bound (n : ℕ) (hn : 2 ≤ n) (k : Fin n → ℝ)
    (hk : ∀ i, 0 < k i) : skewness k - kurtosis k ≤ upperBound := by
  rw [normalized_difference]
  obtain ⟨ha, hb, hbc, hc⟩ := normalized_moments hn k hk
  exact moment_upper_bound _ _ _ ha hb hbc hc

private def endpointMass : ℝ := (9 + Real.sqrt 17) / 16

/-- Reciprocals of one fixed mass and m + 1 equal positive tail masses. -/
private def sharpRates (m : ℕ) : Fin (m + 2) → ℝ :=
  fun i => if i = 0 then endpointMass⁻¹ else ((m : ℝ) + 1) / (1 - endpointMass)

private lemma sharp_rates_positive (m : ℕ) : ∀ i, 0 < sharpRates m i := by
  have hs0 := Real.sqrt_nonneg (17 : ℝ)
  have hs7 : Real.sqrt 17 < 7 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hu : 0 < endpointMass := by dsimp [endpointMass]; linarith
  have hu1 : endpointMass < 1 := by dsimp [endpointMass]; linarith
  intro i
  dsimp [sharpRates]
  split_ifs <;> positivity

private def approximation (t : ℝ) : ℝ :=
  -12 * (endpointMass ^ 2 + (1 - endpointMass) ^ 2 * t) ^ 2 +
    18 * (endpointMass ^ 3 + (1 - endpointMass) ^ 3 * t ^ 2) -
    6 * (endpointMass ^ 4 + (1 - endpointMass) ^ 4 * t ^ 3) /
      (endpointMass ^ 2 + (1 - endpointMass) ^ 2 * t)

private lemma sharp_value (m : ℕ) :
    skewness (sharpRates m) - kurtosis (sharpRates m) =
      approximation (1 / ((m : ℝ) + 1)) := by
  have hm : 0 < (m : ℝ) + 1 := by positivity
  have hs (j : ℕ) : powerSum (m + 2) j (fun i => (sharpRates m i)⁻¹) =
      endpointMass ^ j + ((m : ℝ) + 1) * ((1 - endpointMass) / ((m : ℝ) + 1)) ^ j := by
    simp [powerSum, sharpRates, Fin.sum_univ_succ, ← inv_pow, inv_div]
  have h1 : powerSum (m + 2) 1 (fun i => (sharpRates m i)⁻¹) = 1 := by
    rw [hs]
    field_simp <;> ring
  have h2 : endpointMass ^ 2 + ((m : ℝ) + 1) *
      ((1 - endpointMass) / ((m : ℝ) + 1)) ^ 2 =
      endpointMass ^ 2 + (1 - endpointMass) ^ 2 * (1 / ((m : ℝ) + 1)) := by
    field_simp <;> ring
  have h3 : endpointMass ^ 3 + ((m : ℝ) + 1) *
      ((1 - endpointMass) / ((m : ℝ) + 1)) ^ 3 =
      endpointMass ^ 3 + (1 - endpointMass) ^ 3 * (1 / ((m : ℝ) + 1)) ^ 2 := by
    field_simp <;> ring
  have h4 : endpointMass ^ 4 + ((m : ℝ) + 1) *
      ((1 - endpointMass) / ((m : ℝ) + 1)) ^ 4 =
      endpointMass ^ 4 + (1 - endpointMass) ^ 4 * (1 / ((m : ℝ) + 1)) ^ 3 := by
    field_simp <;> ring
  rw [skewness, kurtosis, h1, hs 2, hs 3, hs 4, h2, h3, h4]
  dsimp [approximation]
  ring

private lemma sharp_limit :
    Tendsto (fun m : ℕ => skewness (sharpRates m) - kurtosis (sharpRates m))
      atTop (nhds upperBound) := by
  have hu : 0 < endpointMass := by
    have h := sharp_rates_positive 0 0
    simp only [sharpRates, ↓reduceIte, inv_pos] at h
    exact h
  have hc : ContinuousAt approximation 0 := by
    unfold approximation
    fun_prop (disch := positivity)
  have hz : Tendsto (fun m : ℕ => 1 / ((m + 1 : ℕ) : ℝ)) atTop (nhds (0 : ℝ)) :=
    (tendsto_add_atTop_iff_nat 1).mpr tendsto_one_div_atTop_nhds_zero_nat
  have he : approximation 0 = upperBound := by
    have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
    have hs3 : Real.sqrt 17 ^ 3 = 17 * Real.sqrt 17 := by rw [pow_succ, hs]
    have hs4 : Real.sqrt 17 ^ 4 = 289 := by
      calc
        _ = (Real.sqrt 17 ^ 2) ^ 2 := pow_mul _ 2 2
        _ = _ := by rw [hs]; norm_num
    have hid : approximation 0 =
        -12 * endpointMass ^ 4 + 18 * endpointMass ^ 3 - 6 * endpointMass ^ 2 := by
      dsimp [approximation]
      field_simp
      ring
    rw [hid]
    dsimp [endpointMass, upperBound]
    ring_nf
    simp only [hs, hs3, hs4]
    ring
  simpa only [Function.comp_def, ← sharp_value, Nat.cast_add, Nat.cast_one, he] using
    hc.tendsto.comp hz

/-- Ptaszyński's exact upper endpoint, for every actual finite positive rate vector. -/
theorem result : claim := by
  refine ⟨universal_upper_bound, ?_⟩
  refine ⟨?_, ?_⟩
  · rintro s ⟨n, hn, k, hk, rfl⟩
    exact universal_upper_bound n hn k hk
  · intro b hb
    apply le_of_tendsto' sharp_limit
    intro m
    exact hb ⟨m + 2, by omega, sharpRates m, sharp_rates_positive m, rfl⟩

end D5.S3.StatisticalMechanics.UnicyclicSkewnessMinusKurtosisUpperBound
