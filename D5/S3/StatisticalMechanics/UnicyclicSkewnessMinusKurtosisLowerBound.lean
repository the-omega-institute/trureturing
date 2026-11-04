/- GID: D5/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisLowerBound
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/UnicyclicSkewnessMinusKurtosisLowerBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The exact sharp lower endpoint of unicyclic current skewness minus kurtosis. -/

import D5.S3.StatisticalMechanics.UnicyclicSkewnessMinusKurtosisUpperBound

/-! The detailed S − K lower endpoint for actual positive finite rate vectors. -/

noncomputable section

open scoped BigOperators
open Filter
open D5.S3.Quantum.Transport.StrongAbsorption.Foundations (powerSum)

namespace D5.S3.StatisticalMechanics.UnicyclicSkewnessMinusKurtosisLowerBound

open D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum (skewness normalized_simplex)
open D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound (kurtosis)
open D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound
  (normalizedRates p q r normalized_moments)
open D5.S3.StatisticalMechanics.UnicyclicSkewnessMinusKurtosisUpperBound
  (normalized_difference)

/-- The lower endpoint in the detailed S − K display of the primary source. -/
def lowerBound : ℝ := 3 * (107 - 51 * Real.sqrt 17) / 2048

/-- Universal lower bound and greatest lower bound of all actual positive-rate values. -/
def claim : Prop :=
  (∀ n : ℕ, 2 ≤ n → ∀ k : Fin n → ℝ, (∀ i, 0 < k i) →
    lowerBound ≤ skewness k - kurtosis k) ∧
  IsGLB {s : ℝ | ∃ n : ℕ, 2 ≤ n ∧ ∃ k : Fin n → ℝ,
    (∀ i, 0 < k i) ∧ s = skewness k - kurtosis k} lowerBound

private lemma polynomial_lower_bound (u : ℝ) (hu : 0 ≤ u) (hu3 : u ≤ 1 / 3) :
    lowerBound ≤ -12 * u ^ 4 + 18 * u ^ 3 - 6 * u ^ 2 := by
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hs3 : Real.sqrt 17 ^ 3 = 17 * Real.sqrt 17 := by rw [pow_succ, hs]
  have hs0 := Real.sqrt_nonneg (17 : ℝ)
  have hid : -12 * u ^ 4 + 18 * u ^ 3 - 6 * u ^ 2 - lowerBound =
      (u - (9 - Real.sqrt 17) / 16) ^ 2 *
        (-12 * u ^ 2 + (9 + 3 * Real.sqrt 17) / 2 * u +
          (15 + 9 * Real.sqrt 17) / 32) := by
    dsimp [lowerBound]
    ring_nf
    simp only [hs, hs3]
    ring
  have hp : 0 ≤ u * (1 / 3 - u) := mul_nonneg hu (by linarith)
  have hcoef : 0 ≤ -12 * u ^ 2 + (9 + 3 * Real.sqrt 17) / 2 * u +
      (15 + 9 * Real.sqrt 17) / 32 := by
    nlinarith [mul_nonneg hs0 hu]
  have hprod := mul_nonneg (sq_nonneg (u - (9 - Real.sqrt 17) / 16)) hcoef
  linarith

private lemma coarse_lower_bound (u : ℝ) (hu : 1 / 3 ≤ u) (hu1 : u ≤ 1) :
    lowerBound ≤ -(3 / 2) * u * (1 - u) ^ 3 := by
  have hs : 41 / 10 ≤ Real.sqrt 17 := Real.le_sqrt_of_sq_le (by norm_num)
  have hc : lowerBound ≤ -(4 / 27 : ℝ) := by dsimp [lowerBound]; linarith
  have hp : 0 ≤ (u - 1 / 3) *
      (4 / 27 + (u - 1 / 3) * (1 - u) * (4 / 3 - u)) := by
    have h0 : 0 ≤ u - 1 / 3 := by linarith
    have h1 : 0 ≤ 1 - u := by linarith
    have h2 : 0 ≤ 4 / 3 - u := by linarith
    positivity
  have hid : 8 / 81 - u * (1 - u) ^ 3 = (u - 1 / 3) *
      (4 / 27 + (u - 1 / 3) * (1 - u) * (4 / 3 - u)) := by ring
  linarith

private lemma simplex_lower_bound {n : ℕ} (x : Fin n → ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin n)) (hp : 0 < powerSum n 2 x) :
    lowerBound ≤ -12 * powerSum n 2 x ^ 2 + 18 * powerSum n 3 x -
      6 * powerSum n 4 x / powerSum n 2 x := by
  classical
  let a := powerSum n 2 x
  let b := powerSum n 3 x
  let c := powerSum n 4 x
  let u := Real.sqrt a
  have ha : 0 < a := hp
  have hu : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = a := Real.sq_sqrt ha.le
  have hu1 : u ≤ 1 := by
    have hsum := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (f := x) (fun i _ => hx.1 i)
    rw [hx.2] at hsum
    change a ≤ 1 ^ 2 at hsum
    nlinarith
  have hxu (i : Fin n) : x i ≤ u := by
    have hi : x i ^ 2 ≤ a := Finset.single_le_sum
      (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    exact Real.le_sqrt_of_sq_le hi
  change lowerBound ≤ -12 * a ^ 2 + 18 * b - 6 * c / a
  by_cases hsmall : u ≤ 1 / 3
  · have hsum : 0 ≤ ∑ i, x i ^ 2 * (u - x i) * (u + x i - 3 * a) := by
      apply Finset.sum_nonneg
      intro i _
      have hlast : 0 ≤ u + x i - 3 * a := by
        nlinarith [mul_nonneg hu (show 0 ≤ 1 / 3 - u by linarith), hx.1 i]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (hxu i))) hlast
    have hid : (∑ i, x i ^ 2 * (u - x i) * (u + x i - 3 * a)) =
        u ^ 2 * a - c - 3 * a * u * a + 3 * a * b := by
      calc
        _ = ∑ i, (u ^ 2 * x i ^ 2 - x i ^ 4 -
            3 * a * u * x i ^ 2 + 3 * a * x i ^ 3) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ← Finset.mul_sum, a, b, c, powerSum]
    have hpoly := polynomial_lower_bound u hu hsmall
    have hdiff : -12 * u ^ 4 + 18 * u ^ 3 - 6 * u ^ 2 ≤
        -12 * a ^ 2 + 18 * b - 6 * c / a := by
      apply (mul_le_mul_iff_right₀ ha).mp
      rw [hid] at hsum
      have he : (-12 * a ^ 2 + 18 * b - 6 * c / a -
          (-12 * u ^ 4 + 18 * u ^ 3 - 6 * u ^ 2)) * a =
          6 * (u ^ 2 * a - c - 3 * a * u * a + 3 * a * b) := by
        field_simp
        rw [← hu2]
        ring
      nlinarith
    exact hpoly.trans hdiff
  · let d := (3 * a - u) / 2
    have hsum : 0 ≤ ∑ i, x i * (u - x i) * (x i - d) ^ 2 :=
      Finset.sum_nonneg fun i _ =>
        mul_nonneg (mul_nonneg (hx.1 i) (sub_nonneg.mpr (hxu i))) (sq_nonneg _)
    have hid : (∑ i, x i * (u - x i) * (x i - d) ^ 2) =
        -c + (u + 2 * d) * b - (2 * u * d + d ^ 2) * a + u * d ^ 2 := by
      calc
        _ = ∑ i, (-(x i ^ 4) + (u + 2 * d) * x i ^ 3 -
            (2 * u * d + d ^ 2) * x i ^ 2 + u * d ^ 2 * x i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.sum_neg_distrib, ← Finset.mul_sum, hx.2, mul_one, a, b, c, powerSum]
    have hc := coarse_lower_bound u (le_of_not_ge hsmall) hu1
    have hdiff : -(3 / 2) * u * (1 - u) ^ 3 ≤
        -12 * a ^ 2 + 18 * b - 6 * c / a := by
      apply (mul_le_mul_iff_right₀ ha).mp
      rw [hid] at hsum
      have he : (-12 * a ^ 2 + 18 * b - 6 * c / a +
          (3 / 2) * u * (1 - u) ^ 3) * a =
          6 * (-c + (u + 2 * d) * b - (2 * u * d + d ^ 2) * a + u * d ^ 2) := by
        dsimp [d]
        field_simp
        rw [← hu2]
        ring
      nlinarith
    exact hc.trans hdiff

private lemma universal_lower_bound (n : ℕ) (hn : 2 ≤ n) (k : Fin n → ℝ)
    (hk : ∀ i, 0 < k i) : lowerBound ≤ skewness k - kurtosis k := by
  have hx : normalizedRates k ∈ stdSimplex ℝ (Fin n) :=
    normalized_simplex (by omega) k hk
  rw [normalized_difference]
  exact simplex_lower_bound _ hx (normalized_moments hn k hk).1

private def endpointMass : ℝ := (9 - Real.sqrt 17) / 16

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
      atTop (nhds lowerBound) := by
  have hu : 0 < endpointMass := by
    have h := sharp_rates_positive 0 0
    simp only [sharpRates, ↓reduceIte, inv_pos] at h
    exact h
  have hc : ContinuousAt approximation 0 := by
    unfold approximation
    fun_prop (disch := positivity)
  have hz : Tendsto (fun m : ℕ => 1 / ((m + 1 : ℕ) : ℝ)) atTop (nhds (0 : ℝ)) :=
    (tendsto_add_atTop_iff_nat 1).mpr tendsto_one_div_atTop_nhds_zero_nat
  have he : approximation 0 = lowerBound := by
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
    dsimp [endpointMass, lowerBound]
    ring_nf
    simp only [hs, hs3, hs4]
    ring
  simpa only [Function.comp_def, ← sharp_value, Nat.cast_add, Nat.cast_one, he] using
    hc.tendsto.comp hz

/-- The exact universal lower endpoint, with sharpness over actual positive finite rates. -/
theorem result : claim := by
  refine ⟨universal_lower_bound, ?_⟩
  refine ⟨?_, ?_⟩
  · rintro s ⟨n, hn, k, hk, rfl⟩
    exact universal_lower_bound n hn k hk
  · intro b hb
    apply ge_of_tendsto' sharp_limit
    intro m
    exact hb ⟨m + 2, by omega, sharpRates m, sharp_rates_positive m, rfl⟩

end D5.S3.StatisticalMechanics.UnicyclicSkewnessMinusKurtosisLowerBound
