/- GID: D5/S3/StatisticalMechanics/UnicyclicSkewnessPlusKurtosisLowerBound
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/UnicyclicSkewnessPlusKurtosisLowerBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Ptaszyński's sharp finite-cycle lower bound for skewness plus kurtosis. -/

import D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum
import D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound

/-! Ptaszyński's sharp finite-cycle lower bound for the sum of skewness and kurtosis. -/

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

def normalizedRates {n : ℕ} (k : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹)

def p {n : ℕ} (k : Fin n → ℝ) : ℝ := powerSum n 2 (normalizedRates k)

def q {n : ℕ} (k : Fin n → ℝ) : ℝ := powerSum n 3 (normalizedRates k)

def r {n : ℕ} (k : Fin n → ℝ) : ℝ := powerSum n 4 (normalizedRates k)

private lemma normalized_sum {n : ℕ} (k : Fin n → ℝ) :
    skewness k + kurtosis k = 18 * p k ^ 2 - 22 * q k + 6 * r k / p k := by
  rw [D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness_normalized,
    D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.normalized]
  delta D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.simplexFunctional
    p q r normalizedRates
  ring

lemma normalized_moments {n : ℕ} (hn : 2 ≤ n) (k : Fin n → ℝ)
    (hk : ∀ i, 0 < k i) :
    0 < p k ∧ 0 ≤ q k ∧ q k ^ 2 ≤ p k * r k ∧ r k < p k ^ 2 := by
  have hs : 0 < powerSum n 1 (fun j => (k j)⁻¹) := by
    let i : Fin n := ⟨0, by omega⟩
    simp only [powerSum, pow_one]
    exact Finset.sum_pos' (fun j _ => (inv_pos.mpr (hk j)).le)
      ⟨i, Finset.mem_univ i, inv_pos.mpr (hk i)⟩
  have hpos : ∀ i, 0 < normalizedRates k i := by
    intro i
    exact div_pos (inv_pos.mpr (hk i)) hs
  simpa only [p, q, r] using
    (D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.moments hn
      (normalizedRates k) hpos)

private lemma reduced_form (p q r t e : ℝ) (hp : p ≠ 0)
    (hqt : q = p * t) (hre : r = p * (t ^ 2 + e)) :
    18 * p ^ 2 - 22 * q + 6 * r / p + 8 / 27 =
      18 * p ^ 2 - 22 * p * t + 6 * t ^ 2 + 6 * e + 8 / 27 := by
  rw [hqt, hre]
  field_simp
  ring

private lemma low_certificate_identity (p t e : ℝ) :
    18 * p ^ 2 - 22 * p * t + 6 * t ^ 2 + 6 * e + 8 / 27 =
      6 * e + 18 * (p - (11 / 18 : ℝ) * t) ^ 2 +
        13 / 18 * ((11 / 18 : ℝ) ^ 2 - t ^ 2) + 155 / 5832 := by
  ring

private lemma high_certificate_identity (p t e d : ℝ) (hd : d = p - t ^ 2) :
    18 * p ^ 2 - 22 * p * t + 6 * t ^ 2 + 6 * e + 8 / 27 =
      6 * e + d * (18 * d + 36 * t ^ 2 - 22 * t) +
        (t - 2 / 3) ^ 2 * (18 * t ^ 2 + 2 * t + 2 / 3) := by
  rw [hd]
  ring

private lemma low_certificate (p t e : ℝ) (he : 0 ≤ e)
    (ht0 : 0 ≤ t) (ht : t ≤ 11 / 18) :
    0 < 6 * e + 18 * (p - (11 / 18 : ℝ) * t) ^ 2 +
      13 / 18 * ((11 / 18 : ℝ) ^ 2 - t ^ 2) + 155 / 5832 := by
  have hsq : 0 ≤ (p - (11 / 18 : ℝ) * t) ^ 2 := sq_nonneg _
  have hdiff : 0 ≤ (11 / 18 : ℝ) ^ 2 - t ^ 2 := by
    have hsum : 0 ≤ (11 / 18 : ℝ) + t := by linarith
    have hdiff : 0 ≤ (11 / 18 : ℝ) - t := by linarith
    nlinarith [mul_nonneg hsum hdiff]
  nlinarith [sq_nonneg (p - (11 / 18 : ℝ) * t)]

private lemma high_certificate (t e d : ℝ) (he : 0 ≤ e) (hd : 0 < d)
    (ht : 11 / 18 ≤ t) :
    0 < 6 * e + d * (18 * d + 36 * t ^ 2 - 22 * t) +
      (t - 2 / 3) ^ 2 * (18 * t ^ 2 + 2 * t + 2 / 3) := by
  have hcoef : 0 < 18 * d + 36 * t ^ 2 - 22 * t := by
    have htcoef : 0 ≤ 36 * t ^ 2 - 22 * t := by
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ t) (by linarith)]
    linarith
  have hpoly : 0 < 18 * t ^ 2 + 2 * t + 2 / 3 := by
    nlinarith [sq_nonneg (t + 1 / 18 : ℝ)]
  have hterms : 0 ≤ d * (18 * d + 36 * t ^ 2 - 22 * t) :=
    mul_nonneg hd.le hcoef.le
  have hlast : 0 ≤ (t - 2 / 3) ^ 2 * (18 * t ^ 2 + 2 * t + 2 / 3) :=
    mul_nonneg (sq_nonneg _) hpoly.le
  nlinarith

private lemma strict_lower_bound (n : ℕ) (hn : 2 ≤ n) (k : Fin n → ℝ)
    (hk : ∀ i, 0 < k i) : lowerBound < skewness k + kurtosis k := by
  obtain ⟨hp, hq, hqr, hr⟩ := normalized_moments hn k hk
  let pp := p k
  let qq := q k
  let rr := r k
  let t := qq / pp
  let e := rr / pp - t ^ 2
  let d := pp - t ^ 2
  have hpp : 0 < pp := by simpa [pp] using hp
  have hqq : 0 ≤ qq := by simpa [qq] using hq
  have ht0 : 0 ≤ t := div_nonneg hqq hpp.le
  have he : 0 ≤ e := by
    dsimp [e, t]
    apply sub_nonneg.mpr
    apply (le_div_iff₀ hpp).2
    have hq2 : qq ^ 2 = pp ^ 2 * (qq / pp) ^ 2 := by
      field_simp (disch := positivity)
    nlinarith [hqr, hq2]
  have hqt : qq = pp * t := by
    dsimp [t]
    field_simp (disch := positivity)
  have htr : t ^ 2 < pp := by
    dsimp [t]
    rw [div_pow]
    apply (div_lt_iff₀ (sq_pos_of_pos hpp)).2
    have hpr : pp * rr < pp ^ 3 := by nlinarith [hr]
    have hqr' : qq ^ 2 < pp ^ 3 := lt_of_le_of_lt hqr hpr
    nlinarith [hqr']
  have hd : 0 < d := by
    dsimp [d]
    exact sub_pos.mpr htr
  have hre : rr = pp * (t ^ 2 + e) := by
    dsimp [e]
    field_simp (disch := positivity)
    ring
  have hred := reduced_form pp qq rr t e hpp.ne' hqt hre
  have hmain : 0 <
      18 * pp ^ 2 - 22 * qq + 6 * rr / pp + 8 / 27 := by
    by_cases ht : t ≤ 11 / 18
    · rw [hred, low_certificate_identity]
      exact low_certificate pp t e he ht0 ht
    · rw [hred, high_certificate_identity pp t e d rfl]
      exact high_certificate t e d he hd (le_of_not_ge ht)
  have hmain' : 0 < 18 * p k ^ 2 - 22 * q k + 6 * r k / p k + 8 / 27 := by
    simpa only [pp, qq, rr] using hmain
  rw [normalized_sum k]
  dsimp [lowerBound]
  linarith

private def sourceRates (m : ℕ) : Fin (m + 1) → ℝ :=
  fun i => if i = 0 then (2 * (m : ℝ))⁻¹ else 1

private lemma source_rates_positive (m : ℕ) (hm : 1 ≤ m) :
    ∀ i, 0 < sourceRates m i := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  intro i
  rw [sourceRates]
  split_ifs <;> positivity

private lemma source_power_sum (m j : ℕ) (hm : 1 ≤ m) :
    powerSum (m + 1) j (fun i => (sourceRates m i)⁻¹) =
      (2 * (m : ℝ)) ^ j + m := by
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (show m ≠ 0 by omega)
  simp only [powerSum, sourceRates, inv_pow, ite_pow, one_pow,
    Fin.sum_univ_succ, ↓reduceIte, Fin.succ_ne_zero, inv_one,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_one, mul_one, inv_inv]

private lemma source_value (m : ℕ) (hm : 1 ≤ m) :
    skewness (sourceRates m) + kurtosis (sourceRates m) + 8 / 27 =
      2 * (60 * (m : ℝ) ^ 2 - 8 * m + 1) /
        (27 * (m : ℝ) ^ 2 * (4 * m + 1)) := by
  delta D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness
    D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.kurtosis
  rw [source_power_sum m 1 hm, source_power_sum m 2 hm,
    source_power_sum m 3 hm, source_power_sum m 4 hm]
  norm_num
  field_simp
  ring

private def sourceApproximation (t : ℝ) : ℝ :=
  2 * (60 * t - 8 * t ^ 2 + t ^ 3) / (27 * (4 + t))

private lemma source_value_asymptotic (m : ℕ) (hm : 1 ≤ m) :
    skewness (sourceRates m) + kurtosis (sourceRates m) + 8 / 27 =
      sourceApproximation (1 / (m : ℝ)) := by
  rw [source_value m hm]
  dsimp [sourceApproximation]
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  field_simp (disch := positivity)

private lemma source_limit :
    Tendsto (fun m : ℕ => skewness (sourceRates (m + 1)) +
      kurtosis (sourceRates (m + 1))) atTop (nhds lowerBound) := by
  have hc : ContinuousAt sourceApproximation 0 := by
    unfold sourceApproximation
    fun_prop (disch := norm_num)
  have hz : Tendsto (fun m : ℕ => 1 / ((m + 1 : ℕ) : ℝ)) atTop (nhds (0 : ℝ)) :=
    (tendsto_add_atTop_iff_nat 1).mpr tendsto_one_div_atTop_nhds_zero_nat
  have ha : Tendsto (fun m : ℕ =>
      sourceApproximation (1 / ((m + 1 : ℕ) : ℝ))) atTop
      (nhds (0 : ℝ)) := by
    have hzero : sourceApproximation 0 = 0 := by norm_num [sourceApproximation]
    simpa only [Function.comp_def, hzero] using hc.tendsto.comp hz
  have hf : Tendsto (fun m : ℕ =>
      sourceApproximation (1 / ((m + 1 : ℕ) : ℝ)) - 8 / 27)
      atTop (nhds ((0 : ℝ) - 8 / 27)) := ha.sub tendsto_const_nhds
  convert hf using 1
  · funext m
    have hval := source_value_asymptotic (m + 1) (by omega)
    linarith
  · dsimp [lowerBound]
    ring_nf

private lemma greatest_lower_bound :
    IsGLB {s : ℝ | ∃ n : ℕ, 2 ≤ n ∧ ∃ k : Fin n → ℝ,
      (∀ i, 0 < k i) ∧ s = skewness k + kurtosis k} lowerBound := by
  refine ⟨?_, ?_⟩
  · rintro s ⟨n, hn, k, hk, rfl⟩
    exact (strict_lower_bound n hn k hk).le
  · intro b hb
    apply ge_of_tendsto' source_limit
    intro m
    apply hb
    refine ⟨m + 2, by omega, sourceRates (m + 1),
      source_rates_positive (m + 1) (by omega), rfl⟩

theorem result : claim := by
  exact ⟨strict_lower_bound, greatest_lower_bound⟩

end D5.S3.StatisticalMechanics.UnicyclicSkewnessPlusKurtosisLowerBound
