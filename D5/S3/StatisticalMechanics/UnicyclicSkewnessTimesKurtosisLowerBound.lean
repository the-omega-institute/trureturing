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

private lemma lowerBound_lt_three_eighty : lowerBound < -(3 / 80 : ℝ) := by
  have h := source_le_lower_bound (1 / 4) (by norm_num)
  dsimp [sourceExpression] at h
  norm_num at h ⊢
  linarith

private lemma f_strict_scale (t z : ℝ) (ht : 0 < t) (htz : t < z)
    (hz : 0 < z) (hneg : z * (3 * z - 2) * (15 * z ^ 2 - 20 * z + 6) < 0) :
    t ^ 4 * (z * (3 * z - 2) * (15 * z ^ 2 - 20 * z + 6)) > f z := by
  have ht4 : t ^ 4 < z ^ 4 := pow_lt_pow_left₀ htz (le_of_lt ht) (by norm_num)
  have hmul := mul_lt_mul_of_neg_right ht4 hneg
  dsimp [f]
  convert hmul using 1 <;> ring

private lemma normalized_product {n : ℕ} (k : Fin n → ℝ) :
    skewness k * kurtosis k =
      (3 * p k ^ 2 - 2 * q k) * (15 * p k ^ 2 - 20 * q k + 6 * r k / p k) := by
  rw [D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness_normalized,
    D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.normalized]
  delta D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.simplexFunctional
    p q r normalizedRates
  ring

private lemma product_nonnegative (p q r : ℝ) (hp : 0 < p)
    (hprod : 0 ≤ (3 * p ^ 2 - 2 * q) * (15 * p ^ 2 - 20 * q + 6 * r / p)) :
    lowerBound < (3 * p ^ 2 - 2 * q) * (15 * p ^ 2 - 20 * q + 6 * r / p) := by
  exact lt_of_lt_of_le lowerBound_negative hprod

private lemma product_skew_negative (p q r : ℝ) (hp : 0 < p) (hq : 0 ≤ q)
    (hqr : q ^ 2 ≤ p * r) (hr : r < p ^ 2)
    (hskew : 3 * p ^ 2 - 2 * q < 0)
    (hkurt : 0 < 15 * p ^ 2 - 20 * q + 6 * r / p)
    (hskew_lower : -(1 / 16 : ℝ) ≤ 3 * p ^ 2 - 2 * q) :
    lowerBound < (3 * p ^ 2 - 2 * q) * (15 * p ^ 2 - 20 * q + 6 * r / p) := by
  have hdiv : r / p < p := by
    apply (div_lt_iff₀ hp).2
    simpa [pow_two] using hr
  have hq : 3 * p ^ 2 < 2 * q := by linarith
  have hdiv6 : 6 * r / p < 6 * p := by
    calc
      6 * r / p = 6 * (r / p) := by ring
      _ < 6 * p := by nlinarith [hdiv]
  have hkupper0 : 15 * p ^ 2 - 20 * q + 6 * r / p < 6 * p - 15 * p ^ 2 := by
    nlinarith [hdiv6]
  have hkupper : 15 * p ^ 2 - 20 * q + 6 * r / p < 3 / 5 := by
    nlinarith [sq_nonneg (5 * p - 1)]
  have hprod : -(3 / 80 : ℝ) <
      (3 * p ^ 2 - 2 * q) * (15 * p ^ 2 - 20 * q + 6 * r / p) := by
    have hmul := mul_le_mul_of_nonneg_right hskew_lower (le_of_lt hkurt)
    have hscaled : -(15 * p ^ 2 - 20 * q + 6 * r / p) / 16 ≤
        (3 * p ^ 2 - 2 * q) * (15 * p ^ 2 - 20 * q + 6 * r / p) := by
      nlinarith [hmul]
    nlinarith
  exact lt_trans lowerBound_lt_three_eighty hprod

private lemma product_kurtosis_negative (p q r : ℝ) (hp : 0 < p) (hq : 0 ≤ q)
    (hqr : q ^ 2 ≤ p * r) (hr : r < p ^ 2)
    (hpq : p ^ 2 ≤ q)
    (hskew : 0 < 3 * p ^ 2 - 2 * q)
    (hkurt : 15 * p ^ 2 - 20 * q + 6 * r / p < 0) :
    lowerBound < (3 * p ^ 2 - 2 * q) * (15 * p ^ 2 - 20 * q + 6 * r / p) := by
  have hp2 : 0 < p ^ 2 := sq_pos_of_pos hp
  have hqpos : 0 < q := lt_of_lt_of_le hp2 hpq
  let t := q / p
  let z := p ^ 2 / q
  have ht : 0 < t := div_pos hqpos hp
  have hz : 0 < z := div_pos hp2 hqpos
  have hq2p3 : q ^ 2 < p ^ 3 := by
    have hpr : p * r < p ^ 3 := by
      nlinarith [hr]
    exact lt_of_le_of_lt hqr hpr
  have htz : t < z := by
    dsimp [t, z]
    apply (div_lt_div_iff₀ hp hqpos).2
    simpa [pow_two, pow_three, mul_assoc, mul_comm, mul_left_comm] using hq2p3
  have hz1 : z ≤ 1 := by
    dsimp [z]
    apply (div_le_iff₀ hqpos).2
    simpa only [one_mul] using hpq
  have hpt : p = t * z := by
    dsimp [t, z]
    field_simp
  have hqt : q = t ^ 2 * z := by
    dsimp [t, z]
    field_simp
  have ht2r : t ^ 2 ≤ r / p := by
    dsimp [t]
    apply (le_div_iff₀ hp).2
    have heq : (q / p) ^ 2 * p = q ^ 2 / p := by field_simp
    rw [heq]
    apply (div_le_iff₀ hp).2
    simpa [mul_comm] using hqr
  have hk0 : 15 * p ^ 2 - 20 * q + 6 * t ^ 2 ≤
      15 * p ^ 2 - 20 * q + 6 * r / p := by
    have h6 := mul_le_mul_of_nonneg_left ht2r (by norm_num : (0 : ℝ) ≤ 6)
    have h6' : 6 * t ^ 2 ≤ 6 * r / p := by
      calc
        6 * t ^ 2 ≤ 6 * (r / p) := h6
        _ = 6 * r / p := by ring
    linarith
  have hk0neg : 15 * p ^ 2 - 20 * q + 6 * t ^ 2 < 0 :=
    lt_of_le_of_lt hk0 hkurt
  have hpolyneg : z * (3 * z - 2) * (15 * z ^ 2 - 20 * z + 6) < 0 := by
    have hid : 15 * p ^ 2 - 20 * q + 6 * t ^ 2 =
        t ^ 2 * (15 * z ^ 2 - 20 * z + 6) := by
      rw [hpt, hqt]
      ring
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
    have hsid : 3 * p ^ 2 - 2 * q = (t ^ 2 * z) * (3 * z - 2) := by
      rw [hpt, hqt]
      ring
    rw [hsid] at hskew
    have htzpos : 0 < t ^ 2 * z := mul_pos ht2 hz
    have hcoef : 0 < 3 * z - 2 :=
      (mul_pos_iff_of_pos_left htzpos).mp hskew
    have hqz : 0 < z * (3 * z - 2) := mul_pos hz hcoef
    rw [hid] at hk0neg
    have hpoly : 15 * z ^ 2 - 20 * z + 6 < 0 := by
      by_contra hn
      have hnon : 0 ≤ 15 * z ^ 2 - 20 * z + 6 := le_of_not_gt hn
      exact (not_lt_of_ge (mul_nonneg (sq_pos_of_pos ht).le hnon)) hk0neg
    nlinarith [hqz, hpoly]
  have hzlt : z < 1 := by
    by_contra hn
    have hzeq : z = 1 := le_antisymm hz1 (le_of_not_gt hn)
    rw [hzeq] at hpolyneg
    norm_num at hpolyneg
  have hcompare :
      t ^ 4 * (z * (3 * z - 2) * (15 * z ^ 2 - 20 * z + 6)) ≤
        (3 * p ^ 2 - 2 * q) *
          (15 * p ^ 2 - 20 * q + 6 * r / p) := by
    have hmul := mul_le_mul_of_nonneg_left hk0 (le_of_lt hskew)
    have hid : (3 * p ^ 2 - 2 * q) *
          (15 * p ^ 2 - 20 * q + 6 * t ^ 2) =
        t ^ 4 * (z * (3 * z - 2) * (15 * z ^ 2 - 20 * z + 6)) := by
      rw [hpt, hqt]
      ring
    exact hid ▸ hmul
  have hscale := f_strict_scale t z ht htz hz hpolyneg
  have hflb := f_lower_bound z hz hzlt
  exact lt_of_le_of_lt hflb (lt_of_lt_of_le hscale hcompare)

private lemma second_sq_le_third {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : powerSum n 1 x = 1) :
    (powerSum n 2 x) ^ 2 ≤ powerSum n 3 x := by
  have hnon : 0 ≤ ∑ i, x i * (x i - powerSum n 2 x) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hx i) (sq_nonneg _)
  have hid : (∑ i, x i * (x i - powerSum n 2 x) ^ 2) =
      powerSum n 3 x - (powerSum n 2 x) ^ 2 := by
    calc
      _ = ∑ i, (x i ^ 3 - 2 * powerSum n 2 x * x i ^ 2 +
          (powerSum n 2 x) ^ 2 * x i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = powerSum n 3 x - (powerSum n 2 x) ^ 2 := by
        simp only [powerSum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
          ← Finset.sum_mul, ← Finset.mul_sum]
        have hsum' : (∑ i, x i) = 1 := by simpa [powerSum] using hsum
        rw [hsum']
        ring_nf
  rw [hid] at hnon
  linarith

private lemma strict_lower_bound (n : ℕ) (hn : 2 ≤ n) (k : Fin n → ℝ)
    (hk : ∀ i, 0 < k i) : lowerBound < skewness k * kurtosis k := by
  obtain ⟨hp, hq, hqr, hr⟩ := normalized_moments hn k hk
  have hs : 0 < powerSum n 1 (fun i => (k i)⁻¹) := by
    let i : Fin n := ⟨0, by omega⟩
    simp only [powerSum, pow_one]
    exact Finset.sum_pos' (fun j _ => (inv_pos.mpr (hk j)).le)
      ⟨i, Finset.mem_univ i, inv_pos.mpr (hk i)⟩
  have hxpos : ∀ i, 0 < normalizedRates k i := by
    intro i
    exact div_pos (inv_pos.mpr (hk i)) hs
  have hs' : 0 < ∑ i, (k i)⁻¹ := by simpa [powerSum] using hs
  have hsum : powerSum n 1 (normalizedRates k) = 1 := by
    dsimp [powerSum, normalizedRates]
    simp only [pow_one]
    rw [← Finset.sum_div]
    field_simp [ne_of_gt hs']
  have hpq : p k ^ 2 ≤ q k := by
    simpa only [p, q] using
      second_sq_le_third (normalizedRates k) (fun i => (hxpos i).le) hsum
  have hskew_lower : -(1 / 16 : ℝ) ≤ 3 * p k ^ 2 - 2 * q k := by
    have hmin := (D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.result n hn).2
      ⟨k, hk, rfl⟩
    have hval : -(1 / 16 : ℝ) ≤
        D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.minimumValue n := by
      dsimp [D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.minimumValue]
      have hn1 : 0 < (n : ℝ) - 1 := by
        have : (2 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      have hd : 0 < 16 * ((n : ℝ) - 1) ^ 2 := by positivity
      apply (le_div_iff₀ hd).2
      have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
    rw [D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness_normalized] at hmin
    change D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.minimumValue n ≤
      3 * p k ^ 2 - 2 * q k at hmin
    exact le_trans hval hmin
  have hprod := normalized_product k
  rw [hprod]
  by_cases hnonneg : 0 ≤ (3 * p k ^ 2 - 2 * q k) *
      (15 * p k ^ 2 - 20 * q k + 6 * r k / p k)
  · exact product_nonnegative (p k) (q k) (r k) hp hnonneg
  have hneg : (3 * p k ^ 2 - 2 * q k) *
      (15 * p k ^ 2 - 20 * q k + 6 * r k / p k) < 0 := lt_of_not_ge hnonneg
  by_cases hsk : 3 * p k ^ 2 - 2 * q k < 0
  · have hkpos : 0 < 15 * p k ^ 2 - 20 * q k + 6 * r k / p k := by
      by_contra h
      have hk0 : 15 * p k ^ 2 - 20 * q k + 6 * r k / p k ≤ 0 := le_of_not_gt h
      exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos hsk.le hk0)) hneg
    exact product_skew_negative (p k) (q k) (r k) hp hq hqr hr hsk hkpos hskew_lower
  · have hsknonneg : 0 ≤ 3 * p k ^ 2 - 2 * q k := le_of_not_gt hsk
    have hskpos : 0 < 3 * p k ^ 2 - 2 * q k := by
      by_contra h
      have hsk0 : 3 * p k ^ 2 - 2 * q k ≤ 0 := le_of_not_gt h
      have hzero : 3 * p k ^ 2 - 2 * q k = 0 := le_antisymm hsk0 hsknonneg
      rw [hzero] at hneg
      norm_num at hneg
    have hkneg : 15 * p k ^ 2 - 20 * q k + 6 * r k / p k < 0 := by
      by_contra h
      have hk0 : 0 ≤ 15 * p k ^ 2 - 20 * q k + 6 * r k / p k := le_of_not_gt h
      have hnon : 0 ≤ (3 * p k ^ 2 - 2 * q k) *
          (15 * p k ^ 2 - 20 * q k + 6 * r k / p k) :=
        mul_nonneg hsknonneg hk0
      exact (not_lt_of_ge hnon) hneg
    exact product_kurtosis_negative (p k) (q k) (r k) hp hq hqr hr hpq hskpos hkneg

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
