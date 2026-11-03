/- GID: D5/S3/StatisticalMechanics/UnicyclicSkewnessTimesKurtosisLowerBound
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/UnicyclicSkewnessTimesKurtosisLowerBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Ptaszyński's sharp lower bound for unidirectional unicyclic S times K. -/

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
  have h1 : 0 < 1 + A := add_pos zero_lt_one hA0
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

private lemma lowerBound_lt_three_eighty : lowerBound < -(3 / 80 : ℝ) := by
  have h := source_le_lower_bound (1 / 4) (by norm_num)
  dsimp [sourceExpression] at h
  norm_num at h ⊢
  linarith

private lemma lowerBound_negative : lowerBound < 0 :=
  lt_trans lowerBound_lt_three_eighty (by norm_num)

private lemma f_strict_scale (t z : ℝ) (ht : 0 < t) (htz : t < z)
    (hneg : z * (3 * z - 2) * (15 * z ^ 2 - 20 * z + 6) < 0) :
    t ^ 4 * (z * (3 * z - 2) * (15 * z ^ 2 - 20 * z + 6)) > f z := by
  have ht4 : t ^ 4 < z ^ 4 := pow_lt_pow_left₀ htz (le_of_lt ht) (by norm_num)
  have hmul := mul_lt_mul_of_neg_right ht4 hneg
  dsimp [f]
  convert hmul using 1; ring

private lemma normalized_product {n : ℕ} (k : Fin n → ℝ) :
    skewness k * kurtosis k =
      (3 * p k ^ 2 - 2 * q k) * (15 * p k ^ 2 - 20 * q k + 6 * r k / p k) := by
  rw [D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness_normalized,
    D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.normalized]
  delta D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.simplexFunctional
    p q r normalizedRates
  ring

private lemma product_nonnegative (p q r : ℝ)
    (hprod : 0 ≤ (3 * p ^ 2 - 2 * q) * (15 * p ^ 2 - 20 * q + 6 * r / p)) :
    lowerBound < (3 * p ^ 2 - 2 * q) * (15 * p ^ 2 - 20 * q + 6 * r / p) := by
  exact lt_of_lt_of_le lowerBound_negative hprod

private lemma product_skew_negative (p q r : ℝ) (hp : 0 < p) (hr : r < p ^ 2)
    (hskew : 3 * p ^ 2 - 2 * q < 0)
    (hkurt : 0 < 15 * p ^ 2 - 20 * q + 6 * r / p)
    (hskew_lower : -(1 / 16 : ℝ) ≤ 3 * p ^ 2 - 2 * q) :
    lowerBound < (3 * p ^ 2 - 2 * q) * (15 * p ^ 2 - 20 * q + 6 * r / p) := by
  have hdiv : r / p < p := by
    apply (div_lt_iff₀ hp).2
    simpa [pow_two] using hr
  have hq : 3 * p ^ 2 < 2 * q := sub_neg.mp hskew
  have hdiv6 : 6 * r / p < 6 * p := by
    simpa only [mul_div_assoc] using
      mul_lt_mul_of_pos_left hdiv (by norm_num : (0 : ℝ) < 6)
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

private lemma product_kurtosis_negative (p q r : ℝ) (hp : 0 < p)
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
      simpa only [pow_succ', mul_assoc] using mul_lt_mul_of_pos_left hr hp
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
    symm
    rw [div_mul_div_cancel₀' hqpos.ne', pow_two, mul_div_cancel_right₀ _ hp.ne']
  have hqt : q = t ^ 2 * z := by
    dsimp [t, z]
    symm
    rw [div_pow, div_mul_div_cancel₀ (pow_ne_zero 2 hp.ne'), pow_two,
      mul_div_cancel_right₀ _ hqpos.ne']
  have ht2r : t ^ 2 ≤ r / p := by
    dsimp [t]
    rw [div_pow]
    apply (div_le_div_iff₀ (sq_pos_of_pos hp) hp).2
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_right hqr hp.le
  have hk0 : 15 * p ^ 2 - 20 * q + 6 * t ^ 2 ≤
      15 * p ^ 2 - 20 * q + 6 * r / p := by
    apply add_le_add le_rfl
    simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_left ht2r (by norm_num : (0 : ℝ) ≤ 6)
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
    have hpoly : 15 * z ^ 2 - 20 * z + 6 < 0 :=
      neg_of_mul_neg_right hk0neg ht2.le
    exact mul_neg_of_pos_of_neg hqz hpoly
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
  have hscale := f_strict_scale t z ht htz hpolyneg
  have hflb := f_lower_bound z hz hzlt
  exact lt_of_le_of_lt hflb (lt_of_lt_of_le hscale hcompare)

private lemma second_sq_le_third {n : ℕ} (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : powerSum n 1 x = 1) :
    (powerSum n 2 x) ^ 2 ≤ powerSum n 3 x := by
  have hsum' : (∑ i, x i) = 1 := by simpa [powerSum] using hsum
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i => x i ^ 2) (f := x) (g := fun i => x i ^ 3)
    (fun i _ => hx i) (fun i _ => pow_nonneg (hx i) 3)
    (fun i _ => le_of_eq (by ring))
  simpa only [powerSum, hsum', one_mul] using hcs

private lemma strict_lower_bound (n : ℕ) (hn : 2 ≤ n) (k : Fin n → ℝ)
    (hk : ∀ i, 0 < k i) : lowerBound < skewness k * kurtosis k := by
  obtain ⟨hp, _, hqr, hr⟩ := normalized_moments hn k hk
  have hx := D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.normalized_simplex
    (by omega) k hk
  have hpq : p k ^ 2 ≤ q k := by
    simpa only [p, q] using
      second_sq_le_third (normalizedRates k) hx.1
        (by
          change (∑ i, ((k i)⁻¹ / powerSum n 1 (fun j => (k j)⁻¹)) ^ 1) = 1
          simpa only [pow_one] using hx.2)
  have hskew_lower : -(1 / 16 : ℝ) ≤ 3 * p k ^ 2 - 2 * q k := by
    have hmin := (D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.result n hn).2
      ⟨k, hk, rfl⟩
    have hval : -(1 / 16 : ℝ) ≤
        D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.minimumValue n := by
      dsimp [D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.minimumValue]
      have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hn1 : 0 < (n : ℝ) - 1 :=
        sub_pos.mpr (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) hnreal)
      have hd : 0 < 16 * ((n : ℝ) - 1) ^ 2 := by positivity
      apply (le_div_iff₀ hd).2
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
    rw [D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness_normalized] at hmin
    change D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.minimumValue n ≤
      3 * p k ^ 2 - 2 * q k at hmin
    exact le_trans hval hmin
  have hprod := normalized_product k
  rw [hprod]
  by_cases hnonneg : 0 ≤ (3 * p k ^ 2 - 2 * q k) *
      (15 * p k ^ 2 - 20 * q k + 6 * r k / p k)
  · exact product_nonnegative (p k) (q k) (r k) hnonneg
  have hneg : (3 * p k ^ 2 - 2 * q k) *
      (15 * p k ^ 2 - 20 * q k + 6 * r k / p k) < 0 := lt_of_not_ge hnonneg
  by_cases hsk : 3 * p k ^ 2 - 2 * q k < 0
  · have hkpos : 0 < 15 * p k ^ 2 - 20 * q k + 6 * r k / p k :=
      pos_of_mul_neg_right hneg hsk.le
    exact product_skew_negative (p k) (q k) (r k) hp hr hsk hkpos hskew_lower
  · have hsknonneg : 0 ≤ 3 * p k ^ 2 - 2 * q k := le_of_not_gt hsk
    have hkneg : 15 * p k ^ 2 - 20 * q k + 6 * r k / p k < 0 :=
      neg_of_mul_neg_right hneg hsknonneg
    have hskpos : 0 < 3 * p k ^ 2 - 2 * q k := pos_of_mul_neg_left hneg hkneg.le
    exact product_kurtosis_negative (p k) (q k) (r k) hp hqr hr hpq hskpos hkneg

private def sourceRates (u : ℝ) (m : ℕ) : Fin (m + 1) → ℝ :=
  fun i => if i = 0 then (1 - u) / (m * u) else 1

private lemma source_rates_positive (u : ℝ) (m : ℕ) (hu : 0 < u) (hu1 : u < 1)
    (hm : 1 ≤ m) : ∀ i, 0 < sourceRates u m i := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  intro i
  rw [sourceRates.eq_1]
  split_ifs
  · positivity
  · norm_num

private lemma source_power_sum (u : ℝ) (m j : ℕ) :
    powerSum (m + 1) j (fun i => (sourceRates u m i)⁻¹) =
      ((m : ℝ) * u / (1 - u)) ^ j + m := by
  simp only [powerSum, sourceRates.eq_1, inv_pow, ite_pow, one_pow,
    Fin.sum_univ_succ, ↓reduceIte, Fin.succ_ne_zero, inv_one, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  rw [← inv_pow, inv_div]

private def sourceApproximation (u v : ℝ) : ℝ :=
  (3 * (u ^ 2 + (1 - u) ^ 2 * v) ^ 2 -
      2 * (u ^ 3 + (1 - u) ^ 3 * v ^ 2)) *
    (15 * (u ^ 2 + (1 - u) ^ 2 * v) ^ 2 -
      20 * (u ^ 3 + (1 - u) ^ 3 * v ^ 2) +
      6 * (u ^ 4 + (1 - u) ^ 4 * v ^ 3) /
        (u ^ 2 + (1 - u) ^ 2 * v))

private lemma source_value (u : ℝ) (m : ℕ) (hu : 0 < u) (hu1 : u < 1)
    (hm : 1 ≤ m) :
    skewness (sourceRates u m) * kurtosis (sourceRates u m) =
      sourceApproximation u (1 / (m : ℝ)) := by
  have hs (j : ℕ) := source_power_sum u m j
  delta D5.S3.StatisticalMechanics.UnicyclicSkewnessMinimum.skewness
    D5.S3.StatisticalMechanics.UnicyclicKurtosisLowerBound.kurtosis
    sourceApproximation
  rw [hs 1, hs 2, hs 3, hs 4]
  simp only [pow_one]
  field_simp
  ring

private lemma source_limit (u : ℝ) (hu : 0 < u) (hu1 : u < 1) :
    Tendsto (fun m : ℕ => skewness (sourceRates u (m + 1)) *
      kurtosis (sourceRates u (m + 1))) atTop (nhds (f u)) := by
  have hc : ContinuousAt (sourceApproximation u) 0 := by
    unfold sourceApproximation
    fun_prop (disch := positivity)
  have hz : Tendsto (fun m : ℕ => 1 / ((m + 1 : ℕ) : ℝ)) atTop
      (nhds (0 : ℝ)) :=
    (tendsto_add_atTop_iff_nat 1).mpr tendsto_one_div_atTop_nhds_zero_nat
  have ha := hc.tendsto.comp hz
  have hzero : sourceApproximation u 0 = f u := by
    dsimp [sourceApproximation, f]
    field_simp [ne_of_gt hu]
    ring_nf
  have heq : (fun m : ℕ => skewness (sourceRates u (m + 1)) *
      kurtosis (sourceRates u (m + 1))) =
      (fun m : ℕ => sourceApproximation u (1 / ((m + 1 : ℕ) : ℝ))) := by
    funext m
    exact source_value u (m + 1) hu hu1 (by omega)
  rw [heq]
  simpa only [Function.comp_def, hzero] using ha

private lemma constant_minimum :
    ∃ u : ℝ, 0 < u ∧ u < 1 ∧ f u = lowerBound := by
  have hc : Continuous f := by unfold f; fun_prop
  obtain ⟨u, hu, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Set.Icc (0 : ℝ) 1).Nonempty from ⟨0, by norm_num⟩) hc.continuousOn
  have hneg : f u < 0 := by
    have h := hmin (show (4 / 5 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)
    norm_num [f.eq_1] at h ⊢
    linarith
  have hu0 : 0 < u := by
    by_contra h
    have heq : u = 0 := le_antisymm (le_of_not_gt h) hu.1
    rw [heq] at hneg
    norm_num [f.eq_1] at hneg
  have hu1 : u < 1 := by
    by_contra h
    have heq : u = 1 := le_antisymm hu.2 (le_of_not_gt h)
    rw [heq] at hneg
    norm_num [f.eq_1] at hneg
  refine ⟨u, hu0, hu1, le_antisymm ?_ (f_lower_bound u hu0 hu1)⟩
  change f u ≤ sInf (sourceExpression '' Set.Ioi (0 : ℝ))
  apply le_csInf (show (sourceExpression '' Set.Ioi (0 : ℝ)).Nonempty from
    ⟨sourceExpression 1, ⟨1, by norm_num, rfl⟩⟩)
  rintro y ⟨A, hA, rfl⟩
  have hA0 : 0 < A := hA
  let v : ℝ := 1 / (1 + A)
  have hA1 : 0 < 1 + A := add_pos zero_lt_one hA0
  have hv : 0 < v := by dsimp [v]; positivity
  have hv1 : v < 1 := by
    dsimp [v]
    exact (div_lt_one hA1).2 (lt_add_of_pos_right 1 hA0)
  have hAv : (1 - v) / v = A := by
    dsimp [v]
    field_simp
    ring
  rw [← hAv, source_expression_eq_f v hv hv1]
  exact hmin ⟨hv.le, hv1.le⟩

private lemma greatest_lower_bound :
    IsGLB {s : ℝ | ∃ n : ℕ, 2 ≤ n ∧ ∃ k : Fin n → ℝ,
      (∀ i, 0 < k i) ∧ s = skewness k * kurtosis k} lowerBound := by
  refine ⟨?_, ?_⟩
  · rintro s ⟨n, hn, k, hk, rfl⟩
    exact (strict_lower_bound n hn k hk).le
  · intro b hb
    obtain ⟨u, hu, hu1, hmin⟩ := constant_minimum
    have hlim := source_limit u hu hu1
    rw [hmin] at hlim
    apply ge_of_tendsto' hlim
    intro m
    exact hb ⟨m + 2, by omega, sourceRates u (m + 1),
      source_rates_positive u (m + 1) hu hu1 (by omega), rfl⟩

theorem result : claim := by
  exact ⟨strict_lower_bound, greatest_lower_bound⟩

end D5.S3.StatisticalMechanics.UnicyclicSkewnessTimesKurtosisLowerBound
