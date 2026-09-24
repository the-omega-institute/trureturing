/- GID: D5/S0/FiniteGeometry/SylvesterSimplexEhrhartRootContributionLowSupportBound
   generality: G
   mirror-B: D5/B/S0/FiniteGeometry/SylvesterSimplexEhrhartRootContributionLowSupportBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pointwise bound for nontrivial roots of support one through three. -/

import D5.S0.FiniteGeometry.SylvesterSimplexEhrhartRootContributionBound

noncomputable section

namespace D5.S0.FiniteGeometry.SylvesterSimplexEhrhartRootContributionLowSupportBound

open scoped BigOperators

open D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity

open D5.S0.FiniteGeometry.SylvesterSimplexEhrhartRootContributionBound

open private rootLocalCoordinate_pow_partitionWeight rootDenominatorFactor
  rootVanishingQuotient sourceLocalRegularDenominator sourceLocalRegularInverse
  sourceLocalRegularInverse_constantCoeff sourceVanishingFactors
  sourceExponentialLocalJet sourceLocalRootContributionPolynomial
  sourceLocalRootContributionPolynomial_target_coeff sourcePoleOrder
  sourcePoleOrder_add_support_card sourceRootSupport from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartCoefficient

open private baseWeight baseWeight_last base_axisScale_dvd_mass sylvester_pos
  sylvester_sub_one_eq_prod two_le_sylvester from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity

open private partitionWeight partitionWeight_pos partitionWeight_dvd_period from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartSamples

private lemma sylvester_quotient_sum_for_root_bound (m : ℕ) (hm : 1 ≤ m) : ∑ i ∈ Finset.range m,
        (∏ j ∈ Finset.range m, sylvester (j + 1)) / sylvester (i + 1) =
      (∏ j ∈ Finset.range m, sylvester (j + 1)) - 1 := by
  induction m, hm using Nat.le_induction with
  | base => simp [sylvester]
  | succ m hm ih =>
    let P := ∏ j ∈ Finset.range m, sylvester (j + 1)
    let q := sylvester (m + 1)
    have hP : P = q - 1 := by
      dsimp [P, q]
      rw [sylvester_sub_one_eq_prod (m + 1) (by omega), Finset.prod_range_succ']
      simp [sylvester]
    have hd (i : ℕ) (hi : i ∈ Finset.range m) : sylvester (i + 1) ∣ P :=
      Finset.dvd_prod_of_mem _ hi
    have hiP : (∑ i ∈ Finset.range m, P / sylvester (i + 1)) = P - 1 := by
      simpa [P] using ih
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    change (∑ i ∈ Finset.range m, P * q / sylvester (i + 1)) + P * q / q = P * q - 1
    rw [show (∑ i ∈ Finset.range m, P * q / sylvester (i + 1)) =
        (∑ i ∈ Finset.range m, P / sylvester (i + 1)) * q by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      simpa [Nat.mul_comm] using Nat.mul_div_assoc q (hd i hi), hiP,
      Nat.mul_div_left P (sylvester_pos _)]
    have hPpos : 0 < P := Finset.prod_pos fun i hi => sylvester_pos _
    apply Nat.eq_sub_of_add_eq
    rw [← show P + 1 = q by omega, ← show P - 1 + 1 = P by omega]
    rw [show P - 1 + 1 - 1 = P - 1 by omega]
    ring

private def rf (a b : ℂ) : PowerSeries ℂ := (1 : PowerSeries ℂ) -
    PowerSeries.C a * PowerSeries.rescale (-b) (PowerSeries.exp ℂ)
private def nf (a b : ℂ) : PowerSeries ℂ := PowerSeries.C (1 - a) * (rf a b)⁻¹
private def vq (b : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun k => PowerSeries.coeff (k + 1) (rf 1 b)
private def vf (b : ℂ) : PowerSeries ℂ := PowerSeries.C b * (vq b)⁻¹

private lemma vf_coeff (b : ℂ) (hb : b ≠ 0) : PowerSeries.coeff 0 (vf b) = 1 ∧
      PowerSeries.coeff 1 (vf b) = b / 2 ∧
      PowerSeries.coeff 2 (vf b) = b ^ 2 / 12 ∧
      PowerSeries.coeff 3 (vf b) = 0 := by
  have hcoeff2 (f g : PowerSeries ℂ) : PowerSeries.coeff 2 (f * g) =
        PowerSeries.coeff 0 f * PowerSeries.coeff 2 g +
        PowerSeries.coeff 1 f * PowerSeries.coeff 1 g +
        PowerSeries.coeff 2 f * PowerSeries.coeff 0 g := by
    rw [PowerSeries.coeff_mul]
    norm_num [Finset.antidiagonal]
    ring
  have hcoeff3 (f g : PowerSeries ℂ) : PowerSeries.coeff 3 (f * g) =
        PowerSeries.coeff 0 f * PowerSeries.coeff 3 g +
        PowerSeries.coeff 1 f * PowerSeries.coeff 2 g +
        PowerSeries.coeff 2 f * PowerSeries.coeff 1 g +
        PowerSeries.coeff 3 f * PowerSeries.coeff 0 g := by
    rw [PowerSeries.coeff_mul]
    norm_num [Finset.antidiagonal]
    ring
  have hq0 : PowerSeries.constantCoeff (vq b) = b := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [vq, rf, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
  have hmul : vf b * vq b = PowerSeries.C b := by
    dsimp [vf]
    rw [mul_assoc, PowerSeries.inv_mul_cancel]
    · simp
    · simpa [hq0] using hb
  have h0 := congrArg (PowerSeries.coeff 0) hmul
  have h1 := congrArg (PowerSeries.coeff 1) hmul
  have h2 := congrArg (PowerSeries.coeff 2) hmul
  have h3 := congrArg (PowerSeries.coeff 3) hmul
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] at h0
  rw [PowerSeries.coeff_one_mul] at h1
  rw [hcoeff2] at h2
  rw [hcoeff3] at h3
  simp [vq, rf, PowerSeries.coeff_rescale, PowerSeries.coeff_exp] at h0 h1 h2 h3
  have hv0 : PowerSeries.constantCoeff (vf b) = 1 := by
    apply mul_right_cancel₀ hb
    simpa [hq0] using h0
  have hv1 : PowerSeries.coeff 1 (vf b) = b / 2 := by
    apply mul_right_cancel₀ hb
    rw [hv0] at h1
    linear_combination h1
  have hv2 : PowerSeries.coeff 2 (vf b) = b ^ 2 / 12 := by
    apply mul_right_cancel₀ hb
    rw [hv0, hv1] at h2
    linear_combination h2
  have hv3 : PowerSeries.coeff 3 (vf b) = 0 := by
    apply mul_right_cancel₀ hb
    rw [hv0, hv1, hv2] at h3
    linear_combination h3
  exact ⟨by simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hv0, hv1, hv2, hv3⟩

private lemma nf_coeff (a b : ℂ) (ha : a ≠ 1) : PowerSeries.coeff 0 (nf a b) = 1 ∧
      PowerSeries.coeff 1 (nf a b) = -(a / (1 - a)) * b ∧
      PowerSeries.coeff 2 (nf a b) = (a / (1 - a)) ^ 2 * b ^ 2 + (a / (1 - a)) * b ^ 2 / 2 ∧
      PowerSeries.coeff 3 (nf a b) = -((a / (1 - a)) ^ 3 * b ^ 3 +
        (a / (1 - a)) ^ 2 * b ^ 3 + (a / (1 - a)) * b ^ 3 / 6) := by
  have hexp0 : PowerSeries.constantCoeff
      (PowerSeries.rescale (-b) (PowerSeries.exp ℂ)) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_rescale, pow_zero, one_mul, PowerSeries.coeff_exp]
    norm_num
  have hcoeff2 (f g : PowerSeries ℂ) : PowerSeries.coeff 2 (f * g) =
        PowerSeries.coeff 0 f * PowerSeries.coeff 2 g +
        PowerSeries.coeff 1 f * PowerSeries.coeff 1 g +
        PowerSeries.coeff 2 f * PowerSeries.coeff 0 g := by
    rw [PowerSeries.coeff_mul]
    norm_num [Finset.antidiagonal]
    ring
  have hcoeff3 (f g : PowerSeries ℂ) : PowerSeries.coeff 3 (f * g) =
        PowerSeries.coeff 0 f * PowerSeries.coeff 3 g +
        PowerSeries.coeff 1 f * PowerSeries.coeff 2 g +
        PowerSeries.coeff 2 f * PowerSeries.coeff 1 g +
        PowerSeries.coeff 3 f * PowerSeries.coeff 0 g := by
    rw [PowerSeries.coeff_mul]
    norm_num [Finset.antidiagonal]
    ring
  have hc : (1 - a : ℂ) ≠ 0 := sub_ne_zero.mpr ha.symm
  have hconst : PowerSeries.constantCoeff (rf a b) = 1 - a := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [rf, hexp0]
  have hmul : nf a b * rf a b = PowerSeries.C (1 - a) := by
    dsimp [nf]
    rw [mul_assoc, PowerSeries.inv_mul_cancel]
    · simp
    · simpa [hconst] using hc
  have h0 := congrArg (PowerSeries.coeff 0) hmul
  have h1 := congrArg (PowerSeries.coeff 1) hmul
  have h2 := congrArg (PowerSeries.coeff 2) hmul
  have h3 := congrArg (PowerSeries.coeff 3) hmul
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_zero_eq_constantCoeff_apply] at h0
  rw [PowerSeries.coeff_one_mul] at h1
  rw [hcoeff2] at h2
  rw [hcoeff3] at h3
  simp [rf, PowerSeries.coeff_rescale, PowerSeries.coeff_exp, hexp0] at h0 h1 h2 h3
  have hn0 : PowerSeries.constantCoeff (nf a b) = 1 := by
    apply mul_right_cancel₀ hc
    simpa [hconst] using h0
  have hn1 : PowerSeries.coeff 1 (nf a b) = -(a / (1 - a)) * b := by
    rw [hn0] at h1
    field_simp [hc] at h1 ⊢
    linear_combination h1
  have hn2 : PowerSeries.coeff 2 (nf a b) =
      (a / (1 - a)) ^ 2 * b ^ 2 + (a / (1 - a)) * b ^ 2 / 2 := by
    rw [hn0, hn1] at h2
    field_simp [hc] at h2 ⊢
    linear_combination h2
  have hn3 : PowerSeries.coeff 3 (nf a b) = -((a / (1 - a)) ^ 3 * b ^ 3 +
      (a / (1 - a)) ^ 2 * b ^ 3 + (a / (1 - a)) * b ^ 3 / 6) := by
    rw [hn0, hn1, hn2] at h3
    field_simp [hc] at h3 ⊢
    norm_num at h3
    ring_nf at h3 ⊢
    linear_combination (1 / 2) * h3
  exact ⟨by simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hn0, hn1, hn2, hn3⟩

private lemma root_ratio_bound (a : ℂ) (m : ℕ) (hm : 2 ≤ m)
    (hpa : a ^ m = 1) (ha : a ≠ 1) :
    ‖(a / (1 - a)) * ((m : ℂ)⁻¹)‖ ≤ (1 / 2 : ℝ) := by
  have hm0 : m ≠ 0 := by omega
  have hna : ‖a‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hpa hm0
  have hgeom : ∑ i ∈ Finset.range m, a ^ i = 0 := by
    rw [geom_sum_eq ha m, hpa, sub_self, zero_div]
  have hsum : (m : ℂ) = ∑ i ∈ Finset.range m, (1 - a ^ i) := by
    calc
      (m : ℂ) = ∑ i ∈ Finset.range m, (1 : ℂ) := by simp
      _ = (∑ i ∈ Finset.range m, (1 - a ^ i)) + ∑ i ∈ Finset.range m, a ^ i := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := by rw [hgeom, add_zero]
  have hgeomNorm (i : ℕ) : ‖∑ j ∈ Finset.range i, a ^ j‖ ≤ (i : ℝ) := by
    calc _ ≤ ∑ j ∈ Finset.range i, ‖a ^ j‖ := norm_sum_le _ _
      _ = ∑ _j ∈ Finset.range i, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        simp [norm_pow, hna]
      _ = i := by simp
  have hterm (i : ℕ) : ‖1 - a ^ i‖ ≤ ‖1 - a‖ * (i : ℝ) := by
    rw [← mul_neg_geom_sum a i, norm_mul]
    exact mul_le_mul_of_nonneg_left (hgeomNorm i) (norm_nonneg _)
  have hsumRange : (∑ i ∈ Finset.range m, (i : ℝ)) * 2 = (m : ℝ) * ((m - 1 : ℕ) : ℝ) := by
    rw [← Nat.cast_sum]
    exact_mod_cast Finset.sum_range_id_mul_two m
  have hmCast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hmCast] at hsumRange
  have hsumRange' : ∑ i ∈ Finset.range m, (i : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    nlinarith
  have hbound : (m : ℝ) ≤ ‖1 - a‖ * ((m : ℝ) * (m - 1) / 2) := by
    calc
      (m : ℝ) = ‖(m : ℂ)‖ := by simp
      _ = ‖∑ i ∈ Finset.range m, (1 - a ^ i)‖ := by rw [← hsum]
      _ ≤ ∑ i ∈ Finset.range m, ‖1 - a ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range m, ‖1 - a‖ * (i : ℝ) := Finset.sum_le_sum fun i hi => hterm i
      _ = _ := by rw [← Finset.mul_sum, hsumRange']
  have hchord : 2 ≤ (m : ℝ) * ‖1 - a‖ := by
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hmn : (0 : ℝ) < m := by positivity
    nlinarith [norm_nonneg (1 - a)]
  rw [norm_mul, norm_div, hna, one_div, norm_inv, Complex.norm_natCast]
  have hpos : 0 < (m : ℝ) * ‖1 - a‖ := lt_of_lt_of_le (by norm_num) hchord
  rw [inv_eq_one_div, inv_eq_one_div]
  field_simp [norm_pos_iff.mpr (sub_ne_zero.mpr ha.symm), Nat.cast_ne_zero.mpr hm0]
  nlinarith

private lemma nf_bound (a : ℂ) (m : ℕ) (hm : 2 ≤ m)
    (hpa : a ^ m = 1) (ha : a ≠ 1) :
    PowerSeries.coeff 0 (nf a ((m : ℂ)⁻¹)) = 1 ∧
      ‖PowerSeries.coeff 1 (nf a ((m : ℂ)⁻¹))‖ ≤ (1 / 2 : ℝ) ∧
      ‖PowerSeries.coeff 2 (nf a ((m : ℂ)⁻¹))‖ ≤ (1 / 2 : ℝ) ∧
      ‖PowerSeries.coeff 3 (nf a ((m : ℂ)⁻¹))‖ ≤ (1 / 2 : ℝ) := by
  rcases nf_coeff a ((m : ℂ)⁻¹) ha with ⟨h0, h1, h2, h3⟩
  have hq := root_ratio_bound a m hm hpa ha
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hb : ‖((m : ℂ)⁻¹)‖ ≤ (1 / 2 : ℝ) := by
    rw [norm_inv, Complex.norm_natCast, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hmR
  refine ⟨h0, ?_, ?_, ?_⟩
  · rw [h1, norm_mul, norm_neg]
    simpa [norm_mul] using hq
  · rw [h2]
    calc
      _ ≤ ‖(a / (1 - a)) ^ 2 * ((m : ℂ)⁻¹) ^ 2‖ +
          ‖a / (1 - a) * ((m : ℂ)⁻¹) ^ 2 / 2‖ := norm_add_le _ _
      _ = ‖(a / (1 - a) * (m : ℂ)⁻¹) ^ 2‖ +
          ‖a / (1 - a) * (m : ℂ)⁻¹‖ * ‖(m : ℂ)⁻¹‖ / 2 := by
        simp [norm_pow]
        ring
      _ ≤ (1 / 2 : ℝ) ^ 2 + (1 / 2) * (1 / 2) / 2 := by
        gcongr
        simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) hq 2
      _ ≤ 1 / 2 := by norm_num
  · rw [h3, norm_neg]
    calc
      _ ≤ ‖(a / (1 - a)) ^ 3 * ((m : ℂ)⁻¹) ^ 3 +
            (a / (1 - a)) ^ 2 * ((m : ℂ)⁻¹) ^ 3‖ +
          ‖a / (1 - a) * ((m : ℂ)⁻¹) ^ 3 / 6‖ := norm_add_le _ _
      _ ≤ (‖(a / (1 - a)) ^ 3 * ((m : ℂ)⁻¹) ^ 3‖ +
            ‖(a / (1 - a)) ^ 2 * ((m : ℂ)⁻¹) ^ 3‖) +
          ‖a / (1 - a) * ((m : ℂ)⁻¹) ^ 3 / 6‖ := by
        gcongr
        exact norm_add_le _ _
      _ = ‖a / (1 - a) * (m : ℂ)⁻¹‖ ^ 3 +
          ‖a / (1 - a) * (m : ℂ)⁻¹‖ ^ 2 * ‖(m : ℂ)⁻¹‖ +
          ‖a / (1 - a) * (m : ℂ)⁻¹‖ * ‖(m : ℂ)⁻¹‖ ^ 2 / 6 := by
        simp [norm_pow]
        ring
      _ ≤ (1 / 2 : ℝ) ^ 3 + (1 / 2) ^ 2 * (1 / 2) + (1 / 2) * (1 / 2) ^ 2 / 6 := by
        gcongr
      _ ≤ 1 / 2 := by norm_num

private lemma unit_prod_bound {ι : Type} (T : Finset ι)
    (f : ι → PowerSeries ℂ)
    (hf0 : ∀ i ∈ T, PowerSeries.coeff 0 (f i) = 1)
    (hf1 : ∀ i ∈ T, ‖PowerSeries.coeff 1 (f i)‖ ≤ (1 / 2 : ℝ))
    (hf2 : ∀ i ∈ T, ‖PowerSeries.coeff 2 (f i)‖ ≤ (1 / 2 : ℝ))
    (hf3 : ∀ i ∈ T, ‖PowerSeries.coeff 3 (f i)‖ ≤ (1 / 2 : ℝ)) :
    PowerSeries.coeff 0 (∏ i ∈ T, f i) = 1 ∧
      ‖PowerSeries.coeff 1 (∏ i ∈ T, f i)‖ ≤ (T.card : ℝ) / 2 ∧
      ‖PowerSeries.coeff 2 (∏ i ∈ T, f i)‖ ≤ (T.card : ℝ) / 2 + (T.card : ℝ) ^ 2 / 4 ∧
      ‖PowerSeries.coeff 3 (∏ i ∈ T, f i)‖ ≤
        (T.card : ℝ) / 2 + (T.card : ℝ) ^ 2 / 2 + (T.card : ℝ) ^ 3 / 8 := by
  classical
  have hcoeff2 (p q : PowerSeries ℂ) : PowerSeries.coeff 2 (p * q) =
        PowerSeries.coeff 0 p * PowerSeries.coeff 2 q +
        PowerSeries.coeff 1 p * PowerSeries.coeff 1 q +
        PowerSeries.coeff 2 p * PowerSeries.coeff 0 q := by
    rw [PowerSeries.coeff_mul]
    norm_num [Finset.antidiagonal]
    ring
  have hcoeff3 (p q : PowerSeries ℂ) : PowerSeries.coeff 3 (p * q) =
        PowerSeries.coeff 0 p * PowerSeries.coeff 3 q +
        PowerSeries.coeff 1 p * PowerSeries.coeff 2 q +
        PowerSeries.coeff 2 p * PowerSeries.coeff 1 q +
        PowerSeries.coeff 3 p * PowerSeries.coeff 0 q := by
    rw [PowerSeries.coeff_mul]
    norm_num [Finset.antidiagonal]
    ring
  have hnorm3 (a b c : ℂ) : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
    calc _ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
      _ ≤ _ := by
        gcongr
        exact norm_add_le _ _
  have hnorm4 (a b c d : ℂ) : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    calc _ ≤ ‖a + b + c‖ + ‖d‖ := norm_add_le _ _
      _ ≤ _ := by
        gcongr
        exact hnorm3 _ _ _
  induction T using Finset.induction_on with
  | empty => norm_num
  | @insert i T hi ih =>
      have hr := ih
        (fun j hj => hf0 j (by simp [hj]))
        (fun j hj => hf1 j (by simp [hj]))
        (fun j hj => hf2 j (by simp [hj]))
        (fun j hj => hf3 j (by simp [hj]))
      rcases hr with ⟨h0, h1, h2, h3⟩
      have hi0 := hf0 i (by simp)
      have hi1 := hf1 i (by simp)
      have hi2 := hf2 i (by simp)
      have hi3 := hf3 i (by simp)
      have hi0c := hi0
      have h0c := h0
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at hi0c h0c
      rw [Finset.prod_insert hi]
      constructor
      · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, hi0c, h0c, mul_one]
      constructor
      · rw [PowerSeries.coeff_one_mul, hi0c, h0c]
        simp only [mul_one]
        calc _ ≤ ‖PowerSeries.coeff 1 (f i)‖ +
              ‖PowerSeries.coeff 1 (∏ j ∈ T, f j)‖ := norm_add_le _ _
          _ ≤ (1 / 2 : ℝ) + (T.card : ℝ) / 2 := add_le_add hi1 h1
          _ = ((insert i T).card : ℝ) / 2 := by
            simp [Finset.card_insert_of_notMem hi]
            ring
      constructor
      · rw [hcoeff2, hi0, h0, mul_one, one_mul]
        calc _ ≤ ‖PowerSeries.coeff 2 (∏ j ∈ T, f j)‖ +
              ‖PowerSeries.coeff 1 (f i) * PowerSeries.coeff 1 (∏ j ∈ T, f j)‖ +
              ‖PowerSeries.coeff 2 (f i)‖ := hnorm3 _ _ _
          _ = ‖PowerSeries.coeff 2 (∏ j ∈ T, f j)‖ + ‖PowerSeries.coeff 1 (f i)‖ *
                ‖PowerSeries.coeff 1 (∏ j ∈ T, f j)‖ +
              ‖PowerSeries.coeff 2 (f i)‖ := by rw [norm_mul]
          _ ≤ ((T.card : ℝ) / 2 + (T.card : ℝ) ^ 2 / 4) +
              (1 / 2) * ((T.card : ℝ) / 2) + 1 / 2 := by
            gcongr
          _ ≤ ((insert i T).card : ℝ) / 2 + ((insert i T).card : ℝ) ^ 2 / 4 := by
            have hm : 0 ≤ (T.card : ℝ) := by positivity
            simp [Finset.card_insert_of_notMem hi]
            nlinarith
      · rw [hcoeff3, hi0, h0, mul_one, one_mul]
        calc _ ≤ ‖PowerSeries.coeff 3 (∏ j ∈ T, f j)‖ +
              ‖PowerSeries.coeff 1 (f i) * PowerSeries.coeff 2 (∏ j ∈ T, f j)‖ +
              ‖PowerSeries.coeff 2 (f i) * PowerSeries.coeff 1 (∏ j ∈ T, f j)‖ +
              ‖PowerSeries.coeff 3 (f i)‖ := hnorm4 _ _ _ _
          _ = ‖PowerSeries.coeff 3 (∏ j ∈ T, f j)‖ + ‖PowerSeries.coeff 1 (f i)‖ *
                ‖PowerSeries.coeff 2 (∏ j ∈ T, f j)‖ +
              ‖PowerSeries.coeff 2 (f i)‖ * ‖PowerSeries.coeff 1 (∏ j ∈ T, f j)‖ +
              ‖PowerSeries.coeff 3 (f i)‖ := by rw [norm_mul, norm_mul]
          _ ≤ ((T.card : ℝ) / 2 + (T.card : ℝ) ^ 2 / 2 + (T.card : ℝ) ^ 3 / 8) +
              (1 / 2) * ((T.card : ℝ) / 2 + (T.card : ℝ) ^ 2 / 4) +
              (1 / 2) * ((T.card : ℝ) / 2) + 1 / 2 := by
            gcongr
          _ ≤ ((insert i T).card : ℝ) / 2 + ((insert i T).card : ℝ) ^ 2 / 2 +
              ((insert i T).card : ℝ) ^ 3 / 8 := by
            have hm : 0 ≤ (T.card : ℝ) := by positivity
            simp [Finset.card_insert_of_notMem hi]
            nlinarith

private lemma small_prod_bound {ι : Type} (T : Finset ι)
    (f : ι → PowerSeries ℂ) (t : ι → ℝ)
    (ht : ∀ i ∈ T, 0 ≤ t i)
    (hf0 : ∀ i ∈ T, PowerSeries.coeff 0 (f i) = 1)
    (hf1 : ∀ i ∈ T, ‖PowerSeries.coeff 1 (f i)‖ ≤ t i / 2)
    (hf2 : ∀ i ∈ T, ‖PowerSeries.coeff 2 (f i)‖ ≤ (t i) ^ 2 / 12)
    (hf3 : ∀ i ∈ T, PowerSeries.coeff 3 (f i) = 0) :
    let x := ∑ i ∈ T, t i
    PowerSeries.coeff 0 (∏ i ∈ T, f i) = 1 ∧ ‖PowerSeries.coeff 1 (∏ i ∈ T, f i)‖ ≤ x / 2 ∧
      ‖PowerSeries.coeff 2 (∏ i ∈ T, f i)‖ ≤ x ^ 2 / 2 ∧
      ‖PowerSeries.coeff 3 (∏ i ∈ T, f i)‖ ≤ x ^ 3 / 2 := by
  classical
  have hcoeff2 (p q : PowerSeries ℂ) : PowerSeries.coeff 2 (p * q) =
        PowerSeries.coeff 0 p * PowerSeries.coeff 2 q +
        PowerSeries.coeff 1 p * PowerSeries.coeff 1 q +
        PowerSeries.coeff 2 p * PowerSeries.coeff 0 q := by
    rw [PowerSeries.coeff_mul]
    norm_num [Finset.antidiagonal]
    ring
  have hcoeff3 (p q : PowerSeries ℂ) : PowerSeries.coeff 3 (p * q) =
        PowerSeries.coeff 0 p * PowerSeries.coeff 3 q +
        PowerSeries.coeff 1 p * PowerSeries.coeff 2 q +
        PowerSeries.coeff 2 p * PowerSeries.coeff 1 q +
        PowerSeries.coeff 3 p * PowerSeries.coeff 0 q := by
    rw [PowerSeries.coeff_mul]
    norm_num [Finset.antidiagonal]
    ring
  have hnorm3 (a b c : ℂ) : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by
    calc _ ≤ ‖a + b‖ + ‖c‖ := norm_add_le _ _
      _ ≤ _ := by
        gcongr
        exact norm_add_le _ _
  dsimp only
  induction T using Finset.induction_on with
  | empty => norm_num
  | @insert i T hi ih =>
      have hr := ih
        (fun j hj => ht j (by simp [hj]))
        (fun j hj => hf0 j (by simp [hj]))
        (fun j hj => hf1 j (by simp [hj]))
        (fun j hj => hf2 j (by simp [hj]))
        (fun j hj => hf3 j (by simp [hj]))
      rcases hr with ⟨h0, h1, h2, h3⟩
      have hti := ht i (by simp)
      have hi0 := hf0 i (by simp)
      have hi1 := hf1 i (by simp)
      have hi2 := hf2 i (by simp)
      have hi3 := hf3 i (by simp)
      have hi0c := hi0
      have h0c := h0
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at hi0c h0c
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      constructor
      · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, hi0c, h0c, mul_one]
      constructor
      · rw [PowerSeries.coeff_one_mul, hi0c, h0c]
        simp only [mul_one]
        calc _ ≤ ‖PowerSeries.coeff 1 (f i)‖ +
              ‖PowerSeries.coeff 1 (∏ j ∈ T, f j)‖ := norm_add_le _ _
          _ ≤ t i / 2 + (∑ j ∈ T, t j) / 2 := add_le_add hi1 h1
          _ = _ := by ring
      constructor
      · rw [hcoeff2, hi0, h0, mul_one, one_mul]
        calc _ ≤ ‖PowerSeries.coeff 2 (∏ j ∈ T, f j)‖ +
              ‖PowerSeries.coeff 1 (f i) * PowerSeries.coeff 1 (∏ j ∈ T, f j)‖ +
              ‖PowerSeries.coeff 2 (f i)‖ := hnorm3 _ _ _
          _ = ‖PowerSeries.coeff 2 (∏ j ∈ T, f j)‖ + ‖PowerSeries.coeff 1 (f i)‖ *
                ‖PowerSeries.coeff 1 (∏ j ∈ T, f j)‖ +
              ‖PowerSeries.coeff 2 (f i)‖ := by rw [norm_mul]
          _ ≤ (∑ j ∈ T, t j) ^ 2 / 2 + (t i / 2) * ((∑ j ∈ T, t j) / 2) + (t i) ^ 2 / 12 := by
            gcongr
          _ ≤ _ := by
            have hs : 0 ≤ ∑ j ∈ T, t j := Finset.sum_nonneg fun j hj => ht j (by simp [hj])
            nlinarith [sq_nonneg (t i), sq_nonneg (∑ j ∈ T, t j)]
      · rw [hcoeff3, hi0, h0, hi3, mul_one, one_mul, add_zero]
        calc _ ≤ ‖PowerSeries.coeff 3 (∏ j ∈ T, f j)‖ +
              ‖PowerSeries.coeff 1 (f i) * PowerSeries.coeff 2 (∏ j ∈ T, f j)‖ +
              ‖PowerSeries.coeff 2 (f i) * PowerSeries.coeff 1 (∏ j ∈ T, f j)‖ := hnorm3 _ _ _
          _ = ‖PowerSeries.coeff 3 (∏ j ∈ T, f j)‖ + ‖PowerSeries.coeff 1 (f i)‖ *
                ‖PowerSeries.coeff 2 (∏ j ∈ T, f j)‖ +
              ‖PowerSeries.coeff 2 (f i)‖ * ‖PowerSeries.coeff 1 (∏ j ∈ T, f j)‖ := by
            rw [norm_mul, norm_mul]
          _ ≤ (∑ j ∈ T, t j) ^ 3 / 2 + (t i / 2) * ((∑ j ∈ T, t j) ^ 2 / 2) +
              ((t i) ^ 2 / 12) * ((∑ j ∈ T, t j) / 2) := by
            gcongr
          _ ≤ _ := by
            have hs : 0 ≤ ∑ j ∈ T, t j := Finset.sum_nonneg fun j hj => ht j (by simp [hj])
            nlinarith [sq_nonneg (t i), sq_nonneg (∑ j ∈ T, t j), mul_nonneg (sq_nonneg (t i)) hs,
              mul_nonneg hti (sq_nonneg (∑ j ∈ T, t j))]

/-- For literal paper support sizes one through three, the actual source jet has
the normalized pointwise bound needed before the fixed-support root sums. -/
theorem sourceNontrivialRootContribution_card_one_to_three_bound
    (n : ℕ) (hn : 7 ≤ n) (ζ : ℂ)
    (hζ : ζ ∈ Polynomial.nthRootsFinset
      (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester
        (n + 1) - 1)
      (1 : ℂ))
    (hζne : ζ ≠ 1) (c : ℤ) (hc : c = 0 ∨ c = -1)
    (hRcard : (Finset.univ.filter fun i : Fin n =>
      ζ ^ ((D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester
          (n + 1) - 1) /
        D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester
          (i.1 + 1)) ≠ 1).card ≤ 3) :
    let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester
        (n + 1) - 1
    let R := Finset.univ.filter fun i : Fin n => ζ ^ (M /
      D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester
        (i.1 + 1)) ≠ 1
    let S := ∏ i ∈ R, D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester
        (i.1 + 1)
    let chord : Fin n → ℂ := fun i => 1 - ζ ^ (M /
      D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester
        (i.1 + 1))
    R.Nonempty ∧ sourceRootSupport (n + 1) ζ =
        insert none (insert (some (Fin.last n)) (R.image fun i => some i.castSucc)) ∧
      (sourceRootSupport (n + 1) ζ).card = R.card + 2 ∧
      sourcePoleOrder (n + 1) ζ = n - R.card ∧
      0 < ((n + 1 - 6).factorial : ℝ) * (S : ℝ) * ‖1 - ζ‖ ^ 2 * ∏ i ∈ R, ‖chord i‖ ∧
      ‖(sourceLocalRootContributionPolynomial (n + 1) ζ c).coeff (n + 1 - 6)‖ ≤
        16 / (((n + 1 - 6).factorial : ℝ) * (S : ℝ) * ‖1 - ζ‖ ^ 2 * ∏ i ∈ R, ‖chord i‖) := by
  classical
  dsimp only
  have hcoeff2 (p q : PowerSeries ℂ) : PowerSeries.coeff 2 (p * q) =
        PowerSeries.coeff 0 p * PowerSeries.coeff 2 q +
        PowerSeries.coeff 1 p * PowerSeries.coeff 1 q +
        PowerSeries.coeff 2 p * PowerSeries.coeff 0 q := by
    rw [PowerSeries.coeff_mul]
    norm_num [Finset.antidiagonal]
    ring
  have hcoeff3 (p q : PowerSeries ℂ) : PowerSeries.coeff 3 (p * q) =
        PowerSeries.coeff 0 p * PowerSeries.coeff 3 q +
        PowerSeries.coeff 1 p * PowerSeries.coeff 2 q +
        PowerSeries.coeff 2 p * PowerSeries.coeff 1 q +
        PowerSeries.coeff 3 p * PowerSeries.coeff 0 q := by
    rw [PowerSeries.coeff_mul]
    norm_num [Finset.antidiagonal]
    ring
  have hnorm3 (a b d : ℂ) : ‖a + b + d‖ ≤ ‖a‖ + ‖b‖ + ‖d‖ := by
    calc _ ≤ ‖a + b‖ + ‖d‖ := norm_add_le _ _
      _ ≤ _ := by
        gcongr
        exact norm_add_le _ _
  have hnorm4 (a b d e : ℂ) : ‖a + b + d + e‖ ≤ ‖a‖ + ‖b‖ + ‖d‖ + ‖e‖ := by
    calc _ ≤ ‖a + b + d‖ + ‖e‖ := norm_add_le _ _
      _ ≤ _ := by
        gcongr
        exact hnorm3 _ _ _
  let syl := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester
  let M := syl (n + 1) - 1
  let R := Finset.univ.filter fun i : Fin n => ζ ^ (M / syl (i.1 + 1)) ≠ 1
  let S := ∏ i ∈ R, syl (i.1 + 1)
  let chord : Fin n → ℂ := fun i => 1 - ζ ^ (M / syl (i.1 + 1))
  let F : Option (Fin (n + 1)) → PowerSeries ℂ := fun j =>
    PowerSeries.C (1 - ζ ^ partitionWeight (n + 1) j) * (rootDenominatorFactor (n + 1) ζ j)⁻¹
  let G : Option (Fin (n + 1)) → PowerSeries ℂ := fun j =>
    PowerSeries.C
      (((M / partitionWeight (n + 1) j : ℕ) : ℂ)⁻¹) *
      (rootVanishingQuotient (n + 1) ζ j)⁻¹
  let VP := ∏ j ∈ sourceVanishingFactors (n + 1) ζ, G j
  let UP := ∏ j ∈ sourceRootSupport (n + 1) ζ, F j
  let E := PowerSeries.rescale ((c : ℂ) * (M : ℂ)⁻¹) (PowerSeries.exp ℂ)
  let B := E * VP
  let T := B * UP
  have hM : 0 < M := Nat.sub_pos_of_lt
      (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester (n + 1) (by omega)))
  have hpow : ζ ^ M = 1 := (Polynomial.mem_nthRootsFinset hM (1 : ℂ)).mp hζ
  have hMtwo : 2 ≤ M := by
    have hn : M ≠ 1 := by
      intro he
      apply hζne
      simpa [he] using hpow
    omega
  have hweight (i : Fin n) : partitionWeight (n + 1) (some i.castSucc) = M / syl (i.1 + 1) := by
    simp [partitionWeight, baseWeight, axisScale, M, syl,
      show i.1 ≠ n by omega]
  have hscale (i : Fin n) : M / partitionWeight (n + 1) (some i.castSucc) = syl (i.1 + 1) := by
    apply Nat.div_eq_of_eq_mul_left
      (partitionWeight_pos (n + 1) (by omega) (some i.castSucc))
    rw [partitionWeight, baseWeight]
    simpa [D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.axisScale,
      M, syl, show i.1 ≠ n by omega, Nat.mul_comm] using
      (Nat.div_mul_cancel
        (base_axisScale_dvd_mass (n + 1) (by omega) i.castSucc)).symm
  have hquotTwo (j : Option (Fin (n + 1))) : 2 ≤ M / partitionWeight (n + 1) j := by
    cases j with
    | none => simpa [partitionWeight] using hMtwo
    | some j =>
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simpa [partitionWeight, baseWeight_last] using hMtwo
        · rw [hscale]
          exact two_le_sylvester (i.1 + 1) (by omega)
  have hfactor (j : Option (Fin (n + 1))) : rootDenominatorFactor (n + 1) ζ j =
        rf (ζ ^ partitionWeight (n + 1) j)
          (((M / partitionWeight (n + 1) j : ℕ) : ℂ)⁻¹) := by
    rw [rootDenominatorFactor, rootLocalCoordinate_pow_partitionWeight (n + 1) (by omega)]
    rfl
  have hinj : Function.Injective
      (fun i : Fin n => (some i.castSucc : Option (Fin (n + 1)))) := by
    intro i j h
    simpa using h
  rcases (show
      sourceRootSupport (n + 1) ζ = insert none (insert (some (Fin.last n))
            (R.image fun i => some i.castSucc)) ∧
        (sourceRootSupport (n + 1) ζ).card = R.card + 2 ∧
        sourcePoleOrder (n + 1) ζ = n - R.card ∧
        ‖ζ ^ (-c)‖ = 1 ∧ _ by
      simpa [M, R, syl] using
        sourceNontrivialRootContribution_support_cutoff n hn ζ hζ hζne c) with
    ⟨hsupport, hcard, hpole, hphase, _⟩
  have hallRange : ∏ i ∈ Finset.range n, syl (i + 1) = M := by
    change (∏ i ∈ Finset.range n, sylvester (i + 1)) = sylvester (n + 1) - 1
    rw [sylvester_sub_one_eq_prod (n + 1) (by omega), Finset.prod_range_succ']
    simp [sylvester]
  have hall : (∏ i : Fin n, syl (i.1 + 1)) = M := by
    calc _ = ∏ i ∈ Finset.range n, syl (i + 1) := Fin.prod_univ_eq_prod_range _ n
      _ = M := hallRange
  have hsumQ : ∑ i : Fin n, M / syl (i.1 + 1) = M - 1 := by
    calc _ = ∑ i ∈ Finset.range n, M / syl (i + 1) :=
        Fin.sum_univ_eq_sum_range _ n
      _ = ∑ i ∈ Finset.range n, (∏ j ∈ Finset.range n, syl (j + 1)) / syl (i + 1) := by
        rw [hallRange]
      _ = (∏ j ∈ Finset.range n, syl (j + 1)) - 1 := by
        simpa [syl] using
          sylvester_quotient_sum_for_root_bound n (le_trans (by norm_num) hn)
      _ = M - 1 := by rw [hallRange]
  have hpowSum (U : Finset (Fin n)) : ζ ^ (∑ i ∈ U, M / syl (i.1 + 1)) =
        ∏ i ∈ U, ζ ^ (M / syl (i.1 + 1)) := by
    induction U using Finset.induction_on with
    | empty => simp
    | @insert i U hi ih =>
        simp [Finset.sum_insert hi, Finset.prod_insert hi, pow_add, ih]
  have hRne : R.Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty] at he
    have ho (i : Fin n) : ζ ^ (M / syl (i.1 + 1)) = 1 := by
      by_contra hn
      have hi : i ∈ R := by simp [R, hn]
      rw [he] at hi
      simp at hi
    have hp : ζ ^ (M - 1) = 1 := by
      rw [← hsumQ, hpowSum]
      exact Finset.prod_eq_one fun i hi => ho i
    have hs : M = (M - 1) + 1 := by omega
    rw [hs, pow_add, hp, one_mul, pow_one] at hpow
    exact hζne hpow
  have hvan : sourceVanishingFactors (n + 1) ζ =
        Rᶜ.image (fun i => (some i.castSucc : Option (Fin (n + 1)))) := by
    ext j
    cases j with
    | none =>
        simp only [sourceVanishingFactors, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [partitionWeight] using hζne
    | some j =>
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp only [sourceVanishingFactors, Finset.mem_filter, Finset.mem_univ, true_and]
          simpa [partitionWeight, baseWeight_last] using hζne
        · simp only [sourceVanishingFactors, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hweight]
          constructor
          · intro hz
            refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
            apply Finset.mem_compl.mpr
            intro hiR
            exact (Finset.mem_filter.mp hiR).2 hz
          · intro him
            rcases Finset.mem_image.mp him with ⟨k, hk, hki⟩
            have hki' : k = i := Fin.castSucc_inj.mp (Option.some.inj hki)
            subst k
            by_contra hne
            apply Finset.mem_compl.mp hk
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩
  have hlocalU (j) (hj : j ∈ sourceRootSupport (n + 1) ζ) : PowerSeries.coeff 0 (F j) = 1 ∧
        ‖PowerSeries.coeff 1 (F j)‖ ≤ (1 / 2 : ℝ) ∧
        ‖PowerSeries.coeff 2 (F j)‖ ≤ (1 / 2 : ℝ) ∧
        ‖PowerSeries.coeff 3 (F j)‖ ≤ (1 / 2 : ℝ) := by
    have hd := partitionWeight_dvd_period (n + 1)
        (Nat.succ_le_succ (Nat.zero_le n)) j
    have hr : (ζ ^ partitionWeight (n + 1) j) ^
            (M / partitionWeight (n + 1) j) = 1 := by
      rw [← pow_mul, Nat.mul_div_cancel' hd]
      exact hpow
    have hn : ζ ^ partitionWeight (n + 1) j ≠ 1 := by
      simpa [sourceRootSupport] using (Finset.mem_filter.mp hj).2
    change
      PowerSeries.coeff 0
          (PowerSeries.C (1 - ζ ^ partitionWeight (n + 1) j) *
            (rootDenominatorFactor (n + 1) ζ j)⁻¹) = 1 ∧
        ‖PowerSeries.coeff 1
          (PowerSeries.C (1 - ζ ^ partitionWeight (n + 1) j) *
            (rootDenominatorFactor (n + 1) ζ j)⁻¹)‖ ≤ (1 / 2 : ℝ) ∧
        ‖PowerSeries.coeff 2
          (PowerSeries.C (1 - ζ ^ partitionWeight (n + 1) j) *
            (rootDenominatorFactor (n + 1) ζ j)⁻¹)‖ ≤ (1 / 2 : ℝ) ∧
        ‖PowerSeries.coeff 3
          (PowerSeries.C (1 - ζ ^ partitionWeight (n + 1) j) *
            (rootDenominatorFactor (n + 1) ζ j)⁻¹)‖ ≤ (1 / 2 : ℝ)
    rw [hfactor]
    exact nf_bound _ _ (hquotTwo j) hr hn
  have hU : PowerSeries.coeff 0 UP = 1 ∧
        ‖PowerSeries.coeff 1 UP‖ ≤ ((sourceRootSupport (n + 1) ζ).card : ℝ) / 2 ∧
        ‖PowerSeries.coeff 2 UP‖ ≤ ((sourceRootSupport (n + 1) ζ).card : ℝ) / 2 +
            ((sourceRootSupport (n + 1) ζ).card : ℝ) ^ 2 / 4 ∧
        ‖PowerSeries.coeff 3 UP‖ ≤ ((sourceRootSupport (n + 1) ζ).card : ℝ) / 2 +
            ((sourceRootSupport (n + 1) ζ).card : ℝ) ^ 2 / 2 +
            ((sourceRootSupport (n + 1) ζ).card : ℝ) ^ 3 / 8 := by
    dsimp [UP]
    exact unit_prod_bound _ F
      (fun j h => (hlocalU j h).1)
      (fun j h => (hlocalU j h).2.1)
      (fun j h => (hlocalU j h).2.2.1)
      (fun j h => (hlocalU j h).2.2.2)
  let t : Option (Fin (n + 1)) → ℝ := fun j =>
    ‖(((M / partitionWeight (n + 1) j : ℕ) : ℂ)⁻¹)‖
  have hlocalV (j) (hj : j ∈ sourceVanishingFactors (n + 1) ζ) : PowerSeries.coeff 0 (G j) = 1 ∧
        ‖PowerSeries.coeff 1 (G j)‖ ≤ t j / 2 ∧
        ‖PowerSeries.coeff 2 (G j)‖ ≤ (t j) ^ 2 / 12 ∧
        PowerSeries.coeff 3 (G j) = 0 := by
    have hr : ζ ^ partitionWeight (n + 1) j = 1 := by
      simpa [sourceVanishingFactors] using (Finset.mem_filter.mp hj).2
    have hb : (((M / partitionWeight (n + 1) j : ℕ) : ℂ)⁻¹) ≠ 0 := by
      simp [Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two (hquotTwo j))]
    have hq : rootVanishingQuotient (n + 1) ζ j =
          vq (((M / partitionWeight (n + 1) j : ℕ) : ℂ)⁻¹) := by
      apply PowerSeries.ext
      intro k
      simp only [rootVanishingQuotient, vq, PowerSeries.coeff_mk]
      rw [hfactor, hr]
    have he : G j = vf (((M / partitionWeight (n + 1) j : ℕ) : ℂ)⁻¹) := by
      dsimp [G, vf]
      rw [hq]
    rw [he]
    rcases vf_coeff _ hb with ⟨h0, h1, h2, h3⟩
    refine ⟨h0, ?_, ?_, h3⟩
    · rw [h1, norm_div, Complex.norm_ofNat]
    · rw [h2, norm_div, norm_pow, Complex.norm_ofNat]
  have hrecip (i : Fin n) : ((syl (i.1 + 1) : ℝ)⁻¹) = ((M / syl (i.1 + 1) : ℕ) : ℝ) / M := by
    have hd : syl (i.1 + 1) ∣ M := by
      rw [← hall]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    have hp := Nat.div_mul_cancel hd
    have hpR : ((M / syl (i.1 + 1) : ℕ) : ℝ) * syl (i.1 + 1) = M := by
      exact_mod_cast hp
    rw [← hpR]
    have hq : M / syl (i.1 + 1) ≠ 0 := by
      intro h
      rw [h, zero_mul] at hp
      omega
    field_simp [Nat.ne_of_gt (sylvester_pos _), hq]
  have hx : ∑ j ∈ sourceVanishingFactors (n + 1) ζ, t j ≤ 1 := by
    rw [hvan, Finset.sum_image hinj.injOn]
    simp_rw [t, hscale, norm_inv, Complex.norm_natCast, hrecip]
    calc
      (∑ i ∈ Rᶜ, ((M / syl (i.1 + 1) : ℕ) : ℝ) / M) ≤
          ∑ i : Fin n, ((M / syl (i.1 + 1) : ℕ) : ℝ) / M :=
        Finset.sum_le_univ_sum_of_nonneg fun i => by positivity
      _ = ((M - 1 : ℕ) : ℝ) / M := by
        field_simp [Nat.ne_of_gt hM]
        calc
          (M : ℝ) * ∑ i : Fin n, ((M / syl (i.1 + 1) : ℕ) : ℝ) / M =
              ∑ i : Fin n, ((M / syl (i.1 + 1) : ℕ) : ℝ) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            field_simp [Nat.ne_of_gt hM]
          _ = ((M - 1 : ℕ) : ℝ) := by exact_mod_cast hsumQ
      _ ≤ 1 := by
        rw [Nat.cast_sub (by omega)]
        apply (div_le_iff₀ (by positivity)).2
        nlinarith
  have hv := small_prod_bound
    (sourceVanishingFactors (n + 1) ζ) G t
    (fun j h => norm_nonneg _)
    (fun j h => (hlocalV j h).1)
    (fun j h => (hlocalV j h).2.1)
    (fun j h => (hlocalV j h).2.2.1)
    (fun j h => (hlocalV j h).2.2.2)
  rcases hv with ⟨hv0, hv1, hv2, hv3⟩
  have hx0 : 0 ≤ ∑ j ∈ sourceVanishingFactors (n + 1) ζ, t j :=
    Finset.sum_nonneg fun j h => norm_nonneg _
  have hV : PowerSeries.coeff 0 VP = 1 ∧
        ‖PowerSeries.coeff 1 VP‖ ≤ 1 / 2 ∧
        ‖PowerSeries.coeff 2 VP‖ ≤ 1 / 2 ∧
        ‖PowerSeries.coeff 3 VP‖ ≤ 1 / 2 := by
    dsimp [VP] at hv0 hv1 hv2 hv3 ⊢
    refine ⟨hv0, hv1.trans ?_, hv2.trans ?_, hv3.trans ?_⟩ <;> nlinarith
  have hz : ‖(c : ℂ) * (M : ℂ)⁻¹‖ ≤ (1 / 2 : ℝ) := by
    rcases hc with rfl | rfl
    · simp
    · rw [show ((-1 : ℤ) : ℂ) = (-1 : ℂ) by norm_num, norm_mul,
        norm_neg, norm_one, one_mul, norm_inv, Complex.norm_natCast]
      simpa [one_div] using one_div_le_one_div_of_le
        (by norm_num : (0 : ℝ) < 2)
        (by exact_mod_cast hMtwo : (2 : ℝ) ≤ M)
  have hB : PowerSeries.coeff 0 B = 1 ∧
        ‖PowerSeries.coeff 1 B‖ ≤ 1 ∧
        ‖PowerSeries.coeff 2 B‖ ≤ 1 ∧
        ‖PowerSeries.coeff 3 B‖ ≤ 1 := by
    rcases hV with ⟨hV0, hV1, hV2, hV3⟩
    have he0 : PowerSeries.coeff 0 E = 1 := by
      simp [E, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
    have he1 : PowerSeries.coeff 1 E = (c : ℂ) * (M : ℂ)⁻¹ := by
      simp [E, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
    have he2 : PowerSeries.coeff 2 E = ((c : ℂ) * (M : ℂ)⁻¹) ^ 2 / 2 := by
      norm_num [E, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
      ring
    have he3 : PowerSeries.coeff 3 E = ((c : ℂ) * (M : ℂ)⁻¹) ^ 3 / 6 := by
      norm_num [E, PowerSeries.coeff_rescale, PowerSeries.coeff_exp, Nat.factorial]
      ring
    have he0c := he0
    have hv0c := hV0
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at he0c hv0c
    dsimp [B]
    constructor
    · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, he0c, hv0c, mul_one]
    constructor
    · rw [PowerSeries.coeff_one_mul, he0c, hv0c, he1]
      simp only [mul_one]
      exact (norm_add_le _ _).trans (by linarith [hV1])
    constructor
    · rw [hcoeff2, he0, hV0, he1, he2, mul_one, one_mul]
      calc _ ≤ ‖PowerSeries.coeff 2 VP‖ +
            ‖(c : ℂ) * (M : ℂ)⁻¹ * PowerSeries.coeff 1 VP‖ +
            ‖((c : ℂ) * (M : ℂ)⁻¹) ^ 2 / 2‖ := hnorm3 _ _ _
        _ = ‖PowerSeries.coeff 2 VP‖ + ‖(c : ℂ) * (M : ℂ)⁻¹‖ * ‖PowerSeries.coeff 1 VP‖ +
            ‖(c : ℂ) * (M : ℂ)⁻¹‖ ^ 2 / 2 := by
          simp [norm_pow]
        _ ≤ (1 / 2 : ℝ) + (1 / 2) * (1 / 2) + (1 / 2) ^ 2 / 2 := by
          gcongr
        _ ≤ 1 := by norm_num
    · rw [hcoeff3, he0, hV0, he1, he2, he3, mul_one, one_mul]
      calc _ ≤ ‖PowerSeries.coeff 3 VP‖ +
            ‖(c : ℂ) * (M : ℂ)⁻¹ * PowerSeries.coeff 2 VP‖ +
            ‖((c : ℂ) * (M : ℂ)⁻¹) ^ 2 / 2 * PowerSeries.coeff 1 VP‖ +
            ‖((c : ℂ) * (M : ℂ)⁻¹) ^ 3 / 6‖ := hnorm4 _ _ _ _
        _ = ‖PowerSeries.coeff 3 VP‖ + ‖(c : ℂ) * (M : ℂ)⁻¹‖ * ‖PowerSeries.coeff 2 VP‖ +
            (‖(c : ℂ) * (M : ℂ)⁻¹‖ ^ 2 / 2) * ‖PowerSeries.coeff 1 VP‖ +
            ‖(c : ℂ) * (M : ℂ)⁻¹‖ ^ 3 / 6 := by
          simp [norm_pow]
        _ ≤ (1 / 2 : ℝ) + (1 / 2) * (1 / 2) + ((1 / 2) ^ 2 / 2) * (1 / 2) + (1 / 2) ^ 3 / 6 := by
          gcongr
        _ ≤ 1 := by norm_num
  have hrc : R.card ≤ 3 := by simpa [R, M, syl] using hRcard
  have hTbound : ‖PowerSeries.coeff (4 - R.card) T‖ ≤ 16 := by
    rcases hB with ⟨hB0, hB1, hB2, hB3⟩
    have hb0 := hB0
    have hu0 := hU.1
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at hb0 hu0
    have huz : PowerSeries.coeff 0 UP = 1 := by
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact hu0
    have hrp : 1 ≤ R.card := Finset.one_le_card.mpr hRne
    interval_cases hr : R.card
    · simp only [T, Nat.reduceSubDiff]
      have hc : (sourceRootSupport (n + 1) ζ).card = 3 := by omega
      rw [hc] at hU
      norm_num at hU
      rcases hU with ⟨_, hU1, hU2, hU3⟩
      rw [hcoeff3, hB0, huz, mul_one, one_mul]
      calc _ ≤ ‖PowerSeries.coeff 3 UP‖ +
            ‖PowerSeries.coeff 1 B * PowerSeries.coeff 2 UP‖ +
            ‖PowerSeries.coeff 2 B * PowerSeries.coeff 1 UP‖ +
            ‖PowerSeries.coeff 3 B‖ := hnorm4 _ _ _ _
        _ ≤ (3 / 2 + 3 ^ 2 / 2 + 3 ^ 3 / 8 : ℝ) + 1 * (3 / 2 + 3 ^ 2 / 4) + 1 * (3 / 2) + 1 := by
          simp only [norm_mul]
          gcongr <;> (try norm_num) <;> assumption
        _ ≤ 16 := by norm_num
    · simp only [T, Nat.reduceSubDiff]
      have hc : (sourceRootSupport (n + 1) ζ).card = 4 := by omega
      rw [hc] at hU
      norm_num at hU
      rcases hU with ⟨_, hU1, hU2, _⟩
      rw [hcoeff2, hB0, huz, mul_one, one_mul]
      calc _ ≤ ‖PowerSeries.coeff 2 UP‖ +
            ‖PowerSeries.coeff 1 B * PowerSeries.coeff 1 UP‖ +
            ‖PowerSeries.coeff 2 B‖ := hnorm3 _ _ _
        _ ≤ (4 / 2 + 4 ^ 2 / 4 : ℝ) + 1 * (4 / 2) + 1 := by
          simp only [norm_mul]
          gcongr <;> (try norm_num) <;> assumption
        _ ≤ 16 := by norm_num
    · simp only [T, Nat.reduceSubDiff]
      have hc : (sourceRootSupport (n + 1) ζ).card = 5 := by omega
      rw [hc] at hU
      norm_num at hU
      rcases hU with ⟨_, hU1, _, _⟩
      rw [PowerSeries.coeff_one_mul, hb0, hu0]
      simp only [mul_one]
      exact (norm_add_le _ _).trans
        ((add_le_add hB1 hU1).trans (by norm_num))
  have hprodInv {α : Type} (U : Finset α) (f : α → PowerSeries ℂ) :
      (∏ i ∈ U, f i)⁻¹ = ∏ i ∈ U, (f i)⁻¹ := by
    induction U using Finset.induction_on with
    | empty => simp
    | @insert i U hi ih =>
        rw [Finset.prod_insert hi, PowerSeries.mul_inv_rev, ih, Finset.prod_insert hi, mul_comm]
  have hnormalized : T = PowerSeries.C
          ((∏ j ∈ sourceVanishingFactors (n + 1) ζ,
              (((M / partitionWeight (n + 1) j : ℕ) : ℂ)⁻¹)) *
            ∏ j ∈ sourceRootSupport (n + 1) ζ, (1 - ζ ^ partitionWeight (n + 1) j)) *
        sourceExponentialLocalJet (n + 1) ζ c := by
    rw [sourceExponentialLocalJet, sourceLocalRegularInverse,
      sourceLocalRegularDenominator, PowerSeries.mul_inv_rev,
      hprodInv, hprodInv]
    simp only [T, B, VP, UP, E, F, G, Finset.prod_mul_distrib, ← map_prod]
    have hs : 1 ≤ syl (n + 1) := sylvester_pos _
    have hcast : (((syl (n + 1) - 1 : ℕ) : ℂ)) = (syl (n + 1) : ℂ) - 1 := by
      norm_num [Nat.cast_sub hs]
    rw [hcast, map_mul]
    ring
  have hsplit : S * ∏ i ∈ Rᶜ, syl (i.1 + 1) = M := by
    simpa [S, hall] using
      Finset.prod_mul_prod_compl R (fun i : Fin n => syl (i.1 + 1))
  have hvprod : (∏ j ∈ sourceVanishingFactors (n + 1) ζ,
        (((M / partitionWeight (n + 1) j : ℕ) : ℂ)⁻¹)) =
        ∏ i ∈ Rᶜ, (syl (i.1 + 1) : ℂ)⁻¹ := by
    rw [hvan, Finset.prod_image hinj.injOn]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hscale]
  have hrootprod : (∏ j ∈ sourceRootSupport (n + 1) ζ,
        (1 - ζ ^ partitionWeight (n + 1) j)) =
        (1 - ζ) ^ 2 * ∏ i ∈ R, chord i := by
    rw [hsupport]
    have hn : (none : Option (Fin (n + 1))) ∉
          insert (some (Fin.last n)) (R.image fun i => some i.castSucc) := by
      simp
    have hl : (some (Fin.last n) : Option (Fin (n + 1))) ∉
          R.image (fun i => some i.castSucc) := by
      simp [Fin.castSucc_ne_last]
    have hbase (i : Fin n) : baseWeight (n + 1) i.castSucc = M / syl (i.1 + 1) := by
      simpa [partitionWeight] using hweight i
    rw [Finset.prod_insert hn, Finset.prod_insert hl, Finset.prod_image hinj.injOn]
    simp [partitionWeight, baseWeight_last, hbase, chord, pow_two]
    ring
  have hS : 0 < S := Finset.prod_pos fun i hi => sylvester_pos _
  have hcomp : (∏ i ∈ Rᶜ, (syl (i.1 + 1) : ℂ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact_mod_cast (Nat.ne_of_gt (sylvester_pos (i.1 + 1)))
  have hsplitC : (S : ℂ) * (∏ i ∈ Rᶜ, (syl (i.1 + 1) : ℂ)) = (M : ℂ) := by
    exact_mod_cast hsplit
  have hqprod : (∏ i ∈ Rᶜ, (syl (i.1 + 1) : ℂ)⁻¹) =
        (S : ℂ) * (M : ℂ)⁻¹ := by
    rw [Finset.prod_inv_distrib]
    field_simp [Nat.ne_of_gt hM, Nat.ne_of_gt hS, hcomp]
    simpa [mul_comm] using hsplitC.symm
  rw [hvprod, hqprod, hrootprod] at hnormalized
  change
    T = PowerSeries.C
        ((S : ℂ) * (M : ℂ)⁻¹ * ((1 - ζ) ^ 2 * ∏ i ∈ R, chord i)) *
      sourceExponentialLocalJet (n + 1) ζ c at hnormalized
  have hcoeff := congrArg (PowerSeries.coeff (4 - R.card)) hnormalized
  rw [PowerSeries.coeff_C_mul] at hcoeff
  have hone : (1 - ζ) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hζne.symm)
  have hchords : (∏ i ∈ R, chord i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact sub_ne_zero.mpr (Finset.mem_filter.mp hi).2.symm
  have hroot : (1 - ζ) ^ 2 * ∏ i ∈ R, chord i ≠ 0 := mul_ne_zero hone hchords
  have hsc : (sourceRootSupport (n + 1) ζ).card ≤ 6 := by omega
  have hExact : (sourceLocalRootContributionPolynomial (n + 1) ζ c).coeff (n + 1 - 6) =
        ζ ^ (-c) * ((n + 1 - 6).factorial : ℂ)⁻¹ * (S : ℂ)⁻¹ *
          ((1 - ζ) ^ 2 * ∏ i ∈ R, chord i)⁻¹ *
          PowerSeries.coeff (4 - R.card) T := by
    rw [sourceLocalRootContributionPolynomial_target_coeff
      (n + 1) (by omega) ζ c hsc, hcard]
    rw [show 6 - (R.card + 2) = 4 - R.card by omega]
    have hMC : (M : ℂ) = (syl (n + 1) : ℂ) - 1 := by
      dsimp [M]
      rw [Nat.cast_sub (by
        have := sylvester_pos (n + 1)
        omega)]
      norm_num
    rw [← hMC]
    change
      ζ ^ (-c) * (M : ℂ)⁻¹ * ((n + 1 - 6).factorial : ℂ)⁻¹ * PowerSeries.coeff (4 - R.card)
            (sourceExponentialLocalJet (n + 1) ζ c) = _
    rw [hcoeff]
    field_simp [Nat.ne_of_gt hM, Nat.ne_of_gt hS, hroot, hone, hchords]
  have hchordPos : 0 < ∏ i ∈ R, ‖chord i‖ := by
    apply Finset.prod_pos
    intro i hi
    exact norm_pos_iff.mpr (by
      simpa [chord] using
        (sub_ne_zero.mpr (Finset.mem_filter.mp hi).2.symm))
  have honePos : 0 < ‖1 - ζ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hζne.symm)
  have hden : 0 < ((n + 1 - 6).factorial : ℝ) * (S : ℝ) * ‖1 - ζ‖ ^ 2 *
        ∏ i ∈ R, ‖chord i‖ := by
    positivity
  refine ⟨hRne, hsupport, hcard, hpole, hden, ?_⟩
  rw [hExact]
  simp only [norm_mul, hphase, one_mul, norm_inv, Complex.norm_natCast, norm_pow, norm_prod]
  have heq : ((n + 1 - 6).factorial : ℝ)⁻¹ * (S : ℝ)⁻¹ *
          (‖1 - ζ‖ ^ 2 * ∏ i ∈ R, ‖chord i‖)⁻¹ =
        1 / (((n + 1 - 6).factorial : ℝ) * (S : ℝ) * ‖1 - ζ‖ ^ 2 * ∏ i ∈ R, ‖chord i‖) := by
    field_simp [ne_of_gt hden]
  rw [heq]
  calc _ = ‖PowerSeries.coeff (4 - R.card) T‖ /
        (((n + 1 - 6).factorial : ℝ) * (S : ℝ) * ‖1 - ζ‖ ^ 2 * ∏ i ∈ R, ‖chord i‖) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hTbound (le_of_lt hden)

end D5.S0.FiniteGeometry.SylvesterSimplexEhrhartRootContributionLowSupportBound
