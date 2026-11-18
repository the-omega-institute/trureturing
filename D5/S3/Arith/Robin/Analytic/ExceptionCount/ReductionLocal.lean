/- GID: D5/S3/Arith/Robin/Analytic/ExceptionCount/ReductionLocal
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/Analytic/ExceptionCount/ReductionLocal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Convexity bounds for normalized real-power divisor factors. -/

import D5.S3.Arith.Robin.Analytic.LcmPowerLocalFactorBound

/-! Local-factor majorants and finite support replacement. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Set
open scoped BigOperators

namespace D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionLocal
open LcmPowerLocalFactorBound

private lemma power_difference_le {κ r t : ℝ} (hκ : 1 ≤ κ)
    (hr0 : 0 < r) (hrhalf : r ≤ 1 / 2) (ht0 : 0 < t) (htr : t ≤ r ^ 2) :
    (1 - t) ^ κ - (r - t) ^ κ ≤ 1 - r ^ κ := by
  have hr1 : r < 1 := by linarith
  have htlt : t < r := lt_of_le_of_lt htr (by nlinarith)
  have hB0 : 0 ≤ r - t := by linarith
  have hAr : r < 1 - t := by nlinarith
  have hA0 : 0 ≤ 1 - t := by linarith
  have hA1 : 1 - t < 1 := by linarith
  have hc := convexOn_rpow hκ
  have hfirst := hc.slope_mono_adjacent (x := r - t) (y := r) (z := 1 - t)
    hB0 hA0 (by linarith) hAr
  have hsecond := hc.slope_mono_adjacent (x := r) (y := 1 - t) (z := 1)
    hr0.le (by norm_num) hAr hA1
  have hcompare := hfirst.trans hsecond
  have hden : r - (r - t) = t := by ring
  have hden' : 1 - (1 - t) = t := by ring
  rw [hden, hden', Real.one_rpow] at hcompare
  have h := (div_le_div_iff_of_pos_right ht0).mp hcompare
  linarith

/-- The normalized prime-power factor is bounded by its infinite-exponent endpoint. -/
theorem local_factor_upper_bound {κ r a : ℝ} (hκ : 1 ≤ κ) (hr0 : 0 ≤ r)
    (hrhalf : r ≤ 1 / 2) (ha : 1 ≤ a) :
    normalizedLocalFactor κ r a ≤ (1 - r) ^ (-κ) * (1 - r ^ κ) := by
  rcases eq_or_lt_of_le hr0 with rfl | hr
  · have hκ0 : κ ≠ 0 := by linarith
    have ha0 : a ≠ 0 := by linarith
    have ha1 : a + 1 ≠ 0 := by linarith
    simp [normalizedLocalFactor, hκ0, ha0, ha1]
  have hr1 : r ≤ 1 := by linarith
  have ht0 : 0 < r ^ (a + 1) := Real.rpow_pos_of_pos hr _
  have htr : r ^ (a + 1) ≤ r ^ 2 := by
    simpa only [Real.rpow_two] using
      (Real.rpow_le_rpow_of_exponent_ge hr hr1 (show (2 : ℝ) ≤ a + 1 by linarith))
  have hbase : 0 ≤ 1 - r ^ a :=
    sub_nonneg.mpr (Real.rpow_le_one hr.le hr1 (by linarith))
  have hid : r ^ κ * (1 - r ^ a) ^ κ = (r - r ^ (a + 1)) ^ κ := by
    rw [← Real.mul_rpow hr.le hbase, Real.rpow_add hr, Real.rpow_one]
    congr 1
    ring
  have hb := power_difference_le hκ hr hrhalf ht0 htr
  dsimp only [normalizedLocalFactor]
  rw [hid]
  exact mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg (by linarith) _)

private lemma power_increment_monotone {κ : ℝ} (hκ : 1 ≤ κ) :
    MonotoneOn (fun t : ℝ => (t + 1) ^ κ - t ^ κ) (Ici 0) := by
  have hder (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt (fun t : ℝ => (t + 1) ^ κ - t ^ κ)
        (κ * ((t + 1) ^ (κ - 1) - t ^ (κ - 1))) t := by
    convert (((hasDerivAt_id t).add_const 1).rpow_const
      (p := κ) (Or.inr (by linarith))).sub
        (Real.hasDerivAt_rpow_const (Or.inr hκ)) using 1
    · rfl
    · dsimp only [id_eq]
      ring
  apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
  · intro t ht
    exact (hder t ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (hder t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hder t (interior_subset ht)).deriv]
    exact mul_nonneg (by linarith) (sub_nonneg.mpr
      (Real.rpow_le_rpow (interior_subset ht) (by linarith) (by linarith)))

/-- The infinite-exponent endpoint increases with the reciprocal prime. -/
theorem endpoint_monotone {κ : ℝ} (hκ : 1 ≤ κ) :
    MonotoneOn (fun r : ℝ => (1 - r) ^ (-κ) * (1 - r ^ κ)) (Ico 0 1) := by
  have hid (r : ℝ) (hr : r ∈ Ico (0 : ℝ) 1) :
      (1 - r) ^ (-κ) * (1 - r ^ κ) =
        (r / (1 - r) + 1) ^ κ - (r / (1 - r)) ^ κ := by
    have hpos : 0 < 1 - r := sub_pos.mpr hr.2
    have hsum : r / (1 - r) + 1 = 1 / (1 - r) := by field_simp; ring
    rw [hsum, Real.div_rpow hr.1 hpos.le, Real.div_rpow zero_le_one hpos.le,
      Real.one_rpow, Real.rpow_neg hpos.le]
    ring
  intro r hr s hs hrs
  have hr' : 0 ≤ r ∧ r < 1 := hr
  have hs' : 0 ≤ s ∧ s < 1 := hs
  dsimp only
  rw [hid r hr, hid s hs]
  apply power_increment_monotone hκ (div_nonneg hr.1 (by linarith))
    (div_nonneg hs.1 (by linarith))
  apply (div_le_div_iff₀ (by linarith : 0 < 1 - r)
    (by linarith : 0 < 1 - s)).mpr
  nlinarith

/-- A larger initial support dominates a smaller support when all missing
factors dominate all displaced factors at a common boundary. -/
theorem support_product_le {S T : Finset ℕ} {f : ℕ → ℝ} {B : ℝ}
    (hcard : S.card ≤ T.card) (hB : 1 ≤ B)
    (hpos : ∀ p ∈ S, 0 ≤ f p)
    (hlo : ∀ p ∈ S \ T, f p ≤ B)
    (hhi : ∀ p ∈ T \ S, B ≤ f p) :
    (∏ p ∈ S, f p) ≤ ∏ p ∈ T, f p := by
  classical
  have hST : (∏ p ∈ S \ T, f p) ≤ B ^ (S \ T).card := by
    simpa using Finset.prod_le_prod₀
      (fun p hp => hpos p (Finset.mem_sdiff.mp hp).1) hlo
  have hTS : B ^ (T \ S).card ≤ ∏ p ∈ T \ S, f p := by
    simpa using Finset.prod_le_prod₀ (fun _ _ => zero_le_one.trans hB) hhi
  have hcounts : (S \ T).card ≤ (T \ S).card :=
    Finset.card_sdiff_le_card_sdiff_iff.mpr hcard
  have hpow : B ^ (S \ T).card ≤ B ^ (T \ S).card :=
    pow_le_pow_right₀ hB hcounts
  have hprod := hST.trans (hpow.trans hTS)
  have hcommon : 0 ≤ ∏ p ∈ S ∩ T, f p :=
    Finset.prod_nonneg (fun p hp => hpos p (Finset.mem_inter.mp hp).1)
  have hidS : S \ (S ∩ T) = S \ T := by ext p; simp
  have hidT : T \ (S ∩ T) = T \ S := by ext p; simp
  rw [← Finset.prod_sdiff (s₁ := S ∩ T) (s₂ := S) Finset.inter_subset_left,
    ← Finset.prod_sdiff (s₁ := S ∩ T) (s₂ := T) Finset.inter_subset_right,
    hidS, hidT]
  exact mul_le_mul_of_nonneg_right hprod hcommon

end D5.S3.Arith.Robin.Analytic.ExceptionCount.ReductionLocal
