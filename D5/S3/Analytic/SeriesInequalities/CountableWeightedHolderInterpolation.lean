/- GID: D5/S3/Analytic/SeriesInequalities/CountableWeightedHolderInterpolation
   generality: I
   mirror-B: D5/B/S3/Analytic/SeriesInequalities/CountableWeightedHolderInterpolation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Countable weighted geometric means obey a Holder interpolation bound. -/

/- Library-search audit trail (2026-08-27):
* Searches of pinned `Mathlib/**/*.lean` for Holder, rpow, tsum, summable, interpolation,
  and log-convex combinations found the lower-level theorem
  `Real.inner_le_Lp_mul_Lq_tsum_of_nonneg`, but no theorem with nonnegative summable endpoint
  families and positive complementary weights as its interface.
* Repository search found three private specializations: `Zeta/ZetaRenyiMonotone` and
  `ZetaEntropyPlane/TemperatureAntitone`, both merged and frozen with 2026-08-23 search
  receipts, and `Convexity/GoldenDisplacementSeriesLogConvexity`, revised with this module.
* The two frozen modules cannot be changed into consumers. The three implementations still
  establish demand beyond the extraction threshold, and the displacement revision gives this
  public declaration a consumer in the same delivery.
-/

import Mathlib.Analysis.MeanInequalities

namespace D5.S3.Analytic.SeriesInequalities.CountableWeightedHolderInterpolation

noncomputable section

/-- Countable weighted Holder interpolation for two nonnegative summable real families. -/
theorem countable_weighted_holder_interpolation
    {ι : Type*} {f g : ι → ℝ} {a b : ℝ}
    (hf_nonneg : ∀ i, 0 ≤ f i) (hg_nonneg : ∀ i, 0 ≤ g i)
    (hf_sum : Summable f) (hg_sum : Summable g)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    (∑' i, f i ^ a * g i ^ b) ≤ (∑' i, f i) ^ a * (∑' i, g i) ^ b := by
  have hconj : a⁻¹.HolderConjugate b⁻¹ :=
    Real.HolderConjugate.inv_inv ha hb hab
  have hpow_f : (fun i : ι => (f i ^ a) ^ a⁻¹) = f := by
    funext i
    rw [← Real.rpow_mul (hf_nonneg i)]
    have hcancel : a * a⁻¹ = 1 := by field_simp [ha.ne']
    rw [hcancel, Real.rpow_one]
  have hpow_g : (fun i : ι => (g i ^ b) ^ b⁻¹) = g := by
    funext i
    rw [← Real.rpow_mul (hg_nonneg i)]
    have hcancel : b * b⁻¹ = 1 := by field_simp [hb.ne']
    rw [hcancel, Real.rpow_one]
  have hf_power_sum : Summable (fun i : ι => (f i ^ a) ^ a⁻¹) := by
    rw [hpow_f]
    exact hf_sum
  have hg_power_sum : Summable (fun i : ι => (g i ^ b) ^ b⁻¹) := by
    rw [hpow_g]
    exact hg_sum
  have hholder := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hconj
    (fun i : ι => Real.rpow_nonneg (hf_nonneg i) a)
    (fun i : ι => Real.rpow_nonneg (hg_nonneg i) b)
    hf_power_sum hg_power_sum
  have ha_inv : 1 / a⁻¹ = a := by field_simp [ha.ne']
  have hb_inv : 1 / b⁻¹ = b := by field_simp [hb.ne']
  simpa only [hpow_f, hpow_g, ha_inv, hb_inv] using hholder

end

end D5.S3.Analytic.SeriesInequalities.CountableWeightedHolderInterpolation
