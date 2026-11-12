/- GID: D5/S3/Arith/Robin/PriceRecord/ActualRecordElementarySingleTwoTail
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualRecordElementarySingleTwoTail
   mirror-E: none(waiver:elementary-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Elementary single extra binary layer for all original records. -/

import D5.S3.Arith.Robin.PriceRecord.ActualRecordSingleTwoTail
import D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap

/-! Actual finite prime exchanges at the original arbitrary positive price.
The logarithmically weighted marginal estimate uses the original record balance
law and elementary gain bounds. No BHP supplier or infinite record tail is used. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.ActualRecordElementarySingleTwoTail

open Real Filter Finset
open scoped Topology BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (price_record_prime_structure)
open D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope (beta gain beta_pos beta_nat)
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
  (layerPrime valuation_above_layer_prime)
open D5.S3.Arith.Robin.PriceRecord.LogarithmicLayerRigidity
open D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature (normalized_gain_bounds)
open D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
  (FullRecord logMass priceLip price_variation priceLip_half_bound first_beta_lower
   largestPrime_prime)
open D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack
  (actual_finite_predecessor topGain auxiliaryGain)
open D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap (ownPrice)

private theorem weighted_gain_error {α : Type*} {l : Filter α}
    (X u : α → ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hX : ∀ᶠ t in l, 0 ≤ X t) (hu : Tendsto u l atTop)
    (hsmall : Tendsto (fun t => X t / u t) l (𝓝 0)) :
    Tendsto (fun t => X t * (gain j (u t) * u t ^ j - 1)) l (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using hsmall.neg) tendsto_const_nhds
  · filter_upwards [hX, hu.eventually_ge_atTop 2] with t hXt hut
    have hh := mul_le_mul_of_nonneg_left (normalized_gain_bounds hj hut).1 hXt
    nlinarith only [hh]
  · filter_upwards [hX, hu.eventually_ge_atTop 2] with t hXt hut
    have hh := mul_le_mul_of_nonneg_left (normalized_gain_bounds hj hut).2.1 hXt
    nlinarith only [hh]

private theorem weighted_boundary_limit {α : Type*} {l : Filter α}
    (m : α → ℕ) (mu : α → ℝ) (hm : ∀ t, 2 ≤ m t)
    (hmu : ∀ t, 0 < mu t) (hrecord : ∀ t, FullRecord (m t) (mu t))
    (hP : Tendsto (fun t => (largestPrime (m t) : ℝ)) l atTop) :
    Tendsto (fun t => log (largestPrime (m t) : ℝ) *
      (beta 2 (layerPrime (m t) 2 : ℝ) / beta 1 (largestPrime (m t) : ℝ) - 1))
      l (𝓝 0) := by
  let P : α → ℝ := fun t => largestPrime (m t)
  let Q : α → ℝ := fun t => layerPrime (m t) 2
  let X : α → ℝ := fun t => log (P t)
  let H : α → ℝ := fun t => log (Q t)
  let A : α → ℝ := fun t => gain 1 (P t) * P t
  let B : α → ℝ := fun t => gain 2 (Q t) * Q t ^ 2
  let R : α → ℝ := fun t => Q t ^ 2 * H t / (P t * X t)
  have hratio := record_ratio_limit m mu hm hmu hrecord 2 (by omega) hP
  obtain ⟨hQ, hHX, _hsep⟩ := coarse_scale_limits P Q 2 (by omega)
    (fun t => Nat.cast_nonneg _) hP hratio
  have hX : Tendsto X l atTop := tendsto_log_atTop.comp hP
  have hH : Tendsto H l atTop := tendsto_log_atTop.comp hQ
  have hXH : Tendsto (fun t => X t / H t) l (𝓝 2) := by
    simpa using hHX.inv₀ (by norm_num : (2 : ℝ)⁻¹ ≠ 0)
  have hXP : Tendsto (fun t => X t / P t) l (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hP
  have hHQ : Tendsto (fun t => H t / Q t) l (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hQ
  have hXQ : Tendsto (fun t => X t / Q t) l (𝓝 0) := by
    apply (show Tendsto (fun t => X t / H t * (H t / Q t)) l (𝓝 0) from
      by simpa using hXH.mul hHQ).congr'
    filter_upwards [hH.eventually_gt_atTop 0] with t ht
    field_simp [ht.ne']
  have hAerr : Tendsto (fun t => X t * (A t - 1)) l (𝓝 0) := by
    simpa [A] using weighted_gain_error X P 1 (by omega)
      (hX.eventually_ge_atTop 0) hP hXP
  have hBerr : Tendsto (fun t => X t * (B t - 1)) l (𝓝 0) :=
    weighted_gain_error X Q 2 (by omega) (hX.eventually_ge_atTop 0) hQ hXQ
  have hA : Tendsto A l (𝓝 1) := by
    have hh := hAerr.div_atTop hX
    have hh' := hh.add_const 1
    simp only [zero_add] at hh'
    apply hh'.congr'
    filter_upwards [hX.eventually_gt_atTop 0] with t ht
    field_simp [ht.ne']
  have hR : Tendsto R l (𝓝 1) := by
    have hh := hratio.mul hHX
    norm_num only [Nat.cast_ofNat, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0)] at hh
    convert hh using 1 <;> dsimp [R, H, X] <;> congr 1
    funext t
    ring
  have hRerr : Tendsto (fun t => X t * (R t - 1)) l (𝓝 0) :=
    record_logarithmic_balance_limit m mu hm hmu hrecord 2 (by omega) hP
  have hnum := (hBerr.sub hAerr).sub (hA.mul hRerr)
  have hden := hA.mul hR
  have hlim := hnum.div hden (by norm_num : (1 : ℝ) * 1 ≠ 0)
  simp only [sub_zero, mul_zero, zero_sub, one_mul, zero_div] at hlim
  apply hlim.congr'
  filter_upwards [hP.eventually_gt_atTop 1, hQ.eventually_gt_atTop 1] with t hp hq
  have hg : gain 1 (P t) ≠ 0 :=
    (HigherLayerLogSlope.gain_pos (by linarith) (by omega)).ne'
  change (X t * (B t - 1) - X t * (A t - 1) - A t * (X t * (R t - 1))) /
    (A t * R t) = X t * (beta 2 (Q t) / beta 1 (P t) - 1)
  dsimp [A, B, R, X, H, beta]
  field_simp [hg, (by linarith : P t ≠ 0), (by linarith : Q t ≠ 0),
    (log_pos hp).ne', (log_pos hq).ne'] <;> ring

end D5.S3.Arith.Robin.PriceRecord.ActualRecordElementarySingleTwoTail
