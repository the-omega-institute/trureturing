/- GID: D5/S3/Arith/Robin/PriceRecord/QuantitativeMovingPriceMinimizerClock
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/QuantitativeMovingPriceMinimizerClock
   mirror-E: none(waiver:quantitative-prime-number-theorem)
   anchors: []
   utility: none
   digest: All fixed logarithmic orders for the moving-price clock on the literal prime prefix. -/

import D5.S3.Arith.Robin.PriceRecord.FixedPriceMinimizerClock
import D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster
import D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel

/-!
# Quantitative clock localization at a moving price

The second-layer clock is squeezed at the actual marginal cutoff. The
relative price band gives bounded cutoff displacement, and the quantitative
prime estimate and the finite higher-layer bound give the logarithmic rate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.QuantitativeMovingPriceMinimizerClock

open Filter Finset Real
open scoped BigOperators Topology Chebyshev
open FixedSupportIntegerActivationEnvelope (clockIncrement)
open FixedPriceMinimizerClock
  (IsMinimizer layer_optimality headClock clock_split higher_bounds
    majorant majorant_atTop higherBound eventual_price_bounds endpoint_inside_prefix)
open HigherLayerClampedCutoff (cutoff cutoff_spec cutoff_antitone cutoff_occupancy cutoff_movement)
open HigherLayerLogSlope (beta beta_strictAntiOn)
open RealInfimumPrimeBoundary
  (prefixH prefixEll prefixPrice prefixH_atTop prefixEll_atTop eventual_prefix_domains)
open IntegerInfimumSecondOrder (log_pow_over_H_rpow log_pow_over_sqrt_H)
open QuantitativePrimeAbel (theta_error_log_power)
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference (referencePrice)

private def baseCutoff (P : ℕ) : ℝ := cutoff 2 (prefixPrice P)
private def logScale (n P : ℕ) : ℝ := log (prefixH P) ^ n / sqrt (prefixH P)

private theorem baseCutoff_ratio :
    Tendsto (fun P => baseCutoff P / sqrt (prefixH P)) atTop (𝓝 (sqrt 2)) := by
  simpa only [baseCutoff, Function.comp_def, sqrt_eq_rpow, prefixPrice,
    ActualRobinClockCovariance.g, referencePrice, Nat.cast_ofNat, one_div] using
    (FixedLayerShrinkingPrimeRoster.root_ratio (show 2 ≤ (2 : ℕ) by decide)).comp prefixH_atTop

private theorem baseCutoff_atTop : Tendsto baseCutoff atTop atTop := by
  exact (FixedLayerShrinkingPrimeRoster.root_atTop (j := 2) le_rfl).comp prefixH_atTop

private theorem baseCutoff_log_ratio :
    Tendsto (fun P => log (baseCutoff P) / log (prefixH P)) atTop (𝓝 (1 / 2 : ℝ)) := by
  simpa only [baseCutoff, Function.comp_def, prefixPrice,
    ActualRobinClockCovariance.g, referencePrice, Nat.cast_ofNat, one_div] using
    (FixedLayerShrinkingPrimeRoster.root_log_ratio (show 2 ≤ (2 : ℕ) by decide)).comp prefixH_atTop

private theorem logScale_nonneg (n : ℕ) {P : ℕ} (hH : 1 ≤ prefixH P) :
    0 ≤ logScale n P :=
  div_nonneg (pow_nonneg (log_nonneg hH) n) (sqrt_nonneg _)

private theorem price_ratio_tendsto {lam : ℕ → ℝ} {C : ℝ}
    (hband : ∀ᶠ P : ℕ in atTop,
      |lam P / prefixPrice P - 1| ≤ C / sqrt (prefixH P)) :
    Tendsto (fun P => lam P / prefixPrice P) atTop (𝓝 1) := by
  have hhi := (tendsto_sqrt_atTop.comp prefixH_atTop).const_div_atTop C
  have hlo := hhi.neg
  simp only [neg_zero] at hlo
  have herr : Tendsto (fun P => lam P / prefixPrice P - 1) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
      (hband.mono fun _ h => (abs_le.mp h).1)
      (hband.mono fun _ h => (abs_le.mp h).2)
  simpa only [sub_add_cancel, zero_add] using herr.add_const 1

private theorem cutoff_displacement {lam : ℕ → ℝ} {C : ℝ}
    (hband : ∀ᶠ P : ℕ in atTop,
      |lam P / prefixPrice P - 1| ≤ C / sqrt (prefixH P)) :
    ∀ᶠ P : ℕ in atTop,
      |cutoff 2 (lam P) - baseCutoff P| ≤ 27 * (|C| + 1) := by
  let D : ℝ := |C| + 1
  have hD : 0 < D := by dsimp [D]; linarith only [abs_nonneg C]
  have hs := (tendsto_sqrt_atTop.comp prefixH_atTop).const_div_atTop D
  have hsqrt2 : sqrt (2 : ℝ) < 3 := by
    rw [sqrt_lt' (by norm_num : (0 : ℝ) < 3)]
    norm_num
  filter_upwards [hband, eventual_prefix_domains, prefixH_atTop.eventually_gt_atTop 0,
    hs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 9)),
    baseCutoff_ratio.eventually (eventually_lt_nhds hsqrt2)]
    with P hbandP hdomains hH hsSmall hbase
  let s : ℝ := D / sqrt (prefixH P)
  let η := prefixPrice P
  let lo := cutoff 2 ((1 + s) * η)
  let hi := cutoff 2 ((1 - s) * η)
  have hη : 0 < η := hdomains.2.2.2.1
  have hSqrt : 0 < sqrt (prefixH P) := sqrt_pos.mpr hH
  have hsPos : 0 < s := div_pos hD hSqrt
  have hsSmall' : s ≤ 1 / 9 := le_of_lt hsSmall
  have hsHalf : s ≤ 1 / 2 := by linarith only [hsSmall']
  have hj : 2 ≤ (2 : ℕ) := le_rfl
  have hBand : |lam P / η - 1| ≤ s := hbandP.trans
    (div_le_div_of_nonneg_right
      ((le_abs_self C).trans (by dsimp [D]; linarith)) hSqrt.le)
  have hLamLo : (1 - s) * η ≤ lam P := (le_div_iff₀ hη).mp (by
    linarith only [(abs_le.mp hBand).1])
  have hLamHi : lam P ≤ (1 + s) * η := (div_le_iff₀ hη).mp (by
    linarith only [(abs_le.mp hBand).2])
  have hPosLo : 0 < (1 - s) * η := mul_pos (by linarith only [hsHalf]) hη
  have hPosHi : 0 < (1 + s) * η := mul_pos (by linarith only [hsPos]) hη
  have hLam : 0 < lam P := hPosLo.trans_le hLamLo
  have hBaseLo : lo ≤ baseCutoff P :=
    cutoff_antitone hj hη hPosHi (by nlinarith only [mul_nonneg hsPos.le hη.le])
  have hBaseHi : baseCutoff P ≤ hi :=
    cutoff_antitone hj hPosLo hη (by nlinarith only [mul_nonneg hsPos.le hη.le])
  have hMoveLo : lo ≤ cutoff 2 (lam P) := cutoff_antitone hj hLam hPosHi hLamHi
  have hMoveHi : cutoff 2 (lam P) ≤ hi := cutoff_antitone hj hPosLo hLam hLamLo
  have hWidth : hi - lo ≤ 9 * s * hi / 2 := by
    simpa only [Nat.cast_ofNat] using (cutoff_movement hj hη hsPos hsHalf)
  have hHiNonneg : 0 ≤ hi :=
    (by norm_num : (0 : ℝ) ≤ 2).trans (cutoff_spec hj hPosLo).1
  have hHi : hi ≤ 2 * baseCutoff P := by
    nlinarith only [hWidth, hBaseLo, mul_nonneg (show 0 ≤ 1 - 9 * s by linarith) hHiNonneg]
  have hBase : baseCutoff P ≤ 3 * sqrt (prefixH P) := ((div_lt_iff₀ hSqrt).mp hbase).le
  have hScale : s * sqrt (prefixH P) = D := div_mul_cancel₀ D hSqrt.ne'
  have hWidthD : hi - lo ≤ 27 * D := by
    calc
      hi - lo ≤ 9 * s * hi / 2 := hWidth
      _ ≤ 9 * s * (2 * (3 * sqrt (prefixH P))) / 2 := by
        have h := hHi.trans (mul_le_mul_of_nonneg_left hBase (by norm_num))
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h (by positivity)) (by norm_num)
      _ = 27 * D := by linear_combination 27 * hScale
  exact abs_le.mpr ⟨by linarith only [hWidthD, hMoveLo, hBaseHi],
    by linarith only [hWidthD, hMoveHi, hBaseLo]⟩

private theorem head_at_cutoff {P : ℕ} {lam : ℝ} {a : ℕ → ℕ}
    (ha : IsMinimizer (Nat.primesLE P) lam a) (hlam : 0 < lam)
    (hinside : cutoff 2 lam ≤ (P : ℝ)) :
    θ (cutoff 2 lam - 1) ≤ headClock P a ∧ headClock P a ≤ θ (cutoff 2 lam) := by
  classical
  have hj : 2 ≤ (2 : ℕ) := le_rfl
  obtain ⟨htwo, hcutPrice, _, _⟩ := cutoff_spec hj hlam
  simp only [Chebyshev.theta_eq_sum_primesLE, headClock]
  constructor
  · apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hfloor, hprime⟩ := Nat.mem_primesLE.mp hp
      have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
      have hpLow := (Nat.le_floor_iff (show 0 ≤ cutoff 2 lam - 1 by linarith)).mp hfloor
      have hpBelow : (p : ℝ) < cutoff 2 lam := by linarith only [hpLow]
      have hpP : p ≤ P := by exact_mod_cast hpBelow.le.trans hinside
      have hpS := Nat.mem_primesLE.mpr ⟨hpP, hprime⟩
      have hprofit := (cutoff_occupancy hj hlam hpTwo).mpr hpBelow
      have htake : 2 ≤ a p := by
        by_contra! hskip
        exact (not_le_of_gt hprofit) ((layer_optimality ha hpS hprime hj).2 hskip)
      exact mem_filter.mpr ⟨hpS, htake⟩
    · intro p hp _
      exact (Nat.mem_primesLE.mp (mem_filter.mp hp).1).2.log_pos.le
  · apply sum_le_sum_of_subset_of_nonneg
    · intro p hp
      obtain ⟨hpS, htake⟩ := mem_filter.mp hp
      have hprime := (Nat.mem_primesLE.mp hpS).2
      have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast hprime.two_le
      have hpCut : (p : ℝ) ≤ cutoff 2 lam := by
        by_contra! hAbove
        have hDrop := beta_strictAntiOn hj
          (show cutoff 2 lam ∈ Set.Ici 2 from htwo)
          (show (p : ℝ) ∈ Set.Ici 2 from hpTwo) hAbove
        exact (not_lt_of_ge ((layer_optimality ha hpS hprime hj).1 htake))
          (hDrop.trans_le hcutPrice)
      exact Nat.mem_primesLE.mpr
        ⟨(Nat.le_floor_iff (show 0 ≤ cutoff 2 lam by linarith)).mpr hpCut, hprime⟩
    · intro p hp _
      exact (Nat.mem_primesLE.mp hp).2.log_pos.le

private theorem offset_tendsto (n : ℕ) {y : ℕ → ℝ} {K : ℝ}
    (hy : ∀ᶠ P : ℕ in atTop, |y P - baseCutoff P| ≤ K) :
    Tendsto (fun P => logScale n P * (y P - baseCutoff P)) atTop (𝓝 0) := by
  have hUpper := (log_pow_over_sqrt_H n).mul_const K
  have hLower := (log_pow_over_sqrt_H n).mul_const (-K)
  simp only [zero_mul] at hLower hUpper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hLower hUpper
  · filter_upwards [hy, prefixH_atTop.eventually_ge_atTop 1] with P hp hH
    exact mul_le_mul_of_nonneg_left (abs_le.mp hp).1 (logScale_nonneg n hH)
  · filter_upwards [hy, prefixH_atTop.eventually_ge_atTop 1] with P hp hH
    exact mul_le_mul_of_nonneg_left (abs_le.mp hp).2 (logScale_nonneg n hH)

private theorem endpoint_ratio {y : ℕ → ℝ} {K : ℝ}
    (hy : ∀ᶠ P : ℕ in atTop, |y P - baseCutoff P| ≤ K) :
    Tendsto (fun P => y P / sqrt (prefixH P)) atTop (𝓝 (sqrt 2)) := by
  have h := baseCutoff_ratio.add (offset_tendsto 0 hy)
  rw [add_zero] at h
  apply h.congr
  intro P
  simp only [logScale, pow_zero]
  ring

private theorem theta_endpoint_tendsto (n : ℕ) {y : ℕ → ℝ} {K : ℝ}
    (hy : ∀ᶠ P : ℕ in atTop, |y P - baseCutoff P| ≤ K) :
    Tendsto (fun P => logScale n P * (θ (y P) - baseCutoff P)) atTop (𝓝 0) := by
  have hyTop : Tendsto y atTop atTop := by
    apply tendsto_atTop_mono' atTop ?_ (tendsto_atTop_add_const_right atTop (-K) baseCutoff_atTop)
    filter_upwards [hy] with P hp
    change baseCutoff P + -K ≤ y P
    linarith only [(abs_le.mp hp).1]
  have hyRatio := endpoint_ratio hy
  have hSqrt : sqrt (2 : ℝ) ≠ 0 := (sqrt_pos.mpr (by norm_num)).ne'
  have hyBase : Tendsto (fun P => y P / baseCutoff P) atTop (𝓝 1) := by
    have h := hyRatio.div baseCutoff_ratio hSqrt
    rw [div_self hSqrt] at h
    apply h.congr'
    filter_upwards [prefixH_atTop.eventually_gt_atTop 0] with P hH
    exact div_div_div_cancel_right₀ (sqrt_pos.mpr hH).ne' _ _
  have hyLog : Tendsto (fun P => log (y P) / log (prefixH P)) atTop (𝓝 (1 / 2 : ℝ)) := by
    have h := baseCutoff_log_ratio.add ((hyBase.log one_ne_zero).div_atTop prefixEll_atTop)
    rw [add_zero] at h
    apply h.congr'
    filter_upwards [hyTop.eventually_gt_atTop 0, baseCutoff_atTop.eventually_gt_atTop 0]
      with P hyPos hbPos
    change log (baseCutoff P) / log (prefixH P) +
      log (y P / baseCutoff P) / log (prefixH P) = _
    rw [log_div hyPos.ne' hbPos.ne']
    ring
  have hInv : Tendsto (fun P => log (prefixH P) / log (y P)) atTop (𝓝 ((1 / 2 : ℝ)⁻¹)) := by
    simpa only [inv_div] using hyLog.inv₀ (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have hPnt := (theta_error_log_power n).tendsto_div_nhds_zero.comp hyTop
  have h := ((hPnt.mul (hInv.pow n)).mul hyRatio).add (offset_tendsto n hy)
  simp only [zero_mul, zero_add] at h
  apply h.congr'
  filter_upwards [hyTop.eventually_gt_atTop 1, prefixH_atTop.eventually_gt_atTop 0]
    with P hyOne hH
  have hyNe : y P ≠ 0 := by linarith only [hyOne]
  change (θ (y P) - y P) / (y P / log (y P) ^ n) *
    (log (prefixH P) / log (y P)) ^ n * (y P / sqrt (prefixH P)) +
    logScale n P * (y P - baseCutoff P) = _
  simp only [logScale, div_pow, div_div_eq_mul_div]
  field_simp [hyNe, (log_pos hyOne).ne', (sqrt_pos.mpr hH).ne']
  ring

private theorem higher_bound_weighted_tendsto (n : ℕ) :
    Tendsto (fun P => logScale n P * higherBound P) atTop (𝓝 0) := by
  let D : ℝ := 2 / log 2
  have hlogTwo : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hD : 0 < D := div_pos (by norm_num) hlogTwo
  have hcubic : Tendsto (fun P => majorant P ^ (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp majorant_atTop
  have hTheta := EulerLayerRootCorrection.prime_number_limits.2.comp hcubic
  have hLog : Tendsto (fun P => log (majorant P) / majorant P ^ (1 / 12 : ℝ)) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 12)).tendsto_div_nhds_zero.comp
      majorant_atTop
  have hShape : Tendsto (fun P => higherBound P / majorant P ^ (5 / 12 : ℝ)) atTop (𝓝 0) := by
    have h := (hLog.div_const (log 2)).mul hTheta
    simp only [zero_div, zero_mul] at h
    apply h.congr'
    filter_upwards [majorant_atTop.eventually_gt_atTop 0] with P hB
    change log (majorant P) / majorant P ^ (1 / 12 : ℝ) / log 2 *
      (θ (majorant P ^ (1 / 3 : ℝ)) / majorant P ^ (1 / 3 : ℝ)) = _
    have hPow : majorant P ^ (1 / 12 : ℝ) * majorant P ^ (1 / 3 : ℝ) =
        majorant P ^ (5 / 12 : ℝ) := by
      rw [← rpow_add hB, show (1 / 12 : ℝ) + 1 / 3 = 5 / 12 by norm_num]
    rw [← hPow, higherBound]
    field_simp [hlogTwo.ne', (rpow_pos_of_pos hB (1 / 12 : ℝ)).ne',
      (rpow_pos_of_pos hB (1 / 3 : ℝ)).ne'] <;> ring
  have hSmall : Tendsto (fun P => D ^ (5 / 12 : ℝ) *
      (log (prefixH P) ^ (n + 1) / prefixH P ^ (1 / 12 : ℝ))) atTop (𝓝 0) := by
    simpa only [prefixEll, mul_zero] using
      (log_pow_over_H_rpow (n + 1) (by norm_num : (0 : ℝ) < 1 / 12)).const_mul
        (D ^ (5 / 12 : ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hSmall
  · filter_upwards [majorant_atTop.eventually_ge_atTop 1, prefixH_atTop.eventually_ge_atTop 1]
      with P hB hH
    exact mul_nonneg (logScale_nonneg n hH)
      (mul_nonneg (div_nonneg (log_nonneg hB) hlogTwo.le) (Chebyshev.theta_nonneg _))
  · filter_upwards [hShape.eventually (eventually_lt_nhds zero_lt_one),
      majorant_atTop.eventually_gt_atTop 0, prefixH_atTop.eventually_gt_atTop 0,
      prefixEll_atTop.eventually_ge_atTop 1, prefixH_atTop.eventually_ge_atTop 1]
      with P hRatio hB hH hL hHOne
    let H := prefixH P
    have hL' : 1 ≤ log H := hL
    have hL0 : 0 ≤ log H := zero_le_one.trans hL'
    have hBound := ((div_lt_iff₀ (rpow_pos_of_pos hB (5 / 12 : ℝ))).mp hRatio).le
    have hScale := logScale_nonneg n hHOne
    have hPower : majorant P ^ (5 / 12 : ℝ) ≤ D ^ (5 / 12 : ℝ) *
        (H ^ (5 / 12 : ℝ) * log H) := by
      change (D * (H * log H)) ^ (5 / 12 : ℝ) ≤ _
      rw [mul_rpow hD.le (mul_nonneg hH.le hL0), mul_rpow hH.le hL0]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (rpow_le_self_of_one_le hL' (by norm_num))
          (rpow_nonneg hH.le _)) (rpow_nonneg hD.le _)
    have hNormalize : H ^ (5 / 12 : ℝ) / sqrt H = 1 / H ^ (1 / 12 : ℝ) := by
      rw [sqrt_eq_rpow, ← rpow_sub hH, show (5 / 12 : ℝ) - 1 / 2 = -(1 / 12) by norm_num,
        rpow_neg hH.le]
      exact (one_div _).symm
    calc
      logScale n P * higherBound P ≤ logScale n P * majorant P ^ (5 / 12 : ℝ) := by
        exact mul_le_mul_of_nonneg_left (by simpa only [one_mul] using hBound) hScale
      _ ≤ logScale n P * (D ^ (5 / 12 : ℝ) * (H ^ (5 / 12 : ℝ) * log H)) :=
        mul_le_mul_of_nonneg_left hPower hScale
      _ = D ^ (5 / 12 : ℝ) * (log H ^ (n + 1) / H ^ (1 / 12 : ℝ)) := by
        change log H ^ n / sqrt H * _ = _
        calc
          _ = D ^ (5 / 12 : ℝ) * (log H ^ (n + 1) * (H ^ (5 / 12 : ℝ) / sqrt H)) := by
            rw [pow_succ]
            ring
          _ = _ := by rw [hNormalize]; ring

/-- At each fixed logarithmic order, the clock of any eventual supported
minimizing selection is asymptotic to the actual second-layer prefix cutoff
with vanishing normalized error. -/
theorem moving_price_minimizer_clock_log_power_tendsto (n : ℕ) {C : ℝ}
    {lam : ℕ → ℝ} {a : ℕ → ℕ → ℕ}
    (hband : ∀ᶠ P : ℕ in atTop,
      |lam P / prefixPrice P - 1| ≤ C / sqrt (prefixH P))
    (ha : ∀ᶠ P : ℕ in atTop, IsMinimizer (Nat.primesLE P) (lam P) (a P)) :
    Tendsto (fun P => log (prefixH P) ^ n *
      (clockIncrement (Nat.primesLE P) (a P) - cutoff 2 (prefixPrice P)) /
        sqrt (prefixH P)) atTop (𝓝 0) := by
  let t : ℕ → ℝ := fun P => cutoff 2 (lam P)
  let K : ℝ := 27 * (|C| + 1)
  have ht : ∀ᶠ P : ℕ in atTop, |t P - baseCutoff P| ≤ K := cutoff_displacement hband
  have htLow : ∀ᶠ P : ℕ in atTop, |t P - 1 - baseCutoff P| ≤ K + 1 := by
    filter_upwards [ht] with P hp
    exact abs_le.mpr ⟨by linarith only [(abs_le.mp hp).1],
      by linarith only [(abs_le.mp hp).2]⟩
  have hSqrt : sqrt (2 : ℝ) < 3 := by
    rw [sqrt_lt' (by norm_num : (0 : ℝ) < 3)]
    norm_num
  have hInside : ∀ᶠ P : ℕ in atTop, t P ≤ (P : ℝ) := by
    filter_upwards [(endpoint_ratio ht).eventually (eventually_lt_nhds hSqrt),
      endpoint_inside_prefix 3, prefixH_atTop.eventually_gt_atTop 0] with P hRatio hP hH
    exact (((div_lt_iff₀ (sqrt_pos.mpr hH)).mp hRatio).le).trans hP
  have hPrices := eventual_price_bounds (price_ratio_tendsto hband)
  have hBounds : ∀ᶠ P : ℕ in atTop,
      logScale n P * (θ (t P - 1) - baseCutoff P) ≤
        logScale n P * (clockIncrement (Nat.primesLE P) (a P) - baseCutoff P) ∧
      logScale n P * (clockIncrement (Nat.primesLE P) (a P) - baseCutoff P) ≤
        logScale n P * (θ (t P) - baseCutoff P) + logScale n P * higherBound P := by
    filter_upwards [ha, hPrices, hInside, prefixH_atTop.eventually_ge_atTop 1]
      with P hMin hPrice hP hH
    have hHead : θ (t P - 1) ≤ headClock P (a P) ∧ headClock P (a P) ≤ θ (t P) :=
      head_at_cutoff hMin hPrice.1 hP
    have hHigher :=
      higher_bounds hMin hPrice.1 hPrice.2.1 hPrice.2.2
    have hScale := logScale_nonneg n hH
    rw [clock_split hMin.1, ← mul_add]
    refine ⟨mul_le_mul_of_nonneg_left ?_ hScale, mul_le_mul_of_nonneg_left ?_ hScale⟩
    · linarith only [hHead.1, hHigher.1]
    · unfold higherBound
      linarith only [hHead.2, hHigher.2]
  have hHigh := (theta_endpoint_tendsto n ht).add (higher_bound_weighted_tendsto n)
  rw [add_zero] at hHigh
  have hGoal : Tendsto (fun P => logScale n P *
      (clockIncrement (Nat.primesLE P) (a P) - baseCutoff P)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' (theta_endpoint_tendsto n htLow) hHigh
      (hBounds.mono fun _ hp => hp.1) (hBounds.mono fun _ hp => hp.2)
  apply hGoal.congr'
  exact Eventually.of_forall fun P => by
    dsimp only [baseCutoff, logScale]
    ring

end D5.S3.Arith.Robin.PriceRecord.QuantitativeMovingPriceMinimizerClock
