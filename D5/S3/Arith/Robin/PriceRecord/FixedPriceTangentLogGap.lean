/- GID: D5/S3/Arith/Robin/PriceRecord/FixedPriceTangentLogGap
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/FixedPriceTangentLogGap
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: []
   utility: none
   digest: The second-layer cutoff determines the fixed-price gap at each fixed log order. -/

import D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentCorrection
import D5.S3.Arith.Robin.PriceRecord.QuantitativeMovingPriceMinimizerClock
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Logarithmic precision for the tangent correction

The finite curvature bounds control the quadratic approximation error at both
minimizers. The moving-price clock estimate then gives the centered gap
at every fixed logarithmic order.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentLogGap

open Filter Real
open scoped Topology
open FixedSupportIntegerActivationEnvelope (integerInfimum clockIncrement)
open FixedLayerFiniteActivation (fixedPriceMinimum)
open FixedPriceMinimizerClock (IsMinimizer)
open FixedPriceTangentCorrection (prefix_minimizers_tangent_bounds tangent_remainder_quadratic)
open HigherLayerClampedCutoff (cutoff)
open IntegerInfimumSecondOrder (log_pow_over_sqrt_H)
open OwnClockFixedSupport (ownPrice tangentRemainder)
open QuantitativeMovingPriceMinimizerClock
  (baseCutoff_ratio moving_price_minimizer_clock_log_power_tendsto)
open RealInfimumPrimeBoundary
  (prefixH prefixPrice prefixH_atTop prefixEll_atTop eventual_prefix_domains)
open D5.S3.Arith.Robin.ActualRobinClockCovariance (activationDensity)

private def tangentQuadratic (H u : ℝ) : ℝ := (1 + 1 / log H) * (u ^ 2 / (2 * H))

/-- The quadratic error at the base clock is between zero and
`4 * (u / H)` times the quadratic for every nonnegative displacement. -/
private theorem scaled_tangent_quadratic_error_bounds {H u : ℝ}
    (hH : 1 < H) (hL : 1 ≤ log H) (hu : 0 ≤ u) :
    let Q := tangentQuadratic H u
    let R := H * log H * tangentRemainder H (H + u)
    0 ≤ Q - R ∧ Q - R ≤ 4 * (u / H) * Q := by
  let T := H + u
  let v := u / H
  let r := 1 + v
  let D := H ^ 2 * (log H) ^ 2
  have hH₀ : 0 < H := zero_lt_one.trans hH
  have hL₀ : 0 < log H := log_pos hH
  have hHT : H ≤ T := le_add_of_nonneg_right hu
  have hT : 1 < T := hH.trans_le hHT
  have hLT : 0 < log T := log_pos hT
  have hv : 0 ≤ v := div_nonneg hu hH₀.le
  have hr₁ : 1 ≤ r := le_add_of_nonneg_right hv
  have hr₀ : 0 < r := zero_lt_one.trans_le hr₁
  have hrSub : r - 1 = v := by dsimp only [r]; ring
  have hTmul : T = H * r := by
    dsimp only [T, r, v]
    field_simp [hH₀.ne'] <;> ring
  have hLogLower : log H ≤ log T := log_le_log hH₀ hHT
  have hLogUpper : log T ≤ log H * r := by
    have hlog : log r ≤ v := by
      simpa only [hrSub] using log_le_sub_one_of_pos hr₀
    rw [hTmul, log_mul hH₀.ne' hr₀.ne']
    calc
      log H + log r ≤ log H + v := add_le_add le_rfl hlog
      _ ≤ log H + log H * v := by
        have h := mul_le_mul_of_nonneg_right hL hv
        simpa only [one_mul] using add_le_add (le_refl (log H)) h
      _ = log H * r := by dsimp only [r]; ring
  have hDen : T ^ 2 * (log T) ^ 2 ≤ D * r ^ 4 := by
    calc
      T ^ 2 * (log T) ^ 2 ≤ T ^ 2 * (log H * r) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLT.le hLogUpper 2) (sq_nonneg T)
      _ = D * r ^ 4 := by rw [hTmul]; dsimp only [D]; ring
  have hDensity : activationDensity H / r ^ 4 ≤ activationDensity T := by
    unfold activationDensity
    rw [div_div]
    change (log H + 1) / (D * r ^ 4) ≤ (log T + 1) / (T ^ 2 * (log T) ^ 2)
    exact (div_le_div_of_nonneg_right (add_le_add hLogLower (le_refl 1))
      (mul_nonneg (mul_nonneg (sq_nonneg H) (sq_nonneg (log H))) (pow_nonneg hr₀.le 4))).trans
      (div_le_div_of_nonneg_left (add_nonneg hLT.le zero_le_one)
        (mul_pos (pow_pos (zero_lt_one.trans hT) 2) (pow_pos hLT 2)) hDen)
  have hInv : 1 - r⁻¹ ≤ v := by
    rw [← one_div, one_sub_div hr₀.ne', hrSub]
    exact div_le_self hv hr₁
  have hBernoulli : 1 + 4 * (r⁻¹ - 1) ≤ 1 / r ^ 4 := by
    have hz : (-1 : ℝ) ≤ r⁻¹ :=
      (by norm_num : (-1 : ℝ) ≤ 0).trans (inv_nonneg.mpr hr₀.le)
    simpa only [Nat.cast_ofNat, inv_pow, one_div] using one_add_mul_sub_le_pow hz 4
  have hFactor : 1 - 4 * v ≤ 1 / r ^ 4 := by linarith only [hInv, hBernoulli]
  have hScale : 0 ≤ H * log H := mul_nonneg hH₀.le hL₀.le
  have hQ₀ : 0 ≤ tangentQuadratic H u := by
    unfold tangentQuadratic
    exact mul_nonneg (add_nonneg zero_le_one (div_nonneg zero_le_one hL₀.le))
      (div_nonneg (sq_nonneg u) (mul_nonneg (by norm_num) hH₀.le))
  have hQ : H * log H * (activationDensity H * u ^ 2 / 2) = tangentQuadratic H u := by
    unfold activationDensity tangentQuadratic
    field_simp [hH₀.ne', hL₀.ne'] <;> ring
  have hCurv := tangent_remainder_quadratic hH hu
  have hLower : (1 - 4 * v) * tangentQuadratic H u ≤ H * log H * tangentRemainder H T := by
    calc
      _ ≤ (1 / r ^ 4) * tangentQuadratic H u := mul_le_mul_of_nonneg_right hFactor hQ₀
      _ = H * log H * ((activationDensity H / r ^ 4) * u ^ 2 / 2) := by rw [← hQ]; ring
      _ ≤ H * log H * (activationDensity T * u ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hDensity (sq_nonneg u))
            (by norm_num)) hScale
      _ ≤ _ := mul_le_mul_of_nonneg_left hCurv.1 hScale
  have hUpper := mul_le_mul_of_nonneg_left hCurv.2 hScale
  rw [hQ] at hUpper
  change 0 ≤ tangentQuadratic H u - H * log H * tangentRemainder H T ∧
    tangentQuadratic H u - H * log H * tangentRemainder H T ≤ 4 * v * tangentQuadratic H u
  refine ⟨sub_nonneg.mpr hUpper, ?_⟩
  calc
    _ ≤ tangentQuadratic H u - (1 - 4 * v) * tangentQuadratic H u :=
      sub_le_sub_left hLower _
    _ = _ := by ring

private theorem scaled_remainder_log_power_tendsto (n : ℕ) {u c : ℕ → ℝ}
    (hu₀ : ∀ᶠ P in atTop, 0 ≤ u P)
    (hc : Tendsto (fun P => c P / sqrt (prefixH P)) atTop (𝓝 (sqrt 2)))
    (hclock : ∀ k : ℕ, Tendsto (fun P => log (prefixH P) ^ k * (u P - c P) /
      sqrt (prefixH P)) atTop (𝓝 0)) :
    Tendsto (fun P => log (prefixH P) ^ n *
      (prefixH P * log (prefixH P) * tangentRemainder (prefixH P) (prefixH P + u P) -
        tangentQuadratic (prefixH P) (c P))) atTop (𝓝 0) := by
  let weight (P : ℕ) : ℝ := log (prefixH P) ^ n
  let Q (v : ℕ → ℝ) (P : ℕ) : ℝ := tangentQuadratic (prefixH P) (v P)
  let R (P : ℕ) : ℝ := prefixH P * log (prefixH P) *
    tangentRemainder (prefixH P) (prefixH P + u P)
  have hzero := hclock 0
  simp only [pow_zero, one_mul] at hzero
  have hu : Tendsto (fun P => u P / sqrt (prefixH P)) atTop (𝓝 (sqrt 2)) := by
    have h := hzero.add hc
    rw [zero_add] at h
    apply h.congr
    intro P
    change (u P - c P) / sqrt (prefixH P) + c P / sqrt (prefixH P) = _
    rw [← add_div, sub_add_cancel]
  have hfactor : Tendsto (fun P => 1 + 1 / log (prefixH P)) atTop (𝓝 1) := by
    simpa only [add_zero, RealInfimumPrimeBoundary.prefixEll] using
      (prefixEll_atTop.const_div_atTop (1 : ℝ)).const_add 1
  have hQ : Tendsto (Q u) atTop (𝓝 1) := by
    have h := hfactor.mul ((hu.pow 2).div_const 2)
    rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), div_self (by norm_num : (2 : ℝ) ≠ 0), mul_one] at h
    apply h.congr'
    filter_upwards [prefixH_atTop.eventually_gt_atTop 0] with P hH
    change (1 + 1 / log (prefixH P)) * ((u P / sqrt (prefixH P)) ^ 2 / 2) =
      tangentQuadratic (prefixH P) (u P)
    simp only [tangentQuadratic, div_pow, sq_sqrt hH.le, div_div, mul_comm (prefixH P) 2]
  have hscale : Tendsto (fun P => weight P / sqrt (prefixH P)) atTop (𝓝 0) :=
    log_pow_over_sqrt_H n
  have hmajor : Tendsto (fun P => weight P * (4 * (u P / prefixH P) * Q u P)) atTop (𝓝 0) := by
    have h := (hscale.mul (hu.const_mul 4)).mul hQ
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [prefixH_atTop.eventually_gt_atTop 0] with P hH
    have hdiv : u P / sqrt (prefixH P) / sqrt (prefixH P) = u P / prefixH P := by
      rw [div_div, ← pow_two, sq_sqrt hH.le]
    change (weight P / sqrt (prefixH P)) * (4 * (u P / sqrt (prefixH P))) * Q u P =
      weight P * (4 * (u P / prefixH P) * Q u P)
    rw [← hdiv]
    ring
  have hbounds : ∀ᶠ P : ℕ in atTop,
      0 ≤ weight P * (Q u P - R P) ∧
        weight P * (Q u P - R P) ≤ weight P * (4 * (u P / prefixH P) * Q u P) := by
    filter_upwards [hu₀, prefixH_atTop.eventually_gt_atTop 1, eventual_prefix_domains]
      with P huP hH hd
    have h := scaled_tangent_quadratic_error_bounds hH hd.2.2.1 huP
    have hn : 0 ≤ weight P := pow_nonneg (log_pos hH).le n
    exact ⟨mul_nonneg hn h.1, mul_le_mul_of_nonneg_left h.2 hn⟩
  have hrepair : Tendsto (fun P => weight P * (Q u P - R P)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmajor
      (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)
  have hquadratic : Tendsto (fun P => weight P * (Q u P - Q c P)) atTop (𝓝 0) := by
    have h := ((hclock n).mul (hu.add hc)).mul (hfactor.div_const 2)
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [prefixH_atTop.eventually_gt_atTop 0] with P hH
    let H := prefixH P
    let factor : ℝ := 1 + 1 / log H
    change (weight P * (u P - c P) / sqrt H) * (u P / sqrt H + c P / sqrt H) *
      (factor / 2) = weight P * (factor * (u P ^ 2 / (2 * H)) - factor * (c P ^ 2 / (2 * H)))
    have hprod : (weight P * (u P - c P) / sqrt H) * ((u P + c P) / sqrt H) =
        weight P * (u P ^ 2 - c P ^ 2) / H := by
      rw [div_mul_div_comm, ← pow_two, sq_sqrt hH.le]
      congr 1
      ring
    rw [← add_div, hprod]
    field_simp [hH.ne'] <;> ring
  have h := hquadratic.sub hrepair
  rw [sub_zero] at h
  apply h.congr
  intro P
  change weight P * (Q u P - Q c P) - weight P * (Q u P - R P) =
    weight P * (R P - Q c P)
  ring

/-- The scaled gap between the fixed-price minimum and the integer infimum
agrees with the quadratic evaluated at the actual second-layer clamped cutoff,
with error vanishing after multiplication by any fixed power of the log clock. -/
theorem fixed_price_tangent_correction_log_power_tendsto (n : ℕ) :
    Tendsto (fun P : ℕ =>
      let H := prefixH P
      let L := log H
      let U := cutoff 2 (prefixPrice P)
      let V := fixedPriceMinimum (Nat.primesLE P) (prefixPrice P)
      let I := integerInfimum (Nat.primesLE P)
      L ^ n * (H * L * (V - I) - (1 + 1 / L) * (U ^ 2 / (2 * H)))) atTop (𝓝 0) := by
  obtain ⟨a, b, C, hab⟩ := prefix_minimizers_tangent_bounds
  let U (P : ℕ) : ℝ := cutoff 2 (prefixPrice P)
  let lam (P : ℕ) : ℝ := ownPrice (Nat.primesLE P) (fun p => (b P p : ℝ))
  have ha : ∀ᶠ P in atTop, IsMinimizer (Nat.primesLE P) (prefixPrice P) (a P) :=
    hab.mono fun _ h => h.1.1
  have hb : ∀ᶠ P in atTop, IsMinimizer (Nat.primesLE P) (lam P) (b P) :=
    hab.mono fun _ h => h.1.2
  have haRatio : (fun P => prefixPrice P / prefixPrice P) =ᶠ[atTop] (fun _ => (1 : ℝ)) :=
    hab.mono fun _ h => h.2.2.1.1
  have haBand : ∀ᶠ P in atTop,
      |prefixPrice P / prefixPrice P - 1| ≤ (0 : ℝ) / sqrt (prefixH P) :=
    haRatio.mono fun P h => by
      change prefixPrice P / prefixPrice P = 1 at h
      simp only [h, sub_self, abs_zero, zero_div, le_refl]
  have hbBand : ∀ᶠ P in atTop, |lam P / prefixPrice P - 1| ≤ C / sqrt (prefixH P) :=
    hab.mono fun _ h => h.2.2.1.2
  have haClock (k : ℕ) := moving_price_minimizer_clock_log_power_tendsto k haBand ha
  have hbClock (k : ℕ) := moving_price_minimizer_clock_log_power_tendsto k hbBand hb
  have hU : Tendsto (fun P => U P / sqrt (prefixH P)) atTop (𝓝 (sqrt 2)) := baseCutoff_ratio
  have haLim := scaled_remainder_log_power_tendsto n
    (u := fun P => clockIncrement (Nat.primesLE P) (a P))
    (hab.mono fun _ h => h.2.1.1) hU haClock
  have hbLim := scaled_remainder_log_power_tendsto n
    (u := fun P => clockIncrement (Nat.primesLE P) (b P))
    (hab.mono fun _ h => h.2.1.2) hU hbClock
  let center (P : ℕ) (x : ℝ) : ℝ :=
    log (prefixH P) ^ n * (x - tangentQuadratic (prefixH P) (U P))
  let rem (x : ℕ → ℕ → ℕ) (P : ℕ) : ℝ := prefixH P * log (prefixH P) *
    tangentRemainder (prefixH P) (prefixH P + clockIncrement (Nat.primesLE P) (x P))
  let gap (P : ℕ) : ℝ := prefixH P * log (prefixH P) *
    (fixedPriceMinimum (Nat.primesLE P) (prefixPrice P) - integerInfimum (Nat.primesLE P))
  have hbounds : ∀ᶠ P in atTop, center P (rem a P) ≤ center P (gap P) ∧
      center P (gap P) ≤ center P (rem b P) := by
    filter_upwards [hab, prefixH_atTop.eventually_gt_atTop 1] with P h hH
    have hmono : Monotone (center P) := fun _ _ hxy =>
      mul_le_mul_of_nonneg_left (sub_le_sub_right hxy _) (pow_nonneg (log_pos hH).le n)
    exact ⟨hmono h.2.2.2.1, hmono h.2.2.2.2⟩
  change Tendsto (fun P => center P (gap P)) atTop (𝓝 0)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' haLim hbLim
    (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)

end D5.S3.Arith.Robin.PriceRecord.FixedPriceTangentLogGap
