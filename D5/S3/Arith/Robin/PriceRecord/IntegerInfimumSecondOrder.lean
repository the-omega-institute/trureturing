/- GID: D5/S3/Arith/Robin/PriceRecord/IntegerInfimumSecondOrder
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/IntegerInfimumSecondOrder
   mirror-E: none(waiver:general-theorem-no-numerical-experiment)
   anchors: []
   utility: none
   digest: The second-order limit for the complete integer Robin infimum on prime prefixes. -/

import D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope
import D5.S3.Arith.Robin.PriceRecord.PrimeSquareTail
import D5.S3.Arith.Robin.PriceRecord.RealInfimumPrimeBoundary

/-!
# Second-order integer Robin infimum on prime prefixes

The price is the tangent price of the prefix clock. The first activation
splits at the real root of the square-log equation. The second activation
and both finite-envelope errors vanish at the scale of the correction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.IntegerInfimumSecondOrder

open Finset Filter Real Asymptotics
open scoped Topology BigOperators Chebyshev
open RealInfimumPrimeBoundary (prefixH prefixEll prefixH_atTop prefix_H_ratio)
open FixedSupportIntegerActivationEnvelope
  (activationSum secondActivationSum integerInfimum finite_integer_activation_envelope)
open QuantitativePrimeAbel (primeInterval squareSum theta_error_log_power)
open OwnClockFixedSupport (primeSupport)
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (finite_cubic_tail)

local notation "H" => prefixH
local notation "ℓ" => prefixEll

private lemma sqrt_two_sq : (sqrt 2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num)

private lemma one_lt_sqrt_two : (1 : ℝ) < sqrt 2 :=
  (lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).2 (by norm_num)

private lemma squareLog_strictMono : StrictMonoOn (fun x : ℝ => x ^ 2 * log x) (Set.Ici 1) := by
  intro x hx y _ hxy
  change 1 ≤ x at hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hsq : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx0.le hxy.le 2
  calc
    x ^ 2 * log x < x ^ 2 * log y :=
      mul_lt_mul_of_pos_left (log_lt_log hx0 hxy) (sq_pos_of_pos hx0)
    _ ≤ y ^ 2 * log y := mul_le_mul_of_nonneg_right hsq (log_nonneg (hx.trans hxy.le))

private lemma exists_cutoff {x : ℝ} (hx : 1 < x) :
    ∃ t : ℝ, t ∈ Set.Icc (sqrt x) (sqrt 2 * sqrt x) ∧ t ^ 2 * log t = x * log x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hs : 1 < sqrt x := (lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).2 (by simpa using hx)
  have hsu : sqrt x ≤ sqrt 2 * sqrt x := by
    simpa using mul_le_mul_of_nonneg_right one_lt_sqrt_two.le (sqrt_nonneg x)
  have hc : ContinuousOn (fun t : ℝ => t ^ 2 * log t) (Set.Icc (sqrt x) (sqrt 2 * sqrt x)) := by
    refine (continuous_id.pow 2).continuousOn.mul (continuousOn_log.mono ?_)
    intro y hy
    exact ne_of_gt (zero_lt_one.trans (hs.trans_le hy.1))
  have hleft : (sqrt x) ^ 2 * log (sqrt x) ≤ x * log x := by
    rw [sq_sqrt hx0.le, log_sqrt hx0.le]
    exact mul_le_mul_of_nonneg_left (by linarith [log_pos hx]) hx0.le
  have hright : x * log x ≤ (sqrt 2 * sqrt x) ^ 2 * log (sqrt 2 * sqrt x) := by
    rw [mul_pow, sqrt_two_sq, sq_sqrt hx0.le,
      log_mul (sqrt_pos.2 (by norm_num)).ne' (sqrt_pos.2 hx0).ne', log_sqrt hx0.le]
    nlinarith [mul_nonneg hx0.le (log_nonneg one_lt_sqrt_two.le)]
  exact intermediate_value_Icc hsu hc ⟨hleft, hright⟩

private def cutoff (P : ℕ) : ℝ :=
  if h : 1 < H P then Classical.choose (exists_cutoff h) else 1

private lemma cutoff_spec {P : ℕ} (hP : 1 < H P) :
    sqrt (H P) ≤ cutoff P ∧ cutoff P ≤ sqrt 2 * sqrt (H P) ∧
      cutoff P ^ 2 * log (cutoff P) = H P * ℓ P := by
  have h := Classical.choose_spec (exists_cutoff hP)
  rw [cutoff, dite_eq_left hP]
  exact ⟨h.1.1, h.1.2, h.2⟩

private def cutoffRatio (P : ℕ) : ℝ := cutoff P / sqrt (H P)

private lemma cutoffRatio_bounds {P : ℕ} (hP : 1 < H P) :
    1 ≤ cutoffRatio P ∧ cutoffRatio P ≤ sqrt 2 := by
  have hs := sqrt_pos.2 (zero_lt_one.trans hP)
  exact ⟨(le_div_iff₀ hs).2 (by simpa using (cutoff_spec hP).1),
    (div_le_iff₀ hs).2 (cutoff_spec hP).2.1⟩

private lemma cutoffRatio_mul_sqrt {P : ℕ} (hP : 1 < H P) :
    cutoffRatio P * sqrt (H P) = cutoff P :=
  div_mul_cancel₀ _ (sqrt_pos.2 (zero_lt_one.trans hP)).ne'

private lemma cutoffRatio_sq_mul_log {P : ℕ} (hP : 1 < H P) :
    cutoffRatio P ^ 2 * log (cutoff P) = ℓ P := by
  have h0 : 0 < H P := zero_lt_one.trans hP
  calc
    cutoffRatio P ^ 2 * log (cutoff P) =
        (cutoff P ^ 2 * log (cutoff P)) / H P := by
      rw [cutoffRatio, div_pow, sq_sqrt h0.le, div_mul_eq_mul_div]
    _ = ℓ P := by
      rw [(cutoff_spec hP).2.2, mul_comm (H P) (ℓ P), mul_div_cancel_right₀ _ h0.ne']

private lemma log_cutoff {P : ℕ} (hP : 1 < H P) :
    log (cutoff P) = ℓ P / 2 + log (cutoffRatio P) := by
  have h0 : 0 < H P := zero_lt_one.trans hP
  have hb : 0 < cutoffRatio P := zero_lt_one.trans_le (cutoffRatio_bounds hP).1
  rw [← cutoffRatio_mul_sqrt hP, log_mul hb.ne' (sqrt_pos.2 h0).ne', log_sqrt h0.le]
  change log (cutoffRatio P) + ℓ P / 2 = _
  ring

private lemma cutoffRatio_equation {P : ℕ} (hP : 1 < H P) :
    cutoffRatio P ^ 2 * (1 / 2 + log (cutoffRatio P) / ℓ P) = 1 := by
  have he : ℓ P ≠ 0 := (log_pos hP).ne'
  have h := cutoffRatio_sq_mul_log hP
  rw [log_cutoff hP] at h
  field_simp [he]
  linarith only [h]

private lemma sqrt_H_atTop : Tendsto (fun P => sqrt (H P)) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp prefixH_atTop

private lemma cutoff_atTop : Tendsto cutoff atTop atTop :=
  tendsto_atTop_mono' atTop
    ((prefixH_atTop.eventually_gt_atTop 1).mono fun _ hP => (cutoff_spec hP).1)
    sqrt_H_atTop

private lemma cutoffRatio_limit : Tendsto cutoffRatio atTop (𝓝 (sqrt 2)) := by
  have hell : Tendsto ℓ atTop atTop := Real.tendsto_log_atTop.comp prefixH_atTop
  have hz : Tendsto (fun P => log (cutoffRatio P) / ℓ P) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (hell.const_div_atTop (log (sqrt 2)))
    filter_upwards [prefixH_atTop.eventually_gt_atTop 1] with P hP
    obtain ⟨hl, hu⟩ := cutoffRatio_bounds hP
    have hpos : 0 < cutoffRatio P := zero_lt_one.trans_le hl
    have he : 0 < ℓ P := log_pos hP
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (log_nonneg hl) he.le)]
    exact div_le_div_of_nonneg_right (log_le_log hpos hu) he.le
  have hden := hz.const_add (1 / 2 : ℝ)
  rw [add_zero] at hden
  have hquot : Tendsto (fun P => 1 / (1 / 2 + log (cutoffRatio P) / ℓ P))
      atTop (𝓝 ((1 : ℝ) / (1 / 2))) :=
    tendsto_const_nhds.div hden (by norm_num : (1 / 2 : ℝ) ≠ 0)
  have hs : Tendsto (fun P => sqrt (1 / (1 / 2 + log (cutoffRatio P) / ℓ P)))
      atTop (𝓝 (sqrt 2)) := by
    have hc : (1 : ℝ) / (1 / 2 : ℝ) = 2 := by norm_num
    simpa only [hc] using hquot.sqrt
  apply hs.congr'
  filter_upwards [prefixH_atTop.eventually_gt_atTop 1] with P hP
  have hB : 0 < cutoffRatio P := zero_lt_one.trans_le (cutoffRatio_bounds hP).1
  have he : 0 < ℓ P := log_pos hP
  have hd : 0 < 1 / 2 + log (cutoffRatio P) / ℓ P := by
    have := div_nonneg (log_nonneg (cutoffRatio_bounds hP).1) he.le
    linarith
  have hsq : 1 / (1 / 2 + log (cutoffRatio P) / ℓ P) = cutoffRatio P ^ 2 := by
    exact (div_eq_iff hd.ne').2 (cutoffRatio_equation hP).symm
  change sqrt (1 / (1 / 2 + log (cutoffRatio P) / ℓ P)) = cutoffRatio P
  rw [hsq, sqrt_sq hB.le]

private lemma cutoffRatio_correction :
    Tendsto (fun P => ℓ P * (cutoffRatio P - sqrt 2)) atTop
      (𝓝 (-sqrt 2 * log (sqrt 2))) := by
  have hlog := cutoffRatio_limit.log (sqrt_pos.2 (by norm_num)).ne'
  have hden : sqrt (2 : ℝ) + sqrt 2 ≠ 0 := by positivity
  have h := (((cutoffRatio_limit.pow 2).const_mul (-2)).mul hlog).div
    (cutoffRatio_limit.add_const (sqrt 2)) hden
  have hc : -2 * (sqrt 2 : ℝ) ^ 2 * log (sqrt 2) / (sqrt 2 + sqrt 2) =
      -sqrt 2 * log (sqrt 2) := by
    apply (div_eq_iff hden).2
    ring
  rw [hc] at h
  apply h.congr'
  filter_upwards [prefixH_atTop.eventually_gt_atTop 1] with P hP
  have hB : 0 < cutoffRatio P := zero_lt_one.trans_le (cutoffRatio_bounds hP).1
  have hd : cutoffRatio P + sqrt 2 ≠ 0 := by positivity
  have hid := cutoffRatio_sq_mul_log hP
  rw [log_cutoff hP] at hid
  change -2 * cutoffRatio P ^ 2 * log (cutoffRatio P) / (cutoffRatio P + sqrt 2) =
    ℓ P * (cutoffRatio P - sqrt 2)
  apply (div_eq_iff hd).2
  linear_combination -2 * hid + ℓ P * sqrt_two_sq

private lemma activation_split (P : ℕ) {t : ℝ} (ht : 1 < t) (htP : t ≤ (P : ℝ))
    (hcut : t ^ 2 * log t = H P * ℓ P) (hH : 1 < H P) :
    activationSum (Nat.primesLE P) (1 / (H P * ℓ P)) =
      (1 / (H P * ℓ P)) * θ t + squareSum t (P : ℝ) := by
  classical
  let lam : ℝ := 1 / (H P * ℓ P)
  have ht0 : 0 ≤ t := by linarith
  have hHℓ : 0 < H P * ℓ P := mul_pos (zero_lt_one.trans hH) (log_pos hH)
  let head := Nat.primesLE ⌊t⌋₊
  have hfloor : ⌊t⌋₊ ≤ P := Nat.floor_le_of_le htP
  have hsub : head ⊆ Nat.primesLE P := Nat.primesLE_mono hfloor
  have htail : Nat.primesLE P \ head = primeInterval t (P : ℝ) := by
    ext p
    by_cases hp : p.Prime <;>
      simp [head, primeInterval, Nat.mem_primesLE, hp, not_le, and_comm]
  have hmin (p : ℕ) (hp : p.Prime) :
      lam * log (p : ℝ) ≤ 1 / (p : ℝ) ^ 2 ↔ (p : ℝ) ≤ t := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hp2 : 0 < (p : ℝ) ^ 2 := by positivity
    calc
      lam * log (p : ℝ) ≤ 1 / (p : ℝ) ^ 2 ↔
          (p : ℝ) ^ 2 * log (p : ℝ) ≤ t ^ 2 * log t := by
        dsimp only [lam]
        rw [one_div_mul_eq_div, div_le_div_iff₀ hHℓ hp2, hcut, one_mul,
          mul_comm (log (p : ℝ)) ((p : ℝ) ^ 2)]
      _ ↔ (p : ℝ) ≤ t := squareLog_strictMono.le_iff_le hp1.le ht.le
  let f := fun p : ℕ => min (lam * log (p : ℝ)) (1 / (p : ℝ) ^ 2)
  have hh : (∑ p ∈ head, f p) = lam * θ t := by
    rw [Chebyshev.theta_eq_sum_primesLE, mul_sum]
    apply sum_congr rfl
    intro p hp
    obtain ⟨hple, hprime⟩ := Nat.mem_primesLE.mp hp
    exact min_eq_left ((hmin p hprime).2 ((Nat.le_floor_iff ht0).1 hple))
  have hs : (∑ p ∈ Nat.primesLE P \ head, f p) = squareSum t (P : ℝ) := by
    rw [htail, squareSum]
    apply sum_congr rfl
    intro p hp
    have hp' := mem_filter.mp hp
    have htp := (Nat.floor_lt ht0).1 (Finset.mem_Ioc.mp hp'.1).1
    apply min_eq_right
    exact le_of_lt (lt_of_not_ge fun h => htp.not_ge ((hmin p hp'.2).1 h))
  change (∑ p ∈ Nat.primesLE P, f p) = _
  rw [← sum_sdiff hsub (f := f), hs, hh, add_comm]

lemma log_pow_over_H_rpow (k : ℕ) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun P => ℓ P ^ k / (H P) ^ a) atTop (𝓝 0) := by
  simpa only [Function.comp_def, prefixEll, rpow_natCast] using
    ((isLittleO_log_rpow_rpow_atTop (k : ℝ) ha).tendsto_div_nhds_zero.comp prefixH_atTop)

lemma log_pow_over_sqrt_H (k : ℕ) :
    Tendsto (fun P => ℓ P ^ k / sqrt (H P)) atTop (𝓝 0) := by
  simpa only [sqrt_eq_rpow] using
    log_pow_over_H_rpow k (show (0 : ℝ) < 1 / 2 by norm_num)

private lemma sqrt_H_log_pow_over_P (k : ℕ) :
    Tendsto (fun P : ℕ => sqrt (H P) * ℓ P ^ k / (P : ℝ)) atTop (𝓝 0) := by
  have h := (log_pow_over_sqrt_H k).mul prefix_H_ratio
  rw [zero_mul] at h
  apply h.congr'
  filter_upwards [prefixH_atTop.eventually_gt_atTop 1,
    eventually_gt_atTop (0 : ℕ)] with P hH hP
  have hp : (P : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  have hs : 0 < sqrt (H P) := sqrt_pos.2 (zero_lt_one.trans hH)
  change ℓ P ^ k / sqrt (H P) * (H P / (P : ℝ)) = _
  rw [← sq_sqrt (zero_lt_one.trans hH).le]
  simp only [sqrt_sq hs.le]
  field_simp [hp, hs.ne']

private lemma cutoff_eventually_le :
    ∀ᶠ P : ℕ in atTop, cutoff P ≤ (P : ℝ) := by
  have h := (sqrt_H_log_pow_over_P 0).const_mul (sqrt 2)
  simp only [pow_zero, mul_one, mul_zero] at h
  filter_upwards [prefixH_atTop.eventually_gt_atTop 1, eventually_gt_atTop (0 : ℕ),
    h.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)] with P hH hP hr
  have hp : (0 : ℝ) < P := by exact_mod_cast hP
  have hupper : sqrt 2 * sqrt (H P) < (P : ℝ) := by
    rw [← mul_div_assoc] at hr
    simpa only [one_mul] using (div_lt_iff₀ hp).1 hr
  exact (cutoff_spec hH).2.1.trans hupper.le

private def price (P : ℕ) : ℝ := 1 / (H P * ℓ P)
private def scale (P : ℕ) : ℝ := sqrt (H P) * ℓ P ^ 2
private def firstActivation (P : ℕ) : ℝ := activationSum (Nat.primesLE P) (price P)

private lemma scale_cutoff {P : ℕ} (hP : 1 < H P) :
    scale P = cutoffRatio P ^ 3 * cutoff P * log (cutoff P) ^ 2 := by
  calc
    scale P = sqrt (H P) * (cutoffRatio P ^ 2 * log (cutoff P)) ^ 2 := by
      rw [cutoffRatio_sq_mul_log hP, scale]
    _ = _ := by rw [← cutoffRatio_mul_sqrt hP]; ring

private lemma head_error_zero :
    Tendsto (fun P => ℓ P * (θ (cutoff P) / sqrt (H P) - cutoffRatio P)) atTop (𝓝 0) := by
  have h := (cutoffRatio_limit.pow 3).mul
    ((theta_error_log_power 1).tendsto_div_nhds_zero.comp cutoff_atTop)
  rw [mul_zero] at h
  apply h.congr'
  filter_upwards [prefixH_atTop.eventually_gt_atTop 1,
    cutoff_atTop.eventually_gt_atTop 1] with P hP ht
  have hs : 0 < sqrt (H P) := sqrt_pos.2 (zero_lt_one.trans hP)
  have hB : 0 < cutoffRatio P := zero_lt_one.trans_le (cutoffRatio_bounds hP).1
  change cutoffRatio P ^ 3 * ((θ (cutoff P) - cutoff P) /
    (cutoff P / log (cutoff P) ^ (1 : ℕ))) = _
  simp only [pow_one]
  rw [← cutoffRatio_sq_mul_log hP, ← cutoffRatio_mul_sqrt hP]
  have hlog : 0 < log (cutoffRatio P * sqrt (H P)) := by
    rw [cutoffRatio_mul_sqrt hP]
    exact log_pos ht
  field_simp [hs.ne', hB.ne', hlog.ne']

private def tailEndpoint (x : ℝ) : ℝ :=
  1 / (x * log x) - 1 / (x * log x ^ 2)

private lemma scale_tailEndpoint {P : ℕ} (hP : 1 < H P) (ht : 1 < cutoff P) :
    scale P * tailEndpoint (cutoff P) =
      ℓ P * cutoffRatio P - cutoffRatio P ^ 3 := by
  rw [scale_cutoff hP, tailEndpoint, ← cutoffRatio_sq_mul_log hP]
  field_simp [(zero_lt_one.trans ht).ne', (log_pos ht).ne']

private lemma upper_endpoint_zero :
    Tendsto (fun P : ℕ => scale P * tailEndpoint (P : ℝ)) atTop (𝓝 0) := by
  have hinv :=
    (tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_div_atTop 1
  have h := (sqrt_H_log_pow_over_P 2).mul (hinv.sub (hinv.pow 2))
  simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), sub_self, mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with P hP
  have hp : (1 : ℝ) < P := by exact_mod_cast hP
  change (sqrt (H P) * ℓ P ^ 2 / (P : ℝ)) *
    (1 / log (P : ℝ) - (1 / log (P : ℝ)) ^ (2 : ℕ)) = _
  unfold scale tailEndpoint
  field_simp [(zero_lt_one.trans hp).ne', (log_pos hp).ne']

private lemma finite_tail_error_zero :
    Tendsto (fun P => scale P * (squareSum (cutoff P) (P : ℝ) -
      tailEndpoint (cutoff P))) atTop (𝓝 0) := by
  obtain ⟨Y, _, hY⟩ := PrimeSquareTail.prime_square_tail_logarithmic_refinements
  have hinv := (tendsto_log_atTop.comp cutoff_atTop).const_div_atTop 1
  have hmajorant := (cutoffRatio_limit.pow 3).mul
    ((hinv.const_mul 2).add ((hinv.pow 7).const_mul 5))
  simp only [mul_zero, zero_pow (by decide : (7 : ℕ) ≠ 0), add_zero] at hmajorant
  have hz : Tendsto (fun P => scale P * (squareSum (cutoff P) (P : ℝ) -
      tailEndpoint (cutoff P) + tailEndpoint (P : ℝ))) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hmajorant
    filter_upwards [cutoff_atTop.eventually_ge_atTop Y, cutoff_eventually_le,
      cutoff_atTop.eventually_gt_atTop 1, prefixH_atTop.eventually_gt_atTop 1] with
      P hPY hle ht hP
    have ht0 : 0 < cutoff P := zero_lt_one.trans ht
    have hlog := log_pos ht
    have hscale : 0 ≤ scale P := by unfold scale; positivity
    have hbnd : |squareSum (cutoff P) (P : ℝ) - tailEndpoint (cutoff P) +
        tailEndpoint (P : ℝ)| ≤
        2 / (cutoff P * log (cutoff P) ^ 3) + 5 / (cutoff P * log (cutoff P) ^ 9) :=
      (hY (cutoff P) (P : ℝ) hPY hle).1
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hscale]
    calc
      _ ≤ scale P * (2 / (cutoff P * log (cutoff P) ^ 3) +
          5 / (cutoff P * log (cutoff P) ^ 9)) :=
        mul_le_mul_of_nonneg_left hbnd hscale
      _ = cutoffRatio P ^ 3 * (2 * (1 / log (cutoff P)) +
          5 * (1 / log (cutoff P)) ^ (7 : ℕ)) := by
        rw [scale_cutoff hP]
        field_simp [ht0.ne', hlog.ne']
  have h := hz.sub upper_endpoint_zero
  rw [sub_zero] at h
  exact h.congr fun P => by ring

private lemma firstActivation_correction :
    Tendsto (fun P => ℓ P * (sqrt (H P) * ℓ P * firstActivation P - 2 * sqrt 2))
      atTop (𝓝 (-sqrt 2 * (2 + log 2))) := by
  have h := (((cutoffRatio_correction.const_mul 2).sub (cutoffRatio_limit.pow 3)).add
    head_error_zero).add finite_tail_error_zero
  have hc : 2 * (-sqrt 2 * log (sqrt 2)) - (sqrt 2) ^ (3 : ℕ) + 0 + 0 =
      -sqrt 2 * (2 + log 2) := by
    rw [log_sqrt (by norm_num : (0 : ℝ) ≤ 2), pow_succ, sqrt_two_sq]
    ring
  rw [hc] at h
  apply h.congr'
  filter_upwards [prefixH_atTop.eventually_gt_atTop 1, cutoff_eventually_le,
    cutoff_atTop.eventually_gt_atTop 1] with P hP hle ht
  have hH : 0 < H P := zero_lt_one.trans hP
  have hℓ : 0 < ℓ P := log_pos hP
  have hs := sqrt_pos.2 hH
  have hsplit := activation_split P ht hle (cutoff_spec hP).2.2 hP
  have hhead : scale P * (price P * θ (cutoff P)) =
      ℓ P * (θ (cutoff P) / sqrt (H P)) := by
    rw [scale, price, ← sq_sqrt hH.le]
    simp only [sqrt_sq hs.le]
    field_simp [hs.ne', hℓ.ne']
  have hnorm : ∀ z : ℝ, ℓ P * (sqrt (H P) * ℓ P * z - 2 * sqrt 2) =
      scale P * z - 2 * ℓ P * sqrt 2 := by
    intro z
    unfold scale
    ring
  change 2 * (ℓ P * (cutoffRatio P - sqrt 2)) - cutoffRatio P ^ 3 +
      ℓ P * (θ (cutoff P) / sqrt (H P) - cutoffRatio P) +
      scale P * (squareSum (cutoff P) (P : ℝ) - tailEndpoint (cutoff P)) = _
  rw [hnorm, firstActivation, price, hsplit, mul_add, ← price, hhead,
    mul_sub (scale P) (squareSum (cutoff P) (P : ℝ)) (tailEndpoint (cutoff P)),
    scale_tailEndpoint hP ht]
  ring

private def secondActivation (P : ℕ) : ℝ := secondActivationSum (Nat.primesLE P) (price P)

private lemma theta_eventually_le :
    ∀ᶠ x : ℝ in atTop, θ x ≤ 2 * x := by
  filter_upwards [(theta_error_log_power 0).bound (show (0 : ℝ) < 1 by norm_num),
    eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have hb : |θ x - x| ≤ x := by
    simpa only [pow_zero, div_one, one_mul, Real.norm_eq_abs, abs_of_pos hx0] using hx
  linarith [(abs_le.mp hb).2]

private lemma secondActivation_nonneg {P : ℕ} (hP : 1 < H P) : 0 ≤ secondActivation P := by
  have hprice : 0 ≤ price P :=
    (one_div_pos.mpr (mul_pos (zero_lt_one.trans hP) (log_pos hP))).le
  unfold secondActivation secondActivationSum
  apply sum_nonneg
  intro p hp
  have hprime := (Nat.mem_primesLE.mp hp).2
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hprime.one_lt.le
  exact le_min (mul_nonneg hprice (log_nonneg hp1)) (by positivity)

private lemma secondActivation_le (P : ℕ) {u : ℝ} (hu : 0 < u) (hP : 1 < H P) :
    secondActivation P ≤ price P * θ u + 2 / u ^ 2 := by
  classical
  let S := Nat.primesLE P
  let f := fun p : ℕ => min (price P * log (p : ℝ)) (1 / (p : ℝ) ^ 3)
  have hprice : 0 ≤ price P :=
    (one_div_pos.mpr (mul_pos (zero_lt_one.trans hP) (log_pos hP))).le
  change (∑ p ∈ S, f p) ≤ price P * θ u + 2 / u ^ 2
  let head := S.filter fun p : ℕ => (p : ℝ) ≤ u
  let tail := S.filter fun p : ℕ => ¬ (p : ℝ) ≤ u
  have hsub : head ⊆ Nat.primesLE ⌊u⌋₊ := by
    intro p hp
    have hh := mem_filter.mp hp
    exact Nat.mem_primesLE.mpr
      ⟨(Nat.le_floor_iff hu.le).2 hh.2, (Nat.mem_primesLE.mp hh.1).2⟩
  have hhead : (∑ p ∈ head, f p) ≤ price P * θ u := by
    calc
      _ ≤ ∑ p ∈ head, price P * log (p : ℝ) :=
        sum_le_sum fun _ _ => min_le_left _ _
      _ ≤ ∑ p ∈ Nat.primesLE ⌊u⌋₊, price P * log (p : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => by
          have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.one_lt.le
          exact mul_nonneg hprice (log_nonneg hp1)
      _ = _ := by rw [Chebyshev.theta_eq_sum_primesLE, mul_sum]
  have htail : (∑ p ∈ tail, f p) ≤ 2 / u ^ 2 := by
    calc
      _ ≤ ∑ p ∈ tail, 1 / (p : ℝ) ^ 3 := sum_le_sum fun _ _ => min_le_right _ _
      _ ≤ _ := finite_cubic_tail hu tail fun p hp => lt_of_not_ge (mem_filter.mp hp).2
  have hsplit : (∑ p ∈ head, f p) + (∑ p ∈ tail, f p) = ∑ p ∈ S, f p :=
    sum_filter_add_sum_filter_not S (fun p : ℕ => (p : ℝ) ≤ u) f
  rw [← hsplit]
  exact add_le_add hhead htail

private lemma secondActivation_small :
    Tendsto (fun P => scale P * secondActivation P) atTop (𝓝 0) := by
  have hell : Tendsto ℓ atTop atTop := Real.tendsto_log_atTop.comp prefixH_atTop
  let u : ℕ → ℝ := fun P => (H P) ^ (1 / 3 : ℝ)
  have hu := (tendsto_rpow_atTop (show (0 : ℝ) < 1 / 3 by norm_num)).comp prefixH_atTop
  have htheta : ∀ᶠ P : ℕ in atTop, θ (u P) ≤ 2 * u P := hu.eventually theta_eventually_le
  have hmajorant := (log_pow_over_H_rpow 2 (show (0 : ℝ) < 1 / 6 by norm_num)).const_mul 4
  rw [mul_zero] at hmajorant
  refine squeeze_zero_norm' ?_ hmajorant
  filter_upwards [htheta, prefixH_atTop.eventually_gt_atTop 1,
    hell.eventually_ge_atTop 1] with P hθ hP hℓ
  have hH : 0 < H P := zero_lt_one.trans hP
  have hℓ0 : 0 < ℓ P := zero_lt_one.trans_le hℓ
  have hprice : 0 ≤ price P := (one_div_pos.mpr (mul_pos hH hℓ0)).le
  have hu0 : 0 < u P := rpow_pos_of_pos hH _
  have hcub : u P ^ 3 = H P := by
    dsimp only [u]
    rw [← rpow_mul_natCast hH.le]
    norm_num
  have hhead : price P * (2 * u P) ≤ 2 / u P ^ 2 := by
    calc
      _ = (2 / u P ^ 2) * (1 / ℓ P) := by
        rw [price, ← hcub]
        field_simp [hu0.ne', hℓ0.ne'] <;> ring
      _ ≤ (2 / u P ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left ((div_le_iff₀ hℓ0).2 (by simpa using hℓ)) (by positivity)
      _ = _ := mul_one _
  have hbound : secondActivation P ≤ 4 / u P ^ 2 := by
    calc
      _ ≤ price P * θ (u P) + 2 / u P ^ 2 := secondActivation_le P hu0 hP
      _ ≤ 2 / u P ^ 2 + 2 / u P ^ 2 :=
        add_le_add ((mul_le_mul_of_nonneg_left hθ hprice).trans hhead) le_rfl
      _ = _ := by rw [← add_div]; norm_num
  have hscale : 0 ≤ scale P := by unfold scale; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hscale (secondActivation_nonneg hP))]
  calc
    _ ≤ scale P * (4 / u P ^ 2) := mul_le_mul_of_nonneg_left hbound hscale
    _ = 4 * (ℓ P ^ 2 / (H P) ^ (1 / 6 : ℝ)) := by
      have hpow : u P ^ 2 = sqrt (H P) * (H P) ^ (1 / 6 : ℝ) := by
        dsimp only [u]
        rw [← rpow_mul_natCast hH.le, sqrt_eq_rpow, ← rpow_add hH]
        congr 1 <;> norm_num
      rw [scale, hpow]
      field_simp [(sqrt_pos.2 hH).ne', (rpow_pos_of_pos hH (1 / 6 : ℝ)).ne'] <;> ring

private def trialCutoff (P : ℕ) : ℝ := sqrt (sqrt (H P))
private def radius (P : ℕ) : ℝ := 1 / sqrt (H P)
private def lowerError (P : ℕ) : ℝ :=
  2 * price P * log (1 / price P) + 16 * ℓ P * radius P ^ 2
private def upperError (P : ℕ) : ℝ :=
  price P * trialCutoff P * (log (1 / price P) + 1) + 4 / trialCutoff P ^ 3

private lemma trialCutoff_sq (P : ℕ) : trialCutoff P ^ 2 = sqrt (H P) :=
  sq_sqrt (sqrt_nonneg _)

private lemma trialCutoff_fourth {P : ℕ} (hH : 0 ≤ H P) : trialCutoff P ^ 4 = H P := by
  rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, trialCutoff_sq, sq_sqrt hH]

private lemma log_inv_price_bounds {P : ℕ} (hH : 0 < H P) (hℓ : 1 ≤ ℓ P) :
    0 ≤ log (1 / price P) ∧ log (1 / price P) ≤ 2 * ℓ P := by
  have he : 0 < ℓ P := zero_lt_one.trans_le hℓ
  have hid : log (1 / price P) = ℓ P + log (ℓ P) := by
    rw [price, one_div_div, div_one, log_mul hH.ne' he.ne', ← prefixEll]
  rw [hid]
  have hl := log_le_sub_one_of_pos he
  constructor
  · exact add_nonneg he.le (log_nonneg hℓ)
  · linarith

private lemma lowerError_nonneg {P : ℕ} (hH : 0 < H P) (hℓ : 1 ≤ ℓ P) :
    0 ≤ lowerError P := by
  have he : 0 < ℓ P := zero_lt_one.trans_le hℓ
  have hprice : 0 < price P := one_div_pos.mpr (mul_pos hH he)
  have hlog := (log_inv_price_bounds hH hℓ).1
  unfold lowerError
  exact add_nonneg (mul_nonneg (by positivity) hlog) (by positivity)

private lemma lowerError_small : Tendsto (fun P => scale P * lowerError P) atTop (𝓝 0) := by
  have hell : Tendsto ℓ atTop atTop := Real.tendsto_log_atTop.comp prefixH_atTop
  have hb := (log_pow_over_sqrt_H 3).const_mul 20
  rw [mul_zero] at hb
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [prefixH_atTop.eventually_gt_atTop 1, hell.eventually_ge_atTop 1]
    with P hP hℓ
  have hH : 0 < H P := zero_lt_one.trans hP
  have he : 0 < ℓ P := zero_lt_one.trans_le hℓ
  have hs : 0 < sqrt (H P) := sqrt_pos.2 hH
  have hprice : 0 < price P := one_div_pos.mpr (mul_pos hH he)
  have hlog := (log_inv_price_bounds hH hℓ).2
  have hlin : 2 * price P * log (1 / price P) ≤ 4 / H P := by
    calc
      _ ≤ 2 * price P * (2 * ℓ P) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by rw [price]; field_simp [hH.ne', he.ne'] <;> ring
  have hquad : radius P ^ 2 = 1 / H P := by
    rw [radius, div_pow, one_pow, sq_sqrt hH.le]
  have herr : lowerError P ≤ 20 * ℓ P / H P := by
    have hconst : 4 / H P ≤ 4 * ℓ P / H P :=
      div_le_div_of_nonneg_right (by linarith) hH.le
    rw [lowerError, hquad]
    calc
      _ ≤ 4 / H P + 16 * ℓ P * (1 / H P) := add_le_add hlin le_rfl
      _ ≤ 4 * ℓ P / H P + 16 * ℓ P * (1 / H P) := add_le_add hconst le_rfl
      _ = _ := by ring
  have hscale : 0 ≤ scale P := by unfold scale; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hscale (lowerError_nonneg hH hℓ))]
  calc
    _ ≤ scale P * (20 * ℓ P / H P) := mul_le_mul_of_nonneg_left herr hscale
    _ = 20 * (ℓ P ^ 3 / sqrt (H P)) := by
      rw [scale, ← sq_sqrt hH.le]
      simp only [sqrt_sq hs.le]
      field_simp [hs.ne'] <;> ring

private lemma upperError_small : Tendsto (fun P => scale P * upperError P) atTop (𝓝 0) := by
  have hell : Tendsto ℓ atTop atTop := Real.tendsto_log_atTop.comp prefixH_atTop
  have hqsmall : Tendsto (fun P => ℓ P ^ 2 / trialCutoff P) atTop (𝓝 0) := by
    have h := log_pow_over_H_rpow 2 (show (0 : ℝ) < 1 / 4 by norm_num)
    apply h.congr'
    filter_upwards [prefixH_atTop.eventually_gt_atTop 1] with P hP
    have hh : 0 ≤ H P := (zero_lt_one.trans hP).le
    have hid : trialCutoff P = (H P) ^ (1 / 4 : ℝ) := by
      rw [trialCutoff, sqrt_eq_rpow, sqrt_eq_rpow, ← rpow_mul hh]
      congr 1 <;> norm_num
    rw [hid]
  have hb := hqsmall.const_mul 7
  rw [mul_zero] at hb
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [prefixH_atTop.eventually_gt_atTop 1, hell.eventually_ge_atTop 1]
    with P hP hℓ
  have hH : 0 < H P := zero_lt_one.trans hP
  have he : 0 < ℓ P := zero_lt_one.trans_le hℓ
  have hq : 0 < trialCutoff P := sqrt_pos.2 (sqrt_pos.2 hH)
  have hprice : 0 < price P := one_div_pos.mpr (mul_pos hH he)
  obtain ⟨hl0, hl⟩ := log_inv_price_bounds hH hℓ
  have hterm : price P * trialCutoff P * (log (1 / price P) + 1) ≤
      3 / trialCutoff P ^ 3 := by
    calc
      _ ≤ (price P * trialCutoff P) * (3 * ℓ P) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by
        rw [price, ← trialCutoff_fourth hH.le]
        field_simp [hq.ne', he.ne'] <;> ring
  have herr : upperError P ≤ 7 / trialCutoff P ^ 3 := by
    unfold upperError
    rw [show (7 : ℝ) = 3 + 4 by norm_num, add_div]
    exact add_le_add hterm le_rfl
  have herr0 : 0 ≤ upperError P := by
    unfold upperError
    have hlog : 0 ≤ log (1 / price P) + 1 := add_nonneg hl0 (by norm_num)
    exact add_nonneg (mul_nonneg (by positivity) hlog) (by positivity)
  have hscale : 0 ≤ scale P := by unfold scale; positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hscale herr0)]
  calc
    _ ≤ scale P * (7 / trialCutoff P ^ 3) := mul_le_mul_of_nonneg_left herr hscale
    _ = 7 * (ℓ P ^ 2 / trialCutoff P) := by
      rw [scale, ← trialCutoff_sq P]
      field_simp [hq.ne'] <;> ring

private lemma activation_over_radius_zero :
    Tendsto (fun P => sqrt (H P) * (firstActivation P + secondActivation P)) atTop (𝓝 0) := by
  have hell : Tendsto ℓ atTop atTop := Real.tendsto_log_atTop.comp prefixH_atTop
  have hinv := hell.const_div_atTop 1
  have h := ((firstActivation_correction.add secondActivation_small).mul (hinv.pow 2)).add
    (hinv.const_mul (2 * sqrt 2))
  simp only [add_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero] at h
  apply h.congr'
  filter_upwards [hell.eventually_gt_atTop 0] with P hP
  change (ℓ P * (sqrt (H P) * ℓ P * firstActivation P - 2 * sqrt 2) +
      scale P * secondActivation P) * (1 / ℓ P) ^ (2 : ℕ) +
      2 * sqrt 2 * (1 / ℓ P) = _
  unfold scale
  field_simp [hP.ne']
  ring

private lemma integer_envelope_eventually :
    ∀ᶠ P : ℕ in atTop,
      firstActivation P + secondActivation P - lowerError P ≤
        integerInfimum (Nat.primesLE P) ∧
      integerInfimum (Nat.primesLE P) ≤
        firstActivation P + secondActivation P + upperError P := by
  have hell : Tendsto ℓ atTop atTop := Real.tendsto_log_atTop.comp prefixH_atTop
  have hqtop : Tendsto trialCutoff atTop atTop :=
    Real.tendsto_sqrt_atTop.comp sqrt_H_atTop
  have hrsmall := (log_pow_over_sqrt_H 1).const_mul 2
  simp only [mul_zero, pow_one] at hrsmall
  filter_upwards [prefixH_atTop.eventually_gt_atTop (exp 1),
    hell.eventually_ge_atTop 1, hqtop.eventually_ge_atTop 2,
    hrsmall.eventually_lt_const (show (0 : ℝ) < 1 by norm_num),
    activation_over_radius_zero.eventually_lt_const (show (0 : ℝ) < 1 by norm_num)] with
    P hP hℓ hq hr hA
  have hH : 1 < H P := (Real.one_lt_exp_iff.2 (show (0 : ℝ) < 1 by norm_num)).trans hP
  have hH0 : 0 < H P := zero_lt_one.trans hH
  have he : 0 < ℓ P := zero_lt_one.trans_le hℓ
  have hs : 0 < sqrt (H P) := sqrt_pos.2 hH0
  have hs1 : 1 < sqrt (H P) := (lt_sqrt (show (0 : ℝ) ≤ 1 by norm_num)).2 (by simpa using hH)
  have hr0 : 0 < radius P := one_div_pos.mpr hs
  have hr1 : radius P ≤ 1 := (div_le_iff₀ hs).2 (by simpa using hs1.le)
  have hrs : 2 * ℓ P * radius P ≤ 1 := by
    simpa only [radius, div_eq_mul_inv, one_mul, mul_assoc] using hr.le
  have hquart : price P * trialCutoff P ^ 4 ≤ 1 := by
    have hid : price P * trialCutoff P ^ 4 = 1 / ℓ P := by
      rw [price, trialCutoff_fourth hH0.le]
      field_simp [hH0.ne', he.ne']
    rw [hid]
    exact (div_le_iff₀ he).2 (by simpa using hℓ)
  have hsupport : primeSupport (Nat.primesLE P) := fun p hp => (Nat.mem_primesLE.mp hp).2
  have henv := finite_integer_activation_envelope hsupport hP hr0 hr1 hrs hq hquart
  change min (radius P)
      (firstActivation P + secondActivation P - 2 * price P * log (1 / price P) -
        16 * ℓ P * radius P ^ 2) ≤ integerInfimum (Nat.primesLE P) ∧
    integerInfimum (Nat.primesLE P) ≤ firstActivation P + secondActivation P +
      price P * trialCutoff P * (log (1 / price P) + 1) + 4 / trialCutoff P ^ 3 at henv
  have hlower : firstActivation P + secondActivation P - lowerError P ≤ radius P := by
    have hact : firstActivation P + secondActivation P < radius P :=
      (lt_div_iff₀ hs).2 (by simpa only [mul_comm] using hA)
    exact (sub_le_self _ (lowerError_nonneg hH0 hℓ)).trans hact.le
  have hl : min (radius P) (firstActivation P + secondActivation P - lowerError P) ≤
      integerInfimum (Nat.primesLE P) := by
    simpa only [lowerError, sub_sub] using henv.1
  rw [min_eq_right hlower] at hl
  exact ⟨hl, by simpa only [upperError, ← add_assoc] using henv.2⟩

private lemma integer_transfer :
    Tendsto (fun P => scale P * (integerInfimum (Nat.primesLE P) - firstActivation P))
      atTop (𝓝 0) := by
  have hl := lowerError_small.neg
  have hu := secondActivation_small.add upperError_small
  rw [neg_zero] at hl
  rw [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [integer_envelope_eventually, prefixH_atTop.eventually_gt_atTop 1]
      with P henv hP
    have hscale : 0 ≤ scale P := by unfold scale; positivity
    have h := mul_le_mul_of_nonneg_left henv.1 hscale
    have hsecond := mul_nonneg hscale (secondActivation_nonneg hP)
    change -(scale P * lowerError P) ≤
      scale P * (integerInfimum (Nat.primesLE P) - firstActivation P)
    nlinarith only [h, hsecond]
  · filter_upwards [integer_envelope_eventually] with P henv
    have hscale : 0 ≤ scale P := by unfold scale; positivity
    have h := mul_le_mul_of_nonneg_left henv.2 hscale
    change scale P * (integerInfimum (Nat.primesLE P) - firstActivation P) ≤
      scale P * secondActivation P + scale P * upperError P
    nlinarith only [h]

/-- The second-order limit for the complete baseline-subtracted integer
Robin infimum over initial prime supports. -/
theorem actual_integer_infimum_second_order :
    Tendsto (fun P : ℕ =>
      prefixEll P * (sqrt (prefixH P) * prefixEll P * integerInfimum (Nat.primesLE P) -
        2 * sqrt 2)) atTop (𝓝 (-sqrt 2 * (2 + log 2))) := by
  have h := firstActivation_correction.add integer_transfer
  rw [add_zero] at h
  apply h.congr
  intro P
  unfold scale
  ring

end D5.S3.Arith.Robin.PriceRecord.IntegerInfimumSecondOrder
