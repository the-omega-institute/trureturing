/- GID: D5/S3/Arith/Robin/PriceRecord/RealInfimumSecondOrder
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/RealInfimumSecondOrder
   mirror-E: none(waiver:general-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Exact sixteen for the original real IMAGE infimum on prime prefixes. -/
/- SOURCE_ONLY_UNCOMPILED. This file contains source scripts, not a native
acceptance claim. No target-limit, minimizer, RH or distribution hypotheses.
The final16 transfer uses the original all-vector finite sublevel squeeze
at r=1/sqrt(H), with both exponential divided differences paid explicitly.
The canonical prefix boundary proves its finite squeeze directly from the
original pointwise price maximum and the full real image.
The unchanged realInfimum is sInf(realValues) from OwnClockFixedSupport. -/
import D5.S3.Arith.Robin.PriceRecord.PrimeBoundarySecondOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.RealInfimumSecondOrder
open Real Filter
open scoped Topology
open OwnClockFixedSupport BoundaryPrimePrice
open RealInfimumPrimeBoundary PrimeBoundarySecondOrder

private lemma H_top : Tendsto prefixH atTop atTop :=
  prefixH_atTop
private lemma ell_top : Tendsto prefixEll atTop atTop := tendsto_log_atTop.comp H_top
private lemma l_top : Tendsto (fun P => log (prefixY P)) atTop atTop :=
  tendsto_log_atTop.comp prefix_Y_atTop
private lemma C_identity (P : ℕ) : prefixC P = 1 + prefixH P * prefixEll P := by
  simp only [prefixC, prefixPrice, cutoff,
    D5.S3.Arith.Robin.ActualRobinClockCovariance.g, one_div, inv_inv, prefixEll]

private lemma calibrated_normalization :
    Tendsto (fun P : ℕ => prefixEll P *
      (sqrt (prefixH P) * prefixEll P * sqrt (prefixEll P) * prefixQ P - 8) +
      8 * log (prefixEll P)) atTop (𝓝 16) := by
  let L := prefixEll
  let q : ℕ → ℝ := fun P => log (L P)
  let l : ℕ → ℝ := fun P => log (prefixY P)
  let A : ℕ → ℝ := fun P => prefixY P * l P * prefixQ P
  let k : ℕ → ℝ := fun P => sqrt (prefixH P * L P) / prefixY P
  let s : ℕ → ℝ := fun P => log (prefixC P / (prefixH P * L P))
  have hi : Tendsto (fun P => 1 / l P) atTop (𝓝 0) := l_top.const_div_atTop 1
  have hA1 : Tendsto (fun P => l P * (A P - 4)) atTop (𝓝 4) := by
    have h := (calibrated_Q_second_order.mul hi).add_const 4
    norm_num at h
    apply h.congr'
    filter_upwards [eventual_scale_positivity] with P hP
    dsimp only [A, l]
    field_simp [hP.2.2.2.2.1.ne']
    <;> ring
  have hA : Tendsto A atTop (𝓝 4) := by
    have h := (hA1.mul hi).add_const 4
    norm_num at h
    apply h.congr'
    filter_upwards [eventual_scale_positivity] with P hP
    dsimp only [A, l]
    field_simp [hP.2.2.2.2.1.ne']
    <;> ring
  have hratio : Tendsto (fun P => L P / l P) atTop (𝓝 2) := by
    have h := prefix_log_Y_div_ell.inv₀ (by norm_num : (1 / 2 : ℝ) ≠ 0)
    norm_num at h
    simpa only [inv_div] using h
  have hk : Tendsto k atTop (𝓝 1) := by
    have h := prefix_Y_div_sqrt_H_ell.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa only [inv_div, inv_one] using h
  have hs : Tendsto s atTop (𝓝 0) := by
    simpa only [log_one] using
      prefix_C_div_H_ell.log (by norm_num : (1 : ℝ) ≠ 0)
  have hkerr : Tendsto (fun P => L P * (k P - 1)) atTop (𝓝 0) := by
    have h := (((H_top.const_div_atTop 1).div prefix_C_div_H_ell
      (by norm_num : (1 : ℝ) ≠ 0)).neg).div (hk.add_const 1)
      (by norm_num : (1 : ℝ) + 1 ≠ 0)
    norm_num at h
    apply h.congr'
    filter_upwards [eventual_scale_positivity] with P hP
    rcases hP with ⟨hH, hL, hC, hr, hl, _, hP, _⟩
    have hs1 : sqrt (prefixH P * L P) ^ 2 = prefixH P * L P := sq_sqrt (by positivity)
    have hs2 : prefixY P ^ 2 = prefixC P := sq_sqrt hC.le
    have hkpos : 0 < k P := div_pos (sqrt_pos.mpr (by positivity)) hr
    have hksq : k P ^ 2 = prefixH P * L P / prefixC P := by
      dsimp only [k]
      rw [div_pow, hs1, hs2]
    have hkmul : (k P - 1) * (k P + 1) = -1 / prefixC P := by
      calc
        _ = k P ^ 2 - 1 := by ring
        _ = _ := by
          rw [hksq, C_identity]
          field_simp [show 1 + prefixH P * prefixEll P ≠ 0 by
            rw [← C_identity]; exact hC.ne']
          <;> ring
    have hidentity : L P * (k P - 1) = -L P / (prefixC P * (k P + 1)) := by
      calc
        _ = L P * ((k P - 1) * (k P + 1)) / (k P + 1) := by
          field_simp [show k P + 1 ≠ 0 by linarith]; ring
        _ = _ := by rw [hkmul]; ring
    rw [hidentity]
    field_simp [hH.ne', hL.ne', hC.ne', show k P + 1 ≠ 0 by linarith]
    <;> ring
  have hq : Tendsto (fun P => q P / L P) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp ell_top
  have hq2 : Tendsto (fun P => q P ^ 2 / L P) atTop (𝓝 0) := by
    have h := (Real.isLittleO_log_rpow_rpow_atTop (2 : ℕ)
      (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.comp ell_top
    simpa only [rpow_natCast, rpow_one] using h
  have hlogid : ∀ᶠ P : ℕ in atTop, 2 * l P = L P + q P + s P := by
    filter_upwards [eventual_log_C_identity, eventual_scale_positivity] with P hlog hP
    dsimp only [l, prefixY]
    rw [log_sqrt hP.2.2.1.le]
    change 2 * (log (prefixC P) / 2) = _
    linarith only [hlog]
  have hconstant : Tendsto (fun P => L P * (4 * L P / l P - 8) + 8 * q P)
      atTop (𝓝 0) := by
    have h := ((((hq2.add (hq.mul hs)).mul hratio).const_mul 4).sub
      ((hratio.mul hs).const_mul 4))
    norm_num at h
    apply h.congr'
    filter_upwards [hlogid, eventual_scale_positivity] with P hlog hP
    have hL : L P ≠ 0 := hP.2.1.ne'
    have hl : l P ≠ 0 := hP.2.2.2.2.1.ne'
    have hid : L P * (4 * L P / l P - 8) + 8 * q P =
        4 * q P * (q P + s P) / l P - 4 * L P * s P / l P := by
      rw [show s P = 2 * l P - L P - q P by linarith only [hlog]]
      field_simp [hl]
      <;> ring
    rw [hid]
    field_simp [hL, hl]
    <;> ring
  have h := (((hkerr.mul hratio).mul hA).add ((hratio.pow 2).mul hA1)).add hconstant
  norm_num at h
  apply h.congr'
  filter_upwards [eventual_scale_positivity] with P hP
  rcases hP with ⟨hH, hL, hC, hr, hl, _, hp, hlp⟩
  dsimp only [k, A, l, L, q]
  rw [sqrt_mul hH.le]
  field_simp [hr.ne', hl.ne']
  <;> ring

/-- Direct finite-sublevel transfer on the original full real image.
The exact public error type is unchanged. Both nested exponential remainders
are paid at r=1/sqrt(H); no attained optimizer or response estimate is used. -/
theorem actual_calibration_error_negligible :
    Tendsto (fun P : ℕ => prefixEll P *
      (sqrt (prefixH P) * prefixEll P * sqrt (prefixEll P)) *
      (prefixQ P - (realInfimum (Nat.primesLE P) - baseline (Nat.primesLE P))))
      atTop (𝓝 0) := by
  let r : ℕ → ℝ := fun P => 1 / sqrt (prefixH P)
  let u : ℕ → ℝ := fun P => prefixEll P * (exp (r P) - 1)
  let A : ℕ → ℝ := fun P => exp (u P) - 1
  have hrpos : ∀ᶠ P : ℕ in atTop, 0 < r P := by
    filter_upwards [eventual_scale_positivity] with P hP
    exact one_div_pos.mpr (sqrt_pos.mpr hP.1)
  have hrzero : Tendsto r atTop (𝓝 (0 : ℝ)) :=
    (tendsto_sqrt_atTop.comp H_top).const_div_atTop 1
  have hellrzero : Tendsto (fun P => prefixEll P * r P) atTop (𝓝 (0 : ℝ)) := by
    have h := (Real.isLittleO_log_rpow_rpow_atTop (1 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp H_top
    simpa only [rpow_one, ← sqrt_eq_rpow, prefixEll, r, mul_one_div] using h
  have hfirst : Tendsto (fun P => (exp (r P) - 1) / r P)
      atTop (𝓝 (1 : ℝ)) :=
    exp_difference_quotient hrzero (hrpos.mono (fun _ h => h.ne'))
  have huzero : Tendsto u atTop (𝓝 (0 : ℝ)) := by
    have h := hellrzero.mul hfirst
    norm_num only [zero_mul] at h
    apply h.congr'
    filter_upwards [hrpos] with P hr
    dsimp only [u]
    field_simp [hr.ne']
    <;> ring
  have hinnerpos : ∀ᶠ P : ℕ in atTop, 0 < exp (r P) - 1 := by
    filter_upwards [hrpos] with P hr
    have h := exp_lt_exp.mpr hr
    rw [exp_zero] at h
    exact sub_pos.mpr h
  have hupos : ∀ᶠ P : ℕ in atTop, 0 < u P := by
    filter_upwards [eventual_scale_positivity, hinnerpos] with P hP hi
    exact mul_pos hP.2.1 hi
  have hsecond : Tendsto (fun P => A P / u P) atTop (𝓝 (1 : ℝ)) :=
    exp_difference_quotient huzero (hupos.mono (fun _ h => h.ne'))
  have hAratio : Tendsto (fun P => A P / (prefixEll P * r P))
      atTop (𝓝 (1 : ℝ)) := by
    have h := hsecond.mul hfirst
    norm_num only [one_mul] at h
    apply h.congr'
    filter_upwards [eventual_scale_positivity, hrpos, hinnerpos] with P hP hr hi
    dsimp only [u]
    field_simp [hP.2.1.ne', hr.ne', hi.ne']
    <;> ring
  -- Recover the leading Q scale from the unchanged second-order normalization.
  have hM : Tendsto (fun P : ℕ =>
      sqrt (prefixH P) * prefixEll P * sqrt (prefixEll P) * prefixQ P)
      atTop (𝓝 (8 : ℝ)) := by
    have hlog : Tendsto (fun P => log (prefixEll P) / prefixEll P)
        atTop (𝓝 (0 : ℝ)) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp ell_top
    have h := ((calibrated_normalization.mul (ell_top.const_div_atTop 1)).sub
      (hlog.const_mul 8)).add_const 8
    norm_num only [mul_zero, sub_zero, zero_add] at h
    apply h.congr'
    filter_upwards [eventual_scale_positivity] with P hP
    field_simp [hP.2.1.ne']
    <;> ring
  have hQsmall : Tendsto (fun P : ℕ => sqrt (prefixH P) * prefixQ P)
      atTop (𝓝 (0 : ℝ)) := by
    have h := (hM.mul (ell_top.const_div_atTop 1)).mul
      ((tendsto_sqrt_atTop.comp ell_top).const_div_atTop 1)
    norm_num only [mul_zero, zero_mul] at h
    apply h.congr'
    filter_upwards [eventual_scale_positivity] with P hP
    field_simp [hP.2.1.ne', (sqrt_pos.mpr hP.2.1).ne']
    <;> ring
  have hQr : ∀ᶠ P : ℕ in atTop, prefixQ P ≤ r P := by
    filter_upwards [hQsmall.eventually_lt_const (by norm_num : (0 : ℝ) < 1),
      eventual_scale_positivity] with P hsmall hP
    change prefixQ P ≤ 1 / sqrt (prefixH P)
    exact ((lt_div_iff₀ (sqrt_pos.mpr hP.1)).mpr
      (by simpa only [mul_comm] using hsmall)).le
  have hfour : Tendsto (fun P : ℕ => prefixEll P ^ 4 / sqrt (prefixH P))
      atTop (𝓝 (0 : ℝ)) := by
    have h := (Real.isLittleO_log_rpow_rpow_atTop (4 : ℕ)
      (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero.comp H_top
    simpa only [rpow_natCast, ← sqrt_eq_rpow, prefixEll] using h
  have hfactor : Tendsto (fun P : ℕ =>
      prefixEll P ^ 3 * sqrt (prefixEll P) / sqrt (prefixH P))
      atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero' _ _ hfour
    · filter_upwards [eventual_scale_positivity] with P hP
      exact div_nonneg (mul_nonneg (pow_nonneg hP.2.1.le 3) (sqrt_nonneg _))
        (sqrt_nonneg _)
    · filter_upwards [eventual_prefix_domains, eventual_scale_positivity] with P hd hp
      have hs : sqrt (prefixEll P) ≤ prefixEll P :=
        sqrt_le_self_iff.mpr (Or.inr hd.2.2.1)
      apply div_le_div_of_nonneg_right _ (sqrt_nonneg _)
      calc
        prefixEll P ^ 3 * sqrt (prefixEll P) ≤ prefixEll P ^ 3 * prefixEll P :=
          mul_le_mul_of_nonneg_left hs (pow_nonneg hp.2.1.le 3)
        _ = prefixEll P ^ 4 := by ring
  have hupper : Tendsto (fun P : ℕ => prefixEll P *
      (sqrt (prefixH P) * prefixEll P * sqrt (prefixEll P)) *
      (A P ^ 2 / prefixEll P)) atTop (𝓝 (0 : ℝ)) := by
    have h := (hAratio.pow 2).mul hfactor
    norm_num only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventual_scale_positivity] with P hP
    -- Exact identity: scale*A²/ell = (A/(ell*r))²*ell³*sqrt(ell)/sqrt(H).
    dsimp only [r]
    field_simp [hP.2.1.ne', (sqrt_pos.mpr hP.1).ne']
    <;> ring
  have hfinite : ∀ᶠ P : ℕ in atTop,
      0 ≤ prefixQ P -
        (realInfimum (Nat.primesLE P) - baseline (Nat.primesLE P)) ∧
      prefixQ P - (realInfimum (Nat.primesLE P) - baseline (Nat.primesLE P)) ≤
        A P ^ 2 / prefixEll P := by
    filter_upwards [eventual_prefix_domains, eventual_scale_positivity, hrpos, hQr]
      with P hdom hpos hr hq
    have hs := RealInfimumPrimeBoundary.real_infimum_fixed_price_squeeze
      hdom.1 hdom.2.1 hdom.2.2.1 hr
    change min (r P) (prefixQ P - A P ^ 2 / prefixEll P) ≤
        realInfimum (Nat.primesLE P) - baseline (Nat.primesLE P) ∧
      realInfimum (Nat.primesLE P) - baseline (Nat.primesLE P) ≤ prefixQ P at hs
    have hE : 0 ≤ A P ^ 2 / prefixEll P :=
      div_nonneg (sq_nonneg _) hpos.2.1.le
    rw [min_eq_right (by linarith only [hq, hE])] at hs
    constructor <;> linarith only [hs.1, hs.2]
  apply squeeze_zero' _ _ hupper
  · filter_upwards [hfinite, eventual_scale_positivity] with P herr hpos
    exact mul_nonneg
      (mul_nonneg hpos.2.1.le
        (mul_nonneg (mul_nonneg (sqrt_nonneg _) hpos.2.1.le) (sqrt_nonneg _))) herr.1
  · filter_upwards [hfinite, eventual_scale_positivity] with P herr hpos
    exact mul_le_mul_of_nonneg_left herr.2
      (mul_nonneg hpos.2.1.le
        (mul_nonneg (mul_nonneg (sqrt_nonneg _) hpos.2.1.le) (sqrt_nonneg _)))

/-- Exact requested second-order limit for the unchanged FULL real image
infimum. All positivity is paid eventually; the final domain is all N.
No RH, counting, minimizer, calibration-rate or desired-limit premise. -/
theorem actual_real_infimum_second_order :
    Tendsto (fun P : ℕ =>
      let H := theta (Nat.primesLE P)
      let ell := log H
      let M := sqrt H * ell * sqrt ell *
        (realInfimum (Nat.primesLE P) - baseline (Nat.primesLE P))
      ell * (M - 8) + 8 * log ell) atTop (𝓝 16) := by
  have h := calibrated_normalization.sub actual_calibration_error_negligible
  norm_num only [sub_zero] at h
  apply h.congr'
  exact Filter.Eventually.of_forall (fun P => by
    dsimp only [prefixH, prefixEll]
    ring)

end D5.S3.Arith.Robin.PriceRecord.RealInfimumSecondOrder
