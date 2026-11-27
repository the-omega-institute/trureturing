/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtLogSquareGap
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/MangoldtLogSquareGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Logarithm-squared savings below the critical Mangoldt envelope characterize RH. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtCriticalGap
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelCusp
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Use the cusp of the actual kernel at the shrinking scale y exp(−y/2)/4. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set Real
open scoped Topology
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.Mertens.IntegratedExplicit
open ActualKernelCusp (R c cusp_quadratic_limit)
open RHSharpActualEnvelope (G actual_G_control)
open ActualKernelLocalPositivity (K)
open D5.S3.Arith.Robin.CompleteMertensPeak (U)
open private phaseDeficit phaseDeficit_le_second_difference positiveExp negativeExp
  negativeExp_pos negativeExp_add negativeExp_sub negativeExp_mul_positiveExp
  G_second_difference_le residualConstant residualConstant_nonneg abs_G_sub_K_le
  eventually_abs_exp_sub_one_le from D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtCriticalGap

namespace D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtLogSquareGap

/-- The actual kernel deficit has leading coefficient one half at the right endpoint. -/
private theorem deficit_log_limit :
    Tendsto (fun t : ℝ => (firstLiMass - K t) / (t * log (1 / t)))
      (𝓝[>] 0) (𝓝 (1 / 2)) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlog : Tendsto (fun t : ℝ => (log t)⁻¹) (𝓝[>] 0) (𝓝 0) :=
    tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero
  have hR : Tendsto (fun t : ℝ => (R t / t ^ 2) * t + c) (𝓝[>] 0) (𝓝 c) := by
    simpa using (cusp_quadratic_limit.mul ht).add_const c
  have hlim : Tendsto (fun t : ℝ => (1 / 2 : ℝ) + ((R t / t ^ 2) * t + c) * (log t)⁻¹)
      (𝓝[>] 0) (𝓝 (1 / 2)) := by
    simpa only [mul_zero, add_zero] using (hR.mul hlog).const_add (1 / 2 : ℝ)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (zero_lt_one' ℝ))]
    with t ht0 ht1
  change 0 < t at ht0
  rw [one_div t, log_inv]
  unfold R
  field_simp [ht0.ne', (log_neg ht0 ht1).ne]
  ring

private def step (y : ℝ) := y / 4 * negativeExp y

private theorem step_pos {y : ℝ} (hy : 0 < y) : 0 < step y :=
  mul_pos (by positivity) (negativeExp_pos y)

private theorem step_small : Tendsto step atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have H := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) (1/2) (by norm_num)
    convert H.div_const 4 using 1
    · ext y
      simp only [step, negativeExp, rpow_one]
      rw [show -(1/2:ℝ)*y = -y/2 by ring]
      ring
    · norm_num
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy using step_pos hy

private theorem log_step_scale : Tendsto (fun y : ℝ => -log (step y) / y) atTop (𝓝 (1/2)) := by
  have L : Tendsto (fun y : ℝ => log y / y) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero)
  have D : Tendsto (fun y : ℝ => log 4 / y) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds (x:=log 4)).mul tendsto_inv_atTop_zero
  have E := (tendsto_const_nhds (x:=(1/2:ℝ))).sub (L.sub D)
  apply (by simpa using E : Tendsto (fun y : ℝ => 1/2 - (log y/y-log 4/y)) atTop (𝓝 (1/2))).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  rw [step, log_mul (by positivity) (negativeExp_pos y).ne',log_div hy.ne' (by norm_num),
    negativeExp,log_exp]
  field_simp
  ring

private theorem sinh_slope : Tendsto (fun t : ℝ => (positiveExp t - negativeExp t) / t)
    (𝓝[>] 0) (𝓝 1) := by
  have hp : HasDerivAt positiveExp (1/2) 0 := by
    convert ((hasDerivAt_id (0:ℝ)).div_const 2).exp using 1 <;> first | rfl | norm_num
  have hn : HasDerivAt negativeExp (-(1/2)) 0 := by
    convert ((hasDerivAt_id (0:ℝ)).neg.div_const 2).exp using 1 <;> first | rfl | norm_num
  have hs := (hp.sub hn).tendsto_slope_zero_right
  norm_num [positiveExp, negativeExp, smul_eq_mul, div_eq_mul_inv, mul_comm] at hs ⊢
  exact hs

private theorem midpoint_transfer (rh : RiemannHypothesis) :
    ∀ᶠ y : ℝ in atTop,
      2 * phaseDeficit (step y) - 4 * (firstLiMass - G y) ≤
        positiveExp y * step y * (positiveExp (step y) - negativeExp (step y)) +
          4 * (firstLiMass + 1) * step y + 12 * negativeExp y * residualConstant := by
  filter_upwards [eventually_gt_atTop (2:ℝ),step_small.eventually eventually_abs_exp_sub_one_le,
    (actual_G_control rh).1 1 one_pos] with y hy hs hG
  let h := step y
  have hp : 0 < h := step_pos (by linarith)
  obtain ⟨hplus,hminus,h1⟩ := hs
  change |positiveExp h-1| ≤ 2*h at hplus
  change |negativeExp h-1| ≤ 2*h at hminus
  change h ≤ 1 at h1
  have hq := (negativeExp_pos y).le
  have hR := residualConstant_nonneg
  have err := abs_G_sub_K_le (by linarith : 0 < y)
  have errP := abs_G_sub_K_le (by linarith : 0 < y+h)
  have errN := abs_G_sub_K_le (by linarith : 0 < y-h)
  rw [negativeExp_add] at errP
  rw [negativeExp_sub] at errN
  have scale (z : ℝ) (hz : z ≤ 3) :
      negativeExp y*z*residualConstant ≤ 3*negativeExp y*residualConstant := by
    nlinarith [mul_nonneg (mul_nonneg hq hR) (sub_nonneg.mpr hz)]
  have ep := (le_abs_self _).trans (errP.trans (scale _ (by linarith [(abs_le.mp hminus).2])))
  have en := (le_abs_self _).trans (errN.trans (scale _ (by linarith [(abs_le.mp hplus).2])))
  have ey := (abs_le.mp err).1
  have ey' := (abs_le.mp err).2
  have hc : |2-(positiveExp h + negativeExp h)| ≤ 4*h := by
    rw [abs_le]
    constructor <;> linarith [(abs_le.mp hplus).1,(abs_le.mp hplus).2,
      (abs_le.mp hminus).1,(abs_le.mp hminus).2]
  have mul := mul_le_mul hc hG.le (abs_nonneg _) (by positivity)
  rw [← abs_mul] at mul
  have coeff := (le_abs_self _).trans mul
  have tr := phaseDeficit_le_second_difference rh y h
  have mid := G_second_difference_le y h
  unfold phaseDeficit at tr ⊢
  change 2 * (firstLiMass - K h) - 4 * (firstLiMass - G y) ≤ _
  change _ ≤ positiveExp y * h * (positiveExp h - negativeExp h) +
    4 * (firstLiMass + 1) * h + 12 * negativeExp y * residualConstant
  linarith

private theorem origin_scale : Tendsto (fun y : ℝ => phaseDeficit (step y) /
    (negativeExp y * y ^ 2)) atTop (𝓝 (1/16)) := by
  have H := ((deficit_log_limit.comp step_small).mul log_step_scale).div_const 4
  apply (by convert H using 1 <;> norm_num :
    Tendsto (fun y : ℝ => (firstLiMass - K (step y)) / (step y * log (1 / step y))
      * (-log (step y) / y) / 4) atTop (𝓝 (1/16))).congr'
  filter_upwards [eventually_gt_atTop (0:ℝ), step_small.eventually
    (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (zero_lt_one' ℝ)))]
    with y hy hh
  have hp := step_pos hy
  have hl := (log_neg hp hh).ne
  rw [one_div, log_inv]
  unfold phaseDeficit
  field_simp [hp.ne', hl, (negativeExp_pos y).ne', hy.ne']
  unfold step
  ring

private theorem log_time_gap (rh : RiemannHypothesis) (c : ℝ) (hc : c < 1/64) :
    ∀ᶠ y : ℝ in atTop, c * (negativeExp y * y ^ 2) ≤ firstLiMass - G y := by
  let A (y : ℝ) := phaseDeficit (step y) / (negativeExp y * y ^ 2)
  let S (y : ℝ) := (positiveExp (step y) - negativeExp (step y)) / step y
  have ha : Tendsto A atTop (𝓝 (1/16)) := origin_scale
  have hs : Tendsto S atTop (𝓝 1) := sinh_slope.comp step_small
  have hi : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have H := (((ha.const_mul 2).sub (hs.div_const 16)).sub
    (hi.const_mul (firstLiMass + 1))).sub ((hi.pow 2).const_mul (12*residualConstant))
  have hh := H.eventually_const_lt (show 4*c < _ by norm_num; linarith)
  filter_upwards [hh,midpoint_transfer rh,eventually_gt_atTop (0:ℝ)] with y h ht hy
  change 4*c < 2*A y - S y/16 - (firstLiMass+1)*y⁻¹ -
    12*residualConstant*(y⁻¹)^2 at h
  have hq := negativeExp_pos y
  have hp := step_pos hy
  let w := negativeExp y * y^2
  have hw : 0 < w := mul_pos hq (sq_pos_of_pos hy)
  have a : A y*w = phaseDeficit (step y) := div_mul_cancel₀ _ hw.ne'
  have s : S y/16*w = positiveExp y*step y*(positiveExp (step y)-negativeExp (step y)) := by
    dsimp only [S,w]
    have pr := negativeExp_mul_positiveExp y
    field_simp [hp.ne']
    unfold step
    linear_combination (norm := ring) -(y^2 * negativeExp y *
      (positiveExp (y/4*negativeExp y)-negativeExp (y/4*negativeExp y))) * pr
  have b : (firstLiMass+1)*y⁻¹*w = 4*(firstLiMass+1)*step y := by
    dsimp only [w,step]
    field_simp
  have r : 12*residualConstant*(y⁻¹)^2*w = 12*negativeExp y*residualConstant := by
    dsimp only [w]
    field_simp
  have hm := mul_lt_mul_of_pos_right h hw
  simp only [sub_mul, mul_assoc (2:ℝ), a,s,b,r] at hm
  change c*w ≤ _
  linarith

/-- The real-axis critical Mangoldt gap eventually saves every strict submultiple
of one sixty-fourth of the squared logarithm exactly under classical RH. -/
theorem rh_iff_eventually_log_squared_gap :
    RiemannHypothesis ↔ ∀ c : ℝ, c < 1/64 → ∀ᶠ x : ℝ in atTop,
      U x ≤ firstLiMass * sqrt x - c * (log x)^2 := by
  constructor
  · intro rh c hc
    filter_upwards [tendsto_log_atTop.eventually (log_time_gap rh c hc),
      eventually_gt_atTop (1:ℝ)] with x h hx
    have hx0 := zero_lt_one.trans hx
    have hw : negativeExp (log x) * sqrt x = 1 := by
      simpa [positiveExp, exp_half, exp_log hx0] using negativeExp_mul_positiveExp (log x)
    change c*(negativeExp (log x)*(log x)^2) ≤ firstLiMass - G (log x) at h
    rw [G,exp_log hx0] at h
    change c*(negativeExp (log x)*(log x)^2) ≤ firstLiMass - negativeExp (log x)*U x at h
    apply le_of_mul_le_mul_left (a:=negativeExp (log x)) _ (negativeExp_pos _)
    nlinarith [congrArg (fun t : ℝ => firstLiMass*t) hw]
  · intro h
    apply MangoldtCriticalGap.rh_iff_critical_gap_tendsto_atTop.mpr
    have L : Tendsto (fun x : ℝ => (1/128:ℝ)*(log x)^2) atTop atTop :=
      (tendsto_pow_atTop (by decide : 2 ≠ 0) |>.comp tendsto_log_atTop).const_mul_atTop (by norm_num)
    apply tendsto_atTop_mono' _ _ L
    filter_upwards [h (1/128) (by norm_num)] with x hx
    linarith

end D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtLogSquareGap
