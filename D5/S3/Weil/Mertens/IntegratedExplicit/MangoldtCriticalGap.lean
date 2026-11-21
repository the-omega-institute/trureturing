/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtCriticalGap
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/MangoldtCriticalGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The additive gap below the sharp critical Mertens envelope diverges exactly under RH. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualLinearPeak
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelGlobalStrictPositivity

/-! A near-zero slope bound for the complete cosine series transfers to an additive
gap at infinity via the midpoint inequality for the complete Mangoldt ramps. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Set Real
open scoped Topology
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope
  (G actual_G_control abs_G_sub_normalized_actualH_le coeff_real coeff_norm_hasSum)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelGlobalStrictPositivity (actual_cosine_hasSum)
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
open D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelSubexponential (K_eq_linearKernel)
open D5.S3.Arith.Robin.CompleteMertensPeak (U)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds

namespace D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtCriticalGap

private def phaseDeficit (y : ℝ) : ℝ := firstLiMass - K y

private theorem phaseDeficit_le_second_difference (rh : RiemannHypothesis) (y h : ℝ) :
    2 * phaseDeficit h - 4 * phaseDeficit y ≤
      2 * K y - K (y + h) - K (y - h) := by
  have series (s : ℝ) :
      HasSum (fun k => ‖actualCoeff k‖ * cos ((actualZero k).im * s)) (K s) := by
    have hnorm (k : ℕ) : ‖actualCoeff k‖ = 1 / (1 / 4 + (actualZero k).im ^ 2) := by
      rw [coeff_real rh k, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (one_div_pos.mpr (by positivity))]
    simpa only [Complex.ofReal_re, hnorm] using Complex.hasSum_re (actual_cosine_hasSum rh s)
  have mass := coeff_norm_hasSum rh
  have lhs := ((mass.sub (series h)).mul_left 2).sub ((mass.sub (series y)).mul_left 4)
  have rhs := (((series y).mul_left 2).sub (series (y + h))).sub (series (y - h))
  apply hasSum_le _ lhs rhs
  intro k
  simp only [mul_add, mul_sub, Real.cos_add, Real.cos_sub]
  have m := norm_nonneg (actualCoeff k)
  have cy := sub_nonneg.mpr (cos_le_one ((actualZero k).im * y))
  have ch : 0 ≤ cos ((actualZero k).im * h)+1 := by linarith [neg_one_le_cos ((actualZero k).im * h)]
  nlinarith [mul_nonneg m (mul_nonneg cy ch)]

private theorem phaseDeficit_div_tendsto_atTop :
    Tendsto (fun h : ℝ => phaseDeficit h / h) (𝓝[>] 0) atTop := by
  apply tendsto_atTop.mpr
  intro B
  have hderiv := D1_atBot.eventually (eventually_le_atBot (-B))
  obtain ⟨δ, hδ, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hderiv
  have hlog : 0 < log 2 := log_pos (by norm_num)
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
    (eventually_lt_nhds (lt_min hδ hlog))] with h hp hh
  change 0 < h at hp
  obtain ⟨u, hu, hslope⟩ := exists_hasDerivAt_eq_slope K D1 hp K_continuous.continuousOn
    (fun u hu => hasDerivAt_K hu.1 (hu.2.trans (hh.trans_le (min_le_right _ _))))
  have hu_bound := hbound ⟨hu.1, hu.2.trans (hh.trans_le (min_le_left _ _))⟩
  change D1 u ≤ -B at hu_bound
  rw [hslope, K_zero, sub_zero] at hu_bound
  rw [phaseDeficit, ← neg_sub, neg_div]
  linarith

private def positiveExp (y : ℝ) := exp (y/2)
private def negativeExp (y : ℝ) := exp (-y/2)
private lemma positiveExp_pos (y : ℝ) : 0 < positiveExp y := exp_pos _
private theorem negativeExp_pos (y : ℝ) : 0 < negativeExp y := exp_pos _

private lemma positiveExp_add (y h : ℝ) : positiveExp (y + h) = positiveExp y * positiveExp h := by
  simp [positiveExp, add_div, exp_add]

private lemma positiveExp_sub (y h : ℝ) : positiveExp (y - h) = positiveExp y * negativeExp h := by
  rw [positiveExp, positiveExp, negativeExp, ← exp_add]
  congr 1
  ring

private lemma negativeExp_add (y h : ℝ) : negativeExp (y + h) = negativeExp y * negativeExp h := by
  rw [negativeExp, negativeExp, negativeExp, ← exp_add]
  congr 1
  ring

private lemma negativeExp_sub (y h : ℝ) : negativeExp (y - h) = negativeExp y * positiveExp h := by
  rw [negativeExp, negativeExp, positiveExp, ← exp_add]
  congr 1
  ring

private theorem negativeExp_mul_positiveExp (y : ℝ) : negativeExp y * positiveExp y = 1 := by
  rw [negativeExp, positiveExp, ← exp_add, show -y / 2 + y / 2 = 0 by ring, exp_zero]

private lemma negativeExp_mul_exp (y : ℝ) : negativeExp y * exp y = positiveExp y := by
  rw [negativeExp, positiveExp, ← exp_add]
  congr 1
  ring

private def normalizedRamp (n : ℕ) (y : ℝ) := negativeExp y * mangoldtRamp n (exp y)
private lemma normalizedRamp_eq (n : ℕ) (y : ℝ) : normalizedRamp n y =
    ArithmeticFunction.vonMangoldt n * max (positiveExp y/(n:ℝ)-negativeExp y) 0 := by
  rw [normalizedRamp, mangoldtRamp, mul_left_comm, mul_max_of_nonneg _ _ (negativeExp_pos _).le,
    mul_sub, mul_one, mul_zero, mul_div_assoc', negativeExp_mul_exp]

private theorem normalizedRamp_midpoint (n : ℕ) (y h : ℝ) :
    (positiveExp h + negativeExp h) * normalizedRamp n y ≤
      normalizedRamp n (y + h) + normalizedRamp n (y - h) := by
  rw [normalizedRamp_eq, normalizedRamp_eq, normalizedRamp_eq, positiveExp_add, positiveExp_sub,
    negativeExp_add, negativeExp_sub]
  have hc := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  rw [← mul_add, mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ hc
  rw [mul_max_of_nonneg _ _ (add_nonneg (positiveExp_pos _).le (negativeExp_pos _).le),mul_zero]
  apply max_le
  · have h1 := le_max_left (positiveExp y*positiveExp h/(n:ℝ)-negativeExp y*negativeExp h) 0
    have h2 := le_max_left (positiveExp y*negativeExp h/(n:ℝ)-negativeExp y*positiveExp h) 0
    simp only [div_eq_mul_inv] at *
    linarith
  · exact add_nonneg (le_max_right _ _) (le_max_right _ _)

private def normalizedMangoldt (y : ℝ) := negativeExp y * mangoldtPart (exp y)
private theorem normalizedMangoldt_midpoint (y h : ℝ) :
    (positiveExp h + negativeExp h) * normalizedMangoldt y ≤
      normalizedMangoldt (y + h) + normalizedMangoldt (y - h) := by
  have hs (u : ℝ) : HasSum (fun n => normalizedRamp n u) (normalizedMangoldt u) :=
    ((mangoldtPart_summable (exp_pos u).le).hasSum).mul_left _
  exact hasSum_le (fun n => normalizedRamp_midpoint n y h)
    ((hs y).mul_left (positiveExp h + negativeExp h)) ((hs _).add (hs _))

private theorem G_eq_normalizedMangoldt_add (y : ℝ) :
    G y = normalizedMangoldt y + (1 + eulerMascheroniConstant - y) * positiveExp y := by
  change negativeExp y * U (exp y) = _
  rw [U_eq_complete_ramps (exp_pos _).le, log_exp, normalizedMangoldt, ← negativeExp_mul_exp]
  ring

private theorem G_second_difference_le (y h : ℝ) :
    (positiveExp h + negativeExp h) * G y - G (y + h) - G (y - h) ≤
      positiveExp y * h * (positiveExp h - negativeExp h) := by
  have ht := normalizedMangoldt_midpoint y h
  rw [G_eq_normalizedMangoldt_add, G_eq_normalizedMangoldt_add, G_eq_normalizedMangoldt_add,
    positiveExp_add, positiveExp_sub]
  linarith

private def residualConstant : ℝ := log (2 * π)

private lemma residualConstant_nonneg : 0 ≤ residualConstant :=
  log_nonneg (by linarith [pi_gt_three])

private lemma abs_G_sub_K_le {y : ℝ} (hy : 0 < y) :
    |G y - K y| ≤ negativeExp y * residualConstant := by
  rw [K_eq_linearKernel hy]
  exact (abs_G_sub_normalized_actualH_le hy.le).le

private lemma eventually_abs_exp_sub_one_le : ∀ᶠ h : ℝ in 𝓝[>] 0,
    |positiveExp h-1| ≤ 2*h ∧ |negativeExp h-1| ≤ 2*h ∧ h ≤ 1 := by
  have H (a : ℝ) (ha : |a| < 2) : ∀ᶠ h : ℝ in 𝓝[>] 0, |exp (a*h)-1| ≤ 2*h := by
    have hd : HasDerivAt (fun z : ℝ => exp (a*z)) a 0 := by
      convert ((hasDerivAt_id (0:ℝ)).const_mul a).exp using 1 <;> simp
    have hs := hd.tendsto_slope_zero_right.abs.eventually_le_const ha
    filter_upwards [hs,self_mem_nhdsWithin] with h hh hp
    change 0 < h at hp
    simpa [← div_eq_inv_mul, abs_div, abs_of_pos hp, div_le_iff₀ hp] using hh
  filter_upwards [H (1/2) (by norm_num),H (-1/2) (by norm_num),
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (zero_lt_one' ℝ))] with h a b c
  exact ⟨by simpa [positiveExp, div_eq_mul_inv, mul_comm] using a,
    by simpa [negativeExp, div_eq_mul_inv, mul_comm] using b, c.le⟩

private lemma negativeExp_tendsto_zero_right : Tendsto negativeExp atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,Eventually.of_forall negativeExp_pos⟩
  exact (Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (tendsto_id.atTop_mul_const (by norm_num : (0 : ℝ) < 1 / 2))).congr
      (fun y => by simp [negativeExp, div_eq_mul_inv, neg_mul])

private lemma eventually_phaseDeficit_transfer_le (rh : RiemannHypothesis) :
    ∃ B : ℝ, ∀ᶠ y : ℝ in atTop,
      2 * phaseDeficit (negativeExp y) - 4 * phaseDeficit y ≤ B * negativeExp y := by
  let C := firstLiMass + 1
  refine ⟨4 + 4 * C + 8 * residualConstant, ?_⟩
  filter_upwards [eventually_gt_atTop (2 : ℝ),
    negativeExp_tendsto_zero_right.eventually eventually_abs_exp_sub_one_le,
    (actual_G_control rh).1 1 one_pos] with y hy loc hG
  let h := negativeExp y
  have hp : 0<h := negativeExp_pos y
  obtain ⟨hv,hw,h1⟩ := loc
  change |positiveExp h-1| ≤ 2*h at hv
  change |negativeExp h-1| ≤ 2*h at hw
  change h ≤ 1 at h1
  have gyr := abs_G_sub_K_le (by linarith : 0<y)
  have gpl := abs_G_sub_K_le (by linarith : 0<y+h)
  have gmi := abs_G_sub_K_le (by linarith : 0<y-h)
  rw [negativeExp_add] at gpl
  rw [negativeExp_sub] at gmi
  change |G y-K y| ≤ h*residualConstant at gyr
  change |G (y+h)-K (y+h)| ≤ h*negativeExp h*residualConstant at gpl
  change |G (y-h)-K (y-h)| ≤ h*positiveExp h*residualConstant at gmi
  have c1 := abs_le.mp hv
  have c2 := abs_le.mp hw
  have corr (z : ℝ) (hz : z ≤ 3) : h*z*residualConstant ≤ 3*h*residualConstant := by
    nlinarith [mul_nonneg (mul_nonneg hp.le residualConstant_nonneg) (sub_nonneg.mpr hz)]
  have hP := (le_abs_self _).trans (gpl.trans (corr _ (by linarith)))
  have hN := (le_abs_self _).trans (gmi.trans (corr _ (by linarith)))
  have hY := (neg_le_abs _).trans gyr
  have gb : |G y| ≤ C := hG.le
  have um : |2-(positiveExp h+negativeExp h)| ≤ 4*h := by rw [abs_le]; constructor <;> linarith
  have coeff := mul_le_mul um gb (abs_nonneg _) (by linarith : 0 ≤ 4*h)
  rw [← abs_mul] at coeff
  have hcoeff := (le_abs_self _).trans coeff
  have gm := G_second_difference_le y h
  have hyh : positiveExp y*h=1 := by simpa [h,mul_comm] using negativeExp_mul_positiveExp y
  rw [hyh,one_mul] at gm
  have tr := phaseDeficit_le_second_difference rh y h
  change 2*phaseDeficit h -4*phaseDeficit y ≤ (4+4*C+8*residualConstant)*h
  dsimp only [C]
  linarith

private theorem critical_gap_tendsto_atTop (rh : RiemannHypothesis) :
    Tendsto (fun x : ℝ => firstLiMass*sqrt x-U x) atTop atTop := by
  obtain ⟨B,hB⟩ := eventually_phaseDeficit_transfer_le rh
  have hc := phaseDeficit_div_tendsto_atTop.comp negativeExp_tendsto_zero_right
  have hd : Tendsto (fun y : ℝ => phaseDeficit y / negativeExp y) atTop atTop := by
    apply tendsto_atTop.mpr
    intro D
    filter_upwards [hB,hc.eventually_ge_atTop (2*D+B/2)] with y ht hs
    change 2*D+B/2 ≤ phaseDeficit (negativeExp y)/negativeExp y at hs
    apply (le_div_iff₀ (negativeExp_pos _)).2
    linarith [(le_div_iff₀ (negativeExp_pos _)).mp hs]
  apply tendsto_atTop.mpr
  intro D
  filter_upwards [Real.tendsto_log_atTop.eventually (hd.eventually_ge_atTop (D + residualConstant)),
    eventually_gt_atTop (1 : ℝ)] with x hx h1
  have hx0 := zero_lt_one.trans h1
  have y := abs_G_sub_K_le (log_pos h1)
  have hs := (le_div_iff₀ (negativeExp_pos _)).mp hx
  have hw : negativeExp (log x) * sqrt x = 1 := by
    simpa [positiveExp, Real.exp_half, exp_log hx0] using negativeExp_mul_positiveExp (log x)
  have hy := (le_abs_self _).trans y
  rw [G, exp_log hx0] at hy
  change negativeExp (log x) * U x - K (log x) ≤
    negativeExp (log x) * residualConstant at hy
  change (D+residualConstant)*negativeExp (log x) ≤ firstLiMass-K (log x) at hs
  apply le_of_mul_le_mul_left (a:=negativeExp (log x)) _ (negativeExp_pos _)
  nlinarith [congrArg (fun z : ℝ => firstLiMass*z) hw]

/-- The additive gap below the sharp critical envelope diverges along the real
atTop filter exactly when RH holds. -/
theorem rh_iff_critical_gap_tendsto_atTop :
    RiemannHypothesis ↔ Tendsto (fun x : ℝ => firstLiMass * sqrt x - U x) atTop atTop := by
  refine ⟨critical_gap_tendsto_atTop, ?_⟩
  intro hgap
  obtain ⟨a, ha⟩ := eventually_atTop.mp
    (tendsto_exp_atTop.eventually (hgap.eventually_ge_atTop (0 : ℝ)))
  let t := max a 1
  have ht : 0 < t := zero_lt_one.trans_le (le_max_right _ _)
  apply actual_kernel_affine_tail_implies_rh t 0 (firstLiMass + residualConstant) ht
  intro y hy
  have hy0 := ht.trans_le hy
  have hU : U (exp y) ≤ firstLiMass * sqrt (exp y) :=
    sub_nonneg.mp (ha y ((le_max_left _ _).trans hy))
  have hG : G y ≤ firstLiMass := by
    change negativeExp y * U (exp y) ≤ firstLiMass
    calc
      _ ≤ negativeExp y * (firstLiMass * sqrt (exp y)) :=
        mul_le_mul_of_nonneg_left hU (negativeExp_pos y).le
      _ = firstLiMass := by
        rw [← exp_half, mul_left_comm, ← show positiveExp y = exp (y / 2) from rfl,
          negativeExp_mul_positiveExp, mul_one]
  have hdiff := (neg_le_abs (G y - K y)).trans (abs_G_sub_K_le hy0)
  have hdecay : negativeExp y ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have hR := mul_le_of_le_one_left residualConstant_nonneg hdecay
  rw [zero_mul, zero_add]
  linarith

end D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtCriticalGap
