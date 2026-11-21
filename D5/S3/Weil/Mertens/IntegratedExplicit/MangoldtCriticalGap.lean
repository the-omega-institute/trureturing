/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtCriticalGap
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/MangoldtCriticalGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Under RH the additive gap below the sharp critical Mertens envelope diverges. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope
import Batteries.Tactic.OpenPrivate

/-! normalizedMangoldt near-zero slope bound for the complete cosine series transfers to an additive
gap at infinity via the midpoint inequality for the complete Mangoldt ramps. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Set Real
open scoped Topology
open D5.S3.Weil.Mertens.IntegratedExplicit
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope (G)
open D5.S3.Arith.Robin.CompleteMertensPeak (U)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (firstLiMass actualZero)
open private on_line coeff_real coeff_norm_hasSum normalizedH from
  D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope

namespace D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtCriticalGap

private def cosineProfile (y : ℝ) : ℝ := (normalizedH y).re
private def phaseDeficit (y : ℝ) : ℝ := firstLiMass - cosineProfile y

private lemma normalized_term_re (rh : RiemannHypothesis) (s : ℝ) (k : ℕ) :
    ((exp (-s/2) : ℂ) * (actualCoeff k * Complex.exp ((s : ℂ) * actualZero k))).re =
      ‖actualCoeff k‖ * cos (s * (actualZero k).im) := by
  have hc := coeff_real rh k
  rw [hc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr (by positivity))]
  have hp : (exp (-s/2) : ℂ) * Complex.exp ((s:ℂ) * actualZero k) =
      Complex.exp (((s*(actualZero k).im:ℝ):ℂ)*Complex.I) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, on_line rh k]
    ring
  rw [mul_left_comm, hp, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

private theorem cosineProfile_hasSum (rh : RiemannHypothesis) (s : ℝ) :
    HasSum (fun k => ‖actualCoeff k‖ * cos (s*(actualZero k).im)) (cosineProfile s) := by
  exact (Complex.hasSum_re (((actualH_summable s).hasSum).mul_left ((exp (-s/2):ℝ):ℂ))).congr_fun
    (fun k => (normalized_term_re rh s k).symm)

private theorem phaseDeficit_le_second_difference (rh : RiemannHypothesis) (y h : ℝ) :
    2 * phaseDeficit h - 4 * phaseDeficit y ≤
      2 * cosineProfile y - cosineProfile (y + h) - cosineProfile (y - h) := by
  have mass := coeff_norm_hasSum rh
  have lhs := ((mass.sub (cosineProfile_hasSum rh h)).mul_left 2).sub
    ((mass.sub (cosineProfile_hasSum rh y)).mul_left 4)
  have rhs := (((cosineProfile_hasSum rh y).mul_left 2).sub (cosineProfile_hasSum rh (y+h))).sub
    (cosineProfile_hasSum rh (y-h))
  apply hasSum_le _ lhs rhs
  intro k
  simp only [add_mul, sub_mul, Real.cos_add, Real.cos_sub]
  have m := norm_nonneg (actualCoeff k)
  have cy := sub_nonneg.mpr (cos_le_one (y*(actualZero k).im))
  have ch : 0 ≤ cos (h*(actualZero k).im)+1 := by linarith [neg_one_le_cos (h*(actualZero k).im)]
  nlinarith [mul_nonneg m (mul_nonneg cy ch)]

private theorem cosineProfile_eq {y : ℝ} (hy : 0 < y) :
    cosineProfile y = exp (-y/2) * (U (exp y) - log (2*π) + trivialT y) := by
  rw [cosineProfile, normalizedH, actual_integrated_explicit_formula hy, ← Complex.ofReal_mul,
    Complex.ofReal_re]

private theorem trivial_drop_div_tendsto_atTop :
    Tendsto (fun h : ℝ => (trivialT 0 - trivialT h) / h) (𝓝[>] 0) atTop := by
  apply tendsto_atTop.mpr
  intro B
  obtain ⟨N,hN⟩ := (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually_ge_atTop (6*B)).exists
  have cutoff_pos : (0 : ℝ) < 1 / (2 * ((N : ℝ) + 1)) := by positivity
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds cutoff_pos)] with h hpos hsmall
  change 0 < h at hpos
  have hbound (n : ℕ) (hn : n ∈ Finset.range N) :
      h / (6 * ((n:ℝ)+1)) ≤ trivialCoeff n * (1-exp (-(2*((n:ℝ)+1))*h)) := by
    let a := 2*((n:ℝ)+1)*h
    have ha : 0 ≤ a := by dsimp [a]; positivity
    have hnN : (n:ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hn).le
    have ha1 : a ≤ 1 := by
      have hh := (lt_div_iff₀ (by positivity : (0:ℝ) < 2*((N:ℝ)+1))).mp hsmall
      dsimp [a]
      nlinarith [mul_le_mul_of_nonneg_right hnN hpos.le]
    have hex := add_one_le_exp a
    have hrec : exp (-a) ≤ 1 / (1+a) := by
      rw [exp_neg, inv_eq_one_div]
      apply one_div_le_one_div_of_le (by linarith)
      linarith
    have hl : a/2 ≤ 1-exp (-a) := by
      have haux : a/2 ≤ 1-1/(1+a) := by
        field_simp [show 0<1+a by linarith]
        nlinarith [mul_nonneg ha (sub_nonneg.mpr ha1)]
      linarith
    rw [show -(2*((n:ℝ)+1))*h = -a by dsimp [a]; ring]
    apply le_trans _ (mul_le_mul_of_nonneg_left hl (trivialCoeff_nonneg _))
    dsimp [trivialCoeff,a]
    field_simp
    nlinarith [mul_nonneg hpos.le (Nat.cast_nonneg (α:=ℝ) n)]
  have hs := trivialCoeff_hasSum.summable.sub (trivialT_summable hpos.le)
  have hdrop : trivialT 0 - trivialT h =
      ∑' n, (trivialCoeff n - trivialCoeff n * exp (-(2*((n:ℝ)+1))*h)) := by
    rw [trivialT, trivialT, ← Summable.tsum_sub]
    · simp
    · simpa using trivialCoeff_hasSum.summable
    · exact trivialT_summable hpos.le
  have hpart := hs.sum_le_tsum (Finset.range N) (fun n _ => by
    have hexp : exp (-(2 * ((n : ℝ) + 1)) * h) ≤ 1 :=
      exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hpos.le)
    exact sub_nonneg.mpr (mul_le_of_le_one_right (trivialCoeff_nonneg n) hexp))
  have hsum := Finset.sum_le_sum hbound
  rw [hdrop]
  apply (le_div_iff₀ hpos).2
  calc
    B * h ≤ (∑ i ∈ Finset.range N, 1 / ((i : ℝ) + 1)) * (h / 6) := by
      nlinarith [mul_le_mul_of_nonneg_right hN hpos.le]
    _ = ∑ i ∈ Finset.range N, h / (6 * ((i : ℝ) + 1)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ ≤ _ := hsum
    _ ≤ _ := by simpa only [mul_sub, mul_one] using hpart

private def smoothBackground (h : ℝ) : ℝ :=
  exp (-h / 2) * ((1 + eulerMascheroniConstant - h) * exp h - log (2 * π))

private theorem U_exp_of_lt_log_two {h : ℝ} (hh : h < log 2) :
    U (exp h) = (1 + eulerMascheroniConstant - h) * exp h := by
  have h2 : exp h < (2:ℝ) := (lt_log_iff_exp_lt (by norm_num)).mp hh
  rw [U_eq_complete_ramps (exp_pos _).le,
    mangoldtPart_eq_range (N := 2) (exp_pos _).le (by simpa using h2)]
  simp [Finset.sum_range_succ, mangoldtRamp, Real.log_exp]
  ring

private theorem phaseDeficit_div_tendsto_atTop :
    Tendsto (fun h : ℝ => phaseDeficit h / h) (𝓝[>] 0) atTop := by
  have hM : firstLiMass = smoothBackground 0 + trivialT 0 := by
    simp [smoothBackground, trivialT, firstLiMass, trivialCoeff_hasSum.tsum_eq,
      log_mul (by norm_num : (2 : ℝ) ≠ 0) (sqrt_pos.mpr pi_pos).ne',
      log_mul (by norm_num : (2 : ℝ) ≠ 0) pi_pos.ne', log_sqrt pi_pos.le]
    ring
  have hd : DifferentiableAt ℝ smoothBackground 0 := by unfold smoothBackground; fun_prop
  have ht := hd.hasDerivAt.tendsto_slope_zero_right
  have hb : ∀ᶠ h : ℝ in 𝓝[>] 0,
      (smoothBackground h - smoothBackground 0) / h ≤ deriv smoothBackground 0 + 1 := by
    simpa only [zero_add, smul_eq_mul, ← div_eq_inv_mul] using
      (ht.eventually_le_const (lt_add_one _))
  apply tendsto_atTop.mpr
  intro B
  have log_two_pos : 0 < log 2 := log_pos (by norm_num)
  filter_upwards [hb,
    trivial_drop_div_tendsto_atTop.eventually_ge_atTop (B + deriv smoothBackground 0 + 1),
    self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds log_two_pos)] with h hs ht hp hl
  change 0 < h at hp
  have hf : cosineProfile h = smoothBackground h + exp (-h/2)*trivialT h := by
    rw [cosineProfile_eq hp, U_exp_of_lt_log_two hl, smoothBackground]
    ring
  have hle := mul_le_of_le_one_left (trivialT_nonneg hp.le)
    (exp_le_one_iff.mpr (by linarith : -h / 2 ≤ 0))
  rw [phaseDeficit, hM, hf]
  apply (le_div_iff₀ hp).2
  have h1 := (le_div_iff₀ hp).mp ht
  have h2 := (div_le_iff₀ hp).mp hs
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

private def residualConstant : ℝ := |log (2 * π)| + |1 - log 2|

private lemma residualConstant_nonneg : 0 ≤ residualConstant :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

private lemma abs_G_sub_cosineProfile_le {y : ℝ} (hy : 0 < y) :
    |G y - cosineProfile y| ≤ negativeExp y * residualConstant := by
  rw [cosineProfile_eq hy, G]
  change |negativeExp y * U (exp y) - negativeExp y * (U (exp y)-log (2*π)+trivialT y)| ≤ _
  rw [show negativeExp y * U (exp y) - negativeExp y * (U (exp y)-log (2*π)+trivialT y) =
    negativeExp y*(log (2*π)-trivialT y) by ring, abs_mul,abs_of_pos (negativeExp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (negativeExp_pos _).le
  have ht := trivialT_le_mass hy.le
  have ha := abs_sub (log (2*π)) (trivialT y)
  rw [abs_of_nonneg (trivialT_nonneg hy.le)] at ha
  unfold residualConstant
  linarith [le_abs_self (1-log 2)]

private lemma abs_G_le (rh : RiemannHypothesis) {y : ℝ} (hy : 0 < y) :
    |G y| ≤ firstLiMass + residualConstant := by
  have hf : |cosineProfile y| ≤ firstLiMass := by
    rw [← (cosineProfile_hasSum rh y).tsum_eq, ← Real.norm_eq_abs]
    exact tsum_of_norm_bounded (coeff_norm_hasSum rh) (fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _)]
      exact mul_le_of_le_one_right (norm_nonneg _) (abs_cos_le_one _))
  have hr := abs_G_sub_cosineProfile_le hy
  have hw : negativeExp y ≤ 1 := exp_le_one_iff.mpr (by linarith)
  calc
    |G y| ≤ |G y - cosineProfile y| + |cosineProfile y| := by
      simpa using abs_sub_le (G y) (cosineProfile y) 0
    _ ≤ firstLiMass + residualConstant := by
      linarith [mul_le_of_le_one_left residualConstant_nonneg hw]

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
  exact Real.tendsto_exp_atBot.comp (by
    simpa only [negativeExp, show (fun y : ℝ => -y/2) = (fun y => y*(-1/2)) by funext y; ring] using
      (tendsto_id.atTop_mul_const_of_neg (by norm_num : (-1 / 2 : ℝ) < 0) :
        Tendsto (fun y : ℝ => y * (-1 / 2)) atTop atBot))

private lemma eventually_phaseDeficit_transfer_le (rh : RiemannHypothesis) :
    ∃ B : ℝ, ∀ᶠ y : ℝ in atTop,
      2 * phaseDeficit (negativeExp y) - 4 * phaseDeficit y ≤ B * negativeExp y := by
  let C := firstLiMass+residualConstant
  refine ⟨4+4*C+8*residualConstant,?_⟩
  filter_upwards [eventually_gt_atTop (2 : ℝ),
    negativeExp_tendsto_zero_right.eventually eventually_abs_exp_sub_one_le] with y hy loc
  let h := negativeExp y
  have hp : 0<h := negativeExp_pos y
  obtain ⟨hv,hw,h1⟩ := loc
  change |positiveExp h-1| ≤ 2*h at hv
  change |negativeExp h-1| ≤ 2*h at hw
  change h ≤ 1 at h1
  have gyr := abs_G_sub_cosineProfile_le (by linarith : 0<y)
  have gpl := abs_G_sub_cosineProfile_le (by linarith : 0<y+h)
  have gmi := abs_G_sub_cosineProfile_le (by linarith : 0<y-h)
  rw [negativeExp_add] at gpl
  rw [negativeExp_sub] at gmi
  change |G y-cosineProfile y| ≤ h*residualConstant at gyr
  change |G (y+h)-cosineProfile (y+h)| ≤ h*negativeExp h*residualConstant at gpl
  change |G (y-h)-cosineProfile (y-h)| ≤ h*positiveExp h*residualConstant at gmi
  have c1 := abs_le.mp hv
  have c2 := abs_le.mp hw
  have corr (z : ℝ) (hz : z ≤ 3) : h*z*residualConstant ≤ 3*h*residualConstant := by
    nlinarith [mul_nonneg (mul_nonneg hp.le residualConstant_nonneg) (sub_nonneg.mpr hz)]
  have hP := (le_abs_self _).trans (gpl.trans (corr _ (by linarith)))
  have hN := (le_abs_self _).trans (gmi.trans (corr _ (by linarith)))
  have hY := (neg_le_abs _).trans gyr
  have gb := abs_G_le rh (by linarith : 0<y)
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

/-- Under RH the additive gap below the sharp critical envelope diverges along the real
atTop filter. -/
theorem critical_gap_tendsto_atTop (rh : RiemannHypothesis) :
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
  have y := abs_G_sub_cosineProfile_le (log_pos h1)
  have hs := (le_div_iff₀ (negativeExp_pos _)).mp hx
  have hw : negativeExp (log x) * sqrt x = 1 := by
    simpa [positiveExp, Real.exp_half, exp_log hx0] using negativeExp_mul_positiveExp (log x)
  have hy := (le_abs_self _).trans y
  rw [G, exp_log hx0] at hy
  change negativeExp (log x) * U x - cosineProfile (log x) ≤
    negativeExp (log x) * residualConstant at hy
  change (D+residualConstant)*negativeExp (log x) ≤ firstLiMass-cosineProfile (log x) at hs
  apply le_of_mul_le_mul_left (a:=negativeExp (log x)) _ (negativeExp_pos _)
  nlinarith [congrArg (fun z : ℝ => firstLiMass*z) hw]

end D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtCriticalGap
