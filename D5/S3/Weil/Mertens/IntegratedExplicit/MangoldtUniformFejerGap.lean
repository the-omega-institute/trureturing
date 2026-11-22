/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/MangoldtUniformFejerGap
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/MangoldtUniformFejerGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One real tail achieves the limiting Fejér coefficient with a log-log correction. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtFejerGap
import Batteries.Tactic.OpenPrivate

/-! On a single tail, control every Fejér step up to half the logarithmic scale.
This permits taking the degree limit at a fixed real argument. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set Real Finset
open scoped Topology BigOperators
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (firstLiMass firstLiMass_pos)
open D5.S3.Weil.Mertens.IntegratedExplicit
open ActualKernelLocalPositivity (K K_zero)
open RHSharpActualEnvelope (G actual_G_control)
open ActualKernelCusp (R c cusp_remainder_bound)
open private phaseDeficit positiveExp negativeExp positiveExp_pos negativeExp_pos negativeExp_add
  negativeExp_sub negativeExp_mul_positiveExp G_second_difference_le residualConstant
  residualConstant_nonneg abs_G_sub_K_le from D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtCriticalGap
open D5.S3.Arith.Robin.CompleteMertensPeak (U)
open MangoldtFejerGap (rh_iff_eventually_fejer_gap)
open private pairs amplitude pairDistance sum_pairDistance amplitude_nonneg amplitude_moment
  combined_phase phase_positive shift curvature from D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtFejerGap

namespace D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtUniformFejerGap

private def loss : ℝ := 2 * |c| + 4 * firstLiMass + 7

private lemma cusp_lower {b y : ℝ} (hb : b ∈ Icc (0:ℝ) (1/2)) (hy : 0 < y)
    (ht : shift b y ≤ 1/2) :
    shift b y * (y/2 - log y - 2*|c| - 2) ≤ 2*phaseDeficit (shift b y) := by
  rcases hb.1.eq_or_lt with hz | hp
  · subst b
    simp [shift, phaseDeficit, K_zero]
  · let t := shift b y
    have hp' : 0 < t := mul_pos (mul_pos hp hy) (negativeExp_pos _)
    have hR := (abs_le.mp (cusp_remainder_bound hp' ht)).2
    have hv : log t ≤ log y - y/2 := by
      dsimp [t, shift]
      rw [log_mul (mul_pos hp hy).ne' (negativeExp_pos _).ne', log_mul hp.ne' hy.ne',
        negativeExp, log_exp]
      linarith [log_nonpos hp.le (by linarith [hb.2])]
    change t * (y/2 - log y - 2*|c| - 2) ≤ 2*(firstLiMass-K t)
    unfold R at hR
    nlinarith only [hR, mul_le_mul_of_nonneg_left hv hp'.le,
      mul_le_mul_of_nonneg_right (le_abs_self c) hp'.le,
      mul_le_mul_of_nonneg_left ht hp'.le]

private lemma exponential_bounds {t : ℝ} (ht : 0 ≤ t) (hhalf : t ≤ 1/2) :
    positiveExp t-negativeExp t ≤ t + t^2 ∧
      |2-(positiveExp t + negativeExp t)| ≤ 4*t ∧
      positiveExp t ≤ 2 ∧ negativeExp t ≤ 2 := by
  have hp : |t/2| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have hn : |-t/2| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
  have P := abs_le.mp (Real.abs_exp_sub_one_sub_id_le hp)
  have N := abs_le.mp (Real.abs_exp_sub_one_sub_id_le hn)
  unfold positiveExp negativeExp
  have ht2 := mul_le_mul_of_nonneg_left hhalf ht
  refine ⟨by nlinarith [P.2,N.1,sq_nonneg t],abs_le.mpr ⟨?_,?_⟩,?_,?_⟩ <;>
    nlinarith [P.1,P.2,N.1,N.2]

private lemma uniform_curvature {y t : ℝ} (hy : 2 < y) (ht : 0 ≤ t) (hhalf : t ≤ 1/2)
    (hG : |G y| ≤ firstLiMass+1) :
    curvature y t + 2*(G y-K y) ≤ positiveExp y*t*(t+t^2) +
      4*(firstLiMass+1)*t + 12*negativeExp y*residualConstant := by
  obtain ⟨slope, weight, right, left⟩ := exponential_bounds ht hhalf
  have hr := (le_abs_self _).trans (abs_G_sub_K_le (by linarith : 0 < y+t))
  have hl := (le_abs_self _).trans (abs_G_sub_K_le (by linarith : 0 < y-t))
  rw [negativeExp_add] at hr
  rw [negativeExp_sub] at hl
  have qR := mul_nonneg (negativeExp_pos y).le residualConstant_nonneg
  have W := mul_le_mul weight hG (abs_nonneg _) (by positivity)
  rw [← abs_mul] at W
  have w := (le_abs_self _).trans W
  have ramp := (G_second_difference_le y t).trans
    (mul_le_mul_of_nonneg_left slope (mul_nonneg (positiveExp_pos _).le ht))
  unfold curvature
  nlinarith only [hr,hl,w,ramp,qR,mul_le_mul_of_nonneg_left right qR,
    mul_le_mul_of_nonneg_left left qR]

private lemma eventual_small : ∀ᶠ y : ℝ in atTop, y^2*negativeExp y ≤ 1 := by
  have L := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2:ℝ) (1/2) (by norm_num)
  have h := L.eventually_le_const (zero_lt_one' ℝ)
  filter_upwards [h] with y hy
  change y ^ (2:ℝ) * exp (-(1/2:ℝ)*y) ≤ 1 at hy
  rwa [rpow_two, show -(1/2:ℝ)*y = -y/2 by ring] at hy

private theorem uniform_pairs (rh : RiemannHypothesis) : ∀ᶠ y : ℝ in atTop, ∀ b ∈ Icc (0:ℝ) (1/2),
    negativeExp y * ((b/2-b^2)*y^2 - b*y*log y - loss*b*y - 12*residualConstant) ≤
      (2*phaseDeficit (shift b y) - curvature y (shift b y)) - 2*(G y-K y) := by
  filter_upwards [eventually_gt_atTop (2:ℝ), eventual_small, (actual_G_control rh).1 1 one_pos]
    with y hy hq hG
  intro b hb
  let t := shift b y
  have hqpos := negativeExp_pos y
  have hy0 : 0 < y := by linarith
  have ht : 0 ≤ t := mul_nonneg (mul_nonneg hb.1 hy0.le) hqpos.le
  have hyt : y*t ≤ 1/2 := by
    change y*(b*y*negativeExp y) ≤ _
    nlinarith only [mul_le_mul_of_nonneg_left hq hb.1,hb.2]
  have hhalf : t ≤ 1/2 := by nlinarith [mul_le_mul_of_nonneg_right (show 1 ≤ y by linarith) ht]
  have cusp := cusp_lower hb hy0 hhalf
  have mid := uniform_curvature hy ht hhalf hG.le
  have qP := negativeExp_mul_positiveExp y
  have qr : positiveExp y*t*t = b^2*y^2*negativeExp y := by
    dsimp [t,shift]
    linear_combination (b^2*y^2*negativeExp y)*qP
  have hcost : positiveExp y*t*(t+t^2) ≤ (b^2*y^2+b*y)*negativeExp y := by
    have hbt : b*(y*t) ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hyt hb.1,hb.2]
    have h := mul_le_mul_of_nonneg_right hbt ht
    calc
      _ = (positiveExp y*t*t)*(1+t) := by ring
      _ = b^2*y^2*negativeExp y*(1+t) := by rw [qr]
      _ ≤ _ := by
        dsimp [t, shift] at h ⊢
        nlinarith only [h]
  change t*(y/2-log y-2*|c|-2) ≤ 2*phaseDeficit t at cusp
  change _ ≤ 2*phaseDeficit t - curvature y t - 2*(G y-K y)
  unfold loss
  dsimp only [t,shift] at cusp mid hcost ⊢
  linarith

private lemma first_moment {N : ℕ} (hN : 0 < (N : ℝ)) :
    ∑ p ∈ pairs N, amplitude N p = ((N : ℝ)^2 - 1) / 6 := by
  have h : (∑ p ∈ pairs N, pairDistance p.1 p.2) = (N : ℝ) * ((N : ℝ)^2-1)/3 := by
    rw [pairs, sum_product]
    exact sum_pairDistance N
  simp only [amplitude, ← sum_div, h]
  field_simp
  ring

private lemma amplitude_mem {N : ℕ} (hN : 0 < (N : ℝ)) (p : ℕ × ℕ) (hp : p ∈ pairs N) :
    amplitude N p ∈ Icc (0 : ℝ) (1/2) := by
  refine ⟨amplitude_nonneg N p, ?_⟩
  have hp' : p.1 < N ∧ p.2 < N := by simpa [pairs] using hp
  have hj : (p.1 : ℝ) < N := by exact_mod_cast hp'.1
  have hk : (p.2 : ℝ) < N := by exact_mod_cast hp'.2
  unfold amplitude pairDistance
  apply (div_le_iff₀ (by positivity)).mpr
  rw [abs_le]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) p.1, Nat.cast_nonneg (α := ℝ) p.2]

/-- A bound for every positive integral degree gives the limiting inequality at the same point. -/
private lemma all_degrees {L E : ℝ} (bound : ∀ N : ℕ, 0 < (N : ℝ) → (N : ℝ)^2 * L ≤ E) :
    L ≤ 0 := by
  by_contra! hL
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (E / L))
  have hn : 1 < (N : ℝ) := (le_max_left _ _).trans_lt hN
  have he := (div_lt_iff₀ hL).mp ((le_max_right _ _).trans_lt hN)
  have hsq : (N : ℝ) ≤ (N : ℝ)^2 := by nlinarith
  exact (not_lt_of_ge (bound N (by linarith))) (he.trans_le (mul_le_mul_of_nonneg_right hsq hL.le))

private lemma log_gap_at (rh : RiemannHypothesis) (B y : ℝ)
    (h : ∀ b ∈ Icc (0 : ℝ) (1/2),
      negativeExp y * ((b/2-b^2)*y^2-b*y*log y-B*b*y-12*residualConstant) ≤
        (2*phaseDeficit (shift b y)-curvature y (shift b y))-2*(G y-K y)) :
    negativeExp y * (y^2/48 - y*log y/12 - B*y/12 - 6*residualConstant) ≤ firstLiMass - G y := by
  let A := y^2/48 - y*log y/12 - B*y/12
  have bounded : negativeExp y * (A-6*residualConstant) - (firstLiMass-G y) ≤ 0 := by
    apply all_degrees (E := negativeExp y * A)
    intro N hN
    have cardN : ((pairs N).card : ℝ) = (N : ℝ)^2 := by simp [pairs, pow_two]
    have moment := amplitude_moment hN
    have linearMoment := first_moment hN
    have sumBound := sum_le_sum (s := pairs N) (fun p hp => show
      negativeExp y * ((amplitude N p/2-(amplitude N p)^2)*y^2 - amplitude N p*(y*log y)
        - amplitude N p*(B*y) - 12*residualConstant) ≤ _ from by
      convert h (amplitude N p) (amplitude_mem hN p hp) using 1; ring)
    rw [← Finset.mul_sum] at sumBound
    simp only [sum_sub_distrib, ← sum_mul, moment, linearMoment, Finset.sum_const,
      nsmul_eq_mul, cardN] at sumBound
    have phaseBound := combined_phase rh (pairs N) (fun p => shift (amplitude N p) y)
      (fun u => phase_positive N u y) y
    rw [cardN, sum_sub_distrib] at phaseBound
    have combined := sumBound.trans (sub_le_sub_right phaseBound _)
    unfold phaseDeficit at combined
    dsimp [A]
    linarith only [combined]
  dsimp [A] at bounded
  linarith only [bounded]

/-- The uniform pair estimate gives an absolute linear loss on one common real tail. -/
private theorem forward_of_pairs (rh : RiemannHypothesis) (B : ℝ)
    (bound : ∀ᶠ y : ℝ in atTop, ∀ b ∈ Icc (0 : ℝ) (1/2),
      negativeExp y * ((b/2-b^2)*y^2-b*y*log y-B*b*y-12*residualConstant) ≤
        (2*phaseDeficit (shift b y)-curvature y (shift b y))-2*(G y-K y)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      U x ≤ firstLiMass * sqrt x - (log x)^2/48 + (log x)*log (log x)/12 + C*log x := by
  let C := |B|/12 + 6*residualConstant
  refine ⟨C, by dsimp [C]; positivity [residualConstant_nonneg], ?_⟩
  have correction : ∀ᶠ y : ℝ in atTop,
      negativeExp y * (y^2/48 - y*log y/12 - C*y) ≤ firstLiMass - G y := by
    filter_upwards [bound, eventually_ge_atTop (1:ℝ)] with y hy hy1
    apply le_trans _ (log_gap_at rh B y hy)
    apply mul_le_mul_of_nonneg_left _ (negativeExp_pos y).le
    dsimp [C]
    nlinarith only [mul_nonneg (sub_nonneg.mpr (le_abs_self B)) (show 0 ≤ y by linarith),
      mul_nonneg residualConstant_nonneg (sub_nonneg.mpr hy1)]
  filter_upwards [tendsto_log_atTop.eventually correction, eventually_gt_atTop (1:ℝ)] with x hx hx1
  have hx0 := zero_lt_one.trans hx1
  have hw : negativeExp (log x) * sqrt x = 1 := by
    simpa [positiveExp, exp_half, exp_log hx0] using negativeExp_mul_positiveExp (log x)
  rw [G, exp_log hx0] at hx
  change negativeExp (log x) * ((log x)^2/48-log x*log (log x)/12-C*log x) ≤
    firstLiMass - negativeExp (log x)*U x at hx
  apply le_of_mul_le_mul_left (a := negativeExp (log x)) _ (negativeExp_pos _)
  linarith only [hx, congrArg (fun t : ℝ => firstLiMass*t) hw]


private theorem converse (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
    U x ≤ firstLiMass * sqrt x - (log x)^2/48 + (log x)*log (log x)/12 + C*log x) :
    RiemannHypothesis := by
  obtain ⟨C, _, bound⟩ := h
  apply rh_iff_eventually_fejer_gap.mpr
  intro c hc
  have logDiv : Tendsto (fun y : ℝ => log y / y) atTop (𝓝 0) := by
    simpa using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero)
  have inv : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have small : Tendsto (fun y : ℝ => (log y / y)/12 + C / y) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (logDiv.div_const 12).add (inv.const_mul C)
  have tail : ∀ᶠ y : ℝ in atTop, y * log y/12 + C*y ≤ (1/48-c)*y^2 := by
    filter_upwards [small.eventually_lt_const (show 0 < 1/48-c by linarith),
      eventually_gt_atTop (0:ℝ)] with y hy hy0
    have eqn : ((log y/y)/12+C/y)*y^2 = y*log y/12+C*y := by
      field_simp
    rw [← eqn]
    exact mul_le_mul_of_nonneg_right hy.le (sq_nonneg y)
  filter_upwards [bound, tendsto_log_atTop.eventually tail] with x hx hcorr
  linarith only [hx,hcorr]


/-- Classical RH is equivalent to one common upper envelope with the limiting
Fejér coefficient and an explicit logarithmic lower-order term. -/
theorem rh_iff_eventually_uniform_fejer_gap :
    RiemannHypothesis ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      U x ≤ firstLiMass * sqrt x - (log x)^2/48 + (log x)*log (log x)/12 + C*log x :=
  ⟨fun rh => forward_of_pairs rh loss (uniform_pairs rh), converse⟩

end D5.S3.Weil.Mertens.IntegratedExplicit.MangoldtUniformFejerGap
