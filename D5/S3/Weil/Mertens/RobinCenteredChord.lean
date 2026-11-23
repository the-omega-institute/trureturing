/- GID: D5/S3/Weil/Mertens/RobinCenteredChord
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/RobinCenteredChord
   mirror-E: none(waiver:analytic-integral-estimate)
   anchors: []
   utility: none
   digest: Balanced short-interval Chebyshev integrals for the exact Robin chord. -/

import D5.S3.Weil.Mertens.RobinWeightedRamp
import D5.S3.Arith.Robin.ActualRobinClockCovariance

/-! The signed Robin chord cancels constant shifts in the Chebyshev error.
The resulting local range bound also controls the weighted positive mass. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Mertens.RobinCenteredChord

open Real Set MeasureTheory
open D5.S3.Arith.Robin.ActualRobinClockCovariance
  (activationDensity density_integrable density_integral)
open D5.S3.Arith.Robin.CompleteMertensPeak (psiErrorKernel complete_mertens_ledger)
open D5.S3.Weil.Mertens.RobinWeightedRamp (R u ramp_eq_neg_weightedTail)
open D5.S3.Weil.Mertens.WeightedTailTransport (weightedTail)
open D5.S3.Weil.Mertens.WeightedTailWindowMass (weightedNegativeMass)

noncomputable section

private lemma u_pos {x : ℝ} (hx : 1 < x) : 0 < u x :=
  mul_pos (zero_lt_one.trans hx) (log_pos hx)

private lemma u_strictMonoOn : StrictMonoOn u (Ioi 1) := by
  intro x hx y hy hxy
  have hx' : 1 < x := hx
  have hlog := log_le_log (zero_lt_one.trans hx') hxy.le
  exact (mul_lt_mul_of_pos_right hxy (log_pos hx')).trans_le
    (mul_le_mul_of_nonneg_left hlog (by linarith))

private lemma weighted_kernel_eq (t : ℝ) :
    psiErrorKernel t * WeightedTailTransport.r t =
      (Chebyshev.psi t - t) * activationDensity t := by
  unfold psiErrorKernel WeightedTailTransport.r activationDensity
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private lemma weightedTail_sub_eq_interval {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    weightedTail psiErrorKernel a - weightedTail psiErrorKernel b =
      ∫ t in a..b, (Chebyshev.psi t - t) * activationDensity t := by
  unfold weightedTail
  simpa only [weighted_kernel_eq] using
    (intervalIntegral.integral_Ioi_sub_Ioi (complete_mertens_ledger ha).2.1 hab)

private lemma intervalIntegrable_weighted_error {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => (Chebyshev.psi t - t) * activationDensity t) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have hint : IntegrableOn (fun t => psiErrorKernel t * WeightedTailTransport.r t) (Ioc a b) :=
    (complete_mertens_ledger ha).2.1.mono_set Ioc_subset_Ioi_self
  simpa only [weighted_kernel_eq] using hint

private lemma centered_kernel_eq (m : ℝ) :
    (fun t => (Chebyshev.psi t - t - m) * activationDensity t) =
      (fun t => (Chebyshev.psi t - t) * activationDensity t - m * activationDensity t) :=
  funext fun t => sub_mul (Chebyshev.psi t - t) m (activationDensity t)

/-- The primitive `-1 / u` gives the same scaled mass for both halves of the chord. -/
theorem chord_weight_balance {a b x p q : ℝ} (ha : 1 < a) (hx : x ∈ Icc a b)
    (hs : p + q = 1) (hc : p * u a + q * u b = u x) :
    let C := p * (u x - u a) / u x
    p * u a * (∫ t in a..x, activationDensity t) = C ∧
      q * u b * (∫ t in x..b, activationDensity t) = C ∧
        q * (u b - u x) / u x = C := by
  dsimp only
  have hx1 := ha.trans_le hx.1
  have hb1 := hx1.trans_le hx.2
  have hax : (∫ t in a..x, activationDensity t) = 1 / u a - 1 / u x :=
    density_integral ha hx.1
  have hxb : (∫ t in x..b, activationDensity t) = 1 / u x - 1 / u b :=
    density_integral hx1 hx.2
  have hbalanced : p * (u x - u a) = q * (u b - u x) := by
    linear_combination u x * hs - hc
  have hC : p * (u x - u a) / u x = q * (u b - u x) / u x :=
    congrArg (fun z : ℝ => z / u x) hbalanced
  refine ⟨?_, ?_, hC.symm⟩
  · rw [hax]
    field_simp [(u_pos ha).ne', (u_pos hx1).ne']
  · rw [hxb, hC]
    field_simp [(u_pos hx1).ne', (u_pos hb1).ne']

/-- The actual Robin chord error is a signed difference of local Chebyshev integrals.
Any constant can be subtracted from the Chebyshev error in both integrals. -/
theorem ramp_chord_centered {a b x p q : ℝ} (ha : 2 ≤ a) (hx : x ∈ Icc a b)
    (hs : p + q = 1) (hc : p * u a + q * u b = u x) (m : ℝ) :
    R x - p * R a - q * R b =
      p * u a * (∫ t in a..x, (Chebyshev.psi t - t - m) * activationDensity t) -
        q * u b * (∫ t in x..b, (Chebyshev.psi t - t - m) * activationDensity t) := by
  have hx2 := ha.trans hx.1
  have hb2 := hx2.trans hx.2
  obtain ⟨hleft, hright, _⟩ := chord_weight_balance (by linarith : 1 < a) hx hs hc
  have hcenter {s t : ℝ} (hs2 : 2 ≤ s) (hst : s ≤ t) :
      (∫ v in s..t, (Chebyshev.psi v - v - m) * activationDensity v) =
        weightedTail psiErrorKernel s - weightedTail psiErrorKernel t -
          m * (∫ v in s..t, activationDensity v) := by
    have hw := density_integrable (by linarith : 1 < s) hst
    rw [centered_kernel_eq m,
      intervalIntegral.integral_sub (intervalIntegrable_weighted_error hs2 hst) (hw.const_mul m),
      intervalIntegral.integral_const_mul, ← weightedTail_sub_eq_interval hs2 hst]
  rw [ramp_eq_neg_weightedTail hx2, ramp_eq_neg_weightedTail ha, ramp_eq_neg_weightedTail hb2,
    hcenter ha hx.1, hcenter hx2 hx.2]
  linear_combination weightedTail psiErrorKernel x * hc + m * hleft - m * hright

/-- A range of width `U - L` for the Chebyshev error on the cell controls the
absolute Robin chord error by that width times the common scaled mass. -/
theorem abs_ramp_chord_error_le {a b x p q L U : ℝ} (ha : 2 ≤ a) (hx : x ∈ Icc a b)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hs : p + q = 1) (hc : p * u a + q * u b = u x)
    (hrange : ∀ t ∈ Icc a b, L ≤ Chebyshev.psi t - t ∧ Chebyshev.psi t - t ≤ U) :
    |R x - p * R a - q * R b| ≤ (U - L) * (p * (u x - u a) / u x) := by
  have ha1 : 1 < a := by linarith
  have hx1 := ha1.trans_le hx.1
  obtain ⟨hpa, hqb, _⟩ := chord_weight_balance ha1 hx hs hc
  have hbounds {s t k : ℝ} (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) (hk : 0 ≤ k) :
      0 ≤ k * (∫ v in s..t, (Chebyshev.psi v - v - L) * activationDensity v) ∧
        k * (∫ v in s..t, (Chebyshev.psi v - v - L) * activationDensity v) ≤
          (U - L) * (k * (∫ v in s..t, activationDensity v)) := by
    have hs1 := ha1.trans_le has
    have hw := density_integrable hs1 hst
    have hw0 (v : ℝ) (hv : v ∈ Icc s t) : 0 ≤ activationDensity v := by
      unfold activationDensity
      positivity [log_pos (hs1.trans_le hv.1)]
    have hvRange (v : ℝ) (hv : v ∈ Icc s t) :
        L ≤ Chebyshev.psi v - v ∧ Chebyshev.psi v - v ≤ U :=
      hrange v ⟨has.trans hv.1, hv.2.trans htb⟩
    have hint : IntervalIntegrable
        (fun v => (Chebyshev.psi v - v - L) * activationDensity v) volume s t := by
      rw [centered_kernel_eq L]
      exact (intervalIntegrable_weighted_error (ha.trans has) hst).sub (hw.const_mul L)
    have hlo : 0 ≤ ∫ v in s..t, (Chebyshev.psi v - v - L) * activationDensity v :=
      intervalIntegral.integral_nonneg hst (fun v hv =>
        mul_nonneg (sub_nonneg.mpr (hvRange v hv).1) (hw0 v hv))
    have hhi : (∫ v in s..t, (Chebyshev.psi v - v - L) * activationDensity v) ≤
        (U - L) * (∫ v in s..t, activationDensity v) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_mono_on hst hint (hw.const_mul (U - L)) (fun v hv =>
        mul_le_mul_of_nonneg_right (sub_le_sub_right (hvRange v hv).2 L) (hw0 v hv))
    exact ⟨mul_nonneg hk hlo, (mul_le_mul_of_nonneg_left hhi hk).trans_eq (by ring)⟩
  have hleft := hbounds le_rfl hx.1 hx.2 (mul_nonneg hp (u_pos ha1).le)
  have hright := hbounds hx.1 hx.2 le_rfl (mul_nonneg hq (u_pos (hx1.trans_le hx.2)).le)
  rw [hpa] at hleft
  rw [hqb] at hright
  rw [ramp_chord_centered ha hx hs hc L, abs_le]
  exact ⟨by linarith only [hleft.1, hright.2], by linarith only [hleft.2, hright.1]⟩

/-- The common scaled mass has an explicit coordinate formula and a bound
uniform in the interior point of the cell. -/
theorem chord_weight_coefficient {a b x p q : ℝ} (ha : 1 < a) (hab : a < b)
    (hx : x ∈ Icc a b) (hs : p + q = 1) (hc : p * u a + q * u b = u x) :
    let C := p * (u x - u a) / u x
    C = (u x - u a) * (u b - u x) / (u x * (u b - u a)) ∧
      C ≤ (u b - u a) / (4 * u a) := by
  dsimp only
  have hx1 := ha.trans_le hx.1
  have hb1 := hx1.trans_le hx.2
  have hgap := sub_pos.mpr (u_strictMonoOn ha hb1 hab)
  have hux := u_strictMonoOn.monotoneOn ha hx1 hx.1
  have hp : p = (u b - u x) / (u b - u a) := by
    apply (eq_div_iff hgap.ne').2
    linear_combination u b * hs - hc
  have hC : p * (u x - u a) / u x = (u x - u a) * (u b - u x) / (u x * (u b - u a)) := by
    rw [hp]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hprod : (u x - u a) * (u b - u x) ≤ (u b - u a) ^ 2 / 4 := by
    nlinarith only [sq_nonneg ((u x - u a) - (u b - u x))]
  refine ⟨hC, ?_⟩
  rw [hC]
  have hden : 0 < 4 * u a := mul_pos (by norm_num) (u_pos ha)
  apply (div_le_div_iff₀ (mul_pos (u_pos hx1) hgap) hden).2
  calc
    _ ≤ ((u b - u a) ^ 2 / 4) * (4 * u a) :=
      mul_le_mul_of_nonneg_right hprod hden.le
    _ = (u b - u a) ^ 2 * u a := by ring
    _ ≤ (u b - u a) ^ 2 * u x := mul_le_mul_of_nonneg_left hux (sq_nonneg _)
    _ = _ := by ring

private lemma coordinate_gap_le {a b : ℝ} (ha : exp 1 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 2 * a) : u b - u a ≤ 3 * (b - a) * log a := by
  have ha0 := (exp_pos 1).trans_le ha
  have hb0 := ha0.trans_le hab
  have hlog := (le_log_iff_exp_le ha0).2 ha
  have hd := log_le_sub_one_of_pos (div_pos hb0 ha0)
  rw [log_div hb0.ne' ha0.ne', show b / a - 1 = (b - a) / a by field_simp] at hd
  have hba : b / a ≤ 2 := (div_le_iff₀ ha0).2 hb
  calc
    u b - u a = (b - a) * log a + b * (log b - log a) := by unfold u; ring
    _ ≤ (b - a) * log a + b * ((b - a) / a) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hd hb0.le)
    _ = (b - a) * (log a + b / a) := by ring
    _ ≤ (b - a) * (3 * log a) :=
      mul_le_mul_of_nonneg_left (by linarith only [hba, hlog]) (sub_nonneg.mpr hab)
    _ = _ := by ring

/-- The weighted positive part of the coordinate chord approximates the actual
Robin mass with a two-sided error controlled by the Chebyshev range on the cell. -/
theorem abs_mass_sub_chord_le {a b L U : ℝ} (ha : exp 1 ≤ a) (hab : a < b)
    (hb : b ≤ 2 * a)
    (hrange : ∀ t ∈ Icc a b, L ≤ Chebyshev.psi t - t ∧ Chebyshev.psi t - t ≤ U) :
    let q (t : ℝ) := (u t - u a) / (u b - u a)
    let H (t : ℝ) := (1 - q t) * R a + q t * R b
    |weightedNegativeMass psiErrorKernel a b -
        (∫ t in a..b, (log t / (1 + log t)) / (t * sqrt t) * max (H t) 0)| ≤
      3 * (U - L) * (b - a) ^ 2 / (4 * a ^ 2 * sqrt a) := by
  dsimp only
  have ha2 := Real.exp_one_gt_two.le.trans ha
  have ha1 : 1 < a := by linarith
  have ha0 : 0 < a := by linarith
  have hb1 := ha1.trans hab
  have hgap := sub_pos.mpr (u_strictMonoOn ha1 hb1 hab)
  have hwidth : 0 ≤ U - L :=
    sub_nonneg.mpr ((hrange a ⟨le_rfl, hab.le⟩).1.trans (hrange a ⟨le_rfl, hab.le⟩).2)
  let q (t : ℝ) := (u t - u a) / (u b - u a)
  let H (t : ℝ) := (1 - q t) * R a + q t * R b
  let w (t : ℝ) := (log t / (1 + log t)) / (t * sqrt t)
  change |weightedNegativeMass psiErrorKernel a b -
    (∫ t in a..b, w t * max (H t) 0)| ≤ _
  have hw (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ w t ∧ w t ≤ 1 / (a * sqrt a) := by
    have ht0 := ha0.trans_le ht.1
    have hl := log_pos (ha1.trans_le ht.1)
    have hratio : log t / (1 + log t) ≤ 1 :=
      (div_le_one (by positivity)).2 (by linarith)
    have hden := mul_le_mul ht.1 (sqrt_le_sqrt ht.1) (sqrt_nonneg a) ht0.le
    exact ⟨by dsimp [w]; positivity,
      (div_le_div_of_nonneg_right hratio (by positivity)).trans
        (one_div_le_one_div_of_le (by positivity) hden)⟩
  have hcoef : (u b - u a) / (4 * u a) ≤ 3 * (b - a) / (4 * a) := calc
    _ ≤ (3 * (b - a) * log a) / (4 * u a) :=
      div_le_div_of_nonneg_right (coordinate_gap_le ha hab.le hb) (by positivity [u_pos ha1])
    _ = _ := by unfold u; field_simp [ha0.ne', (log_pos ha1).ne']
  have hchord (t : ℝ) (ht : t ∈ Icc a b) :
      |R t - H t| ≤ (U - L) * (3 * (b - a) / (4 * a)) := by
    have ht1 := ha1.trans_le ht.1
    have hq : 0 ≤ q t := div_nonneg
      (sub_nonneg.mpr (u_strictMonoOn.monotoneOn ha1 ht1 ht.1)) hgap.le
    have hp : 0 ≤ 1 - q t := sub_nonneg.mpr <| (div_le_one hgap).2 <|
      sub_le_sub_right (u_strictMonoOn.monotoneOn ht1 hb1 ht.2) _
    have hs : 1 - q t + q t = 1 := sub_add_cancel _ _
    have hc : (1 - q t) * u a + q t * u b = u t := by
      have hmul : q t * (u b - u a) = u t - u a := div_mul_cancel₀ _ hgap.ne'
      linarith only [hmul]
    have hlocal := abs_ramp_chord_error_le ha2 ht hp hq hs hc hrange
    have hC := (chord_weight_coefficient ha1 hab ht hs hc).2
    rw [show R t - H t = R t - (1 - q t) * R a - q t * R b by dsimp [H]; ring]
    exact hlocal.trans (mul_le_mul_of_nonneg_left (hC.trans hcoef) hwidth)
  have hdensity (t : ℝ) (ht : t ∈ Icc a b) :
      (WeightedTailInverse.a t / sqrt t) * max (-weightedTail psiErrorKernel t) 0 =
        w t * max (R t) 0 := by
    have ht0 := ha0.trans_le ht.1
    have ht1 := ha1.trans_le ht.1
    have hl := log_pos ht1
    have hmax : max (R t) 0 = u t * max (-weightedTail psiErrorKernel t) 0 := by
      rw [mul_max_of_nonneg _ _ (u_pos ht1).le, mul_zero,
        ramp_eq_neg_weightedTail (ha2.trans ht.1), mul_neg, neg_mul]
    rw [hmax]
    dsimp [w, WeightedTailInverse.a, u]
    field_simp [ht0.ne', (sqrt_pos.2 ht0).ne', (by positivity : 0 < 1 + log t).ne'] <;> ring
  have hlog : ContinuousOn log (Icc a b) := fun t ht =>
    (continuousAt_log (ha0.trans_le ht.1).ne').continuousWithinAt
  have hu : ContinuousOn u (Icc a b) := continuousOn_id.mul hlog
  have htail : ContinuousOn (weightedTail psiErrorKernel) (Icc a b) :=
    (complete_mertens_ledger ha2).2.1.continuousOn_Ici_primitive_Ioi.mono (fun _ ht => ht.1)
  have hR : ContinuousOn R (Icc a b) :=
    (hu.neg.mul htail).congr (fun _ ht => ramp_eq_neg_weightedTail (ha2.trans ht.1))
  have hq : ContinuousOn q (Icc a b) := (hu.sub continuousOn_const).div_const _
  have hH : ContinuousOn H (Icc a b) :=
    ((continuousOn_const.sub hq).mul_const _).add (hq.mul_const _)
  have hwc : ContinuousOn w (Icc a b) :=
    (hlog.div (hlog.const_add 1) (fun t ht =>
      (by positivity [log_pos (ha1.trans_le ht.1)] : 0 < 1 + log t).ne')).div
      (continuousOn_id.mul continuous_sqrt.continuousOn) (fun t ht =>
        (mul_pos (ha0.trans_le ht.1) (sqrt_pos.2 (ha0.trans_le ht.1))).ne')
  have hactual : weightedNegativeMass psiErrorKernel a b =
      ∫ t in a..b, w t * max (R t) 0 := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hab.le]
    exact hdensity
  have hdiff :
      (∫ t in a..b, w t * max (R t) 0 - w t * max (H t) 0) =
        (∫ t in a..b, w t * max (R t) 0) - (∫ t in a..b, w t * max (H t) 0) :=
    intervalIntegral.integral_sub
      ((hwc.mul (hR.sup continuousOn_const)).intervalIntegrable_of_Icc hab.le)
      ((hwc.mul (hH.sup continuousOn_const)).intervalIntegrable_of_Icc hab.le)
  rw [hactual, ← hdiff]
  let M := (1 / (a * sqrt a)) * ((U - L) * (3 * (b - a) / (4 * a)))
  have hpoint (t : ℝ) (ht : t ∈ uIoc a b) :
      ‖w t * max (R t) 0 - w t * max (H t) 0‖ ≤ M := by
    have ht' : t ∈ Icc a b := Ioc_subset_Icc_self (uIoc_of_le hab.le ▸ ht)
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (hw t ht').1]
    exact mul_le_mul (hw t ht').2
      ((abs_max_sub_max_le_abs (R t) (H t) 0).trans (hchord t ht'))
      (abs_nonneg _) (by positivity)
  calc
    _ ≤ M * |b - a| := by
      rw [← Real.norm_eq_abs]
      exact intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = _ := by
      rw [abs_of_pos (sub_pos.mpr hab)]
      dsimp [M]
      field_simp [ha0.ne', (sqrt_pos.2 ha0).ne'] <;> ring

end
end D5.S3.Weil.Mertens.RobinCenteredChord
