/- GID: D5/S3/Analytic/Asymptotics/PhaseLawDyadicCoercivity
   generality: G
   mirror-B: D5/B/S3/Analytic/Asymptotics/PhaseLawDyadicCoercivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive dyadic defects force fourth-moment and high-tail coercivity without counting. -/

import D5.S3.Analytic.Asymptotics.LogarithmicPhaseStiffness

set_option autoImplicit false
open Filter MeasureTheory Set ENNReal
open scoped Topology

namespace D5.S3.Analytic.Asymptotics.PhaseLawDyadicCoercivity

open LogarithmicPhaseStiffness (phaseCost)
noncomputable section

def lowCutoff {ι : Type*} (frequency : ι → ℝ) (strict : Bool) (cutoff : ℝ) (index : ι) :
    Prop := if strict then frequency index < cutoff else frequency index ≤ cutoff

def maskedMoment {ι : Type*} (frequency weight : ι → ℝ) (strict : Bool)
    (power : ℕ) (cutoff : ℝ) : ℝ := by
  classical
  exact ∑' index, if lowCutoff frequency strict cutoff index then
    weight index * frequency index ^ power else 0

def maskedTail {ι : Type*} (frequency weight : ι → ℝ) (strict : Bool) (cutoff : ℝ) :
    ℝ := by
  classical
  exact ∑' index, if (if strict then cutoff < frequency index else cutoff ≤ frequency index)
    then weight index else 0

set_option maxHeartbeats 1600000 in
theorem phase_law_dyadic_coercivity {ι : Type*} (frequency weight : ι → ℝ)
    (hweight : ∀ index, 0 ≤ weight index) (hfrequency : ∀ index, 0 < frequency index)
    (hsum : Summable weight) {alpha error firstTime : ℝ} (halpha : 0 < alpha)
    (herror : 0 ≤ error) (hfirst : 0 < firstTime) (hsmall : firstTime ≤ Real.exp (-1))
    (hlaw : ∀ time, 0 < time → time ≤ firstTime →
      |phaseCost frequency weight time - alpha * time ^ 2 * (Real.log (1 / time)) ^ 2| ≤
        error * time ^ 2 * (Real.log (1 / time) + 1)) :
    ∀ cutoff, 16 / firstTime ≤ cutoff → ∀ strict : Bool,
      maskedMoment frequency weight strict 4 cutoff ≤
        64 * (2 * alpha + 3 * error) * cutoff ^ 2 * (Real.log cutoff + 1) ∧
      maskedTail frequency weight strict cutoff ≤
        32 * (2 * alpha + 3 * error) * cutoff⁻¹ ^ 2 * (Real.log cutoff + 1) := by
  classical
  have hphase_nonneg (time : ℝ) (index : ι) :
      0 ≤ 2 * weight index * (1 - Real.cos (frequency index * time)) :=
    mul_nonneg (mul_nonneg (by norm_num) (hweight index))
      (sub_nonneg.mpr (Real.cos_le_one _))
  have hphase_bound (time : ℝ) (index : ι) :
      2 * weight index * (1 - Real.cos (frequency index * time)) ≤ 4 * weight index := by
    have hcos := Real.neg_one_le_cos (frequency index * time)
    nlinarith [hweight index]
  have hphase_sum (time : ℝ) :
      Summable (fun index => 2 * weight index * (1 - Real.cos (frequency index * time))) :=
    Summable.of_nonneg_of_le (hphase_nonneg time) (hphase_bound time) (hsum.mul_left 4)
  have hmoment_sum (strict : Bool) (power : ℕ) {cutoff : ℝ} (hcutoff : 0 ≤ cutoff) :
      Summable (fun index => if lowCutoff frequency strict cutoff index then
        weight index * frequency index ^ power else 0) := by
    apply Summable.of_nonneg_of_le _ _ (hsum.mul_left (cutoff ^ power))
    · intro index
      have hai := hweight index
      have hgi := (hfrequency index).le
      split_ifs <;> positivity
    · intro index
      split_ifs with hlow
      · have hle : frequency index ≤ cutoff := by
          cases strict <;> simp only [lowCutoff, Bool.false_eq_true, if_false, if_true] at hlow
          · exact hlow
          · exact hlow.le
        calc
          _ ≤ weight index * cutoff ^ power :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hfrequency index).le hle _) (hweight index)
          _ = _ := by ring
      · exact mul_nonneg (pow_nonneg hcutoff _) (hweight index)
  have htail_sum (strict : Bool) (cutoff : ℝ) :
      Summable (fun index => if (if strict then cutoff < frequency index
        else cutoff ≤ frequency index) then weight index else 0) := by
    apply Summable.of_nonneg_of_le _ _ hsum
    · intro index
      split_ifs <;> first | exact hweight index | exact le_rfl
    · intro index
      split_ifs <;> first | exact le_rfl | exact hweight index
  let defect := fun time => 4 * phaseCost frequency weight (time / 2) -
    phaseCost frequency weight time
  have hdefect_sum (time : ℝ) :
      Summable (fun index => 4 * weight index *
        (1 - Real.cos (frequency index * time / 2)) ^ 2) := by
    apply Summable.of_nonneg_of_le _ _ (hsum.mul_left 16)
    · intro index
      exact mul_nonneg (mul_nonneg (by norm_num) (hweight index)) (sq_nonneg _)
    · intro index
      have hc1 := Real.cos_le_one (frequency index * time / 2)
      have hc2 := Real.neg_one_le_cos (frequency index * time / 2)
      have hsq : (1 - Real.cos (frequency index * time / 2)) ^ 2 ≤ 4 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hsq (hweight index)]
  have hdefect_identity (time : ℝ) : defect time =
      ∑' index, 4 * weight index * (1 - Real.cos (frequency index * time / 2)) ^ 2 := by
    dsimp only [defect, phaseCost]
    rw [← tsum_mul_left, ← ( (hphase_sum (time / 2)).mul_left 4).tsum_sub (hphase_sum time)]
    apply tsum_congr
    intro index
    have hdouble := Real.cos_two_mul (frequency index * time / 2)
    rw [show 2 * (frequency index * time / 2) = frequency index * time by ring] at hdouble
    rw [show frequency index * (time / 2) = frequency index * time / 2 by ring, hdouble]
    ring
  have hdefect_nonneg (time : ℝ) : 0 ≤ defect time := by
    rw [hdefect_identity]
    exact tsum_nonneg (fun index =>
      mul_nonneg (mul_nonneg (by norm_num) (hweight index)) (sq_nonneg _))
  have hlogtime {time : ℝ} (htime : 0 < time) (htime_small : time ≤ firstTime) :
      1 ≤ Real.log (1 / time) := by
    have hlog := Real.log_le_log htime (htime_small.trans hsmall)
    rw [Real.log_exp] at hlog
    simpa only [one_div, Real.log_inv] using (show 1 ≤ -Real.log time by linarith)
  have hdefect_bound {time : ℝ} (htime : 0 < time) (htime_small : time ≤ firstTime) :
      defect time ≤ (2 * alpha + 3 * error) * time ^ 2 * (Real.log (1 / time) + 1) := by
    have hhalf := hlaw (time / 2) (by positivity) (by linarith)
    have hwhole := hlaw time htime htime_small
    have hloghalf : Real.log (1 / (time / 2)) = Real.log (1 / time) + Real.log 2 := by
      rw [show 1 / (time / 2) = (1 / time) * 2 by field_simp]
      exact Real.log_mul (by positivity) (by norm_num)
    rw [hloghalf] at hhalf
    have hlog := hlogtime htime htime_small
    have hr0 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    have hr1 : Real.log 2 ≤ 1 := by
      have hlogtwo := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hra : alpha * (Real.log 2) ^ 2 ≤ alpha := by
      have hrsq : (Real.log 2) ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hrsq halpha.le]
    have hrb : error * Real.log 2 ≤ error :=
      (mul_le_mul_of_nonneg_left hr1 herror).trans_eq (mul_one error)
    have hral : alpha * Real.log 2 * Real.log (1 / time) ≤ alpha * Real.log (1 / time) := by
      nlinarith [mul_le_mul_of_nonneg_left hr1 (mul_nonneg halpha.le (by linarith :
        0 ≤ Real.log (1 / time)))]
    have heb : error ≤ error * Real.log (1 / time) := by nlinarith
    have hcoefficient : alpha * (2 * Real.log 2 * Real.log (1 / time) + (Real.log 2) ^ 2) +
        error * (2 * Real.log (1 / time) + Real.log 2 + 2) ≤
          (2 * alpha + 3 * error) * (Real.log (1 / time) + 1) := by nlinarith
    have hscaled := mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg time)
    have hhalf_upper := (abs_le.mp hhalf).2
    have hwhole_lower := (abs_le.mp hwhole).1
    dsimp only [defect]
    nlinarith
  have hscalar_coercive {value : ℝ} (hvalue : |value| ≤ 1) :
      value ^ 4 / 64 ≤ 4 * (1 - Real.cos (value / 2)) ^ 2 := by
    have hhalf : |value / 2| ≤ 1 := by rw [abs_div]; norm_num; linarith
    have hcos := (abs_le.mp (Real.cos_bound hhalf)).2
    rw [(by decide : Even (4 : ℕ)).pow_abs] at hcos
    have hsquare : value ^ 2 ≤ 1 := by nlinarith [sq_abs value, (abs_le.mp hvalue).1, (abs_le.mp hvalue).2]
    have hquartic : value ^ 4 ≤ value ^ 2 := by nlinarith [sq_nonneg (value ^ 2), sq_nonneg value]
    have hlower : value ^ 2 / 16 ≤ 1 - Real.cos (value / 2) := by nlinarith
    nlinarith [sq_nonneg (1 - Real.cos (value / 2) - value ^ 2 / 16), sq_nonneg value]
  have hfirst_one : firstTime ≤ 1 := hsmall.trans (Real.exp_le_one_iff.mpr (by norm_num))
  have hlarge_positive {cutoff : ℝ} (hcutoff : 16 / firstTime ≤ cutoff) : 1 ≤ cutoff := by
    have hmul := (div_le_iff₀ hfirst).mp hcutoff
    nlinarith
  have hquartic_large {cutoff : ℝ} (hcutoff : 16 / firstTime ≤ cutoff) (strict : Bool) :
      maskedMoment frequency weight strict 4 cutoff ≤
        64 * (2 * alpha + 3 * error) * cutoff ^ 2 * (Real.log cutoff + 1) := by
    have hcutoff_one := hlarge_positive hcutoff
    have hcutoff_pos : 0 < cutoff := by linarith
    have htime : 0 < 1 / cutoff := by positivity
    have htime_small : 1 / cutoff ≤ firstTime := by
      apply (div_le_iff₀ hcutoff_pos).mpr
      have hmul := (div_le_iff₀ hfirst).mp hcutoff
      nlinarith
    have hmajorant (index : ι) :
        (if lowCutoff frequency strict cutoff index then weight index * frequency index ^ 4
          else 0) * (1 / cutoff) ^ 4 / 64 ≤
        4 * weight index * (1 - Real.cos (frequency index * (1 / cutoff) / 2)) ^ 2 := by
      split_ifs with hlow
      · have hle : frequency index ≤ cutoff := by
          cases strict <;> simp only [lowCutoff, Bool.false_eq_true, if_false, if_true] at hlow
          · exact hlow
          · exact hlow.le
        have harg : |frequency index * (1 / cutoff)| ≤ 1 := by
          rw [abs_of_nonneg (mul_nonneg (hfrequency index).le (one_div_pos.mpr hcutoff_pos).le)]
          calc
            _ = frequency index / cutoff := by ring
            _ ≤ 1 := (div_le_one hcutoff_pos).mpr hle
        have hcoercive := mul_le_mul_of_nonneg_left (hscalar_coercive harg) (hweight index)
        calc
          _ = weight index * ((frequency index * (1 / cutoff)) ^ 4 / 64) := by ring
          _ ≤ weight index * (4 * (1 - Real.cos (frequency index * (1 / cutoff) / 2)) ^ 2) :=
            hcoercive
          _ = _ := by ring
      · simp only [zero_mul, zero_div]
        exact mul_nonneg (mul_nonneg (by norm_num) (hweight index)) (sq_nonneg _)
    have hsum_bound :=
      (((hmoment_sum strict 4 hcutoff_pos.le).mul_right ((1 / cutoff) ^ 4)).div_const 64).tsum_le_tsum
        hmajorant (hdefect_sum (1 / cutoff))
    rw [tsum_div_const, tsum_mul_right, ← hdefect_identity] at hsum_bound
    change maskedMoment frequency weight strict 4 cutoff * (1 / cutoff) ^ 4 / 64 ≤
      defect (1 / cutoff) at hsum_bound
    have hupper := hdefect_bound htime htime_small
    simp only [one_div] at hsum_bound
    simp only [one_div, Real.log_inv, neg_neg] at hupper
    have hbound := hsum_bound.trans hupper
    have hscaled := mul_le_mul_of_nonneg_right hbound (by positivity : 0 ≤ 64 * cutoff ^ 4)
    field_simp at hscaled
    nlinarith
  have hkernel_average {rate scale : ℝ} (hrate : 0 < rate) (hscale : 0 < scale)
      (hlarge : 8 ≤ rate * scale) :
      15 / 16 * scale ≤ ∫ time in 0..scale, (1 - Real.cos (rate * time / 2)) ^ 2 := by
    have hderivative (time : ℝ) : HasDerivAt
        (fun value => 3 / 2 * value - 4 / rate * Real.sin (rate * value / 2) +
          1 / (2 * rate) * Real.sin (rate * value))
        ((1 - Real.cos (rate * time / 2)) ^ 2) time := by
      have hfirst_deriv := (((hasDerivAt_id time).const_mul rate).div_const 2).sin
      have hsecond_deriv := ((hasDerivAt_id time).const_mul rate).sin
      have hdouble := Real.cos_two_mul (rate * time / 2)
      rw [show 2 * (rate * time / 2) = rate * time by ring] at hdouble
      convert! (((hasDerivAt_id time).const_mul (3 / 2)).sub
        (hfirst_deriv.const_mul (4 / rate))).add
          (hsecond_deriv.const_mul (1 / (2 * rate))) using 1 <;>
        simp only [id_eq, Pi.sub_apply, Pi.add_apply] <;>
        (try field_simp [hrate.ne']) <;> ring_nf at hdouble ⊢ <;> nlinarith only [hdouble]
    have hint : IntervalIntegrable
        (fun time : ℝ => (1 - Real.cos (rate * time / 2)) ^ 2) volume 0 scale :=
      (by fun_prop : Continuous _).intervalIntegrable _ _
    have hprimitive := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun time _ => hderivative time) hint
    simp only [mul_zero, zero_div, Real.sin_zero, sub_zero, add_zero] at hprimitive
    rw [hprimitive]
    have hsine1 := Real.sin_le_one (rate * scale / 2)
    have hsine2 := Real.neg_one_le_sin (rate * scale)
    have hupper : 4 / rate ≤ scale / 2 :=
      (div_le_iff₀ hrate).mpr (by linarith)
    have hlower : 1 / (2 * rate) ≤ scale / 16 :=
      (div_le_iff₀ (by positivity : 0 < 2 * rate)).mpr (by nlinarith)
    have hsin1 := mul_le_mul_of_nonneg_left hsine1 (by positivity : 0 ≤ 4 / rate)
    have hsin2 := mul_le_mul_of_nonneg_left hsine2 (by positivity : 0 ≤ 1 / (2 * rate))
    nlinarith
  have hdefect_uniform {scale : ℝ} (hscale : 0 < scale) (hscale_small : scale ≤ firstTime)
      {time : ℝ} (htime : time ∈ Icc 0 scale) :
      defect time ≤ 5 * (2 * alpha + 3 * error) / 4 * scale ^ 2 *
        (Real.log (1 / scale) + 1) := by
    by_cases hzero : time = 0
    · subst time
      have hlog := hlogtime hscale hscale_small
      simp only [defect, phaseCost, zero_div, mul_zero, Real.cos_zero, sub_self,
        tsum_zero, sub_zero]
      positivity
    · have htime_pos : 0 < time := lt_of_le_of_ne htime.1 (Ne.symm hzero)
      have hlog := hlogtime hscale hscale_small
      have hratio := Real.log_le_sub_one_of_pos (div_pos hscale htime_pos)
      have hlogsplit : Real.log (1 / time) = Real.log (1 / scale) + Real.log (scale / time) := by
        rw [Real.log_div (by norm_num) htime_pos.ne',
          Real.log_div (by norm_num) hscale.ne', Real.log_div hscale.ne' htime_pos.ne']
        simp only [Real.log_one]
        ring
      have hratio_scaled := mul_le_mul_of_nonneg_left hratio (sq_nonneg time)
      have hcancel : time ^ 2 * (scale / time - 1) = scale * time - time ^ 2 := by
        field_simp [htime_pos.ne'] <;> ring
      rw [hcancel] at hratio_scaled
      have hratio_quad : time ^ 2 * Real.log (scale / time) ≤ scale ^ 2 / 4 := by
        nlinarith [sq_nonneg (time - scale / 2)]
      have htime_sq : time ^ 2 ≤ scale ^ 2 := by nlinarith [htime.1, htime.2]
      have hbase := mul_le_mul_of_nonneg_right htime_sq (by linarith :
        0 ≤ Real.log (1 / scale) + 1)
      have hscale_base := mul_le_mul_of_nonneg_left (by linarith :
        1 ≤ Real.log (1 / scale) + 1) (sq_nonneg scale)
      have hbracket : time ^ 2 * (Real.log (1 / time) + 1) ≤
          5 / 4 * scale ^ 2 * (Real.log (1 / scale) + 1) := by
        rw [hlogsplit]
        nlinarith
      have hscaled := mul_le_mul_of_nonneg_left hbracket
        (by positivity : 0 ≤ 2 * alpha + 3 * error)
      exact (hdefect_bound htime_pos (htime.2.trans hscale_small)).trans (by nlinarith)
  have htail_large {cutoff : ℝ} (hcutoff : 16 / firstTime ≤ cutoff) (strict : Bool) :
      maskedTail frequency weight strict cutoff ≤
        32 * (2 * alpha + 3 * error) * cutoff⁻¹ ^ 2 * (Real.log cutoff + 1) := by
    have hcutoff_one := hlarge_positive hcutoff
    have hcutoff_pos : 0 < cutoff := by linarith
    let scale := 8 / cutoff
    have hscale : 0 < scale := by dsimp only [scale]; positivity
    have hscale_small : scale ≤ firstTime := by
      apply (div_le_iff₀ hcutoff_pos).mpr
      have hmul := (div_le_iff₀ hfirst).mp hcutoff
      nlinarith
    let high := fun index => if (if strict then cutoff < frequency index
      else cutoff ≤ frequency index) then weight index else 0
    apply (htail_sum strict cutoff).tsum_le_of_sum_le
    intro finite
    let selected := finite.filter (fun index => if strict then cutoff < frequency index
      else cutoff ≤ frequency index)
    have hhighsum : ∑ index ∈ finite, high index = ∑ index ∈ selected, weight index := by
      simp only [selected, high, Finset.sum_filter]
    change ∑ index ∈ finite, high index ≤ _
    rw [hhighsum]
    have hselected (index : ι) (hindex : index ∈ selected) : cutoff ≤ frequency index := by
      have derivedEstimate := (Finset.mem_filter.mp hindex).2
      cases strict <;> simp only [Bool.false_eq_true, if_false, if_true] at derivedEstimate
      · exact derivedEstimate
      · exact derivedEstimate.le
    have htermint (index : ι) : IntervalIntegrable
        (fun time => 4 * weight index * (1 - Real.cos (frequency index * time / 2)) ^ 2)
        volume 0 scale := (by fun_prop : Continuous _).intervalIntegrable _ _
    have hsumint : IntervalIntegrable
        (fun time => ∑ index ∈ selected,
          4 * weight index * (1 - Real.cos (frequency index * time / 2)) ^ 2)
        volume 0 scale := (by fun_prop : Continuous _).intervalIntegrable _ _
    have hupper_integral := intervalIntegral.integral_mono_on hscale.le hsumint
      (intervalIntegrable_const (c := 5 * (2 * alpha + 3 * error) / 4 * scale ^ 2 *
        (Real.log (1 / scale) + 1))) (fun time htime =>
          ((hdefect_sum time).sum_le_tsum selected
            (fun index _ => mul_nonneg (mul_nonneg (by norm_num) (hweight index)) (sq_nonneg _)))
          |>.trans (by rw [← hdefect_identity]; exact hdefect_uniform hscale hscale_small htime))
    rw [intervalIntegral.integral_finsetSum (fun index _ => htermint index),
      intervalIntegral.integral_const] at hupper_integral
    simp only [sub_zero, smul_eq_mul] at hupper_integral
    have hlower_integral : 15 / 4 * scale * (∑ index ∈ selected, weight index) ≤
        ∑ index ∈ selected, ∫ time in 0..scale,
          4 * weight index * (1 - Real.cos (frequency index * time / 2)) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro index hindex
      rw [intervalIntegral.integral_const_mul]
      have hratescale : 8 ≤ frequency index * scale := by
        dsimp only [scale]
        rw [← mul_div_assoc]
        apply (le_div_iff₀ hcutoff_pos).mpr
        nlinarith [hselected index hindex]
      have hkernel := mul_le_mul_of_nonneg_left
        (hkernel_average (hfrequency index) hscale hratescale)
        (show (0 : ℝ) ≤ 4 * weight index from mul_nonneg (by norm_num) (hweight index))
      nlinarith
    have hcombined := hlower_integral.trans hupper_integral
    have hlogcompare : Real.log (1 / scale) ≤ Real.log cutoff := by
      apply Real.log_le_log (by positivity)
      dsimp only [scale]
      field_simp
      linarith
    have hlog := Real.log_nonneg hcutoff_one
    have htotal : ∑ index ∈ selected, weight index ≤
        (2 * alpha + 3 * error) / 3 * scale ^ 2 * (Real.log (1 / scale) + 1) := by
      nlinarith
    have hlogscaled : (2 * alpha + 3 * error) / 3 * scale ^ 2 * (Real.log (1 / scale) + 1) ≤
        (2 * alpha + 3 * error) / 3 * scale ^ 2 * (Real.log cutoff + 1) :=
      mul_le_mul_of_nonneg_left (by linarith :
        Real.log (1 / scale) + 1 ≤ Real.log cutoff + 1)
        (by positivity : 0 ≤ (2 * alpha + 3 * error) / 3 * scale ^ 2)
    have hcoarse : (2 * alpha + 3 * error) / 3 * scale ^ 2 * (Real.log cutoff + 1) ≤
        32 * (2 * alpha + 3 * error) * cutoff⁻¹ ^ 2 * (Real.log cutoff + 1) := by
      dsimp only [scale]
      have hpositive : 0 ≤ (2 * alpha + 3 * error) * cutoff⁻¹ ^ 2 * (Real.log cutoff + 1) := by
        positivity
      calc
        _ = (64 / 3) * ((2 * alpha + 3 * error) * cutoff⁻¹ ^ 2 * (Real.log cutoff + 1)) := by
          simp only [div_eq_mul_inv]
          ring
        _ ≤ 32 * ((2 * alpha + 3 * error) * cutoff⁻¹ ^ 2 * (Real.log cutoff + 1)) :=
          mul_le_mul_of_nonneg_right (by norm_num : (64 : ℝ) / 3 ≤ 32) hpositive
        _ = _ := by ring
    exact htotal.trans (hlogscaled.trans hcoarse)
  exact fun cutoff hcutoff strict => ⟨hquartic_large hcutoff strict, htail_large hcutoff strict⟩

#print axioms phase_law_dyadic_coercivity

end
end D5.S3.Analytic.Asymptotics.PhaseLawDyadicCoercivity
