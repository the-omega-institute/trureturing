/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondContour4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullDiamondContour4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Horizontal contour deformation and exponential Fourier decay of the null-diamond kernel. -/

import D5.S3.Quantum.Analysis.NullConeGravity.NullDiamondBesselStrip4D
import D5.S3.Analytic.Asymptotics.ExponentialAbsIntegrability
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! Contour deformation by rectangular Cauchy integration, with the angular Fourier normalization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Complex Filter MeasureTheory Set Topology
open scoped Interval
namespace NullConeGravity

private theorem stripB_pos : 0 < stripB := by norm_num [stripB]
private theorem stripB_lt_half : stripB < 1/2 := by norm_num [stripB]
private theorem closed_subset_open : closedStrip ⊆ openStrip :=
  fun _ hz => lt_of_le_of_lt hz stripB_lt_half
private theorem line_mem_closed (r y : ℝ) (hy : |y| ≤ stripB) :
    (r : ℂ) + (y : ℂ) * I ∈ closedStrip := by
  simpa [closedStrip, Complex.mul_im] using hy

private def decay (d r : ℝ) : ℝ := Real.exp (-d * |r|) * (1+|r|)
private theorem decay_nonneg (d r : ℝ) : 0 ≤ decay d r := by
  unfold decay; positivity

private theorem decay_integrable {d : ℝ} (hd : 0 < d) : Integrable (decay d) := by
  have hbase := D5.S3.Analytic.Asymptotics.ExponentialAbsIntegrability.integrable_exp_neg_mul_abs
    (half_pos hd)
  apply (hbase.const_mul (1+2/d)).mono' (by unfold decay; fun_prop)
  filter_upwards [] with r
  have hexp := Real.add_one_le_exp (d/2 * |r|)
  have h1 : 1+|r| ≤ (1+2/d) * Real.exp (d/2 * |r|) := by
    have hA : 1 ≤ Real.exp (d/2 * |r|) := Real.one_le_exp_iff.mpr (by positivity)
    have hB : |r| ≤ 2 * Real.exp (d/2 * |r|) / d := by
      apply (le_div_iff₀ hd).mpr
      linarith
    rw [add_mul, one_mul]
    have hB' : |r| ≤ 2 / d * Real.exp (d / 2 * |r|) := by
      convert hB using 1; ring
    linarith
  rw [Real.norm_of_nonneg (decay_nonneg d r)]
  calc
    decay d r ≤ Real.exp (-d*|r|) * ((1+2/d) * Real.exp (d/2 * |r|)) :=
      mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    _ = (1+2/d) * Real.exp (-(d/2*|r|)) := by
      rw [← mul_left_comm, ← Real.exp_add]
      congr 2
      ring

private theorem decay_tendsto_zero {d : ℝ} (hd : 0 < d) :
    Tendsto (decay d) atTop (𝓝 0) := by
  have h0 : Tendsto (fun r : ℝ => Real.exp (-d*r)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hd)).mpr tendsto_id)
  have h1 : Tendsto (fun r : ℝ => r * Real.exp (-d*r)) atTop (𝓝 0) := by
    simpa [Real.rpow_one] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 d hd
  have h := (h0.add h1).congr' (show (fun r : ℝ => Real.exp (-d*r) + r * Real.exp (-d*r)) =ᶠ[atTop] decay d from by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with r hr
    simp [decay, abs_of_nonneg hr]; ring)
  simpa using h

private theorem line_integrable {f : ℂ → ℂ} {d B : ℝ}
    (hd : 0 < d) (hf : DifferentiableOn ℂ f openStrip)
    (hdecay : ∀ z ∈ closedStrip, ‖f z‖ ≤ B * decay d z.re)
    (y : ℝ) (hy : |y| ≤ stripB) :
    Integrable (fun r : ℝ => f ((r : ℂ) + (y : ℂ)*I)) := by
  have hc : Continuous (fun r : ℝ => f ((r : ℂ) + (y : ℂ)*I)) :=
    hf.continuousOn.comp_continuous (by fun_prop) (fun r => closed_subset_open (line_mem_closed r y hy))
  exact ((decay_integrable hd).const_mul B).mono' hc.aestronglyMeasurable
    (ae_of_all _ fun r => by simpa [Complex.mul_re] using hdecay _ (line_mem_closed r y hy))

theorem horizontal_shift {f : ℂ → ℂ} {d B : ℝ}
    (_hB : 0 ≤ B) (hd : 0 < d)
    (hf : DifferentiableOn ℂ f openStrip)
    (hdecay : ∀ z ∈ closedStrip,
      ‖f z‖ ≤ B * Real.exp (-d * |z.re|) * (1+|z.re|))
    (y : ℝ) (hy : |y| ≤ stripB) :
    (∫ r : ℝ, f (r : ℂ)) =
      ∫ r : ℝ, f ((r : ℂ) + (y : ℂ)*I) := by
  have hmajor (z : ℂ) (hz : z ∈ closedStrip) : ‖f z‖ ≤ B * decay d z.re := by
    simpa [decay, mul_assoc] using hdecay z hz
  have hzero : |(0 : ℝ)| ≤ stripB := by simpa using stripB_pos.le
  let line (v : ℝ) := ∫ r : ℝ, f ((r : ℂ)+(v : ℂ)*I)
  let side (r : ℝ) := ∫ v : ℝ in 0..y, f ((r : ℂ)+(v : ℂ)*I)
  have hside (r : ℝ) : ‖side r‖ ≤ B * decay d r * |y| := by
    simpa only [sub_zero] using
      (intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := y)
        (C := B * decay d r) (f := fun v => f ((r : ℂ)+(v : ℂ)*I)) fun v hv => by
        have hv' : |v| ≤ stripB := by
          simpa using (abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hv)).trans (by simpa using hy)
        simpa [Complex.mul_re] using hmajor _ (line_mem_closed r v hv'))
  have hright : Tendsto side atTop (𝓝 0) :=
    squeeze_zero_norm hside (by simpa using ((decay_tendsto_zero hd).const_mul B).mul_const |y|)
  have hleft : Tendsto (fun R => side (-R)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun R => ?_) (by simpa using ((decay_tendsto_zero hd).const_mul B).mul_const |y|)
    simpa [decay] using hside (-R)
  have hbottom := intervalIntegral_tendsto_integral (line_integrable hd hf hmajor 0 hzero)
    tendsto_neg_atTop_atBot tendsto_id
  have htop := intervalIntegral_tendsto_integral (line_integrable hd hf hmajor y hy)
    tendsto_neg_atTop_atBot tendsto_id
  have hlim := ((hbottom.sub htop).add (hright.const_smul I)).sub (hleft.const_smul I)
  have hrect : (fun R : ℝ =>
      (∫ r : ℝ in -R..R, f ((r : ℂ)+(0 : ℝ)*I)) -
      (∫ r : ℝ in -R..R, f ((r : ℂ)+(y : ℂ)*I)) + I • side R - I • side (-R)) =
      fun _ => 0 := by
    funext R
    have hsub : ([[(-(R : ℂ)).re, ((R : ℂ)+(y : ℂ)*I).re]] ×ℂ
                  [[(-(R : ℂ)).im, ((R : ℂ)+(y : ℂ)*I).im]]) ⊆ openStrip := by
      intro z hz
      apply closed_subset_open
      have hz' : z.im ∈ [[0,y]] := by simpa [Complex.mul_im] using (Complex.mem_reProdIm.mp hz).2
      simpa [closedStrip] using (abs_sub_left_of_mem_uIcc hz').trans (by simpa using hy)
    simpa [side, Complex.mul_re, Complex.mul_im] using
      Complex.integral_boundary_rect_eq_zero_of_differentiableOn f (-(R : ℂ))
        ((R : ℂ)+(y : ℂ)*I) (hf.mono hsub)
  have hlimzero : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (𝓝 (line 0 - line y)) := by
    simpa only [id, hrect, smul_zero, add_zero, sub_zero] using hlim
  have he := sub_eq_zero.mp (tendsto_nhds_unique hlimzero tendsto_const_nhds)
  simpa [line] using he


private def weightedG (M ν lam x : ℝ) (z w : ℂ) : ℂ :=
  Complex.exp (-Complex.I*(ν : ℂ)*z + Complex.I*(lam : ℂ)*w) * stripG M z w x

noncomputable def fourierG (M ν lam x : ℝ) : ℂ :=
  (1/(2*(Real.pi : ℂ))) * ∫ r : ℝ, ∫ s : ℝ, weightedG M ν lam x r s

private theorem measurable_stripG_comp {α : Type*} [MeasurableSpace α] (M : ℝ)
    {z w : α → ℂ} {x : α → ℝ} (hz : Measurable z) (hw : Measurable w) (hx : Measurable x) :
    Measurable (fun a => stripG M (z a) (w a) (x a)) := by
  have hP := besselP2_entire.continuous.measurable
  have hB := besselB2_entire.continuous.measurable
  have hlog := Complex.measurable_log
  unfold stripG correctionLog modularU modularUprime liftedLog
  apply Measurable.ite
  · exact measurableSet_lt hx measurable_const
  · fun_prop
  · exact measurable_const

private theorem measurable_weightedG_comp {α : Type*} [MeasurableSpace α] (M : ℝ)
    {ν lam x : α → ℝ} {z w : α → ℂ} (hν : Measurable ν) (hlam : Measurable lam)
    (hx : Measurable x) (hz : Measurable z) (hw : Measurable w) :
    Measurable (fun a => weightedG M (ν a) (lam a) (x a) (z a) (w a)) := by
  unfold weightedG
  exact (by fun_prop : Measurable fun a =>
    Complex.exp (-Complex.I*(ν a : ℂ)*z a + Complex.I*(lam a : ℂ)*w a)).mul
      (measurable_stripG_comp M hz hw hx)

theorem fourierG_measurable (M : ℝ) :
    Measurable (fun p : ℝ × ℝ × ℝ => fourierG M p.1 p.2.1 p.2.2) := by
  have h : Measurable (fun p : ((ℝ × ℝ × ℝ) × ℝ) × ℝ =>
      weightedG M p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.1.2 p.2) :=
    measurable_weightedG_comp M (by fun_prop) (by fun_prop) (by fun_prop)
      (by fun_prop) (by fun_prop)
  exact measurable_const.mul h.stronglyMeasurable.integral_prod_right'.integral_prod_right'.measurable

private theorem norm_weightedG (M ν lam x : ℝ) (z w : ℂ) :
    ‖weightedG M ν lam x z w‖ = Real.exp (ν*z.im - lam*w.im) * ‖stripG M z w x‖ := by
  rw [weightedG, norm_mul, Complex.norm_exp]
  congr 1
  simp [Complex.add_re, Complex.mul_re, Complex.mul_im, sub_eq_add_neg]

private def radialDecay (r : ℝ) : ℝ := decay (2*Real.pi) r

private theorem radialDecay_integrable : Integrable radialDecay :=
  decay_integrable (by positivity [Real.pi_pos])

private theorem radialDecay_nonneg (r : ℝ) : 0 ≤ radialDecay r := decay_nonneg _ _

private theorem weighted_major (M ν lam x C : ℝ) (hC : 0 ≤ C) (z w : ℂ)
    (hb : ‖stripG M z w x‖ ≤ C * Real.exp (-2*Real.pi*(|z.re|+|w.re|)) *
      (1+|z.re|+|w.re|+|Real.log (1-x)|)) :
    ‖weightedG M ν lam x z w‖ ≤
      (C * Real.exp (ν*z.im - lam*w.im) * (1+|Real.log (1-x)|)) *
        radialDecay z.re * radialDecay w.re := by
  rw [norm_weightedG]
  calc
    _ ≤ Real.exp (ν*z.im - lam*w.im) *
        (C * Real.exp (-2*Real.pi*(|z.re|+|w.re|)) *
        ((1+|z.re|)*(1+|w.re|)*(1+|Real.log (1-x)|))) := by
      apply mul_le_mul_of_nonneg_left (hb.trans ?_) (Real.exp_pos _).le
      apply mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC (Real.exp_pos _).le)
      nlinarith [abs_nonneg z.re, abs_nonneg w.re, abs_nonneg (Real.log (1-x)),
        mul_nonneg (abs_nonneg z.re) (abs_nonneg w.re),
        mul_nonneg (abs_nonneg z.re) (abs_nonneg (Real.log (1-x))),
        mul_nonneg (abs_nonneg w.re) (abs_nonneg (Real.log (1-x))),
        mul_nonneg (mul_nonneg (abs_nonneg z.re) (abs_nonneg w.re))
          (abs_nonneg (Real.log (1-x)))]
    _ = _ := by
      unfold radialDecay decay
      rw [show -2*Real.pi*(|z.re|+|w.re|) = - (2*Real.pi)*|z.re| + -(2*Real.pi)*|w.re| by ring,
        Real.exp_add]
      ring

private theorem weightedG_diff_left (M ν lam x : ℝ) (w : ℂ) :
    DifferentiableOn ℂ (fun z => weightedG M ν lam x z w) openStrip := by
  unfold weightedG
  refine DifferentiableOn.mul ?_ (stripG_diff_left M w x)
  exact (((differentiable_id.const_mul (-Complex.I*(ν : ℂ))).add_const _).cexp).differentiableOn

private theorem weightedG_diff_right (M ν lam x : ℝ) (z : ℂ) :
    DifferentiableOn ℂ (fun w => weightedG M ν lam x z w) openStrip := by
  unfold weightedG
  refine DifferentiableOn.mul ?_ (stripG_diff_right M z x)
  exact (((differentiable_id.const_mul (Complex.I*(lam : ℂ))).const_add _).cexp).differentiableOn

private theorem phase_exponent_le (ν lam : ℝ) (z w : ℂ)
    (hz : z ∈ closedStrip) (hw : w ∈ closedStrip) :
    ν*z.im - lam*w.im ≤ stripB*(|ν|+|lam|) := by
  have hz' : |z.im| ≤ stripB := hz
  have hw' : |w.im| ≤ stripB := hw
  have hν : ν*z.im ≤ |ν| * stripB := calc
    ν*z.im ≤ |ν*z.im| := le_abs_self _
    _ = |ν| * |z.im| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hz' (abs_nonneg _)
  have hlam : -(lam*w.im) ≤ |lam| * stripB := calc
    -(lam*w.im) ≤ |lam*w.im| := neg_le_abs _
    _ = |lam| * |w.im| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hw' (abs_nonneg _)
  nlinarith

private def contourHeight (ν : ℝ) : ℝ := if 0 ≤ ν then -stripB else stripB

private theorem contourHeight_abs (ν : ℝ) : |contourHeight ν| ≤ stripB := by
  by_cases hν : 0 ≤ ν <;> simp [contourHeight, hν, abs_of_pos stripB_pos]

private theorem contourHeight_mul (ν : ℝ) : ν * contourHeight ν = -stripB * |ν| := by
  by_cases hν : 0 ≤ ν
  · simp [contourHeight, hν, abs_of_nonneg hν]; ring
  · simp [contourHeight, hν, abs_of_neg (lt_of_not_ge hν)]; ring

theorem fourierG_bound (M : ℝ) (hM : 0 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν lam x : ℝ, -1 ≤ x → x < 1 →
      ‖fourierG M ν lam x‖ ≤
        C * Real.exp (-stripB*(|ν|+|lam|)) * (1+|Real.log (1-x)|) := by
  obtain ⟨C, hC, hbound⟩ := stripG_bound M hM
  let J := ∫ r : ℝ, radialDecay r
  have hJ : 0 ≤ J := integral_nonneg radialDecay_nonneg
  refine ⟨‖(1/(2*(Real.pi : ℂ)))‖ * C * (1+J^2) + 1, by positivity, ?_⟩
  intro ν lam x hx0 hx1
  let F := weightedG M ν lam x
  let L (r y : ℝ) : ℂ := (r : ℂ) + (y : ℂ)*I
  let K := C * Real.exp (stripB*(|ν|+|lam|)) * (1+|Real.log (1-x)|)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmajor (z w : ℂ) (hz : z ∈ closedStrip) (hw : w ∈ closedStrip) :
      ‖F z w‖ ≤ K * radialDecay z.re * radialDecay w.re := by
    apply (weighted_major M ν lam x C hC.le z w (hbound z w hz hw x hx0 hx1)).trans
    dsimp [K]
    gcongr <;> first | exact radialDecay_nonneg _ | exact phase_exponent_le ν lam z w hz hw
  have hint (y t : ℝ) (hy : |y| ≤ stripB) (ht : |t| ≤ stripB) :
      Integrable (fun p : ℝ × ℝ => F (L p.1 y) (L p.2 t))
        ((volume : Measure ℝ).prod volume) := by
    apply ((radialDecay_integrable.const_mul K).mul_prod radialDecay_integrable).mono'
    · apply Measurable.aestronglyMeasurable
      exact measurable_weightedG_comp M measurable_const measurable_const measurable_const
        (by dsimp [L]; fun_prop) (by dsimp [L]; fun_prop)
    · filter_upwards [] with p
      simpa [L, Complex.mul_re] using hmajor _ _ (line_mem_closed p.1 y hy) (line_mem_closed p.2 t ht)
  have hzero : |(0 : ℝ)| ≤ stripB := by simpa using stripB_pos.le
  let y := contourHeight ν
  let t := -contourHeight lam
  have hy : |y| ≤ stripB := contourHeight_abs ν
  have ht : |t| ≤ stripB := by simpa [t] using contourHeight_abs lam
  have hshiftLeft (s : ℝ) : (∫ r : ℝ, F r s) = ∫ r : ℝ, F (L r y) s := by
    apply horizontal_shift (B := K * radialDecay s) (d := 2*Real.pi)
      (by positivity [radialDecay_nonneg s]) (by positivity [Real.pi_pos]) (weightedG_diff_left M ν lam x s) _ y hy
    intro z hz
    have hs : (s : ℂ) ∈ closedStrip := by simpa using line_mem_closed s 0 hzero
    simpa only [Complex.ofReal_re, radialDecay, decay, mul_assoc, mul_comm, mul_left_comm]
      using hmajor z s hz hs
  have hshiftRight (r : ℝ) : (∫ s : ℝ, F (L r y) s) = ∫ s : ℝ, F (L r y) (L s t) := by
    apply horizontal_shift (B := K * radialDecay r) (d := 2*Real.pi)
      (by positivity [radialDecay_nonneg r]) (by positivity [Real.pi_pos]) (weightedG_diff_right M ν lam x (L r y)) _ t ht
    intro w hw
    simpa only [L, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      radialDecay, decay, mul_assoc, mul_comm, mul_left_comm]
      using hmajor (L r y) w (line_mem_closed r y hy) hw
  have hshift : (∫ r : ℝ, ∫ s : ℝ, F r s) = ∫ r : ℝ, ∫ s : ℝ, F (L r y) (L s t) := calc
    _ = ∫ s : ℝ, ∫ r : ℝ, F r s :=
      integral_integral_swap (show Integrable (Function.uncurry (fun r s : ℝ => F r s))
        ((volume : Measure ℝ).prod volume) by
          change Integrable (fun p : ℝ × ℝ => F p.1 p.2) _
          simpa [L] using hint 0 0 hzero hzero)
    _ = ∫ s : ℝ, ∫ r : ℝ, F (L r y) s := by simp_rw [hshiftLeft]
    _ = ∫ r : ℝ, ∫ s : ℝ, F (L r y) s :=
      (integral_integral_swap (show Integrable (Function.uncurry (fun r s : ℝ => F (L r y) s))
        ((volume : Measure ℝ).prod volume) by
          change Integrable (fun p : ℝ × ℝ => F (L p.1 y) p.2) _
          simpa [L] using hint y 0 hy hzero)).symm
    _ = _ := by simp_rw [hshiftRight]
  let A := C * Real.exp (-stripB*(|ν|+|lam|)) * (1+|Real.log (1-x)|)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hexponent : ν*y - lam*t = -stripB*(|ν|+|lam|) := by
    dsimp [y, t]
    rw [mul_neg, contourHeight_mul, contourHeight_mul]
    ring
  have hpoint (r s : ℝ) : ‖F (L r y) (L s t)‖ ≤ A * radialDecay r * radialDecay s := by
    have hb := weighted_major M ν lam x C hC.le (L r y) (L s t)
      (hbound _ _ (line_mem_closed r y hy) (line_mem_closed s t ht) x hx0 hx1)
    simpa [A, L, Complex.mul_re, Complex.mul_im, hexponent] using hb
  have hprod := (radialDecay_integrable.const_mul A).mul_prod radialDecay_integrable
  have hnorm : ‖∫ r : ℝ, ∫ s : ℝ, F (L r y) (L s t)‖ ≤ A*J^2 := by
    rw [← integral_prod _ (hint y t hy ht)]
    calc
      _ ≤ ∫ p : ℝ × ℝ, A * radialDecay p.1 * radialDecay p.2 ∂((volume : Measure ℝ).prod volume) :=
        norm_integral_le_of_norm_le hprod (ae_of_all _ fun p => hpoint p.1 p.2)
      _ = A*J^2 := by
        rw [integral_prod_mul (fun r => A*radialDecay r) radialDecay, integral_const_mul]
        dsimp [J]
        ring
  change ‖(1/(2*(Real.pi : ℂ))) * ∫ r : ℝ, ∫ s : ℝ, F r s‖ ≤ _
  rw [hshift, norm_mul]
  calc
    _ ≤ ‖(1/(2*(Real.pi : ℂ)))‖ * (A*J^2) := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ ≤ _ := by
      dsimp [A]
      nlinarith [mul_nonneg (norm_nonneg (1/(2*(Real.pi : ℂ)))) hC.le,
        Real.exp_pos (-stripB*(|ν|+|lam|)), abs_nonneg (Real.log (1-x))]

end NullConeGravity
