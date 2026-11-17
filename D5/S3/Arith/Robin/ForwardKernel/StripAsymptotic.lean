/- GID: D5/S3/Arith/Robin/ForwardKernel/StripAsymptotic
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/StripAsymptotic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The forward adjoint remainder has polynomial parameter bounds on a fixed vertical strip. -/

import D5.S3.Arith.Robin.ForwardKernel.Asymptotic
import Mathlib.Analysis.Calculus.MeanValue

namespace D5.S3.Arith.Robin.ForwardKernel.StripAsymptotic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set MeasureTheory Filter
open scoped Topology ENNReal
open ForwardKernel.Remainder ForwardKernel.Asymptotic ForwardKernel.WeightControl
open OriginalMovingWindowMoment (width)

private lemma parameter_norm (s : ℂ) : ‖-s - 1 / 2‖ ≤ 1 + ‖s‖ := by
  calc
    _ ≤ ‖-s‖ + ‖(1 / 2 : ℂ)‖ := norm_sub_le _ _
    _ ≤ _ := by simp; norm_num; linarith

private lemma exp_difference_bound (v : ℂ) (hv : v.re ≤ 3) :
    ‖Complex.exp v - 1‖ ≤ Real.exp 3 * ‖v‖ := by
  have hd : ∀ u ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun u : ℝ => Complex.exp ((u : ℂ) * v))
        (Complex.exp ((u : ℂ) * v) * v) (Icc (0 : ℝ) 1) u := by
    intro u hu
    simpa using (((hasDerivAt_id u).ofReal_comp.mul_const v).cexp).hasDerivWithinAt
  have hb : ∀ u ∈ Ico (0 : ℝ) 1,
      ‖Complex.exp ((u : ℂ) * v) * v‖ ≤ Real.exp 3 * ‖v‖ := by
    intro u hu
    rw [norm_mul, Complex.norm_exp]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith [hu.1, hu.2, mul_nonneg hu.1 (sub_nonneg.mpr hv)]
  simpa using norm_image_sub_le_of_norm_deriv_le_segment_01' hd hb

private lemma power_pointwise (s : ℂ) (hs : -(1 / 5 : ℝ) ≤ s.re)
    (hs' : s.re ≤ 1) {t z : ℝ} (ht : 2 ≤ t) (hz : z ∈ Icc (0 : ℝ) 1) :
    ‖normalizedPower t z s‖ ≤ Real.exp 3 ∧
      ‖normalizedPower t z s - 1‖ ≤
        (2 * Real.exp 3) * (1 + ‖s‖) * t ^ (-1 / 5 : ℝ) ∧
      ‖deriv (fun y => normalizedPower y z s) t‖ ≤
        (2 * Real.exp 3) * (1 + ‖s‖) * t ^ (-6 / 5 : ℝ) := by
  have ht0 : 0 < t := by linarith
  let v : ℂ := (-s - 1 / 2) * (Real.log (coordinate t z / t) : ℂ)
  have hε : t ^ (-1 / 5 : ℝ) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_nonpos zero_lt_one (by linarith : 1 ≤ t)
      (by norm_num : (-1 / 5 : ℝ) ≤ 0)
  have hl := log_fraction_bound ht hz
  have hl' : |Real.log (coordinate t z / t)| ≤ 2 := by nlinarith
  have hv : v.re ≤ 3 := by
    have ha := (abs_le.mp hl').1
    have hb := (abs_le.mp hl').2
    dsimp [v]
    simp only [Complex.mul_re, Complex.sub_re, Complex.neg_re, Complex.div_re,
      Complex.one_re, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im]
    norm_num
    nlinarith
  have hn : ‖v‖ ≤ 2 * (1 + ‖s‖) * t ^ (-1 / 5 : ℝ) := by
    dsimp [v]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ (1 + ‖s‖) * (2 * t ^ (-1 / 5 : ℝ)) :=
        mul_le_mul (parameter_norm s) hl (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hp : ‖normalizedPower t z s‖ ≤ Real.exp 3 := by
    change ‖Complex.exp v‖ ≤ _
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr hv
  refine ⟨hp, ?_, ?_⟩
  · exact (exp_difference_bound v hv).trans (by
      calc
        _ ≤ Real.exp 3 * (2 * (1 + ‖s‖) * t ^ (-1 / 5 : ℝ)) :=
          mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le
        _ = _ := by ring)
  · have hv0 : 0 < coordinate t z / t := div_pos (coordinate_pos ht0 hz.1) ht0
    have hvhalf : (1 / 2 : ℝ) ≤ coordinate t z / t :=
      (le_div_iff₀ ht0).2 (by linarith [coordinate_half ht hz])
    have hf := coordinate_fraction_derivative_bound (by linarith : 1 ≤ t) hz
    rw [(coordinate_fraction_hasDerivAt ht0 hz.1).deriv] at hf
    have hdiv : ((z / 5 * width (coordinate t z)) /
        (t ^ 2 * (1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ)))) /
        (coordinate t z / t) ≤ 2 * t ^ (-6 / 5 : ℝ) := by
      apply (div_le_iff₀ hv0).2
      nlinarith [Real.rpow_pos_of_pos ht0 (-6 / 5 : ℝ)]
    rw [(normalizedPower_hasDerivAt ht0 hz.1 s).deriv, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hf.1 hv0.le)]
    calc
      _ ≤ (Real.exp 3 * (1 + ‖s‖)) * (2 * t ^ (-6 / 5 : ℝ)) :=
        mul_le_mul (mul_le_mul hp (parameter_norm s) (norm_nonneg _) (by positivity))
          hdiv (div_nonneg hf.1 hv0.le) (by positivity)
      _ = _ := by ring

/-- Relative powers are uniformly bounded on the strip and their first errors grow linearly. -/
theorem normalizedPower_strip_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -(1 / 5 : ℝ) ≤ s.re → s.re ≤ 1 →
      ∀ t z : ℝ, 2 ≤ t → z ∈ Icc (0 : ℝ) 1 →
        ‖normalizedPower t z s‖ ≤ C ∧
        ‖normalizedPower t z s - 1‖ ≤ C * (1 + ‖s‖) * t ^ (-1 / 5 : ℝ) ∧
        ‖deriv (fun y => normalizedPower y z s) t‖ ≤
          C * (1 + ‖s‖) * t ^ (-6 / 5 : ℝ) := by
  refine ⟨2 * Real.exp 3, by positivity, ?_⟩
  intro s hs hs' t z ht hz
  have h := power_pointwise s hs hs' ht hz
  exact ⟨h.1.trans (by linarith [Real.exp_pos (3 : ℝ)]), h.2⟩


private lemma body_strip_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -(1 / 5 : ℝ) ≤ s.re → s.re ≤ 1 →
      ∀ t z u : ℝ, 8 ≤ t → z ∈ Icc (0 : ℝ) 1 → u ∈ Icc (0 : ℝ) 1 →
        ‖normalizedBody t z u s - 1‖ ≤ C * (1 + ‖s‖) * t ^ (-1 / 5 : ℝ) ∧
        ‖deriv (fun y => normalizedBody y z u s) t‖ ≤
          C * (1 + ‖s‖) * t ^ (-6 / 5 : ℝ) := by
  obtain ⟨P, hP0, hPower⟩ := normalizedPower_strip_bounds
  refine ⟨51 * P + 10, by positivity, ?_⟩
  intro s hs hs' t z u ht hz hu
  have ht0 : 0 < t := by linarith
  have ht2 : 2 ≤ t := by linarith
  have hx4 : 4 ≤ coordinate t z := by linarith [coordinate_half ht2 hz]
  obtain ⟨hA0, hA1, hAderiv, hAbound⟩ := weightRatio_control hx4 hu.1 hu.2
  have hj := jacobianFactor_bounds ht2 hz
  have hJ0 := hj.1.le
  have hJ1 := hj.2.1
  have hAnorm : ‖(weightRatio (coordinate t z) u : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA0] using hA1
  have hJnorm : ‖(jacobianFactor t z : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hJ0] using hJ1
  have hAerr : ‖(weightRatio (coordinate t z) u : ℂ) - 1‖ ≤
      8 * t ^ (-1 / 5 : ℝ) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact (weightRatio_sub_one hx4 hu.1 hu.2).trans
      (by nlinarith [coordinate_power_one ht2 hz])
  have hJerr : ‖(jacobianFactor t z : ℂ) - 1‖ ≤ 2 * t ^ (-1 / 5 : ℝ) := by
    simpa only [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] using hj.2.2
  have hP := hPower s hs hs' t z ht2 hz
  have hPnorm := hP.1
  have hPerr := hP.2.1
  have hP' := hP.2.2
  have hA' := (ratio_time_control ht hz hu).2
  have hJ' := jacobianFactor_derivative_bound ht2 hz
  constructor
  · have he : normalizedBody t z u s - 1 =
        (normalizedPower t z s - 1) * (weightRatio (coordinate t z) u : ℂ) *
          (jacobianFactor t z : ℂ) +
        ((weightRatio (coordinate t z) u : ℂ) - 1) * (jacobianFactor t z : ℂ) +
        ((jacobianFactor t z : ℂ) - 1) := by unfold normalizedBody; ring
    rw [he]
    calc
      _ ≤ ‖(normalizedPower t z s - 1) * (weightRatio (coordinate t z) u : ℂ) *
            (jacobianFactor t z : ℂ)‖ +
          ‖((weightRatio (coordinate t z) u : ℂ) - 1) * (jacobianFactor t z : ℂ)‖ +
          ‖((jacobianFactor t z : ℂ) - 1)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ((P * (1 + ‖s‖)) *
          t ^ (-1 / 5 : ℝ)) * 1 * 1 +
          (8 * t ^ (-1 / 5 : ℝ)) * 1 + 2 * t ^ (-1 / 5 : ℝ) := by
        simp only [norm_mul]
        gcongr
      _ ≤ _ := by
        have hε := Real.rpow_nonneg ht0.le (-1 / 5 : ℝ)
        nlinarith [norm_nonneg s, mul_nonneg (norm_nonneg s) hε]
  · have hPder := (normalizedPower_hasDerivAt ht0 hz.1 s).differentiableAt
    have hAr := (ratio_time_control ht hz hu).1
    have hJr := (jacobianFactor_hasDerivAt ht0 hz.1).differentiableAt
    have he : deriv (fun y => normalizedBody y z u s) t =
        (deriv (fun y => normalizedPower y z s) t *
            (weightRatio (coordinate t z) u : ℂ) +
          normalizedPower t z s * ((deriv (fun y : ℝ => weightRatio (coordinate y z) u) t : ℝ) : ℂ)) *
            (jacobianFactor t z : ℂ) +
          (normalizedPower t z s * (weightRatio (coordinate t z) u : ℂ)) *
            ((deriv (fun y : ℝ => jacobianFactor y z) t : ℝ) : ℂ) := by
      convert (((hPder.hasDerivAt.mul hAr.hasDerivAt.ofReal_comp).mul
          hJr.hasDerivAt.ofReal_comp).deriv) using 1 <;> rfl
    rw [he]
    calc
      _ ≤ (‖deriv (fun y => normalizedPower y z s) t‖ *
            ‖(weightRatio (coordinate t z) u : ℂ)‖ +
          ‖normalizedPower t z s‖ *
            |deriv (fun y => weightRatio (coordinate y z) u) t|) *
            ‖(jacobianFactor t z : ℂ)‖ +
          (‖normalizedPower t z s‖ * ‖(weightRatio (coordinate t z) u : ℂ)‖) *
            |deriv (fun y => jacobianFactor y z) t| := by
        calc
          _ ≤ _ := norm_add_le _ _
          _ ≤ _ := by
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            gcongr
            simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
              norm_add_le
                (deriv (fun y => normalizedPower y z s) t * (weightRatio (coordinate t z) u : ℂ))
                (normalizedPower t z s *
                  ((deriv (fun y : ℝ => weightRatio (coordinate y z) u) t : ℝ) : ℂ))
      _ ≤ ((P * (1 + ‖s‖)) * t ^ (-6 / 5 : ℝ) * 1 +
          P * (48 * t ^ (-6 / 5 : ℝ))) * 1 +
          (P * 1) * t ^ (-6 / 5 : ℝ) := by gcongr
      _ ≤ _ := by
        have hε := Real.rpow_nonneg ht0.le (-6 / 5 : ℝ)
        nlinarith [mul_nonneg (norm_nonneg s) hε, mul_nonneg hP0.le hε,
          mul_nonneg (mul_nonneg hP0.le (norm_nonneg s)) hε]

private lemma adjoint_strip_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -(1 / 5 : ℝ) ≤ s.re → s.re ≤ 1 →
      ∀ t : ℝ, 8 < t →
        ‖normalizedAdjoint t s - 1 / 2‖ ≤ C * (1 + ‖s‖) * t ^ (-1 / 5 : ℝ) ∧
        ‖deriv (fun y => normalizedAdjoint y s) t‖ ≤
          C * (1 + ‖s‖) * t ^ (-6 / 5 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := body_strip_bounds
  refine ⟨C, hC, ?_⟩
  intro s hs hs' t ht
  have hμ : volume unitSquare < ∞ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  constructor
  · have hconst : IntegrableOn (triangle.indicator (fun _ => (1 : ℂ))) unitSquare :=
      (integrableOn_const hμ.ne).indicator (measurableSet_le measurable_fst measurable_snd)
    rw [normalizedAdjoint, ← triangle_integral,
      ← integral_sub (integrand_integrable ht.le s) hconst]
    have hbound : ∀ p ∈ unitSquare,
        ‖normalizedIntegrand t s p - triangle.indicator (fun _ => (1 : ℂ)) p‖ ≤
          C * (1 + ‖s‖) * t ^ (-1 / 5 : ℝ) := by
      intro p hp
      by_cases htri : p ∈ triangle
      · simpa only [normalizedIntegrand, indicator_of_mem htri] using
          (hb s hs hs' t p.1 p.2 ht.le hp.1 hp.2).1
      · simp only [normalizedIntegrand, indicator_of_notMem htri, sub_self, norm_zero]
        positivity
    simpa only [unitSquare_volume, mul_one] using norm_setIntegral_le_of_norm_le_const hμ hbound
  · rw [(normalizedAdjoint_hasDerivAt ht s).deriv]
    have hbound : ∀ p ∈ unitSquare,
        ‖deriv (fun y => normalizedIntegrand y s p) t‖ ≤
          C * (1 + ‖s‖) * t ^ (-6 / 5 : ℝ) := by
      intro p hp
      by_cases htri : p ∈ triangle
      · simpa only [normalizedIntegrand, indicator_of_mem htri] using
          (hb s hs hs' t p.1 p.2 ht.le hp.1 hp.2).2
      · simp only [normalizedIntegrand, indicator_of_notMem htri, deriv_const', norm_zero]
        positivity
    simpa only [unitSquare_volume, mul_one] using norm_setIntegral_le_of_norm_le_const hμ hbound

/-- The adjoint remainder has linear growth, and its time derivative has quadratic growth. -/
theorem adjointRemainder_strip_C1_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, -(1 / 5 : ℝ) ≤ s.re → s.re ≤ 1 →
      ∀ t : ℝ, 8 < t →
        ‖adjointRemainder t s‖ ≤ C * (1 + ‖s‖) * t ^ (-s.re - 7 / 10) ∧
        ‖deriv (fun y => adjointRemainder y s) t‖ ≤
          C * (1 + ‖s‖) ^ 2 * t ^ (-s.re - 17 / 10) := by
  obtain ⟨B, hB, hb⟩ := adjoint_strip_bounds
  refine ⟨2 * B, by positivity, ?_⟩
  intro s hs hs' t ht
  have ht0 : 0 < t := by linarith
  have hq := hb s hs hs' t ht
  have hdiff := normalizedAdjoint_hasDerivAt ht s
  have hr := (principalPower_hasDerivAt ht0 s).mul (hdiff.sub_const (1 / 2 : ℂ))
  have hnorm : ‖(t : ℂ) ^ (-s - 1 / 2)‖ = t ^ (-s.re - 1 / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    norm_num
  have hnorm' : ‖(t : ℂ) ^ (-s - 1 / 2 - 1)‖ = t ^ (-s.re - 3 / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    congr 1
    norm_num
    ring
  have he : t ^ (-s.re - 1 / 2) * t ^ (-6 / 5 : ℝ) = t ^ (-s.re - 17 / 10) := by
    rw [← Real.rpow_add ht0]
    congr 1
    ring
  have he' : t ^ (-s.re - 3 / 2) * t ^ (-1 / 5 : ℝ) = t ^ (-s.re - 17 / 10) := by
    rw [← Real.rpow_add ht0]
    congr 1
    ring
  constructor
  · unfold adjointRemainder
    rw [norm_mul, hnorm]
    calc
      _ ≤ t ^ (-s.re - 1 / 2) * (B * (1 + ‖s‖) * t ^ (-1 / 5 : ℝ)) := by
        gcongr
        exact hq.1
      _ = B * (1 + ‖s‖) * t ^ (-s.re - 7 / 10) := by
        calc
          _ = (B * (1 + ‖s‖)) *
              (t ^ (-s.re - 1 / 2) * t ^ (-1 / 5 : ℝ)) := by ring
          _ = _ := by
            rw [← Real.rpow_add ht0]
            congr 2
            ring
      _ ≤ _ := by gcongr; linarith
  · have hd : deriv (fun y => adjointRemainder y s) t =
        (-s - 1 / 2) * (t : ℂ) ^ (-s - 1 / 2 - 1) * (normalizedAdjoint t s - 1 / 2) +
        (t : ℂ) ^ (-s - 1 / 2) * deriv (fun y => normalizedAdjoint y s) t := by
      rw [hdiff.deriv]
      convert hr.deriv using 1
      apply congrArg (fun f : ℝ → ℂ => deriv f t)
      funext y
      rfl
    rw [hd]
    calc
      _ ≤ ‖(-s - 1 / 2) * (t : ℂ) ^ (-s - 1 / 2 - 1) *
          (normalizedAdjoint t s - 1 / 2)‖ +
          ‖(t : ℂ) ^ (-s - 1 / 2) * deriv (fun y => normalizedAdjoint y s) t‖ := norm_add_le _ _
      _ ≤ ((1 + ‖s‖) * t ^ (-s.re - 3 / 2)) *
          (B * (1 + ‖s‖) * t ^ (-1 / 5 : ℝ)) +
          t ^ (-s.re - 1 / 2) * (B * (1 + ‖s‖) * t ^ (-6 / 5 : ℝ)) := by
        simp only [norm_mul, hnorm, hnorm']
        gcongr
        · exact parameter_norm s
        · exact hq.1
        · exact hq.2
      _ = B * ((1 + ‖s‖) ^ 2 + (1 + ‖s‖)) * t ^ (-s.re - 17 / 10) := by
        calc
          _ = B * (1 + ‖s‖) ^ 2 *
              (t ^ (-s.re - 3 / 2) * t ^ (-1 / 5 : ℝ)) +
              B * (1 + ‖s‖) * (t ^ (-s.re - 1 / 2) * t ^ (-6 / 5 : ℝ)) := by ring
          _ = _ := by rw [he, he']; ring
      _ ≤ B * (2 * (1 + ‖s‖) ^ 2) * t ^ (-s.re - 17 / 10) := by
        gcongr
        nlinarith [sq_nonneg ‖s‖, norm_nonneg s]
      _ = _ := by ring

end
end D5.S3.Arith.Robin.ForwardKernel.StripAsymptotic
