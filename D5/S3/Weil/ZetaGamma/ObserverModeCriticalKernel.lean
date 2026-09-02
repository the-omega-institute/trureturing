/- GID: D5/S3/Weil/ZetaGamma/ObserverModeCriticalKernel
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/ObserverModeCriticalKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify the symmetric digamma difference kernel and its strict axis positivity. -/

import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition

/-!
# Observer-mode critical kernel

The concrete completed-zeta digamma multiplier is polarized through its
positive-scale Levy representation.  The resulting symmetric difference has
the cosine-modulated kernel, and its zero-frequency value is strictly positive
for every nonzero shift.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaGamma.ObserverModeCriticalKernel

open MeasureTheory Set Topology
open D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition

noncomputable section

/-- The symmetric second difference of the completed-zeta digamma multiplier
has the observer-mode kernel, with strict positivity at zero frequency for
every nonzero shift. -/
theorem observer_mode_critical_kernel (t tau : ℝ) :
    let a : ℝ → ℝ := fun u =>
      (Complex.digamma
        ((1 / 4 : ℂ) + Complex.I * ((u / 2 : ℝ) : ℂ))).re -
        Real.log Real.pi
    (∀ u : ℝ,
      IntegrableOn
        (fun x : ℝ =>
          archimedeanJumpDensity x * (1 - Real.cos (u * x)))
        (Ioi 0) ∧
      a u - a 0 =
        2 * ∫ x : ℝ in Ioi 0,
          archimedeanJumpDensity x * (1 - Real.cos (u * x))) →
      (1 / 2) * (a (t + tau) + a (t - tau)) - a t =
          2 * ∫ x : ℝ in Ioi 0,
            archimedeanJumpDensity x * Real.cos (t * x) *
              (1 - Real.cos (tau * x)) ∧
        (tau ≠ 0 →
          0 < (1 / 2) * (a tau + a (-tau)) - a 0) := by
  dsimp only
  intro hLevy
  constructor
  · obtain ⟨hPlusInt, hPlus⟩ := hLevy (t + tau)
    obtain ⟨hMinusInt, hMinus⟩ := hLevy (t - tau)
    obtain ⟨hCenterInt, hCenter⟩ := hLevy t
    calc
      (1 / 2) *
            (((Complex.digamma
                ((1 / 4 : ℂ) + Complex.I * (((t + tau) / 2 : ℝ) : ℂ))).re -
                Real.log Real.pi) +
              ((Complex.digamma
                ((1 / 4 : ℂ) + Complex.I * (((t - tau) / 2 : ℝ) : ℂ))).re -
                Real.log Real.pi)) -
          ((Complex.digamma
            ((1 / 4 : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ))).re -
            Real.log Real.pi) =
          (∫ x : ℝ in Ioi 0,
              archimedeanJumpDensity x *
                (1 - Real.cos ((t + tau) * x))) +
            (∫ x : ℝ in Ioi 0,
              archimedeanJumpDensity x *
                (1 - Real.cos ((t - tau) * x))) -
            2 * (∫ x : ℝ in Ioi 0,
              archimedeanJumpDensity x * (1 - Real.cos (t * x))) := by
        linear_combination (1 / 2) * hPlus + (1 / 2) * hMinus - hCenter
      _ = ∫ x : ℝ in Ioi 0,
          (archimedeanJumpDensity x * (1 - Real.cos ((t + tau) * x)) +
            archimedeanJumpDensity x * (1 - Real.cos ((t - tau) * x)) -
            2 * (archimedeanJumpDensity x * (1 - Real.cos (t * x)))) := by
        symm
        calc
          (∫ x : ℝ in Ioi 0,
              (archimedeanJumpDensity x * (1 - Real.cos ((t + tau) * x)) +
                archimedeanJumpDensity x * (1 - Real.cos ((t - tau) * x)) -
                2 * (archimedeanJumpDensity x * (1 - Real.cos (t * x))))) =
              (∫ x : ℝ in Ioi 0,
                (archimedeanJumpDensity x * (1 - Real.cos ((t + tau) * x)) +
                  archimedeanJumpDensity x * (1 - Real.cos ((t - tau) * x)))) -
                ∫ x : ℝ in Ioi 0,
                  2 * (archimedeanJumpDensity x * (1 - Real.cos (t * x))) :=
            integral_sub (hPlusInt.add hMinusInt) (hCenterInt.const_mul 2)
          _ = _ := by
            rw [integral_add hPlusInt hMinusInt, integral_const_mul]
      _ = ∫ x : ℝ in Ioi 0,
          2 * (archimedeanJumpDensity x * Real.cos (t * x) *
            (1 - Real.cos (tau * x))) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [show (t + tau) * x = t * x + tau * x by ring,
          show (t - tau) * x = t * x - tau * x by ring,
          Real.cos_add, Real.cos_sub]
        ring
      _ = 2 * ∫ x : ℝ in Ioi 0,
          archimedeanJumpDensity x * Real.cos (t * x) *
            (1 - Real.cos (tau * x)) := by
        rw [integral_const_mul]
  · intro hTau
    let g : ℝ → ℝ := fun x =>
      archimedeanJumpDensity x * (1 - Real.cos (tau * x))
    have hInt : Integrable g (volume.restrict (Ioi 0)) := by
      simpa only [g] using (hLevy tau).1.integrable
    have hNonneg : 0 ≤ᵐ[volume.restrict (Ioi 0)] g := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hExpLt : Real.exp (-2 * x) < 1 := by
        rw [Real.exp_lt_one_iff]
        exact mul_neg_of_neg_of_pos (by norm_num) hx
      have hDensity : 0 ≤ archimedeanJumpDensity x := by
        unfold archimedeanJumpDensity
        exact div_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hExpLt.le)
      exact mul_nonneg hDensity (sub_nonneg.mpr (Real.cos_le_one _))
    let x0 : ℝ := Real.pi / |tau|
    have hAbs : 0 < |tau| := abs_pos.mpr hTau
    have hx0 : 0 < x0 := div_pos Real.pi_pos hAbs
    have hCos : Real.cos (tau * x0) = -1 := by
      rcases lt_or_gt_of_ne hTau with hTauNeg | hTauPos
      · have hAbsEq : |tau| = -tau := abs_of_neg hTauNeg
        rw [show tau * x0 = -Real.pi by
          dsimp only [x0]
          rw [hAbsEq]
          field_simp [hTau]]
        rw [Real.cos_neg, Real.cos_pi]
      · have hAbsEq : |tau| = tau := abs_of_pos hTauPos
        rw [show tau * x0 = Real.pi by
          dsimp only [x0]
          rw [hAbsEq]
          field_simp [hTau]]
        exact Real.cos_pi
    have hExpLt : Real.exp (-2 * x0) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    have hDensityPos : 0 < archimedeanJumpDensity x0 := by
      unfold archimedeanJumpDensity
      exact div_pos (Real.exp_pos _) (sub_pos.mpr hExpLt)
    have hgPos : 0 < g x0 := by
      dsimp only [g]
      rw [hCos]
      nlinarith
    have hDen : 1 - Real.exp (-2 * x0) ≠ 0 :=
      (sub_pos.mpr hExpLt).ne'
    have hDensityContinuous : ContinuousAt archimedeanJumpDensity x0 := by
      unfold archimedeanJumpDensity
      apply ContinuousAt.div
      · fun_prop
      · fun_prop
      · exact hDen
    have hgContinuous : ContinuousAt g x0 := by
      dsimp only [g]
      exact hDensityContinuous.mul (by fun_prop)
    have hEventuallyPos : ∀ᶠ x in 𝓝 x0, 0 < g x :=
      hgContinuous (isOpen_Ioi.mem_nhds hgPos)
    obtain ⟨epsilon, hEpsilon, hBall⟩ :=
      Metric.mem_nhds_iff.mp hEventuallyPos
    let delta : ℝ := min epsilon (x0 / 2)
    have hDelta : 0 < delta := lt_min hEpsilon (half_pos hx0)
    have hBallPos : Metric.ball x0 delta ⊆ Ioi (0 : ℝ) := by
      intro x hx
      have hxAbs : |x - x0| < delta := by
        simpa only [Metric.mem_ball, Real.dist_eq] using hx
      have hxLower := (abs_lt.mp hxAbs).1
      have hDeltaLe : delta ≤ x0 / 2 := min_le_right _ _
      exact lt_of_lt_of_le (half_pos hx0) (by linarith)
    have hBallSupport : Metric.ball x0 delta ⊆ Function.support g := by
      intro x hx
      apply ne_of_gt
      apply hBall
      exact Metric.ball_subset_ball (min_le_left _ _) hx
    have hBallMeasure :
        0 < (volume.restrict (Ioi (0 : ℝ))) (Metric.ball x0 delta) := by
      rw [Measure.restrict_apply Metric.isOpen_ball.measurableSet,
        inter_eq_left.mpr hBallPos]
      exact Metric.isOpen_ball.measure_pos volume
        ⟨x0, Metric.mem_ball_self hDelta⟩
    have hSupportMeasure :
        0 < (volume.restrict (Ioi (0 : ℝ))) (Function.support g) :=
      lt_of_lt_of_le hBallMeasure (measure_mono hBallSupport)
    have hIntegralPos : 0 < ∫ x : ℝ in Ioi 0, g x :=
      (integral_pos_iff_support_of_nonneg_ae hNonneg hInt).2 hSupportMeasure
    have hPositive := (hLevy tau).2
    have hNegative := (hLevy (-tau)).2
    have hNegIntegral :
        (∫ x : ℝ in Ioi 0,
          archimedeanJumpDensity x * (1 - Real.cos (-tau * x))) =
        ∫ x : ℝ in Ioi 0,
          archimedeanJumpDensity x * (1 - Real.cos (tau * x)) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [show -tau * x = -(tau * x) by ring, Real.cos_neg]
    rw [hNegIntegral] at hNegative
    change 0 < ∫ x : ℝ in Ioi 0,
      archimedeanJumpDensity x * (1 - Real.cos (tau * x)) at hIntegralPos
    nlinarith

#print axioms observer_mode_critical_kernel

end

end D5.S3.Weil.ZetaGamma.ObserverModeCriticalKernel
