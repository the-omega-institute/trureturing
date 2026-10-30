/- GID: D5/S3/Analytic/Interpolation/SchurIntegratedKernel
   generality: G
   mirror-B: D5/B/S3/Analytic/Interpolation/SchurIntegratedKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.Poisson, mathlib/module/Mathlib.MeasureTheory.Integral.Prod]
   utility: none
   digest: Integrated Poisson control for the actual Schur boundary kernel. -/

import D5.S3.Analytic.Interpolation.SchurBoundaryKernel
import Mathlib.MeasureTheory.Integral.Prod

/-! The actual integrated disk Poisson density and its signed Schur kernel. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Set Metric Complex MeasureTheory

namespace D5.S3.Analytic.Interpolation.SchurIntegratedKernel

open D5.S3.Analytic.Interpolation.SchurBoundaryKernel

/-- The original disk Poisson density, evaluated on the actual unit circle. -/
def poissonDensity (t θ : ℝ) : ℝ :=
  poissonKernel 0 (t : ℂ) (circleMap 0 1 θ)

/-- The original oriented integral of the Poisson densities. -/
def integratedPoisson (x θ : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, poissonDensity t θ

private theorem circle_norm (θ : ℝ) : ‖circleMap 0 1 θ‖ = 1 := by
  simpa using circleMap_mem_sphere' (0 : ℂ) (1 : ℝ) θ

private theorem density_continuousOn {r : ℝ} (hr : r < 1) :
    ContinuousOn (fun p : ℝ × ℝ => poissonDensity p.1 p.2)
      (Icc (-r) r ×ˢ (univ : Set ℝ)) := by
  unfold poissonDensity poissonKernel
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro p hp
    apply pow_ne_zero 2
    apply norm_ne_zero_iff.mpr
    simp only [sub_zero, sub_ne_zero]
    intro he
    have hh := congrArg norm he
    rw [circle_norm, Complex.norm_real, Real.norm_eq_abs] at hh
    have ht : |p.1| ≤ r := abs_le.mpr hp.1
    linarith

private theorem density_bounds {r t : ℝ} (hr0 : 0 ≤ r) (hr : r < 1)
    (ht : |t| ≤ r) (θ : ℝ) :
    (1 - |t|) / (1 + |t|) ≤ poissonDensity t θ ∧
      poissonDensity t θ ≤ (1 + r) / (1 - r) := by
  have hz : circleMap 0 1 θ ∈ sphere (0 : ℂ) 1 := by
    simpa using circleMap_mem_sphere' (0 : ℂ) (1 : ℝ) θ
  have hw : (t : ℂ) ∈ ball (0 : ℂ) 1 := by
    simpa only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using ht.trans_lt hr
  have hlo := le_re_herglotzRieszKernel hz hw
  have hup := re_herglotzRieszKernel_le hz hw
  rw [← herglotzRieszKernel_def, ← Function.comp_apply (f := Complex.re),
    ← poissonKernel_eq_re_herglotzRieszKernel] at hlo hup
  simp only [sub_zero, Complex.norm_real, Real.norm_eq_abs] at hlo hup
  refine ⟨hlo, hup.trans ?_⟩
  apply (div_le_div_iff₀ (by linarith [abs_nonneg t]) (by linarith)).mpr
  nlinarith

private theorem density_angle_continuous {t : ℝ} (ht : |t| < 1) :
    Continuous (poissonDensity t) := by
  apply continuousOn_univ.mp
  simpa only [Function.comp_def, id_eq] using
    (density_continuousOn (r := |t|) ht).comp
      ((continuous_const.prodMk continuous_id).continuousOn)
      (fun θ _ => ⟨abs_le.mp (le_refl |t|), mem_univ θ⟩)

private theorem density_time_integrable {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (θ : ℝ) :
    IntervalIntegrable (fun t => poissonDensity t θ) volume (-r) r := by
  apply ContinuousOn.intervalIntegrable
  simpa only [uIcc_of_le (by linarith : -r ≤ r), Function.comp_def] using
    (density_continuousOn hr).comp (by fun_prop : ContinuousOn (fun t : ℝ => (t, θ)) (Icc (-r) r))
      (fun t ht => ⟨ht, mem_univ θ⟩)

private theorem integrated_continuous {x : ℝ} (hx : |x| < 1) :
    Continuous (integratedPoisson x) := by
  have hsub : uIcc (0 : ℝ) x ⊆ Icc (-|x|) |x| :=
    uIcc_subset_Icc ⟨by linarith [abs_nonneg x], abs_nonneg x⟩ ⟨neg_abs_le x, le_abs_self x⟩
  have hsub' : uIcc (0 : ℝ) x ⊆ uIcc (-|x|) |x| := by
    simpa only [uIcc_of_le (by linarith [abs_nonneg x] : -|x| ≤ |x|)] using hsub
  apply intervalIntegral.continuous_of_dominated_interval
    (bound := fun _ => (1 + |x|) / (1 - |x|))
  · intro θ
    exact ((density_time_integrable (abs_nonneg x) hx θ).mono_set hsub').aestronglyMeasurable_restrict_uIoc
  · intro θ
    exact Filter.Eventually.of_forall (fun t ht => by
      have ht' : |t| ≤ |x| := by
        have h := uIoc_subset_uIcc ht
        have h' := uIcc_subset_Icc (show (0 : ℝ) ∈ Icc (-|x|) |x| by
          constructor <;> linarith [abs_nonneg x]) ⟨neg_abs_le x, le_abs_self x⟩ h
        exact abs_le.mpr h'
      have hh := density_bounds (abs_nonneg x) hx ht' θ
      rw [Real.norm_eq_abs, abs_of_nonneg (by
        exact (div_nonneg (by linarith [ht'.trans_lt hx]) (by positivity)).trans hh.1)]
      exact hh.2)
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall (fun t ht => by
      have hh := uIoc_subset_uIcc ht
      have hh' := uIcc_subset_Icc (show (0 : ℝ) ∈ Icc (-|x|) |x| by
        constructor <;> linarith [abs_nonneg x]) ⟨neg_abs_le x, le_abs_self x⟩ hh
      exact density_angle_continuous ((abs_le.mpr hh').trans_lt hx))

private def lowerPolynomial (t : ℝ) : ℝ :=
  ((1 - t) / 2) + ((1 - t) / 2) ^ 2 + ((1 - t) / 2) ^ 3 +
    ((1 - t) / 2) ^ 4 + ((1 - t) / 2) ^ 5

private theorem lowerPolynomial_le {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    lowerPolynomial t ≤ (1 - t) / (1 + t) := by
  apply (le_div_iff₀ (by linarith [ht.1] : 0 < 1 + t)).mpr
  have h := pow_nonneg (sub_nonneg.mpr ht.2) 6
  dsimp [lowerPolynomial]
  nlinarith [h]

private theorem lowerPolynomial_integral :
    (∫ t in (0 : ℝ)..1, lowerPolynomial t) = 367 / 960 := by
  have hp (n : ℕ) : (∫ t in (0 : ℝ)..1, ((1 - t) / 2) ^ n) =
      1 / ((n + 1 : ℕ) * (2 : ℝ) ^ n) := by
    have he : (fun t : ℝ => ((1 - t) / 2) ^ n) =
        (fun t => (1 - t) ^ n * (2 ^ n)⁻¹) := by
      funext t; rw [div_pow, div_eq_mul_inv]
    rw [he, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_comp_sub_left (fun t : ℝ => t ^ n)]
    simp only [sub_self, sub_zero]
    rw [integral_pow]
    simp only [one_pow, zero_pow (Nat.succ_ne_zero n), sub_zero]
    push_cast
    rw [← inv_pow, ← mul_inv_rev]
    congr 1
    ring
  unfold lowerPolynomial
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_add, intervalIntegral.integral_add]
  · have h1 := hp 1
    simp only [pow_one] at h1
    rw [h1, hp 2, hp 3, hp 4, hp 5]
    norm_num
  all_goals exact (by fun_prop : Continuous _).intervalIntegrable _ _

private theorem integrated_lower_pos {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (θ : ℝ) :
    x * (3067 / 8100) ≤ integratedPoisson x θ := by
  by_cases hx : x = 0
  · simp [hx, integratedPoisson]
  have hchange : integratedPoisson x θ =
      x * ∫ t in (0 : ℝ)..1, poissonDensity (x * t) θ := by
    have hh := intervalIntegral.integral_comp_mul_left
      (fun t => poissonDensity t θ) hx (a := 0) (b := 1)
    rw [hh]
    simp [integratedPoisson, smul_eq_mul, hx]
  have hlo : (367 / 960 : ℝ) ≤ ∫ t in (0 : ℝ)..1, poissonDensity (x * t) θ := by
    rw [← lowerPolynomial_integral]
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((show Continuous lowerPolynomial by unfold lowerPolynomial; fun_prop).intervalIntegrable _ _)
    · apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      simpa only [Function.comp_def, id_eq] using
        (density_continuousOn hx1).comp
          (show ContinuousOn (fun t : ℝ => (x * t, θ)) (Icc (0 : ℝ) 1) by fun_prop)
          (fun t ht => ⟨⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩, mem_univ θ⟩)
    · intro t ht
      have hxt : |x * t| ≤ x := by rw [abs_of_nonneg (mul_nonneg hx0 ht.1)]; nlinarith [ht.2]
      apply (lowerPolynomial_le ht).trans
      apply le_trans _ (density_bounds hx0 hx1 hxt θ).1
      rw [abs_of_nonneg (mul_nonneg hx0 ht.1)]
      apply (div_le_div_iff₀ (by linarith [ht.1] : 0 < 1 + t)
        (by nlinarith [mul_nonneg hx0 ht.1] : 0 < 1 + x * t)).mpr
      nlinarith [ht.1, ht.2]
  rw [hchange]
  exact (mul_le_mul_of_nonneg_left (by norm_num : (3067 / 8100 : ℝ) ≤ 367 / 960) hx0).trans
    (mul_le_mul_of_nonneg_left hlo hx0)

private theorem density_mean {t : ℝ} (ht : |t| < 1) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), poissonDensity t θ) = 2 * Real.pi := by
  have hw : (t : ℂ) ∈ ball (0 : ℂ) 1 := by
    simpa only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using ht
  have hn : (t : ℂ) ∉ sphere (0 : ℂ) |(1 : ℝ)| := by
    simp only [mem_sphere, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_one]
    exact ne_of_lt ht
  have hc : ContinuousOn (poissonKernel 0 (t : ℂ)) (sphere (0 : ℂ) |(1 : ℝ)|) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hn)
  have hi : CircleIntegrable (fun z => poissonKernel 0 (t : ℂ) z • (1 : ℂ)) 0 1 :=
    (hc.smul continuousOn_const).circleIntegrable'
  have hp := (differentiable_const (1 : ℂ)).diffContOnCl.circleAverage_poissonKernel_smul hw
  have hp' : Real.circleAverage (fun z => poissonKernel 0 (t : ℂ) z • (1 : ℂ)) 0 1 = 1 := by
    simpa only [Pi.smul_apply] using hp
  have hh := Complex.reCLM.circleAverage_comp_comm hi
  rw [hp'] at hh
  have havg : (2 * Real.pi)⁻¹ *
      (∫ θ in (0 : ℝ)..(2 * Real.pi), poissonDensity t θ) = 1 := by
    simpa [Real.circleAverage, Function.comp_def, poissonDensity] using hh
  have hmul := congrArg (fun v : ℝ => (2 * Real.pi) * v) havg
  rwa [← mul_assoc, mul_inv_cancel₀ (ne_of_gt Real.two_pi_pos), one_mul, mul_one] at hmul

private theorem integrated_mean_pos {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), integratedPoisson x θ) = 2 * Real.pi * x := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => poissonDensity p.1 p.2)
      (Icc (0 : ℝ) x ×ˢ Icc (0 : ℝ) (2 * Real.pi)) :=
    (density_continuousOn hx1).mono (by
      intro p hp
      exact ⟨⟨by linarith [hp.1.1], hp.1.2⟩, mem_univ p.2⟩)
  have hi := hc.integrableOn_compact (μ := volume.prod volume) (isCompact_Icc.prod isCompact_Icc)
  have hip : Integrable (fun p : ℝ × ℝ => poissonDensity p.1 p.2)
      ((volume.restrict (Ioc (0 : ℝ) x)).prod
        (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    rw [Measure.prod_restrict]
    exact hi.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hswap : (∫ θ in (0 : ℝ)..(2 * Real.pi), integratedPoisson x θ) =
      ∫ t in (0 : ℝ)..x, ∫ θ in (0 : ℝ)..(2 * Real.pi), poissonDensity t θ := by
    simpa only [integratedPoisson, intervalIntegral.integral_of_le hx0,
      intervalIntegral.integral_of_le Real.two_pi_pos.le] using
      (integral_integral_swap hip).symm
  rw [hswap]
  calc
    _ = ∫ _ in (0 : ℝ)..x, (2 * Real.pi) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) x := by simpa [uIcc_of_le hx0] using ht
      exact density_mean (by rw [abs_of_nonneg ht'.1]; exact ht'.2.trans_lt hx1)
    _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]; ring

private theorem l1_pos {b x : ℝ} (hb : b ∈ Icc (0 : ℝ) 1)
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..(2 * Real.pi),
      |integratedPoisson x θ - boundaryKernel b θ|) ≤ 1 := by
  have hx : |x| < 1 := by rwa [abs_of_nonneg hx0]
  have hA := integrated_continuous hx
  have hB := (boundary_kernel_control b 0 hb).1
  have hpoint (θ : ℝ) : |integratedPoisson x θ - boundaryKernel b θ| ≤
      integratedPoisson x θ - boundaryKernel b θ + 2 * (1 - x) * (3067 / 8100) := by
    have hlo := integrated_lower_pos hx0 hx1 θ
    have hsize := (boundary_kernel_control b θ hb).2.2.2.2.2.2.1
    have hupper := (abs_le.mp hsize).2
    apply abs_le.mpr
    constructor <;> nlinarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) Real.two_pi_pos.le
    ((hA.sub hB).abs.intervalIntegrable _ _)
    (((hA.sub hB).add continuous_const).intervalIntegrable _ _) (fun θ _ => hpoint θ)
  change (∫ θ in (0 : ℝ)..(2 * Real.pi), |integratedPoisson x θ - boundaryKernel b θ|) ≤
    ∫ θ in (0 : ℝ)..(2 * Real.pi), integratedPoisson x θ - boundaryKernel b θ +
      2 * (1 - x) * (3067 / 8100) at hi
  rw [intervalIntegral.integral_add ((hA.sub hB).intervalIntegrable _ _)
      intervalIntegrable_const,
    intervalIntegral.integral_sub (hA.intervalIntegrable _ _) (hB.intervalIntegrable _ _),
    integrated_mean_pos hx0 hx1, (boundary_kernel_control b 0 hb).2.2.2.2.2.1,
    intervalIntegral.integral_const] at hi
  have hh := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr Real.two_pi_pos.le)
  have hnorm : (2 * Real.pi)⁻¹ *
      (2 * Real.pi * x - 0 + (2 * Real.pi - 0) • (2 * (1 - x) * (3067 / 8100))) =
      x + 2 * (1 - x) * (3067 / 8100) := by
    rw [smul_eq_mul]
    field_simp
    <;> ring
  rw [hnorm] at hh
  exact hh.trans (by nlinarith)

private theorem kernel_add_pi {b : ℝ} (hb : b ∈ Icc (0 : ℝ) 1) (θ : ℝ) :
    boundaryKernel b (θ + Real.pi) = -boundaryKernel b θ := by
  have heven : boundaryKernel b (-θ) = boundaryKernel b θ := by
    unfold boundaryKernel
    apply tsum_congr
    intro j
    simp only [boundaryTerm, mul_neg, Real.cos_neg]
  have hh := (boundary_kernel_control b (-θ) hb).2.1
  simpa only [sub_neg_eq_add, add_comm Real.pi, heven] using hh

private theorem density_neg (t θ : ℝ) :
    poissonDensity (-t) θ = poissonDensity t (θ + Real.pi) := by
  have hc : circleMap 0 1 (θ + Real.pi) = -circleMap 0 1 θ := by
    rw [← circleMap_neg_radius]
    simp [circleMap_zero]
  unfold poissonDensity poissonKernel
  rw [hc]
  simp only [sub_zero, Complex.ofReal_neg, norm_neg]
  have he : -circleMap 0 1 θ - (t : ℂ) = -(circleMap 0 1 θ - -(t : ℂ)) := by ring
  rw [he, norm_neg]

private theorem integrated_neg (x θ : ℝ) :
    integratedPoisson (-x) θ = -integratedPoisson x (θ + Real.pi) := by
  have hh := intervalIntegral.integral_comp_neg (fun t => poissonDensity t θ) (a := 0) (b := x)
  simp only [neg_zero] at hh
  rw [intervalIntegral.integral_symm] at hh
  calc
    integratedPoisson (-x) θ = -(∫ t in (0 : ℝ)..x, poissonDensity (-t) θ) := by
      rw [hh]
      simp [integratedPoisson]
    _ = _ := by simp_rw [density_neg]; rfl

private theorem l1_periodic (b x : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) :
    Function.Periodic (fun θ => |integratedPoisson x θ - boundaryKernel b θ|) (2 * Real.pi) := by
  intro θ
  have hA : integratedPoisson x (θ + 2 * Real.pi) = integratedPoisson x θ := by
    unfold integratedPoisson
    apply intervalIntegral.integral_congr
    intro t _
    unfold poissonDensity
    rw [periodic_circleMap]
  have hB : boundaryKernel b (θ + 2 * Real.pi) = boundaryKernel b θ := by
    have he : θ + 2 * Real.pi = (θ + Real.pi) + Real.pi := by ring
    rw [he, kernel_add_pi hb, kernel_add_pi hb, neg_neg]
  rw [hA, hB]

/-- The actual signed boundary kernel has normalized L1 norm at most one on the full
strict interior real interval. The parameter edge b=1 is included. -/
theorem boundary_l1_control (b x : ℝ) (hb : b ∈ Icc (0 : ℝ) 1) (hx : |x| < 1) :
    (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..(2 * Real.pi),
      |integratedPoisson x θ - boundaryKernel b θ|) ≤ 1 := by
  by_cases hx0 : 0 ≤ x
  · exact l1_pos hb hx0 (by rwa [abs_of_nonneg hx0] at hx)
  · have hxneg : 0 ≤ -x := by linarith
    have hx1 : -x < 1 := by rwa [abs_of_neg (by linarith : x < 0)] at hx
    have he (θ : ℝ) : |integratedPoisson x θ - boundaryKernel b θ| =
        |integratedPoisson (-x) (θ + Real.pi) - boundaryKernel b (θ + Real.pi)| := by
      have ha := integrated_neg (-x) θ
      simp only [neg_neg] at ha
      rw [ha, kernel_add_pi hb]
      rw [show -integratedPoisson (-x) (θ + Real.pi) - boundaryKernel b θ =
        -(integratedPoisson (-x) (θ + Real.pi) + boundaryKernel b θ) by ring,
        abs_neg, sub_neg_eq_add]
    simp_rw [he]
    rw [intervalIntegral.integral_comp_add_right]
    have hshift := (l1_periodic b (-x) hb).intervalIntegral_add_eq Real.pi 0
    simp only [zero_add, add_zero] at hshift
    rw [show 2 * Real.pi + Real.pi = Real.pi + 2 * Real.pi by ring, hshift]
    exact l1_pos hb hxneg hx1

#print axioms boundary_l1_control

end D5.S3.Analytic.Interpolation.SchurIntegratedKernel
