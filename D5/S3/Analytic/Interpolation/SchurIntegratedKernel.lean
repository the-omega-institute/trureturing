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
    simp only [one_div, inv_pow]
    rw [← mul_inv_rev]
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
    have hfun : poissonKernel 0 (t : ℂ) • (fun _ : ℂ => (1 : ℂ)) =
        (fun z : ℂ => poissonKernel 0 (t : ℂ) z • (1 : ℂ)) := by
      funext z
      rfl
    rwa [hfun] at hp
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
  rw [intervalIntegral.integral_add
      (f := fun θ => integratedPoisson x θ - boundaryKernel b θ)
      (g := fun _ => 2 * (1 - x) * (3067 / 8100))
      ((hA.sub hB).intervalIntegrable _ _) intervalIntegrable_const,
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
  calc
    integratedPoisson (-x) θ = -(∫ t in (0 : ℝ)..x, poissonDensity (-t) θ) := by
      rw [hh]
      exact intervalIntegral.integral_symm (-x) 0
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
  change |integratedPoisson x (θ + 2 * Real.pi) - boundaryKernel b (θ + 2 * Real.pi)| =
    |integratedPoisson x θ - boundaryKernel b θ|
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
    have hangle : (∫ θ in (0 : ℝ)..(2 * Real.pi),
        |integratedPoisson (-x) (θ + Real.pi) - boundaryKernel b (θ + Real.pi)|) =
        ∫ θ in Real.pi..(2 * Real.pi + Real.pi),
          |integratedPoisson (-x) θ - boundaryKernel b θ| := by
      simpa only [zero_add] using intervalIntegral.integral_comp_add_right
        (fun θ => |integratedPoisson (-x) θ - boundaryKernel b θ|) Real.pi
        (a := 0) (b := 2 * Real.pi)
    rw [hangle]
    have hshift := (l1_periodic b (-x) hb).intervalIntegral_add_eq Real.pi 0
    simp only [zero_add, add_zero] at hshift
    rw [show 2 * Real.pi + Real.pi = Real.pi + 2 * Real.pi by ring, hshift]
    exact l1_pos hb hxneg hx1

private theorem rectangle_swap (F : ℝ × ℝ → ℂ) (a c : ℝ) (hac : a ≤ c)
    (hF : ContinuousOn F (Icc a c ×ˢ Icc (0 : ℝ) (2 * Real.pi))) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), ∫ t in a..c, F (t, θ)) =
      ∫ t in a..c, ∫ θ in (0 : ℝ)..(2 * Real.pi), F (t, θ) := by
  have hi := hF.integrableOn_compact (μ := volume.prod volume)
    (isCompact_Icc.prod isCompact_Icc)
  have hip : Integrable F ((volume.restrict (Ioc a c)).prod
      (volume.restrict (Ioc (0 : ℝ) (2 * Real.pi)))) := by
    rw [Measure.prod_restrict]
    exact hi.mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  simpa only [intervalIntegral.integral_of_le hac,
    intervalIntegral.integral_of_le Real.two_pi_pos.le] using (integral_integral_swap (f := fun t θ => F (t, θ)) hip).symm

private theorem oriented_swap (F : ℝ × ℝ → ℂ) (x : ℝ)
    (hF : ContinuousOn F (uIcc (0 : ℝ) x ×ˢ Icc (0 : ℝ) (2 * Real.pi))) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), ∫ t in (0 : ℝ)..x, F (t, θ)) =
      ∫ t in (0 : ℝ)..x, ∫ θ in (0 : ℝ)..(2 * Real.pi), F (t, θ) := by
  rcases le_total 0 x with hx | hx
  · exact rectangle_swap F 0 x hx (by simpa only [uIcc_of_le hx] using hF)
  · have he := rectangle_swap F x 0 hx (by simpa only [uIcc_of_ge hx] using hF)
    simp_rw [intervalIntegral.integral_symm x 0, intervalIntegral.integral_neg]
    exact congrArg Neg.neg he

private theorem integrated_function_representation (h : ℂ → ℂ) (hh : Differentiable ℂ h)
    (x : ℝ) (hx : |x| < 1) :
    (∫ t in (0 : ℝ)..x, h (t : ℂ)) = ((2 * Real.pi)⁻¹ : ℝ) •
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        h (circleMap 0 1 θ) * (integratedPoisson x θ : ℂ)) := by
  let F : ℝ × ℝ → ℂ := fun p => (poissonDensity p.1 p.2 : ℂ) * h (circleMap 0 1 p.2)
  have ht (t : ℝ) (ht : t ∈ uIcc (0 : ℝ) x) : |t| ≤ |x| := by
    exact abs_le.mpr (uIcc_subset_Icc
      (show (0 : ℝ) ∈ Icc (-|x|) |x| by constructor <;> linarith [abs_nonneg x])
      ⟨neg_abs_le x, le_abs_self x⟩ ht)
  have hP : ContinuousOn (fun p : ℝ × ℝ => poissonDensity p.1 p.2)
      (uIcc (0 : ℝ) x ×ˢ Icc (0 : ℝ) (2 * Real.pi)) :=
    (density_continuousOn hx).mono (fun p hp => ⟨abs_le.mp (ht p.1 hp.1), mem_univ p.2⟩)
  have hF : ContinuousOn F (uIcc (0 : ℝ) x ×ˢ Icc (0 : ℝ) (2 * Real.pi)) :=
    (Complex.continuous_ofReal.comp_continuousOn hP).mul
      (hh.continuous.comp (by fun_prop)).continuousOn
  have hswap := oriented_swap F x hF
  have hp (t : ℝ) (ht' : t ∈ uIcc (0 : ℝ) x) : h (t : ℂ) =
      ((2 * Real.pi)⁻¹ : ℝ) • (∫ θ in (0 : ℝ)..(2 * Real.pi), F (t, θ)) := by
    have hw : (t : ℂ) ∈ ball (0 : ℂ) 1 := by
      simpa only [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using
        (ht t ht').trans_lt hx
    have he := hh.diffContOnCl.circleAverage_poissonKernel_smul hw
    simpa only [Real.circleAverage_def, Pi.smul_apply, Pi.smul_apply', F, poissonDensity, Complex.real_smul] using he.symm
  calc
    _ = ∫ t in (0 : ℝ)..x, ((2 * Real.pi)⁻¹ : ℝ) •
        (∫ θ in (0 : ℝ)..(2 * Real.pi), F (t, θ)) :=
      intervalIntegral.integral_congr (fun t ht' => hp t ht')
    _ = ((2 * Real.pi)⁻¹ : ℝ) •
        (∫ t in (0 : ℝ)..x, ∫ θ in (0 : ℝ)..(2 * Real.pi), F (t, θ)) := by
      rw [intervalIntegral.integral_smul]
    _ = ((2 * Real.pi)⁻¹ : ℝ) •
        (∫ θ in (0 : ℝ)..(2 * Real.pi), ∫ t in (0 : ℝ)..x, F (t, θ)) := by rw [hswap]
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro θ _
      dsimp only [F]
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal]
      exact mul_comm _ _

private theorem primitive_error_interior (h H : ℂ → ℂ) (hh : Differentiable ℂ h)
    (hH : ∀ z : ℂ, HasDerivAt H (h z) z) (hH0 : H 0 = 0)
    (b : ℝ) (hb : b ∈ Ioc (0 : ℝ) 1) (x : ℝ) (hx : |x| < 1) :
    ‖H (x : ℂ) - (1 / (2 * b) : ℝ) • (∫ t in -b..b, H ((t : ℂ) * I))‖ ≤
      sSup ((fun z => ‖h z‖) '' closedBall (0 : ℂ) 1) := by
  let M : ℝ := sSup ((fun z => ‖h z‖) '' closedBall (0 : ℂ) 1)
  have hbd : BddAbove ((fun z => ‖h z‖) '' closedBall (0 : ℂ) 1) :=
    (isCompact_closedBall (0 : ℂ) 1).bddAbove_image hh.continuous.norm.continuousOn
  have hM (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) 1) : ‖h z‖ ≤ M :=
    le_csSup hbd ⟨z, hz, rfl⟩
  have hM0 : 0 ≤ M := (norm_nonneg (h 0)).trans (hM 0 (by simp))
  have hMb (θ : ℝ) : ‖h (circleMap 0 1 θ)‖ ≤ M :=
    hM _ (by simp only [mem_closedBall, dist_zero_right, circle_norm, le_refl])
  have hFTC : (∫ t in (0 : ℝ)..x, h (t : ℂ)) = H (x : ℂ) := by
    simpa only [Complex.ofReal_zero, hH0, sub_zero] using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t (_ : t ∈ uIcc (0 : ℝ) x) => (hH (t : ℂ)).comp_ofReal)
        ((hh.continuous.comp Complex.continuous_ofReal).intervalIntegrable 0 x))
  have hA : H (x : ℂ) = ((2 * Real.pi)⁻¹ : ℝ) •
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        h (circleMap 0 1 θ) * (integratedPoisson x θ : ℂ)) :=
    hFTC.symm.trans (integrated_function_representation h hh x hx)
  have hB := boundary_primitive_representation h H hh hH hH0 b hb
  have hK : Continuous (fun θ => integratedPoisson x θ - boundaryKernel b θ) :=
    (integrated_continuous hx).sub (boundary_kernel_control b 0 ⟨hb.1.le, hb.2⟩).1
  have hhc : Continuous (fun θ : ℝ => h (circleMap 0 1 θ)) := hh.continuous.comp (by fun_prop)
  have hcA : Continuous (fun θ => h (circleMap 0 1 θ) * (integratedPoisson x θ : ℂ)) :=
    hhc.mul (Complex.continuous_ofReal.comp (integrated_continuous hx))
  have hcB : Continuous (fun θ => h (circleMap 0 1 θ) * (boundaryKernel b θ : ℂ)) :=
    hhc.mul (Complex.continuous_ofReal.comp (boundary_kernel_control b 0 ⟨hb.1.le, hb.2⟩).1)
  have hcK : Continuous (fun θ => h (circleMap 0 1 θ) *
      ((integratedPoisson x θ - boundaryKernel b θ : ℝ) : ℂ)) :=
    hhc.mul (Complex.continuous_ofReal.comp hK)
  have he : H (x : ℂ) - (1 / (2 * b) : ℝ) • (∫ t in -b..b, H ((t : ℂ) * I)) =
      ((2 * Real.pi)⁻¹ : ℝ) • (∫ θ in (0 : ℝ)..(2 * Real.pi),
        h (circleMap 0 1 θ) * ((integratedPoisson x θ - boundaryKernel b θ : ℝ) : ℂ)) := by
    rw [hA, hB, ← smul_sub,
      ← intervalIntegral.integral_sub (hcA.intervalIntegrable _ _) (hcB.intervalIntegrable _ _)]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only
    push_cast
    ring
  rw [he, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr Real.two_pi_pos.le)]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..(2 * Real.pi),
        ‖h (circleMap 0 1 θ) * ((integratedPoisson x θ - boundaryKernel b θ : ℝ) : ℂ)‖) :=
      mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm
        Real.two_pi_pos.le) (inv_nonneg.mpr Real.two_pi_pos.le)
    _ ≤ (2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..(2 * Real.pi),
        M * |integratedPoisson x θ - boundaryKernel b θ|) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr Real.two_pi_pos.le)
      apply intervalIntegral.integral_mono_on Real.two_pi_pos.le
        (hcK.norm.intervalIntegrable _ _) ((continuous_const.mul hK.abs).intervalIntegrable _ _)
      intro θ _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hMb θ) (abs_nonneg _)
    _ = M * ((2 * Real.pi)⁻¹ * (∫ θ in (0 : ℝ)..(2 * Real.pi),
        |integratedPoisson x θ - boundaryKernel b θ|)) := by
      rw [intervalIntegral.integral_const_mul]
      ring
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left
      (boundary_l1_control b x ⟨hb.1.le, hb.2⟩ hx) hM0
    _ = M := mul_one M

/-- The actual primitive functional is bounded by the original closed-disk norm on the
full closed real interval and the full closed parameter edge. -/
theorem primitive_error_bound (h H : ℂ → ℂ) (hh : Differentiable ℂ h)
    (hH : ∀ z : ℂ, HasDerivAt H (h z) z) (hH0 : H 0 = 0)
    (b : ℝ) (hb : b ∈ Ioc (0 : ℝ) 1) (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    ‖H (x : ℂ) - (1 / (2 * b) : ℝ) • (∫ t in -b..b, H ((t : ℂ) * I))‖ ≤
      sSup ((fun z => ‖h z‖) '' closedBall (0 : ℂ) 1) := by
  have hHc : Continuous H := (show Differentiable ℂ H from fun z => (hH z).differentiableAt).continuous
  have hc : Continuous (fun x : ℝ =>
      ‖H (x : ℂ) - (1 / (2 * b) : ℝ) • (∫ t in -b..b, H ((t : ℂ) * I))‖) :=
    ((hHc.comp Complex.continuous_ofReal).sub continuous_const).norm
  have hcl : closure (Ioo (-1 : ℝ) 1) = Icc (-1 : ℝ) 1 := closure_Ioo (by norm_num)
  exact le_on_closure (s := Ioo (-1 : ℝ) 1)
    (f := fun x : ℝ => ‖H (x : ℂ) - (1 / (2 * b) : ℝ) •
      (∫ t in -b..b, H ((t : ℂ) * I))‖)
    (g := fun _ => sSup ((fun z => ‖h z‖) '' closedBall (0 : ℂ) 1))
    (fun y hy => primitive_error_interior h H hh hH hH0 b hb y (abs_lt.mpr hy))
    hc.continuousOn continuousOn_const (by simpa only [hcl] using hx)

#print axioms boundary_l1_control
#print axioms primitive_error_bound

end D5.S3.Analytic.Interpolation.SchurIntegratedKernel
