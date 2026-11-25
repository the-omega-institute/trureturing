/- GID: D5/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentArcsine
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/NoncommutingQubit/PetzTangentArcsine
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact arcsine moments for qubit tangent profiles, including repeated poles. -/

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Exact arcsine moments via the positive reciprocal coordinate. -/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter

namespace D5.S3.Quantum.Recovery.PetzTangentArcsine

def arcsineDensity (z : ℝ) : ℝ := (Real.pi * Real.sqrt (1 - z ^ 2))⁻¹

abbrev arcIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : E :=
  ∫ z in Ioo (-1 : ℝ) 1, arcsineDensity z • f z

def kernel (x z : ℝ) : ℝ := (1 - (1 - x ^ 2) * z ^ 2)⁻¹

lemma affine_pos {b z : ℝ} (hb : b ^ 2 < 1) (hz : z ∈ Icc (-1 : ℝ) 1) :
    0 < 1 - b * z := by
  have hL : 0 ≤ 1 + z := by linarith [hz.1]
  have hR : 0 ≤ 1 - z := sub_nonneg.mpr hz.2
  have hz2 : z ^ 2 ≤ 1 := by nlinarith [mul_nonneg hR hL]
  have hbz : (b*z)^2 < 1 := by
    rw [mul_pow]
    exact (mul_le_of_le_one_right (sq_nonneg b) hz2).trans_lt hb
  nlinarith

lemma kernelDen_pos {x z : ℝ} (hx : 0 < x) (hz : z ∈ Icc (-1 : ℝ) 1) :
    0 < 1 - (1 - x ^ 2) * z ^ 2 := by
  have hL : 0 ≤ 1 + z := by linarith [hz.1]
  have hR : 0 ≤ 1 - z := sub_nonneg.mpr hz.2
  have hz2 : z ^ 2 ≤ 1 := by nlinarith [mul_nonneg hR hL]
  rcases le_or_gt x 1 with h | h
  · have h' : 0 ≤ 1 - x ^ 2 := by nlinarith
    nlinarith [mul_le_of_le_one_right h' hz2]
  · have h' : 0 ≤ x ^ 2 - 1 := by nlinarith
    nlinarith [mul_nonneg h' (sq_nonneg z)]

lemma continuousOn_kernel {x : ℝ} (hx : 0 < x) :
    ContinuousOn (kernel x) (Icc (-1 : ℝ) 1) := by
  unfold kernel
  have hc : Continuous (fun z : ℝ => 1-(1-x^2)*z^2) := by fun_prop
  exact hc.continuousOn.inv₀ (fun _ hz => (kernelDen_pos hx hz).ne')

-- The same substitution gives the arcsine moments and the uniform energy.
def reciprocal (r : ℝ) : ℝ := (Real.sqrt (1+r))⁻¹
def jacobian (r : ℝ) : ℝ := (2 * Real.sqrt (1+r) ^ 3)⁻¹

lemma reciprocal_sq {r : ℝ} (hr : 0 < r) :
    reciprocal r ^ 2 = (1+r)⁻¹ := by
  rw [reciprocal, inv_pow, Real.sq_sqrt (by positivity : 0 ≤ 1+r)]

lemma reciprocal_pos {r : ℝ} (hr : 0 < r) : 0 < reciprocal r :=
  inv_pos.mpr (Real.sqrt_pos.2 (by positivity))

private lemma reciprocal_image : reciprocal '' Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 := by
  ext z
  constructor
  · rintro ⟨r, hr, rfl⟩
    have hr' : 0 < r := hr
    have h := reciprocal_pos hr'
    have hs := reciprocal_sq hr'
    have hsq : (1+r)⁻¹ < 1 := (inv_lt_one₀ (by positivity)).2 (by linarith)
    exact ⟨h, by nlinarith⟩
  · intro hz
    have hz0 : 0 < z := hz.1
    have hz1 : z < 1 := hz.2
    have hzsq : 0 < z ^ 2 := sq_pos_of_pos hz0
    refine ⟨(z^2)⁻¹-1, ?_, ?_⟩
    · change 0 < (z^2)⁻¹-1
      rw [sub_pos, one_lt_inv₀ hzsq]
      nlinarith
    · unfold reciprocal
      rw [show 1 + ((z^2)⁻¹-1) = (z^2)⁻¹ by ring,
        Real.sqrt_inv, Real.sqrt_sq hz0.le, inv_inv]

private lemma reciprocal_inj : InjOn reciprocal (Ioi (0 : ℝ)) := by
  intro r hr s hs h
  have h' := congrArg (fun y : ℝ => (y^2)⁻¹) h
  change (reciprocal r ^ 2)⁻¹ = (reciprocal s ^ 2)⁻¹ at h'
  rw [reciprocal_sq hr, reciprocal_sq hs, inv_inv, inv_inv] at h'
  linarith

private lemma reciprocal_deriv (r : ℝ) (hr : 0 < r) :
    HasDerivAt reciprocal (-jacobian r) r := by
  have hr1 : 0 < 1+r := by positivity
  have h := ((Real.hasDerivAt_sqrt hr1.ne').comp r
    ((hasDerivAt_id r).const_add 1)).inv (Real.sqrt_pos.2 hr1).ne'
  convert h using 1 <;> first | rfl | (simp only [jacobian, Function.comp_apply, mul_one]; field_simp [(Real.sqrt_pos.2 hr1).ne'])

lemma reciprocal_change {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) :
    (∫ z in Ioo (0 : ℝ) 1, f z) = ∫ r in Ioi (0 : ℝ), jacobian r • f (reciprocal r) := by
  rw [← reciprocal_image]
  refine (integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun r hr => (reciprocal_deriv r hr).hasDerivWithinAt) reciprocal_inj f).trans ?_
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [abs_neg, abs_of_nonneg (by unfold jacobian; positivity)]

lemma fold_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : ℝ → E} (hf : IntegrableOn f (Ioo (-1 : ℝ) 1)) :
    (∫ z in Ioo (-1 : ℝ) 1, f z) = ∫ z in Ioo (0 : ℝ) 1, (f z + f (-z)) := by
  have hi : IntervalIntegrable f volume (-1) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hf
  have hl : IntervalIntegrable f volume (-1) 0 := hi.mono_set (by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0), uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact Icc_subset_Icc_right zero_le_one)
  have hr : IntervalIntegrable f volume 0 1 := hi.mono_set (by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1), uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact Icc_subset_Icc_left (by norm_num))
  have hn : IntervalIntegrable (fun z => f (-z)) volume 0 1 := by
    simpa using (IntervalIntegrable.iff_comp_neg (f := f)
      (a := (0 : ℝ)) (b := -1)).1 hl.symm
  simp only [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le
    (by norm_num : (-1 : ℝ) ≤ 1), ← intervalIntegral.integral_of_le zero_le_one]
  rw [← intervalIntegral.integral_add_adjacent_intervals hl hr,
    intervalIntegral.integral_add hr hn]
  rw [intervalIntegral.integral_comp_neg]
  simp [add_comm]

private def quadratic (a t : ℝ) : ℝ := (a^2+t^2)⁻¹

private lemma quadratic_scale (a t : ℝ) :
    quadratic a (a*t) = (a^2)⁻¹ * quadratic 1 t := by
  unfold quadratic
  rw [show a^2+(a*t)^2 = a^2*(1^2+t^2) by ring, mul_inv]

private lemma quadratic_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (quadratic a) (Ioi (0 : ℝ)) := by
  have hUnit : IntegrableOn (quadratic 1) (Ioi (0 : ℝ)) := by
    change IntegrableOn (fun t : ℝ => (1^2+t^2)⁻¹) (Ioi 0)
    simpa only [one_pow] using integrable_inv_one_add_sq.integrableOn
  have hScaled : IntegrableOn (fun t => quadratic a (a*t)) (Ioi (0 : ℝ)) :=
    (integrableOn_congr_fun (fun t _ => quadratic_scale a t) measurableSet_Ioi).2
      (hUnit.const_mul (a^2)⁻¹)
  simpa only [mul_zero] using
    (integrableOn_Ioi_comp_mul_left_iff (quadratic a) 0 ha).1 hScaled

private lemma quadratic_integral {a : ℝ} (ha : 0 < a) :
    (∫ t in Ioi (0 : ℝ), quadratic a t) = Real.pi / (2*a) := by
  have h := integral_comp_mul_left_Ioi' (quadratic a) 0 ha
  simp only [mul_zero, quadratic_scale a, smul_eq_mul] at h
  rw [integral_const_mul,
    show quadratic 1 = (fun t : ℝ => (1+t^2)⁻¹) by funext t; simp [quadratic],
    integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero] at h
  rw [← h]
  field_simp [ha.ne'] <;> ring

private lemma quadratic_product_integrable {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t => quadratic a t * quadratic b t) (Ioi (0 : ℝ)) := by
  apply Integrable.mono' ((quadratic_integrable ha).const_mul (b^2)⁻¹)
  · have h (x : ℝ) (hx : 0 < x) : Continuous (quadratic x) :=
      (continuous_const.add (continuous_id.pow 2)).inv₀ (fun t => by
        change x^2+t^2 ≠ 0
        positivity)
    exact ((h a ha).mul (h b hb)).aestronglyMeasurable
  · filter_upwards with t
    change ‖quadratic a t * quadratic b t‖ ≤ (b^2)⁻¹ * quadratic a t
    unfold quadratic
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [mul_comm ((b^2)⁻¹)]
    exact mul_le_mul_of_nonneg_left
      ((inv_le_inv₀ (by positivity : 0 < b^2+t^2) (sq_pos_of_pos hb)).2
        (le_add_of_nonneg_right (sq_nonneg t)))
      (by positivity)

private lemma quadratic_product_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Ioi (0 : ℝ), quadratic a t * quadratic b t) =
      Real.pi / (2*a*b*(a+b)) := by
  by_cases hab : a = b
  · subst b
    -- The inverse-power substitution t ↦ t⁻¹ exchanges q² and t²q².
    have hInv := integral_comp_rpow_Ioi (fun t => quadratic 1 t * quadratic 1 t)
      (p := (-1 : ℝ)) (by norm_num)
    have hEq : (∫ t in Ioi (0 : ℝ), t^2 * (quadratic 1 t * quadratic 1 t)) =
        ∫ t in Ioi (0 : ℝ), quadratic 1 t * quadratic 1 t := by
      refine (setIntegral_congr_fun measurableSet_Ioi ?_).trans hInv
      intro t ht
      have ht0 : 0 < t := ht
      have h₁ : t ^ (-1 : ℝ) = t⁻¹ := by rw [Real.rpow_neg ht0.le, Real.rpow_one]
      have h₂ : t ^ (-2 : ℝ) = (t^2)⁻¹ := by rw [Real.rpow_neg ht0.le, Real.rpow_two]
      norm_num [quadratic, smul_eq_mul, h₁, h₂]
      field_simp [ht0.ne', show 1 + t^2 ≠ 0 by positivity,
        show 1 + (t⁻¹)^2 ≠ 0 by positivity] <;> ring
    have hPoint (t : ℝ) : t^2 * (quadratic 1 t * quadratic 1 t) =
        quadratic 1 t - quadratic 1 t * quadratic 1 t := by
      unfold quadratic
      field_simp [show 1^2+t^2 ≠ 0 by positivity] <;> ring
    have h1 : 0 < (1 : ℝ) := one_pos
    simp_rw [hPoint] at hEq
    rw [integral_sub (quadratic_integrable h1) (quadratic_product_integrable h1 h1),
      quadratic_integral h1] at hEq
    have hUnit : (∫ t in Ioi (0 : ℝ), quadratic 1 t * quadratic 1 t) = Real.pi/4 := by
      linarith
    have hScale := integral_comp_mul_left_Ioi'
      (fun t => quadratic a t * quadratic a t) 0 ha
    simp only [mul_zero, quadratic_scale a, smul_eq_mul] at hScale
    have hProd (t : ℝ) :
        ((a^2)⁻¹ * quadratic 1 t) * ((a^2)⁻¹ * quadratic 1 t) =
          ((a^2)⁻¹)^2 * (quadratic 1 t * quadratic 1 t) := by ring
    simp_rw [hProd] at hScale
    rw [integral_const_mul, hUnit] at hScale
    rw [← hScale]
    field_simp [ha.ne', (add_pos ha ha).ne'] <;> ring
  · have hDiff : b^2-a^2 ≠ 0 := by
      intro h
      apply hab
      rcases mul_eq_zero.mp (show (b-a)*(b+a) = 0 by nlinarith) with e | e
      · linarith
      · linarith
    have h := calc
      (∫ t in Ioi (0 : ℝ), quadratic a t * quadratic b t) =
          ∫ t in Ioi (0 : ℝ), (b^2-a^2)⁻¹ * (quadratic a t - quadratic b t) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _
        unfold quadratic
        field_simp [hDiff, show a^2+t^2 ≠ 0 by positivity,
          show b^2+t^2 ≠ 0 by positivity] <;> ring
      _ = (b^2-a^2)⁻¹ * (Real.pi/(2*a) - Real.pi/(2*b)) := by
        rw [integral_const_mul, integral_sub (quadratic_integrable ha) (quadratic_integrable hb),
          quadratic_integral ha, quadratic_integral hb]
    rw [h]
    field_simp [ha.ne', hb.ne', (add_pos ha hb).ne', hDiff] <;> ring

-- r = t² in the positive reciprocal variable.
private lemma square_change (f : ℝ → ℝ) :
    (∫ r in Ioi (0 : ℝ), (Real.sqrt r)⁻¹ * f r) =
      2 * ∫ t in Ioi (0 : ℝ), f (t^2) := by
  rw [← integral_comp_rpow_Ioi (fun r => (Real.sqrt r)⁻¹ * f r)
    (p := (2 : ℝ)) (by norm_num), ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have ht0 : 0 < t := ht
  norm_num [Real.rpow_two, Real.sqrt_sq ht0.le, smul_eq_mul]
  field_simp [ht0.ne'] <;> ring

private lemma density_jacobian {r : ℝ} (hr : 0 < r) :
    jacobian r * arcsineDensity (reciprocal r) =
      (2 * Real.pi * Real.sqrt r * (1+r))⁻¹ := by
  have hr1 : 0 < 1+r := by positivity
  have hp : 0 < Real.sqrt (1+r) := Real.sqrt_pos.2 hr1
  have hr' : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  unfold arcsineDensity jacobian
  rw [reciprocal_sq hr, show 1-(1+r)⁻¹ = r/(1+r) by field_simp [hr1.ne'] <;> ring,
    Real.sqrt_div hr.le]
  have hs := Real.sq_sqrt hr1.le
  generalize Real.sqrt (1+r) = v at hs hp ⊢
  rw [← hs]
  field_simp [hp.ne', hr'.ne', Real.pi_ne_zero] <;> ring

lemma kernel_reciprocal {x r : ℝ} (hx : 0 < x) (hr : 0 < r) :
    kernel x (reciprocal r) = (1+r)/(x^2+r) := by
  unfold kernel
  rw [reciprocal_sq hr, show 1-(1-x^2)*(1+r)⁻¹ = (x^2+r)/(1+r) by
    field_simp [show 1+r ≠ 0 by positivity] <;> ring, inv_div]

private lemma density_integrable : IntegrableOn arcsineDensity (Ioo (-1 : ℝ) 1) := by
  have hHalf : IntegrableOn arcsineDensity (Ioo (0 : ℝ) 1) := by
    rw [← reciprocal_image, integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioi (fun r hr => (reciprocal_deriv r hr).hasDerivWithinAt)
      reciprocal_inj]
    have h := (integrableOn_Ioi_comp_rpow_iff
      (fun r : ℝ => (2 * Real.pi * Real.sqrt r * (1+r))⁻¹)
      (p := (2 : ℝ)) (by norm_num)).1
    have hr : IntegrableOn (fun r : ℝ => (2 * Real.pi * Real.sqrt r * (1+r))⁻¹) (Ioi 0) := by
      apply h
      refine (integrableOn_congr_fun (g := fun t : ℝ => Real.pi⁻¹ * (1+t^2)⁻¹)
        ?_ measurableSet_Ioi).2 (integrable_inv_one_add_sq.integrableOn.const_mul _)
      intro t ht
      have ht0 : 0 < t := ht
      norm_num [Real.rpow_two, Real.sqrt_sq ht0.le, smul_eq_mul]
      field_simp [ht0.ne', Real.pi_ne_zero, show 1+t^2 ≠ 0 by positivity] <;> ring
    refine (integrableOn_congr_fun ?_ measurableSet_Ioi).2 hr
    intro r hr
    have hr0 : 0 < r := hr
    dsimp only
    rw [abs_neg, abs_of_nonneg (by unfold jacobian; positivity), smul_eq_mul,
      density_jacobian hr0]
  have hi : IntervalIntegrable arcsineDensity volume 0 1 := by
    rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
      integrableOn_Ioc_iff_integrableOn_Ioo]
  have hn : IntervalIntegrable (fun z => arcsineDensity (-z)) volume 0 1 := by
    convert hi using 1
    funext z
    simp only [arcsineDensity, neg_sq]
  have hl := (IntervalIntegrable.iff_comp_neg (f := arcsineDensity)
    (a := (0 : ℝ)) (b := -1)).2 (by simpa using hn)
  have hl' : IntervalIntegrable arcsineDensity volume (-1) 0 := by simpa using hl.symm
  have hf := hl'.trans hi
  rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    integrableOn_Ioc_iff_integrableOn_Ioo] at hf

lemma arc_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    IntegrableOn (fun z => arcsineDensity z • f z) (Ioo (-1 : ℝ) 1) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hf.norm).bddAbove
  apply Integrable.mono' (density_integrable.const_mul C)
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioo
    apply ContinuousOn.smul _ (hf.mono Ioo_subset_Icc_self)
    unfold arcsineDensity
    refine (continuous_const.mul (Real.continuous_sqrt.comp
      (continuous_const.sub (continuous_id.pow 2)))).continuousOn.inv₀ ?_
    intro z hz
    change Real.pi * Real.sqrt (1 - z^2) ≠ 0
    exact mul_ne_zero Real.pi_ne_zero (Real.sqrt_pos.2 (by
      nlinarith [mul_pos (show 0 < 1-z by linarith [hz.2])
        (show 0 < 1+z by linarith [hz.1])])).ne'
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    have hnorm : ‖f z‖ ≤ C := hC ⟨z, Ioo_subset_Icc_self hz, rfl⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by unfold arcsineDensity; positivity),
      mul_comm C]
    exact mul_le_mul_of_nonneg_left hnorm (by unfold arcsineDensity; positivity)

private lemma arc_even {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1 : ℝ) 1))
    (he : ∀ z, f (-z) = f z) :
    arcIntegral f = 2 * ∫ r in Ioi (0 : ℝ),
      (2 * Real.pi * Real.sqrt r * (1+r))⁻¹ * f (reciprocal r) := by
  unfold arcIntegral
  rw [fold_integral (arc_integrable hf)]
  have hFold : (∫ z in Ioo (0 : ℝ) 1, arcsineDensity z • f z +
      arcsineDensity (-z) • f (-z)) =
        2 * ∫ z in Ioo (0 : ℝ) 1, arcsineDensity z * f z := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro z _
    have hd : arcsineDensity (-z) = arcsineDensity z := by simp [arcsineDensity]
    simp only [smul_eq_mul, hd, he z, two_mul]
  rw [hFold, reciprocal_change (fun z => arcsineDensity z * f z)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro r hr
  dsimp only
  rw [smul_eq_mul, ← mul_assoc, density_jacobian hr]

/-- First formula (6), with the actual arcsine density on (-1,1). -/
theorem arcsine_even_moment (x : ℝ) (hx : 0 < x) :
    arcIntegral (kernel x) = 1/x := by
  rw [arc_even (continuousOn_kernel hx) (fun z => by simp [kernel])]
  have h : (∫ r in Ioi (0 : ℝ), (2*Real.pi*Real.sqrt r*(1+r))⁻¹ *
      kernel x (reciprocal r)) =
      (2*Real.pi)⁻¹ * ∫ r in Ioi (0 : ℝ), (Real.sqrt r)⁻¹ * (x^2+r)⁻¹ := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hr0 : 0 < r := hr
    dsimp only
    rw [kernel_reciprocal hx hr0]
    field_simp [Real.pi_ne_zero, (Real.sqrt_pos.2 hr0).ne',
      show 1+r ≠ 0 by positivity, show x^2+r ≠ 0 by positivity] <;> ring
  rw [h, square_change]
  change 2 * ((2*Real.pi)⁻¹ * (2 * ∫ t in Ioi (0 : ℝ), quadratic x t)) = _
  rw [quadratic_integral hx]
  field_simp [Real.pi_ne_zero, hx.ne'] <;> ring

/-- Second formula (6) in node variables. It includes x = g. -/
theorem arcsine_odd_node_moment (x g : ℝ) (hx : 0 < x) (hg : 0 < g) :
    g * arcIntegral (fun z => z^2 * kernel x z * kernel g z) = 1/(x*(x+g)) := by
  have hc : ContinuousOn (fun z => z^2 * kernel x z * kernel g z) (Icc (-1 : ℝ) 1) :=
    ((continuous_id.pow 2).continuousOn.mul (continuousOn_kernel hx)).mul
    (continuousOn_kernel hg)
  rw [arc_even hc (fun z => by simp [kernel])]
  have h : (∫ r in Ioi (0 : ℝ), (2*Real.pi*Real.sqrt r*(1+r))⁻¹ *
      (reciprocal r ^ 2 * kernel x (reciprocal r) * kernel g (reciprocal r))) =
      (2*Real.pi)⁻¹ * ∫ r in Ioi (0 : ℝ), (Real.sqrt r)⁻¹ * ((x^2+r)⁻¹ * (g^2+r)⁻¹) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hr0 : 0 < r := hr
    dsimp only
    rw [kernel_reciprocal hx hr0, kernel_reciprocal hg hr0, reciprocal_sq hr0]
    field_simp [Real.pi_ne_zero, (Real.sqrt_pos.2 hr0).ne',
      show 1+r ≠ 0 by positivity, show x^2+r ≠ 0 by positivity,
      show g^2+r ≠ 0 by positivity] <;> ring
  rw [h, square_change]
  change g * (2 * ((2*Real.pi)⁻¹ *
    (2 * ∫ t in Ioi (0 : ℝ), quadratic x t * quadratic g t))) = _
  rw [quadratic_product_integral hx hg]
  field_simp [Real.pi_ne_zero, hx.ne', hg.ne', (add_pos hx hg).ne'] <;> ring

end D5.S3.Quantum.Recovery.PetzTangentArcsine
