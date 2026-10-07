/- GID: D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel
   generality: I
   mirror-B: D5/B/S3/Fourier/Asymptotics/GaussianFrequencyKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian cosine quotients are Bochner integrable and the logarithmic singular kernel belongs to symmetric L2. -/

import D5.S3.Fourier.Asymptotics.SameNoiseSecondChaos
import D5.S3.Fourier.Asymptotics.CosineNormalizedRemainder
import D5.S3.Fourier.Asymptotics.L2ContinuousPrimitive
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.WithDensityFinite
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Set
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace D5.S3.Fourier.Asymptotics.GaussianFrequencyKernel
open SameNoiseSecondChaos

def spatialMeasure (c κ : ℝ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (c * Real.exp (-κ*x^2/2)))
def spatialMass (c κ : ℝ) : ℝ := c * Real.sqrt (2 * Real.pi / κ)

theorem spatialMeasure_normalized (c κ : ℝ) (hc : 0 ≤ c) (hκ : 0 < κ) :
    spatialMeasure c κ = ENNReal.ofReal (spatialMass c κ) •
      gaussianReal 0 (1 / κ).toNNReal := by
  have hv : (1 / κ).toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr (by positivity))
  have hr : 0 < Real.sqrt (2 * Real.pi / κ) := by positivity
  have hd : (fun x : ℝ => ENNReal.ofReal (c * Real.exp (-κ*x^2/2))) =
      ENNReal.ofReal (spatialMass c κ) • gaussianPDF 0 (1/κ).toNNReal := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, gaussianPDF]
    rw [← ENNReal.ofReal_mul (show 0 ≤ spatialMass c κ by unfold spatialMass; positivity)]
    congr 1
    unfold spatialMass gaussianPDFReal
    rw [Real.coe_toNNReal (1/κ) (by positivity), sub_zero]
    have he : -(x^2)/(2*(1/κ)) = -κ*x^2/2 := by field_simp
    rw [he]
    have hs : 2 * Real.pi * (1 / κ) = 2 * Real.pi / κ := by ring
    rw [hs, mul_assoc, ← mul_assoc (Real.sqrt _) (Real.sqrt _)⁻¹,
      mul_inv_cancel₀ hr.ne', one_mul]
  unfold spatialMeasure
  rw [hd, withDensity_smul (μ := volume) _ (measurable_gaussianPDF _ _),
    ← gaussianReal_of_var_ne_zero 0 hv]

theorem spatialMass_eq_integral (c κ : ℝ) (hc : 0 ≤ c) (hκ : 0 < κ) :
    spatialMass c κ = ∫ x : ℝ, c * Real.exp (-κ*x^2/2) := by
  have hi : (∫ _ : ℝ, (1 : ℝ) ∂spatialMeasure c κ) = spatialMass c κ := by
    rw [spatialMeasure_normalized c κ hc hκ, integral_smul_measure]
    simp [ENNReal.toReal_ofReal (show 0 ≤ spatialMass c κ by unfold spatialMass; positivity)]
  rw [← hi, spatialMeasure,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [] with x
  change (ENNReal.ofReal (c * Real.exp (-κ*x^2/2))).toReal * 1 = _
  rw [ENNReal.toReal_ofReal (mul_nonneg hc (Real.exp_pos _).le), mul_one]

theorem spatialMeasure_finite (c κ : ℝ) (hc : 0 ≤ c) (hκ : 0 < κ) :
    IsFiniteMeasure (spatialMeasure c κ) := by
  rw [spatialMeasure_normalized c κ hc hκ]
  exact ⟨by simp [Measure.smul_apply]⟩

theorem gaussian_difference_law (v : ℝ≥0) :
    ((gaussianReal 0 v).prod (gaussianReal 0 v)).map
      (fun z : ℝ × ℝ => z.1-z.2) = gaussianReal 0 (v+v) := by
  have h := gaussianReal_add_gaussianReal_of_indepFun (m₁ := 0) (m₂ := 0) (v₁ := v) (v₂ := v)
    (indepFun_prod (μ := gaussianReal 0 v) (ν := gaussianReal 0 v)
      measurable_id (measurable_neg : Measurable (fun x : ℝ => -x)))
  have hf : ((gaussianReal 0 v).prod (gaussianReal 0 v)).map
      (fun z : ℝ × ℝ => z.1) = gaussianReal 0 v := by simp
  have hg : ((gaussianReal 0 v).prod (gaussianReal 0 v)).map
      (fun z : ℝ × ℝ => -z.2) = gaussianReal 0 v := by
    rw [← Function.comp_def, ← Measure.map_map measurable_neg measurable_snd]
    simp [gaussianReal_map_neg]
  simpa only [Pi.add_def, id_eq, sub_eq_add_neg, zero_add] using h hf hg

theorem gaussian_fourth (v : ℝ≥0) :
    (∫ x : ℝ, x^4 ∂gaussianReal 0 v) = 3 * (v : ℝ)^2 := by
  have h := CountableGaussianQuadraticFourthMoment.centralMoment_two_mul
    0 (NNReal.sqrt v) 2
  have hv : NNReal.sqrt v ^ 2 = v := NNReal.sq_sqrt v
  rw [hv] at h
  have hs : (Real.sqrt (v : ℝ))^2 = (v : ℝ) := Real.sq_sqrt v.property
  have hp : (Real.sqrt (v : ℝ))^4 = (v : ℝ)^2 := by nlinarith
  simpa [centralMoment, integral_id_gaussianReal, hp, mul_comm] using h

theorem spatial_difference_fourth (c κ : ℝ) (hc : 0 ≤ c) (hκ : 0 < κ) :
    (∫ z : ℝ × ℝ, (z.1-z.2)^4 ∂(spatialMeasure c κ).prod (spatialMeasure c κ)) =
      12 * (∫ x : ℝ, c * Real.exp (-κ*x^2/2)) ^ 2 / κ^2 := by
  rw [← spatialMass_eq_integral c κ hc hκ]
  rw [spatialMeasure_normalized c κ hc hκ, Measure.prod_smul_left,
    Measure.prod_smul_right, integral_smul_measure, integral_smul_measure]
  have hi : (∫ z : ℝ × ℝ, (z.1-z.2)^4
      ∂(gaussianReal 0 (1/κ).toNNReal).prod (gaussianReal 0 (1/κ).toNNReal)) =
      3 * (((1/κ).toNNReal + (1/κ).toNNReal : ℝ≥0) : ℝ)^2 := by
    rw [← gaussian_fourth, ← gaussian_difference_law]
    exact (integral_map (μ := (gaussianReal 0 (1/κ).toNNReal).prod (gaussianReal 0 (1/κ).toNNReal))
      (φ := fun z : ℝ × ℝ => z.1-z.2) (f := fun x : ℝ => x^4) (by fun_prop) (by fun_prop)).symm
  rw [hi]
  simp only [ENNReal.toReal_ofReal (show 0 ≤ spatialMass c κ by unfold spatialMass; positivity),
    smul_eq_mul, NNReal.coe_add, Real.coe_toNNReal (1/κ) (by positivity)]
  ring

theorem spatial_difference_fourth_integrable (c κ : ℝ) (hc : 0 ≤ c) (hκ : 0 < κ) :
    Integrable (fun z : ℝ × ℝ => (z.1-z.2)^4)
      ((spatialMeasure c κ).prod (spatialMeasure c κ)) := by
  rw [spatialMeasure_normalized c κ hc hκ, Measure.prod_smul_left, Measure.prod_smul_right]
  apply Integrable.smul_measure _ (by simp)
  apply Integrable.smul_measure _ (by simp)
  have hi : Integrable (fun x : ℝ => x^4)
      (gaussianReal 0 ((1/κ).toNNReal + (1/κ).toNNReal)) := by
    apply ((memLp_id_gaussianReal (μ := 0)
      (v := (1/κ).toNNReal + (1/κ).toNNReal) 4).integrable_norm_pow' (p := 4)).mono'
      (by fun_prop)
    filter_upwards [] with x
    simp [norm_pow]
  rw [← gaussian_difference_law] at hi
  exact hi.comp_measurable (by fun_prop)

section Frequency
variable (c κ : ℝ) (hc : 0 ≤ c) (hκ : 0 < κ)

def squareDifference : Lp ℝ 2 ((spatialMeasure c κ).prod (spatialMeasure c κ)) :=
  ((memLp_two_iff_integrable_sq (by fun_prop)).mpr
    (by simpa only [← pow_mul] using spatial_difference_fourth_integrable c κ hc hκ)).toLp
    (fun z : ℝ × ℝ => (z.1-z.2)^2)

theorem squareDifference_coe : squareDifference c κ hc hκ =ᵐ[(spatialMeasure c κ).prod
    (spatialMeasure c κ)] (fun z : ℝ × ℝ => (z.1-z.2)^2) := MemLp.coeFn_toLp _

theorem squareDifference_norm : ‖squareDifference c κ hc hκ‖ =
    2 * Real.sqrt 3 * spatialMass c κ / κ := by
  have hn : ‖squareDifference c κ hc hκ‖^2 = 12 * spatialMass c κ^2 / κ^2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    calc (∫ z : ℝ × ℝ, inner ℝ (squareDifference c κ hc hκ z)
        (squareDifference c κ hc hκ z) ∂(spatialMeasure c κ).prod (spatialMeasure c κ)) =
        ∫ z : ℝ × ℝ, (z.1-z.2)^4 ∂(spatialMeasure c κ).prod (spatialMeasure c κ) := by
          apply integral_congr_ae
          filter_upwards [squareDifference_coe c κ hc hκ] with z hz
          rw [hz]
          simp only [RCLike.inner_apply, conj_trivial]
          ring
         _ = _ := by
           simpa only [← spatialMass_eq_integral c κ hc hκ] using
             spatial_difference_fourth c κ hc hκ
  have hmass : 0 ≤ spatialMass c κ := by unfold spatialMass; positivity
  have hs : (Real.sqrt 3)^2 = 3 := Real.sq_sqrt (by norm_num)
  have he : (2 * Real.sqrt 3 * spatialMass c κ / κ)^2 =
      12 * spatialMass c κ^2 / κ^2 := by rw [div_pow]; ring_nf; rw [hs]; ring
  have hp : 0 ≤ 2 * Real.sqrt 3 * spatialMass c κ / κ := by positivity
  nlinarith [norm_nonneg (squareDifference c κ hc hκ)]

def gaussianFrequency (v : ℝ) :
    (letI := spatialMeasure_finite c κ hc hκ; symmetricKernel (spatialMeasure c κ)) :=
  letI := spatialMeasure_finite c κ hc hκ
  (frequencyKernel (spatialMeasure c κ) v).val

theorem gaussianFrequency_coe (v : ℝ) :
    (gaussianFrequency c κ hc hκ v).val =ᵐ[(spatialMeasure c κ).prod (spatialMeasure c κ)]
      (fun z : ℝ × ℝ => Real.cos ((Real.pi/2)*v*(z.1-z.2))-1) := by
  let := spatialMeasure_finite c κ hc hκ
  exact frequencyKernel_coe (spatialMeasure c κ) v

theorem frequency_norm_bound (v : ℝ) :
    ‖gaussianFrequency c κ hc hκ v‖ ≤
      Real.sqrt 3 * (Real.pi/2)^2 * spatialMass c κ * v^2 / κ := by
  have hb : ‖(gaussianFrequency c κ hc hκ v).val‖ ≤
      ((Real.pi/2)^2 * v^2 / 2) * ‖squareDifference c κ hc hκ‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [gaussianFrequency_coe c κ hc hκ v,
      squareDifference_coe c κ hc hκ] with z hd hq
    rw [hd, hq, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (z.1-z.2)),
      abs_of_nonpos (sub_nonpos.mpr (Real.cos_le_one _))]
    have h := Real.one_sub_sq_div_two_le_cos (x := (Real.pi/2)*v*(z.1-z.2))
    nlinarith
  rw [squareDifference_norm c κ hc hκ] at hb
  change ‖(gaussianFrequency c κ hc hκ v).val‖ ≤ _
  convert hb using 1
  ring

theorem frequency_lipschitz :
    ∃ K : ℝ≥0, LipschitzWith K (gaussianFrequency c κ hc hκ) := by
  let := spatialMeasure_finite c κ hc hκ
  let g : Lp ℝ 2 ((spatialMeasure c κ).prod (spatialMeasure c κ)) :=
    (memLp_const (1 : ℝ)).toLp (fun _ => 1) + squareDifference c κ hc hκ
  have hb (v u : ℝ) : ‖gaussianFrequency c κ hc hκ v - gaussianFrequency c κ hc hκ u‖ ≤
      ((Real.pi/2)*‖g‖) * |v-u| := by
    change ‖(gaussianFrequency c κ hc hκ v).val - (gaussianFrequency c κ hc hκ u).val‖ ≤ _
    have hn : ‖(gaussianFrequency c κ hc hκ v).val - (gaussianFrequency c κ hc hκ u).val‖ ≤
        ((Real.pi/2)*|v-u|) * ‖g‖ := by
      apply Lp.norm_le_mul_norm_of_ae_le_mul
      filter_upwards [Lp.coeFn_sub (gaussianFrequency c κ hc hκ v).val
          (gaussianFrequency c κ hc hκ u).val,
        gaussianFrequency_coe c κ hc hκ v, gaussianFrequency_coe c κ hc hκ u,
        Lp.coeFn_add ((memLp_const (1 : ℝ)).toLp (fun _ => 1)) (squareDifference c κ hc hκ),
        (memLp_const (1 : ℝ)).coeFn_toLp, squareDifference_coe c κ hc hκ] with z hd hv hu hg h1 hq
      change ‖((gaussianFrequency c κ hc hκ v).val -
        (gaussianFrequency c κ hc hκ u).val) z‖ ≤ _ * ‖g z‖
      dsimp only [g]
      have heD : ((gaussianFrequency c κ hc hκ v).val -
          (gaussianFrequency c κ hc hκ u).val) z =
          (Real.cos ((Real.pi/2)*v*(z.1-z.2))-1)-
          (Real.cos ((Real.pi/2)*u*(z.1-z.2))-1) := by
        calc _ = (gaussianFrequency c κ hc hκ v).val z -
                 (gaussianFrequency c κ hc hκ u).val z := hd
             _ = _ := congrArg₂ (fun x y : ℝ => x-y) hv hu
      have heG : g z = 1+(z.1-z.2)^2 := by
        calc _ = ((memLp_const (1 : ℝ)).toLp (fun _ => 1)) z +
                 squareDifference c κ hc hκ z := hg
             _ = _ := congrArg₂ (fun x y : ℝ => x+y) h1 hq
      rw [heD, heG, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (show 0 ≤ 1+(z.1-z.2)^2 by positivity)]
      calc |(Real.cos ((Real.pi/2)*v*(z.1-z.2))-1)-
            (Real.cos ((Real.pi/2)*u*(z.1-z.2))-1)| =
          |Real.cos ((Real.pi/2)*v*(z.1-z.2))-Real.cos ((Real.pi/2)*u*(z.1-z.2))| := by congr 1; ring
        _ ≤ |(Real.pi/2)*v*(z.1-z.2)-(Real.pi/2)*u*(z.1-z.2)| := Real.abs_cos_sub_cos_le _ _
        _ = ((Real.pi/2)*|v-u|)*|z.1-z.2| := by
          rw [show (Real.pi/2)*v*(z.1-z.2)-(Real.pi/2)*u*(z.1-z.2) =
            (Real.pi/2)*(v-u)*(z.1-z.2) by ring, abs_mul, abs_mul,
            abs_of_nonneg (show 0 ≤ Real.pi/2 by positivity)]
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          nlinarith [sq_abs (z.1-z.2), sq_nonneg (|z.1-z.2|-1)]
    nlinarith [hn]
  have hC : 0 ≤ (Real.pi/2)*‖g‖ := by positivity
  refine ⟨((Real.pi/2)*‖g‖).toNNReal, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro v u
  simpa only [dist_eq_norm, Real.norm_eq_abs, Real.coe_toNNReal _ hC] using hb v u

theorem frequency_continuous : Continuous (gaussianFrequency c κ hc hκ) :=
  (frequency_lipschitz c κ hc hκ).choose_spec.continuous

def quotientFrequency (v : ℝ) :
    (letI := spatialMeasure_finite c κ hc hκ; symmetricKernel (spatialMeasure c κ)) :=
  v⁻¹ • gaussianFrequency c κ hc hκ v

theorem quotientFrequency_norm (v : ℝ) : ‖quotientFrequency c κ hc hκ v‖ ≤
    (Real.sqrt 3 * (Real.pi/2)^2 * spatialMass c κ / κ) * |v| := by
  by_cases hv : v = 0
  · simp [quotientFrequency, hv]
  rw [quotientFrequency, norm_smul, Real.norm_eq_abs]
  calc |v⁻¹| * ‖gaussianFrequency c κ hc hκ v‖ ≤
      |v⁻¹| * (Real.sqrt 3 * (Real.pi/2)^2 * spatialMass c κ * v^2 / κ) :=
        mul_le_mul_of_nonneg_left (frequency_norm_bound c κ hc hκ v) (abs_nonneg _)
    _ = _ := by rw [abs_inv, ← sq_abs v]; field_simp

theorem quotientFrequency_continuous : Continuous (quotientFrequency c κ hc hκ) := by
  apply continuous_iff_continuousAt.mpr
  intro v
  by_cases hv : v = 0
  · subst v
    have hn : Tendsto (fun u => ‖quotientFrequency c κ hc hκ u‖) (𝓝 0) (𝓝 0) := by
      apply squeeze_zero (fun u => norm_nonneg _) (quotientFrequency_norm c κ hc hκ)
      have hcont : Continuous (fun u : ℝ =>
        (Real.sqrt 3 * (Real.pi/2)^2 * spatialMass c κ / κ) * |u|) :=
        continuous_const.mul continuous_id.abs
      simpa using hcont.tendsto (0 : ℝ)
    have ht : Tendsto (quotientFrequency c κ hc hκ) (𝓝 0) (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr hn
    change Tendsto (quotientFrequency c κ hc hκ) (𝓝 0)
      (𝓝 (quotientFrequency c κ hc hκ 0))
    simpa only [quotientFrequency, inv_zero, zero_smul] using ht
  · exact (continuousAt_inv₀ hv).smul (frequency_continuous c κ hc hκ).continuousAt

theorem quotientFrequency_integrable (s : ℝ) :
    IntegrableOn (quotientFrequency c κ hc hκ) (Set.Icc 0 (Real.exp s)) volume :=
  (quotientFrequency_continuous c κ hc hκ).integrableOn_Icc

theorem frequency_integral_coe (s : ℝ) :
    letI := spatialMeasure_finite c κ hc hκ
    (∫ v in Set.Icc 0 (Real.exp s), quotientFrequency c κ hc hκ v).val
      =ᵐ[(spatialMeasure c κ).prod (spatialMeasure c κ)]
        (fun z : ℝ × ℝ => ∫ v in (0 : ℝ)..Real.exp s,
          (Real.cos ((Real.pi/2)*v*(z.1-z.2))-1)/v) := by
  letI := spatialMeasure_finite c κ hc hκ
  let μ := (spatialMeasure c κ).prod (spatialMeasure c κ)
  let u : ℝ → Lp ℝ 2 μ := fun v => (quotientFrequency c κ hc hκ v).val
  let f : ℝ → Lp ℝ 2 μ := fun t => ∫ v in (0 : ℝ)..t, u v
  let g : ℝ → (ℝ × ℝ) → ℝ := fun v z =>
    (Real.cos ((Real.pi/2)*v*(z.1-z.2))-1)/v
  have hu : Continuous u := (symmetricKernel (spatialMeasure c κ)).subtypeL.continuous.comp
    (quotientFrequency_continuous c κ hc hκ)
  have hg : Measurable (Function.uncurry g) := by
    dsimp [g, Function.uncurry]
    fun_prop
  have heq (v : ℝ) : g v =ᵐ[μ] (fun z => u v z) := by
    filter_upwards [Lp.coeFn_smul (v⁻¹) (gaussianFrequency c κ hc hκ v).val,
      gaussianFrequency_coe c κ hc hκ v] with z hs hf
    change _ = (v⁻¹ • (gaussianFrequency c κ hc hκ v).val) z
    rw [hs]
    change (Real.cos ((Real.pi/2)*v*(z.1-z.2))-1)/v =
      v⁻¹ * (gaussianFrequency c κ hc hκ v).val z
    rw [hf]
    ring
  have hf (t : ℝ) : f t = f 0 + ∫ v in (0 : ℝ)..t, u v := by simp [f]
  have h := (L2ContinuousPrimitive.result μ f u g hu hg heq hf).2.2 (Real.exp s)
  have hmap : (∫ v in (0 : ℝ)..Real.exp s, u v) =
      (∫ v in Set.Icc 0 (Real.exp s), quotientFrequency c κ hc hκ v).val := by
    rw [intervalIntegral.integral_of_le (Real.exp_pos s).le,
      ← integral_Icc_eq_integral_Ioc]
    exact (symmetricKernel (spatialMeasure c κ)).subtypeL.integral_comp_comm
      (quotientFrequency_integrable c κ hc hκ s)
  filter_upwards [h, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)] with z hz hzero
  change f 0 z + (∫ v in (0 : ℝ)..Real.exp s, g v z) = f (Real.exp s) z at hz
  have hf0 : f 0 = 0 := by simp [f]
  rw [hf0, hzero] at hz
  simp only [Pi.zero_apply, zero_add] at hz
  rw [← hmap]
  exact hz.symm

def regularKernel (D s : ℝ) :
    (letI := spatialMeasure_finite c κ hc hκ; symmetricKernel (spatialMeasure c κ)) :=
  letI := spatialMeasure_finite c κ hc hκ
  (1+2*Real.eulerMascheroniConstant+2*D+2*s) •
    diagonalKernel (spatialMeasure c κ) (oneVector (spatialMeasure c κ)) +
    (2 : ℝ) • ∫ v in Set.Icc 0 (Real.exp s), quotientFrequency c κ hc hκ v

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]
variable (W : Lp ℝ 2 (spatialMeasure c κ) →ₗᵢ[ℝ] Lp ℝ 2 P)
variable (hW : ∀ f : Lp ℝ 2 (spatialMeasure c κ),
  HasLaw (fun ω => W f ω) (gaussianReal 0 (‖f‖ ^ 2).toNNReal) P)

def quadraticFrequency (v : ℝ) : Lp ℝ 2 P :=
  letI := spatialMeasure_finite c κ hc hκ
  centeredSquare (spatialMeasure c κ) P W hW (cosineVector (spatialMeasure c κ) v) +
  centeredSquare (spatialMeasure c κ) P W hW (sineVector (spatialMeasure c κ) v) -
  centeredSquare (spatialMeasure c κ) P W hW (oneVector (spatialMeasure c κ))

theorem quadraticFrequency_representation (v : ℝ) :
    letI := spatialMeasure_finite c κ hc hκ
    secondIntegral (spatialMeasure c κ) P W hW (gaussianFrequency c κ hc hκ v) =
      quadraticFrequency c κ hc hκ P W hW v ∧
    quadraticFrequency c κ hc hκ P W hW v =ᵐ[P]
      (fun ω => (W (cosineVector (spatialMeasure c κ) v) ω)^2 +
        (W (sineVector (spatialMeasure c κ) v) ω)^2 -
        (W (oneVector (spatialMeasure c κ)) ω)^2) := by
  let := spatialMeasure_finite c κ hc hκ
  let μ := spatialMeasure c κ
  have he : secondIntegral μ P W hW (gaussianFrequency c κ hc hκ v) =
      finiteSecondIntegral μ P W hW (frequencyKernel μ v) := by
    change (finiteNoiseMap μ P W hW).extendOfNorm (finiteKernelMap μ)
      (finiteKernelMap μ (frequencyCoefficients μ v)) = _
    rw [LinearMap.extendOfNorm_eq (finiteKernelMap_dense μ)
      ⟨Real.sqrt 2, finiteBound μ P W hW⟩]
    exact (finiteSecondIntegral_apply μ P W hW (frequencyCoefficients μ v)).symm
  have hq : finiteSecondIntegral μ P W hW (frequencyKernel μ v) =
      quadraticFrequency c κ hc hκ P W hW v := by
    rw [frequencyKernel, finiteSecondIntegral_apply]
    simp [quadraticFrequency, μ, frequencyCoefficients, finiteNoiseMap]
  exact ⟨he.trans hq, hq ▸ finiteFrequency_sameNoise μ P W hW v⟩

theorem frequency_integral_sameNoise (s : ℝ) :
    letI := spatialMeasure_finite c κ hc hκ
    IntegrableOn (fun v => v⁻¹ • quadraticFrequency c κ hc hκ P W hW v)
      (Set.Icc 0 (Real.exp s)) volume ∧
    secondIntegral (spatialMeasure c κ) P W hW
      (∫ v in Set.Icc 0 (Real.exp s), quotientFrequency c κ hc hκ v) =
      ∫ v in Set.Icc 0 (Real.exp s), v⁻¹ • quadraticFrequency c κ hc hκ P W hW v ∧
    ∀ (D : ℝ) (H : symmetricKernel (spatialMeasure c κ)),
      secondIntegral (spatialMeasure c κ) P W hW
        (regularKernel c κ hc hκ D s - H) =
        (1+2*Real.eulerMascheroniConstant+2*D+2*s) •
          centeredSquare (spatialMeasure c κ) P W hW (oneVector (spatialMeasure c κ)) +
          (2 : ℝ) • (∫ v in Set.Icc 0 (Real.exp s),
            v⁻¹ • quadraticFrequency c κ hc hκ P W hW v) -
          secondIntegral (spatialMeasure c κ) P W hW H := by
  let := spatialMeasure_finite c κ hc hκ
  have he (v : ℝ) : secondIntegral (spatialMeasure c κ) P W hW
      (quotientFrequency c κ hc hκ v) =
      v⁻¹ • quadraticFrequency c κ hc hκ P W hW v := by
    rw [quotientFrequency, map_smul, (quadraticFrequency_representation c κ hc hκ P W hW v).1]
  constructor
  · have h := (secondIntegral (spatialMeasure c κ) P W hW).integrable_comp
      (quotientFrequency_integrable c κ hc hκ s)
    simpa only [IntegrableOn, Function.comp_def, he] using h
  · have hcomm : secondIntegral (spatialMeasure c κ) P W hW
        (∫ v in Set.Icc 0 (Real.exp s), quotientFrequency c κ hc hκ v) =
        ∫ v in Set.Icc 0 (Real.exp s), v⁻¹ • quadraticFrequency c κ hc hκ P W hW v := by
      rw [← (secondIntegral (spatialMeasure c κ) P W hW).integral_comp_comm
        (quotientFrequency_integrable c κ hc hκ s)]
      apply integral_congr_ae
      exact ae_of_all _ he
    refine ⟨hcomm, ?_⟩
    intro D H
    rw [map_sub, regularKernel, map_add, map_smul, map_smul,
      secondIntegral_diagonal, hcomm]


theorem regularKernel_difference (D s : ℝ)
    (H : (letI := spatialMeasure_finite c κ hc hκ; symmetricKernel (spatialMeasure c κ)))
    (hH : H.val =ᵐ[(spatialMeasure c κ).prod (spatialMeasure c κ)]
      (fun z : ℝ × ℝ => 1+2*D-2*Real.log ((Real.pi/2)*|z.1-z.2|))) :
    letI := spatialMeasure_finite c κ hc hκ
    (regularKernel c κ hc hκ D s - H).val
      =ᵐ[(spatialMeasure c κ).prod (spatialMeasure c κ)]
        (fun z : ℝ × ℝ => 2 * CosineIntegralLattice.cosineIntegral
          ((Real.pi/2)*Real.exp s*|z.1-z.2|)) := by
  letI := spatialMeasure_finite c κ hc hκ
  let μ := spatialMeasure c κ
  let J := ∫ v in Set.Icc 0 (Real.exp s), quotientFrequency c κ hc hκ v
  let A := diagonalKernel μ (oneVector μ)
  let b := 1+2*Real.eulerMascheroniConstant+2*D+2*s
  letI : NullSingletonClass μ := by dsimp [μ, spatialMeasure]; infer_instance
  have hdiag : ∀ᵐ z ∂μ.prod μ, z.1-z.2 ≠ 0 := by
    apply (ae_prod_iff_ae_ae ((measurableSet_eq_fun (measurable_fst.sub measurable_snd) measurable_const).compl : MeasurableSet {z : ℝ × ℝ | z.1-z.2 ≠ 0})).mpr
    exact ae_of_all _ fun x => (Measure.ae_ne μ x).mono fun y hy => sub_ne_zero.mpr hy.symm
  have hA : A.val =ᵐ[μ.prod μ] (fun _ => (1 : ℝ)) := by
    have hf := (quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq (oneVector_coe μ)
    have hs := (quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq (oneVector_coe μ)
    filter_upwards [rankOne_coe μ (oneVector μ) (oneVector μ), hf, hs] with z hz hf hs
    change rankOne μ (oneVector μ) (oneVector μ) z = 1
    change oneVector μ z.1 = 1 at hf
    change oneVector μ z.2 = 1 at hs
    rw [hz, hf, hs, one_mul]
  have he : (regularKernel c κ hc hκ D s - H).val =ᵐ[μ.prod μ]
      (fun z : ℝ × ℝ => b+2*(∫ v in (0 : ℝ)..Real.exp s,
        (Real.cos ((Real.pi/2)*v*(z.1-z.2))-1)/v)-H.val z) := by
    filter_upwards [Lp.coeFn_sub (regularKernel c κ hc hκ D s).val H.val,
      Lp.coeFn_add (b • A.val) ((2 : ℝ) • J.val),
      Lp.coeFn_smul b A.val, Lp.coeFn_smul (2 : ℝ) J.val,
      hA, frequency_integral_coe c κ hc hκ s] with z hsub hadd hb htwo hA hJ
    change ((regularKernel c κ hc hκ D s).val-H.val) z = _
    rw [hsub]
    change (b • A.val + (2 : ℝ) • J.val) z - H.val z = _
    rw [hadd]
    change J.val z = _ at hJ
    simp only [Pi.add_apply, hb, htwo, Pi.smul_apply, smul_eq_mul, hA, hJ, mul_one]
  filter_upwards [he, hH, hdiag] with z hz hH hz0
  rw [hz, hH]
  let k := (Real.pi/2)*|z.1-z.2|
  have hk : 0 < k := mul_pos (by positivity) (abs_pos.mpr hz0)
  have hcos (v : ℝ) : Real.cos ((Real.pi/2)*v*(z.1-z.2)) = Real.cos (k*v) := by
    by_cases hd : 0 ≤ z.1-z.2
    · dsimp [k]; rw [abs_of_nonneg hd]; congr 1; ring
    · have hd' : z.1-z.2 ≤ 0 := le_of_not_ge hd
      dsimp [k]; rw [abs_of_nonpos hd']
      rw [show (Real.pi/2)*(-(z.1-z.2))*v = -((Real.pi/2)*v*(z.1-z.2)) by ring, Real.cos_neg]
  have hscale : (∫ v in (0 : ℝ)..Real.exp s,
      (Real.cos ((Real.pi/2)*v*(z.1-z.2))-1)/v) =
      ∫ t in (0 : ℝ)..(k*Real.exp s), (Real.cos t-1)/t := by
    calc
      _ = k * ∫ v in (0 : ℝ)..Real.exp s, (Real.cos (k*v)-1)/(k*v) := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro v _
        change (Real.cos ((Real.pi/2)*v*(z.1-z.2))-1)/v =
          k*((Real.cos (k*v)-1)/(k*v))
        rw [hcos]
        by_cases hv : v = 0
        · simp [hv]
        · field_simp [hk.ne', hv]
      _ = _ := by
        simpa only [smul_eq_mul, mul_zero] using
          (intervalIntegral.smul_integral_comp_mul_left
            (fun t : ℝ => (Real.cos t-1)/t) k (a := 0) (b := Real.exp s))
  have hCi := CosineNormalizedRemainder.positive_normalization (k*Real.exp s)
    (mul_pos hk (Real.exp_pos s))
  rw [Real.log_mul hk.ne' (Real.exp_pos s).ne', Real.log_exp] at hCi
  rw [hscale]
  rw [show (Real.pi/2)*Real.exp s*|z.1-z.2| = k*Real.exp s by dsimp [k]; ring, hCi]
  dsimp [b, k]
  ring

end Frequency
theorem log_square_bound (x : ℝ) (hx : 0 < x) :
    (Real.log x)^2 ≤ 16 * x ^ (-1/2 : ℝ) + x^2 := by
  by_cases h1 : x ≤ 1
  · have hl : Real.log x ≤ 0 := Real.log_nonpos hx.le h1
    have h := Real.log_le_rpow_div (inv_nonneg.mpr hx.le) (by norm_num : (0 : ℝ) < 1/4)
    rw [Real.log_inv, ← Real.rpow_neg_eq_inv_rpow] at h
    have hp : 0 ≤ x ^ (-1/4 : ℝ) := Real.rpow_nonneg hx.le _
    have he : (x ^ (-1/4 : ℝ))^2 = x ^ (-1/2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
    have hb : (Real.log x)^2 ≤ 16 * (x ^ (-1/4 : ℝ))^2 := by
      norm_num at h; nlinarith
    rw [he] at hb
    nlinarith [sq_nonneg x]
  · have hl : 0 ≤ Real.log x := Real.log_nonneg (le_of_not_ge h1)
    have hb := Real.log_le_sub_one_of_pos hx
    have hp : 0 ≤ x ^ (-1/2 : ℝ) := Real.rpow_nonneg hx.le _
    nlinarith

theorem log_square_gaussian_integrable (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => (Real.log |x|)^2 * Real.exp (-b*x^2)) := by
  have hi : IntegrableOn (fun x : ℝ => (Real.log |x|)^2 * Real.exp (-b*x^2)) (Ioi 0) := by
    have hmaj := ((integrableOn_rpow_mul_exp_neg_mul_sq hb
      (by norm_num : (-1 : ℝ) < -1/2)).const_mul 16).add
      (integrableOn_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 2))
    apply hmaj.mono' (by fun_prop)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [abs_of_pos hx]
    dsimp only [Pi.add_apply]
    rw [Real.rpow_two]
    have H := log_square_bound x hx
    nlinarith [Real.exp_pos (-b*x^2)]
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hi⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  simpa only [Function.comp_def, abs_neg, neg_sq, neg_preimage, neg_Iio, neg_zero] using hi

theorem gaussian_log_square_integrable (v : ℝ≥0) (hv : v ≠ 0) :
    Integrable (fun x : ℝ => (Real.log |x|)^2) (gaussianReal 0 v) := by
  rw [gaussianReal_of_var_ne_zero 0 hv]
  apply (integrable_withDensity_iff_integrable_smul' (μ := volume) (measurable_gaussianPDF 0 v)
    (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))).mpr
  have hvpos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have h := (log_square_gaussian_integrable (1/(2*(v : ℝ))) (by positivity)).const_mul
    (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
  apply h.congr
  filter_upwards [] with x
  simp only [gaussianPDF]
  rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 v x)]
  simp only [smul_eq_mul, gaussianPDFReal, sub_zero]
  rw [show -(1/(2*(v : ℝ)))*x^2 = -(x^2)/(2*(v : ℝ)) by ring]
  ring


theorem singularKernel_exists (c κ : ℝ) (hc : 0 ≤ c) (hκ : 0 < κ) (D : ℝ) :
    letI := spatialMeasure_finite c κ hc hκ
    ∃ H : symmetricKernel (spatialMeasure c κ),
      H.val =ᵐ[(spatialMeasure c κ).prod (spatialMeasure c κ)]
        (fun z : ℝ × ℝ => 1+2*D-2*Real.log ((Real.pi/2)*|z.1-z.2|)) ∧
      ∀ s : ℝ, (regularKernel c κ hc hκ D s - H).val
        =ᵐ[(spatialMeasure c κ).prod (spatialMeasure c κ)]
          (fun z : ℝ × ℝ => 2 * CosineIntegralLattice.cosineIntegral
            ((Real.pi/2)*Real.exp s*|z.1-z.2|)) := by
  letI := spatialMeasure_finite c κ hc hκ
  let v : ℝ≥0 := (1/κ).toNNReal
  have hv : v+v ≠ 0 := by
    have : 0 < v := Real.toNNReal_pos.mpr (by positivity)
    positivity
  let ν := gaussianReal 0 (v+v)
  letI : NullSingletonClass ν := nullSingletonClass_gaussianReal hv
  have hlog : MemLp (fun x : ℝ => Real.log |x|) 2 ν :=
    (memLp_two_iff_integrable_sq (Real.measurable_log.comp measurable_abs).aestronglyMeasurable).mpr (gaussian_log_square_integrable (v+v) hv)
  have hm : MemLp (fun x : ℝ => 1+2*D-2*Real.log ((Real.pi/2)*|x|)) 2 ν := by
    have H := (memLp_const (1+2*D-2*Real.log (Real.pi/2)) (p := 2) (μ := ν)).sub
      (hlog.const_mul 2)
    apply H.ae_eq
    filter_upwards [Measure.ae_ne ν 0] with x hx
    simp only [Pi.sub_apply]
    rw [Real.log_mul (by positivity : Real.pi/2 ≠ 0) (abs_ne_zero.mpr hx)]
    ring
  have hmprod : MemLp (fun z : ℝ × ℝ =>
      1+2*D-2*Real.log ((Real.pi/2)*|z.1-z.2|)) 2
      ((gaussianReal 0 v).prod (gaussianReal 0 v)) := by
    rw [show ν = ((gaussianReal 0 v).prod (gaussianReal 0 v)).map
      (fun z : ℝ × ℝ => z.1-z.2) by exact (gaussian_difference_law v).symm] at hm
    exact hm.comp_of_map (by fun_prop)
  have hmw : MemLp (fun z : ℝ × ℝ =>
      1+2*D-2*Real.log ((Real.pi/2)*|z.1-z.2|)) 2
      ((spatialMeasure c κ).prod (spatialMeasure c κ)) := by
    rw [spatialMeasure_normalized c κ hc hκ, Measure.prod_smul_left, Measure.prod_smul_right]
    exact (hmprod.smul_measure (by simp)).smul_measure (by simp)
  let h : Lp ℝ 2 ((spatialMeasure c κ).prod (spatialMeasure c κ)) := hmw.toLp _
  have he : h =ᵐ[(spatialMeasure c κ).prod (spatialMeasure c κ)]
      (fun z : ℝ × ℝ => 1+2*D-2*Real.log ((Real.pi/2)*|z.1-z.2|)) := hmw.coeFn_toLp
  have hsym : h ∈ symmetricKernel (spatialMeasure c κ) := by
    change kernelFlip (spatialMeasure c κ) h - h = 0
    apply sub_eq_zero.mpr
    apply Lp.ext
    have hs := (measurePreserving_swap (μ := spatialMeasure c κ) (ν := spatialMeasure c κ)).quasiMeasurePreserving.ae_eq he
    have hf := Lp.coeFn_compMeasurePreserving h
      (measurePreserving_swap (μ := spatialMeasure c κ) (ν := spatialMeasure c κ))
    filter_upwards [hf, hs, he] with z hz hswap hrep
    change h (Prod.swap z) = 1+2*D-2*Real.log ((Real.pi/2)*|z.2-z.1|) at hswap
    exact hz.trans (hswap.trans (by rw [abs_sub_comm]; exact hrep.symm))
  exact ⟨⟨h, hsym⟩, he, fun s => regularKernel_difference c κ hc hκ D s ⟨h, hsym⟩ he⟩

#print axioms frequency_integral_coe
#print axioms regularKernel_difference
#print axioms frequency_integral_sameNoise
#print axioms singularKernel_exists
end D5.S3.Fourier.Asymptotics.GaussianFrequencyKernel
