/- GID: D5/S3/Fourier/Asymptotics/GaussianFrequencyKernel
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/GaussianFrequencyKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian-weighted cosine kernels have an integrable continuous same-noise quotient. -/

import D5.S3.Fourier.Asymptotics.SameNoiseSecondChaos
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.WithDensityFinite
open MeasureTheory ProbabilityTheory Filter
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

theorem frequency_continuous : Continuous (gaussianFrequency c κ hc hκ) := by
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
  apply LipschitzWith.continuous (K := ((Real.pi/2)*‖g‖).toNNReal)
  apply LipschitzWith.of_dist_le_mul
  intro v u
  simpa only [dist_eq_norm, Real.norm_eq_abs, Real.coe_toNNReal _ hC] using hb v u

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
  have hb (a : Lp ℝ 2 μ →₀ ℝ) :
      ‖finiteNoiseMap μ P W hW a‖ ≤ Real.sqrt 2 * ‖finiteKernelMap μ a‖ := by
    have h := finiteGram μ P W hW a a
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
    have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    have he : (Real.sqrt 2 * ‖finiteKernelMap μ a‖)^2 = 2 * ‖finiteKernelMap μ a‖^2 :=
      by rw [mul_pow, hs]
    have hn : 0 ≤ Real.sqrt 2 * ‖finiteKernelMap μ a‖ := by positivity
    nlinarith [norm_nonneg (finiteNoiseMap μ P W hW a)]
  have he : secondIntegral μ P W hW (gaussianFrequency c κ hc hκ v) =
      finiteSecondIntegral μ P W hW (frequencyKernel μ v) := by
    change (finiteNoiseMap μ P W hW).extendOfNorm (finiteKernelMap μ)
      (finiteKernelMap μ (frequencyCoefficients μ v)) = _
    rw [LinearMap.extendOfNorm_eq (finiteKernelMap_dense μ) ⟨Real.sqrt 2, hb⟩]
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
      ∫ v in Set.Icc 0 (Real.exp s), v⁻¹ • quadraticFrequency c κ hc hκ P W hW v := by
  let := spatialMeasure_finite c κ hc hκ
  have he (v : ℝ) : secondIntegral (spatialMeasure c κ) P W hW
      (quotientFrequency c κ hc hκ v) =
      v⁻¹ • quadraticFrequency c κ hc hκ P W hW v := by
    rw [quotientFrequency, map_smul, (quadraticFrequency_representation c κ hc hκ P W hW v).1]
  constructor
  · have h := (secondIntegral (spatialMeasure c κ) P W hW).integrable_comp
      (quotientFrequency_integrable c κ hc hκ s)
    simpa only [IntegrableOn, Function.comp_def, he] using h
  · rw [← (secondIntegral (spatialMeasure c κ) P W hW).integral_comp_comm
      (quotientFrequency_integrable c κ hc hκ s)]
    apply integral_congr_ae
    exact ae_of_all _ he

end Frequency
end D5.S3.Fourier.Asymptotics.GaussianFrequencyKernel
