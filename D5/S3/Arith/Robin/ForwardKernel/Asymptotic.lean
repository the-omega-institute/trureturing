/- GID: D5/S3/Arith/Robin/ForwardKernel/Asymptotic
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/Asymptotic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The normalized forward adjoint integrand has a uniform first-order C1 error. -/

import D5.S3.Arith.Robin.ForwardKernel.Remainder
import D5.S3.Arith.Robin.ForwardKernel.WeightControl
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Prod

namespace D5.S3.Arith.Robin.ForwardKernel.Asymptotic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set MeasureTheory Filter
open scoped Topology ENNReal
open ForwardKernel.Remainder ForwardKernel.WeightControl
open OriginalMovingWindowMoment (width)

/-- The coefficient left after extracting the principal Mellin power. -/
def normalizedBody (t z u : ℝ) (s : ℂ) : ℂ :=
  normalizedPower t z s * (weightRatio (coordinate t z) u : ℂ) * (jacobianFactor t z : ℂ)

/-- An explicit constant, locally bounded in the complex Mellin parameter. -/
def kernelConstant (s : ℂ) : ℝ :=
  (2 * ‖-s - 1 / 2‖ + 50) * Real.exp (2 * ‖-s - 1 / 2‖) + 10

private lemma coordinate_power_one {t z : ℝ} (ht : 2 ≤ t)
    (hz : z ∈ Icc (0 : ℝ) 1) :
    coordinate t z ^ (-1 / 5 : ℝ) ≤ 2 * t ^ (-1 / 5 : ℝ) := by
  have h := coordinate_neg_power ht hz (show (0 : ℝ) ≤ 1 / 5 by norm_num)
  have htwo : (2 : ℝ) ^ (1 / 5 : ℝ) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (show (1 / 5 : ℝ) ≤ 1 by norm_num)
  convert h.trans (mul_le_mul_of_nonneg_right htwo
    (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ t) (-(1 / 5 : ℝ)))) using 1 <;> norm_num

private lemma coordinate_power_six {t z : ℝ} (ht : 2 ≤ t)
    (hz : z ∈ Icc (0 : ℝ) 1) :
    coordinate t z ^ (-6 / 5 : ℝ) ≤ 4 * t ^ (-6 / 5 : ℝ) := by
  have h := coordinate_neg_power ht hz (show (0 : ℝ) ≤ 6 / 5 by norm_num)
  have htwo : (2 : ℝ) ^ (6 / 5 : ℝ) ≤ 4 := by
    simpa only [Real.rpow_two, show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (show (6 / 5 : ℝ) ≤ 2 by norm_num)
  convert h.trans (mul_le_mul_of_nonneg_right htwo
    (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ t) (-(6 / 5 : ℝ)))) using 1 <;> norm_num

lemma ratio_time_control {t z u : ℝ} (ht : 8 ≤ t)
    (hz : z ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) :
    DifferentiableAt ℝ (fun y => weightRatio (coordinate y z) u) t ∧
      |deriv (fun y => weightRatio (coordinate y z) u) t| ≤ 48 * t ^ (-6 / 5 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have ht2 : 2 ≤ t := by linarith
  have hx4 : 4 ≤ coordinate t z := by linarith [coordinate_half ht2 hz]
  have hratio := weightRatio_control hx4 hu.1 hu.2
  have hd := hratio.2.2.1.comp t (coordinate_hasDerivAt ht0 hz.1)
  refine ⟨hd.differentiableAt, ?_⟩
  have heq : deriv (fun y => weightRatio (coordinate y z) u) t =
      (weightRatio (coordinate t z) u *
        (logSlope (coordinate t z + u * width (coordinate t z)) *
          (1 + (4 / 5 : ℝ) * u * coordinate t z ^ (-1 / 5 : ℝ)) -
            logSlope (coordinate t z))) *
        (1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ))⁻¹ := hd.deriv
  rw [heq, abs_mul]
  have hj := jacobianFactor_bounds ht2 hz
  have hJ : |(1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ))⁻¹| ≤ 1 := by
    change |jacobianFactor t z| ≤ 1
    rw [abs_of_pos hj.1]
    exact hj.2.1
  calc
    _ ≤ (12 * coordinate t z ^ (-6 / 5 : ℝ)) * 1 :=
      mul_le_mul hratio.2.2.2 hJ (abs_nonneg _) (by positivity)
    _ ≤ _ := by nlinarith [coordinate_power_six ht2 hz]

lemma body_differentiable {t z u : ℝ} (ht : 8 ≤ t)
    (hz : z ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) (s : ℂ) :
    DifferentiableAt ℝ (fun y => normalizedBody y z u s) t := by
  have ht0 : 0 < t := by linarith
  exact ((normalizedPower_hasDerivAt ht0 hz.1 s).differentiableAt.mul
    (ratio_time_control ht hz hu).1.hasDerivAt.ofReal_comp.differentiableAt).mul
      (jacobianFactor_hasDerivAt ht0 hz.1).ofReal_comp.differentiableAt

/-- Both the normalized coefficient and its time derivative retain the window-scale gain. -/
theorem normalizedBody_C1_estimate {t z u : ℝ} (ht : 8 ≤ t)
    (hz : z ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1) (s : ℂ) :
    DifferentiableAt ℝ (fun y => normalizedBody y z u s) t ∧
      ‖normalizedBody t z u s - 1‖ ≤ kernelConstant s * t ^ (-1 / 5 : ℝ) ∧
      ‖deriv (fun y => normalizedBody y z u s) t‖ ≤ kernelConstant s * t ^ (-6 / 5 : ℝ) := by
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
  have hP := normalizedPower_bounds ht2 hz s
  have hPnorm := hP.1
  have hPerr := hP.2
  have hP' := normalizedPower_derivative_bound ht2 hz s
  have hA' := (ratio_time_control ht hz hu).2
  have hJ' := jacobianFactor_derivative_bound ht2 hz
  refine ⟨body_differentiable ht hz hu s, ?_, ?_⟩
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
      _ ≤ ((2 * ‖-s - 1 / 2‖ * Real.exp (2 * ‖-s - 1 / 2‖)) *
          t ^ (-1 / 5 : ℝ)) * 1 * 1 +
          (8 * t ^ (-1 / 5 : ℝ)) * 1 + 2 * t ^ (-1 / 5 : ℝ) := by
        simp only [norm_mul]
        gcongr
      _ ≤ _ := by dsimp [kernelConstant]; nlinarith [Real.exp_pos (2 * ‖-s - 1 / 2‖),
        Real.rpow_nonneg ht0.le (-1 / 5 : ℝ)]
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
      _ ≤ ((2 * ‖-s - 1 / 2‖ * Real.exp (2 * ‖-s - 1 / 2‖)) * t ^ (-6 / 5 : ℝ) * 1 +
          Real.exp (2 * ‖-s - 1 / 2‖) * (48 * t ^ (-6 / 5 : ℝ))) * 1 +
          (Real.exp (2 * ‖-s - 1 / 2‖) * 1) * t ^ (-6 / 5 : ℝ) := by gcongr
      _ ≤ _ := by
        dsimp [kernelConstant]
        nlinarith [Real.exp_pos (2 * ‖-s - 1 / 2‖), Real.rpow_nonneg ht0.le (-6 / 5 : ℝ)]

def unitSquare : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1

def triangle : Set (ℝ × ℝ) := {p | p.1 ≤ p.2}

/-- A fixed compact domain for the normalized adjoint, with the exact triangular support. -/
def normalizedIntegrand (t : ℝ) (s : ℂ) (p : ℝ × ℝ) : ℂ :=
  triangle.indicator (fun q => normalizedBody t q.1 q.2 s) p

/-- The normalized coefficient of the inverse-coordinate adjoint. -/
def normalizedAdjoint (t : ℝ) (s : ℂ) : ℂ :=
  ∫ p in unitSquare, normalizedIntegrand t s p

lemma body_continuousOn {t : ℝ} (ht : 8 ≤ t) (s : ℂ) :
    ContinuousOn (fun p : ℝ × ℝ => normalizedBody t p.1 p.2 s) unitSquare := by
  have ht0 : 0 < t := by linarith
  have ht2 : 2 ≤ t := by linarith
  have hx4 : ∀ p ∈ unitSquare, 4 ≤ coordinate t p.1 :=
    fun p hp => by linarith [coordinate_half ht2 hp.1]
  have hx0 : ∀ p ∈ unitSquare, 0 < coordinate t p.1 :=
    fun p hp => by linarith [hx4 p hp]
  have hcoord : ContinuousOn (fun p : ℝ × ℝ => coordinate t p.1) unitSquare :=
    (coordinate_continuousOn_parameter ht0).comp continuous_fst.continuousOn
      (fun _ hp => hp.1)
  have hwidth : ContinuousOn (fun p : ℝ × ℝ => width (coordinate t p.1)) unitSquare :=
    hcoord.rpow_const (fun _ _ => Or.inr (by norm_num))
  have hy : ContinuousOn
      (fun p : ℝ × ℝ => coordinate t p.1 + p.2 * width (coordinate t p.1)) unitSquare :=
    hcoord.add (continuous_snd.continuousOn.mul hwidth)
  have hxy : ∀ p ∈ unitSquare,
      coordinate t p.1 ≤ coordinate t p.1 + p.2 * width (coordinate t p.1) :=
    fun p hp => le_add_of_nonneg_right
      (mul_nonneg hp.2.1 (Real.rpow_nonneg (hx0 p hp).le _))
  have hwx : ContinuousOn
      (fun p : ℝ × ℝ => MellinWeightedVariation.weight (coordinate t p.1)) unitSquare :=
    fun p hp => (OriginalEarlyDivisorQuadrature.weight_deriv
      (by linarith [hx4 p hp])).continuousAt.comp_continuousWithinAt (hcoord p hp)
  have hwy : ContinuousOn
      (fun p : ℝ × ℝ => MellinWeightedVariation.weight
        (coordinate t p.1 + p.2 * width (coordinate t p.1))) unitSquare :=
    fun p hp => (OriginalEarlyDivisorQuadrature.weight_deriv
      (by linarith [hx4 p hp, hxy p hp])).continuousAt.comp_continuousWithinAt (hy p hp)
  have hratio : ContinuousOn
      (fun p : ℝ × ℝ => weightRatio (coordinate t p.1) p.2) unitSquare :=
    hwy.div hwx (fun p hp => (OriginalMovingWindowMoment.weight_pos
      (by linarith [hx4 p hp])).ne')
  have hlog : ContinuousOn
      (fun p : ℝ × ℝ => Real.log (coordinate t p.1 / t)) unitSquare :=
    (hcoord.div_const t).log (fun p hp => (div_pos (hx0 p hp) ht0).ne')
  have hP : ContinuousOn (fun p : ℝ × ℝ => normalizedPower t p.1 s) unitSquare := by
    exact Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hlog).const_mul (-s - 1 / 2))
  have hJ : ContinuousOn (fun p : ℝ × ℝ => jacobianFactor t p.1) unitSquare := by
    apply (continuousOn_const.add
      ((continuous_const.mul continuous_fst).continuousOn.mul
        (hcoord.rpow_const (fun p hp => Or.inl (hx0 p hp).ne')))).inv₀
    intro p hp
    have hz0 : 0 ≤ p.1 := hp.1.1
    have hxpos := hx0 p hp
    change (1 + (4 / 5 : ℝ) * p.1 * coordinate t p.1 ^ (-1 / 5 : ℝ)) ≠ 0
    exact ne_of_gt (by positivity)
  exact (hP.mul (Complex.continuous_ofReal.comp_continuousOn hratio)).mul
    (Complex.continuous_ofReal.comp_continuousOn hJ)

lemma integrand_measurable {t : ℝ} (ht : 8 ≤ t) (s : ℂ) :
    AEStronglyMeasurable (normalizedIntegrand t s) (volume.restrict unitSquare) := by
  have hm : MeasurableSet unitSquare := measurableSet_Icc.prod measurableSet_Icc
  exact ((body_continuousOn ht s).aestronglyMeasurable hm).indicator
    (measurableSet_le measurable_fst measurable_snd)

private lemma unitSquare_volume : volume.real unitSquare = 1 := by
  change (volume.prod volume).real (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) = 1
  rw [measureReal_prod_prod]
  norm_num [Measure.real]

lemma integrand_integrable {t : ℝ} (ht : 8 ≤ t) (s : ℂ) :
    IntegrableOn (normalizedIntegrand t s) unitSquare := by
  have hf := integrand_measurable ht s
  have hμ : volume unitSquare < ∞ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  apply Integrable.mono' (integrableOn_const (C := kernelConstant s + 1) hμ.ne) hf
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
  by_cases htri : p ∈ triangle
  · rw [normalizedIntegrand, indicator_of_mem htri]
    have hc := (normalizedBody_C1_estimate ht hp.1 hp.2 s).2.1
    have hε : t ^ (-1 / 5 : ℝ) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_nonpos zero_lt_one (by linarith : 1 ≤ t)
        (show (-1 / 5 : ℝ) ≤ 0 by norm_num)
    have hC0 : 0 ≤ kernelConstant s := by unfold kernelConstant; positivity
    calc
      _ ≤ ‖normalizedBody t p.1 p.2 s - 1‖ + 1 := by
        have h := norm_add_le (normalizedBody t p.1 p.2 s - 1) (1 : ℂ)
        simpa using h
      _ ≤ kernelConstant s + 1 := by nlinarith
  · rw [normalizedIntegrand, indicator_of_notMem htri, norm_zero]
    unfold kernelConstant
    positivity

private lemma triangle_integral :
    (∫ p in unitSquare, triangle.indicator (fun _ => (1 : ℂ)) p) = 1 / 2 := by
  have hμ : volume unitSquare < ∞ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  have htri : MeasurableSet triangle := measurableSet_le measurable_fst measurable_snd
  have hf : IntegrableOn (triangle.indicator (fun _ => (1 : ℂ))) unitSquare :=
    (integrableOn_const hμ.ne).indicator htri
  have hprod : (volume.restrict unitSquare : Measure (ℝ × ℝ)) =
      (volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1)) := by
    rw [Measure.prod_restrict]
    rfl
  rw [hprod, integral_prod _ (by rwa [← hprod])]
  have hsection : ∀ z ∈ Icc (0 : ℝ) 1,
      (∫ u in Icc (0 : ℝ) 1, triangle.indicator (fun _ => (1 : ℂ)) (z, u)) =
        ((1 - z : ℝ) : ℂ) := by
    intro z hz
    have he : (fun u : ℝ => triangle.indicator (fun _ => (1 : ℂ)) (z, u)) =
        (Ici z).indicator (fun _ => (1 : ℂ)) := by
      funext u
      rfl
    rw [he, integral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici]
    have hi : Ici z ∩ Icc (0 : ℝ) 1 = Icc z 1 := by
      ext u
      simp only [mem_inter_iff, mem_Ici, mem_Icc]
      constructor
      · exact fun h => ⟨h.1, h.2.2⟩
      · exact fun h => ⟨h.1, hz.1.trans h.1, h.2⟩
    rw [hi]
    simp [integral_const, Measure.real, Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hz.2), Complex.real_smul]
  have he : (∫ z in Icc (0 : ℝ) 1,
      ∫ u in Icc (0 : ℝ) 1, triangle.indicator (fun _ => (1 : ℂ)) (z, u)) =
      ∫ z in Icc (0 : ℝ) 1, ((1 - z : ℝ) : ℂ) := by
    apply setIntegral_congr_fun measurableSet_Icc hsection
  rw [he, integral_complex_ofReal]
  have hi : (∫ z in Icc (0 : ℝ) 1, (1 - z)) = 1 / 2 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    simpa using OriginalMovingWindowMoment.triangle_integral 0 1 1
  rw [hi]
  norm_num

/-- Exact triangular normalization and a uniform first-order error. -/
theorem normalizedAdjoint_error {t : ℝ} (ht : 8 ≤ t) (s : ℂ) :
    ‖normalizedAdjoint t s - 1 / 2‖ ≤ kernelConstant s * t ^ (-1 / 5 : ℝ) := by
  have hμ : volume unitSquare < ∞ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  have htri : MeasurableSet triangle := measurableSet_le measurable_fst measurable_snd
  have hconst : IntegrableOn (triangle.indicator (fun _ => (1 : ℂ))) unitSquare :=
    (integrableOn_const hμ.ne).indicator htri
  rw [normalizedAdjoint, ← triangle_integral,
    ← integral_sub (integrand_integrable ht s) hconst]
  have hb : ∀ p ∈ unitSquare,
      ‖normalizedIntegrand t s p - triangle.indicator (fun _ => (1 : ℂ)) p‖ ≤
        kernelConstant s * t ^ (-1 / 5 : ℝ) := by
    intro p hp
    by_cases hpt : p ∈ triangle
    · simpa only [normalizedIntegrand, indicator_of_mem hpt] using
        (normalizedBody_C1_estimate ht hp.1 hp.2 s).2.1
    · simp only [normalizedIntegrand, indicator_of_notMem hpt, sub_self, norm_zero]
      unfold kernelConstant
      positivity
  simpa only [unitSquare_volume, mul_one] using norm_setIntegral_le_of_norm_le_const hμ hb

lemma integrand_differentiable {t : ℝ} (ht : 8 ≤ t) (s : ℂ)
    (p : ℝ × ℝ) (hp : p ∈ unitSquare) :
    DifferentiableAt ℝ (fun y => normalizedIntegrand y s p) t := by
  by_cases hpt : p ∈ triangle
  · simpa only [normalizedIntegrand, indicator_of_mem hpt] using
      body_differentiable ht hp.1 hp.2 s
  · simpa only [normalizedIntegrand, indicator_of_notMem hpt] using
      (differentiableAt_const (c := (0 : ℂ)))

lemma integrand_derivative_bound {t : ℝ} (ht : 8 ≤ t) (s : ℂ)
    (p : ℝ × ℝ) (hp : p ∈ unitSquare) :
    ‖deriv (fun y => normalizedIntegrand y s p) t‖ ≤
      kernelConstant s * t ^ (-6 / 5 : ℝ) := by
  by_cases hpt : p ∈ triangle
  · simpa only [normalizedIntegrand, indicator_of_mem hpt] using
      (normalizedBody_C1_estimate ht hp.1 hp.2 s).2.2
  · simp only [normalizedIntegrand, indicator_of_notMem hpt, deriv_const', norm_zero]
    unfold kernelConstant
    positivity

lemma integrand_derivative_measurable {t : ℝ} (ht : 8 < t) (s : ℂ) :
    AEStronglyMeasurable (fun p => deriv (fun y => normalizedIntegrand y s p) t)
      (volume.restrict unitSquare) := by
  let h : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hpos : ∀ n, 0 < h n := fun n => by dsimp [h]; positivity
  have hseq : Tendsto h atTop (𝓝[>] (0 : ℝ)) := by
    exact tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hpos⟩
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n p => (h n)⁻¹ • (normalizedIntegrand (t + h n) s p - normalizedIntegrand t s p))
  · intro n
    exact ((integrand_measurable (by linarith [hpos n]) s).sub
      (integrand_measurable ht.le s)).const_smul ((h n)⁻¹)
  · filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    exact ((integrand_differentiable ht.le s p hp).hasDerivAt.tendsto_slope_zero_right).comp hseq

/-- Differentiation commutes with the fixed triangular integral. -/
lemma normalizedAdjoint_hasDerivAt {t : ℝ} (ht : 8 < t) (s : ℂ) :
    HasDerivAt (fun y => normalizedAdjoint y s)
      (∫ p in unitSquare, deriv (fun y => normalizedIntegrand y s p) t) t := by
  have hμ : volume unitSquare < ∞ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  have hC0 : 0 ≤ kernelConstant s := by unfold kernelConstant; positivity
  have hbound : ∀ᵐ p ∂volume.restrict unitSquare, ∀ y ∈ Ioi (8 : ℝ),
      ‖deriv (fun v => normalizedIntegrand v s p) y‖ ≤ kernelConstant s := by
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    intro y hy
    have hy8 : 8 < y := hy
    have hε : y ^ (-6 / 5 : ℝ) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_nonpos zero_lt_one (by linarith : 1 ≤ y)
        (show (-6 / 5 : ℝ) ≤ 0 by norm_num)
    exact (integrand_derivative_bound hy8.le s p hp).trans (mul_le_of_le_one_right hC0 hε)
  have hdiff : ∀ᵐ p ∂volume.restrict unitSquare, ∀ y ∈ Ioi (8 : ℝ),
      HasDerivAt (fun v => normalizedIntegrand v s p)
        (deriv (fun v => normalizedIntegrand v s p) y) y := by
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    intro y hy
    exact (integrand_differentiable (le_of_lt hy) s p hp).hasDerivAt
  have hmeas : ∀ᶠ y in 𝓝 t,
      AEStronglyMeasurable (normalizedIntegrand y s) (volume.restrict unitSquare) := by
    filter_upwards [Ioi_mem_nhds ht] with y hy
    exact integrand_measurable (le_of_lt hy) s
  have hi := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict unitSquare) (Ioi_mem_nhds ht) hmeas
    (integrand_integrable ht.le s) (integrand_derivative_measurable ht s)
    hbound (integrableOn_const hμ.ne) hdiff
  exact hi.2

/-- Differentiation of the fixed triangular integral keeps its uniform scale gain. -/
theorem normalizedAdjoint_derivative {t : ℝ} (ht : 8 < t) (s : ℂ) :
    DifferentiableAt ℝ (fun y => normalizedAdjoint y s) t ∧
      ‖deriv (fun y => normalizedAdjoint y s) t‖ ≤
        kernelConstant s * t ^ (-6 / 5 : ℝ) := by
  have hμ : volume unitSquare < ∞ :=
    (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  refine ⟨(normalizedAdjoint_hasDerivAt ht s).differentiableAt, ?_⟩
  rw [(normalizedAdjoint_hasDerivAt ht s).deriv]
  simpa only [unitSquare_volume, mul_one] using
    norm_setIntegral_le_of_norm_le_const hμ (integrand_derivative_bound ht.le s)

/-- The adjoint written in the inverse window coordinates. -/
def inverseAdjoint (t : ℝ) (s : ℂ) : ℂ :=
  (t : ℂ) ^ (-s - 1 / 2) * normalizedAdjoint t s

/-- The exact remainder after subtracting the triangular principal coefficient. -/
def adjointRemainder (t : ℝ) (s : ℂ) : ℂ :=
  (t : ℂ) ^ (-s - 1 / 2) * (normalizedAdjoint t s - 1 / 2)

private lemma principal_mul_normalizedPower {t z : ℝ} (ht : 0 < t) (hz : 0 ≤ z) (s : ℂ) :
    (t : ℂ) ^ (-s - 1 / 2) * normalizedPower t z s =
      (coordinate t z : ℂ) ^ (-s - 1 / 2) := by
  have hx := coordinate_pos ht hz
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'),
    normalizedPower, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.exp_add, ← Complex.ofReal_log ht.le, ← Complex.ofReal_log hx.le,
    Real.log_div hx.ne' ht.ne', Complex.ofReal_sub]
  congr 1
  ring

/-- The fixed triangular integral is exactly the iterated inverse-coordinate formula. -/
theorem inverseAdjoint_eq_iterated {t : ℝ} (ht : 8 ≤ t) (s : ℂ) :
    inverseAdjoint t s =
      ∫ z in Icc (0 : ℝ) 1, (coordinate t z : ℂ) ^ (-s - 1 / 2) *
        ((∫ u in z..1, weightRatio (coordinate t z) u : ℝ) : ℂ) /
          ((1 + (4 / 5 : ℝ) * z * coordinate t z ^ (-1 / 5 : ℝ) : ℝ) : ℂ) := by
  have ht0 : 0 < t := by linarith
  have hprod : (volume.restrict unitSquare : Measure (ℝ × ℝ)) =
      (volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (0 : ℝ) 1)) := by
    rw [Measure.prod_restrict]
    rfl
  have hsection : ∀ z ∈ Icc (0 : ℝ) 1,
      (∫ u in Icc (0 : ℝ) 1, normalizedIntegrand t s (z, u)) =
      normalizedPower t z s * ((∫ u in z..1, weightRatio (coordinate t z) u : ℝ) : ℂ) *
        (jacobianFactor t z : ℂ) := by
    intro z hz
    have he : (fun u : ℝ => normalizedIntegrand t s (z, u)) =
        (Ici z).indicator (fun u => normalizedBody t z u s) := by
      funext u
      rfl
    rw [he, integral_indicator measurableSet_Ici,
      Measure.restrict_restrict measurableSet_Ici]
    have hi : Ici z ∩ Icc (0 : ℝ) 1 = Icc z 1 := by
      ext u
      simp only [mem_inter_iff, mem_Ici, mem_Icc]
      constructor
      · exact fun h => ⟨h.1, h.2.2⟩
      · exact fun h => ⟨h.1, hz.1.trans h.1, h.2⟩
    rw [hi]
    unfold normalizedBody
    rw [integral_mul_const, integral_const_mul, integral_complex_ofReal,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hz.2]
  unfold inverseAdjoint normalizedAdjoint
  have hint : Integrable (normalizedIntegrand t s)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod
        (volume.restrict (Icc (0 : ℝ) 1))) := by
    rw [← hprod]
    exact integrand_integrable ht s
  rw [hprod, integral_prod _ hint]
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro z hz
  dsimp only
  rw [hsection z hz]
  calc
    _ = ((t : ℂ) ^ (-s - 1 / 2) * normalizedPower t z s) *
        ((∫ u in z..1, weightRatio (coordinate t z) u : ℝ) : ℂ) *
          (jacobianFactor t z : ℂ) := by ring
    _ = _ := by
      rw [principal_mul_normalizedPower ht0 hz.1 s]
      simp only [jacobianFactor, Complex.ofReal_inv, div_eq_mul_inv]

lemma principalPower_hasDerivAt {t : ℝ} (ht : 0 < t) (s : ℂ) :
    HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s - 1 / 2))
      ((-s - 1 / 2) * (t : ℂ) ^ (-s - 1 / 2 - 1)) t := by
  by_cases hp : -s - 1 / 2 = 0
  · simp only [hp, Complex.cpow_zero, zero_mul]
    exact hasDerivAt_const t 1
  · exact hasDerivAt_ofReal_cpow_const ht.ne' hp

/-- The normalized forward kernel has a C1 remainder smaller by t^(-1/5). -/
theorem inverseAdjoint_C1_remainder_estimate {t : ℝ} (ht : 8 < t) (s : ℂ) :
    inverseAdjoint t s = (1 / 2 : ℂ) * (t : ℂ) ^ (-s - 1 / 2) + adjointRemainder t s ∧
    DifferentiableAt ℝ (fun y => adjointRemainder y s) t ∧
      ‖adjointRemainder t s‖ ≤ kernelConstant s *
        t ^ (-s.re - 1 / 2) * t ^ (-1 / 5 : ℝ) ∧
      ‖deriv (fun y => adjointRemainder y s) t‖ ≤
        ((‖-s - 1 / 2‖ + 1) * kernelConstant s) *
          t ^ (-s.re - 3 / 2) * t ^ (-1 / 5 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have hq := normalizedAdjoint_derivative ht s
  have hp := principalPower_hasDerivAt ht0 s
  have hr := hp.mul (hq.1.hasDerivAt.sub_const (1 / 2 : ℂ))
  have hnorm : ‖(t : ℂ) ^ (-s - 1 / 2)‖ = t ^ (-s.re - 1 / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    norm_num
  have hnorm' : ‖(t : ℂ) ^ (-s - 1 / 2 - 1)‖ = t ^ (-s.re - 3 / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    congr 1
    norm_num
    ring
  refine ⟨by unfold inverseAdjoint adjointRemainder; ring, hr.differentiableAt, ?_, ?_⟩
  · unfold adjointRemainder
    rw [norm_mul, hnorm]
    calc
      _ ≤ t ^ (-s.re - 1 / 2) * (kernelConstant s * t ^ (-1 / 5 : ℝ)) :=
        mul_le_mul_of_nonneg_left (normalizedAdjoint_error ht.le s) (by positivity)
      _ = _ := by ring
  · have heq : deriv (fun y => adjointRemainder y s) t =
        (-s - 1 / 2) * (t : ℂ) ^ (-s - 1 / 2 - 1) *
          (normalizedAdjoint t s - 1 / 2) +
        (t : ℂ) ^ (-s - 1 / 2) * deriv (fun y => normalizedAdjoint y s) t := hr.deriv
    rw [heq]
    calc
      _ ≤ ‖(-s - 1 / 2) * (t : ℂ) ^ (-s - 1 / 2 - 1) *
            (normalizedAdjoint t s - 1 / 2)‖ +
          ‖(t : ℂ) ^ (-s - 1 / 2) * deriv (fun y => normalizedAdjoint y s) t‖ :=
        norm_add_le _ _
      _ ≤ (‖-s - 1 / 2‖ * t ^ (-s.re - 3 / 2)) *
            (kernelConstant s * t ^ (-1 / 5 : ℝ)) +
          t ^ (-s.re - 1 / 2) * (kernelConstant s * t ^ (-6 / 5 : ℝ)) := by
        simp only [norm_mul, hnorm, hnorm']
        gcongr
        · exact normalizedAdjoint_error ht.le s
        · exact hq.2
      _ = _ := by
        have he : t ^ (-s.re - 1 / 2) * t ^ (-6 / 5 : ℝ) =
            t ^ (-s.re - 3 / 2) * t ^ (-1 / 5 : ℝ) := by
          rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]
          congr 1
          ring
        calc
          _ = ‖-s - 1 / 2‖ * kernelConstant s *
                (t ^ (-s.re - 3 / 2) * t ^ (-1 / 5 : ℝ)) +
              kernelConstant s * (t ^ (-s.re - 1 / 2) * t ^ (-6 / 5 : ℝ)) := by ring
          _ = _ := by rw [he]; ring

/-- Both remainder estimates are uniform on every compact complex parameter set. -/
theorem inverseAdjoint_uniform_C1_remainder (K : Set ℂ) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ s ∈ K, ∀ t : ℝ, 8 < t →
      ‖adjointRemainder t s‖ ≤ C * t ^ (-s.re - 1 / 2) * t ^ (-1 / 5 : ℝ) ∧
      ‖deriv (fun y => adjointRemainder y s) t‖ ≤
        C * t ^ (-s.re - 3 / 2) * t ^ (-1 / 5 : ℝ) := by
  have hc : Continuous (fun s : ℂ => (‖-s - 1 / 2‖ + 1) * kernelConstant s) := by
    unfold kernelConstant
    fun_prop
  obtain ⟨M, hM⟩ := hK.bddAbove_image hc.continuousOn
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro s hs t ht
  have hC : (‖-s - 1 / 2‖ + 1) * kernelConstant s ≤ max 1 M :=
    (hM (mem_image_of_mem _ hs)).trans (le_max_right _ _)
  have hC0 : 0 ≤ kernelConstant s := by unfold kernelConstant; positivity
  have hC' : kernelConstant s ≤ max 1 M :=
    (le_mul_of_one_le_left hC0 (le_add_of_nonneg_left (norm_nonneg _))).trans hC
  have hmain := inverseAdjoint_C1_remainder_estimate ht s
  constructor
  · exact hmain.2.2.1.trans (by gcongr)
  · exact hmain.2.2.2.trans (by gcongr)

#print axioms inverseAdjoint_eq_iterated
#print axioms inverseAdjoint_uniform_C1_remainder

end

end D5.S3.Arith.Robin.ForwardKernel.Asymptotic
