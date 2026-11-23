/- GID: D5/S3/Fourier/Concentration/UniformPerturbationEuclidean
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/UniformPerturbationEuclidean
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Euclidean-scale interval bounds on a finite uniform perturbation law. -/

import D5.S3.Fourier.Concentration.ContinuousSpectralPerturbations
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

/-! Coordinate character factorization for affine sums on the perturbation law. -/

set_option autoImplicit false

noncomputable section

open Complex MeasureTheory Set Finset
open scoped ENNReal Interval
open D5.S3.Fourier.Concentration.ContinuousSpectralPerturbations

namespace D5.S3.Fourier.Concentration.UniformPerturbationEuclidean

private theorem charFun_intervalNoise {r : ℝ} (hr : 0 < r) (t : ℝ) :
    charFun (intervalNoise r) t = (Real.sinc (r * t) : ℂ) := by
  let _ := intervalNoise_probability hr
  by_cases ht : t = 0
  · simp [ht]
  rw [charFun_apply_real, intervalNoise, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]
  simp only [← Complex.ofReal_mul]
  rw [intervalIntegral.integral_comp_mul_left (fun x : ℝ => Complex.exp (x * I)) ht]
  rw [mul_neg, ← mul_comm r t, integral_exp_mul_I_eq_sinc]
  rw [real_smul, real_smul]
  push_cast
  field_simp [hr.ne', ht]

private theorem charFun_sum_intervalNoise {J : Type*} [Fintype J] (r a : J → ℝ)
    (hr : ∀ j, 0 < r j) (t : ℝ) :
    charFun ((Measure.pi fun j => intervalNoise (r j)).map
      (fun x : J → ℝ => ∑ j, a j * x j)) t =
      ∏ j, (Real.sinc (r j * (t * a j)) : ℂ) := by
  have (j : J) : IsProbabilityMeasure (intervalNoise (r j)) := intervalNoise_probability (hr j)
  have hf : Measurable (fun x : J → ℝ => ∑ j, a j * x j) := by fun_prop
  rw [charFun_apply_real, integral_map hf.aemeasurable (by fun_prop)]
  have hphase (x : J → ℝ) :
      Complex.exp (t * (∑ j, (a j : ℂ) * x j) * I) =
        ∏ j, Complex.exp ((t * a j : ℝ) * (x j : ℂ) * I) := by
    rw [← Complex.exp_sum]
    congr 1
    simp only [ofReal_mul, mul_sum, sum_mul]
    exact sum_congr rfl (fun j _ => by ring)
  simp_rw [ofReal_sum, ofReal_mul, hphase]
  calc
    _ = ∏ j, ∫ x : ℝ, Complex.exp ((t * a j : ℝ) * (x : ℂ) * I) ∂intervalNoise (r j) :=
      integral_fintype_prod_eq_prod
        (fun (j : J) (x : ℝ) => Complex.exp ((t * a j : ℝ) * (x : ℂ) * I))
    _ = _ := prod_congr rfl (fun j _ => by
      rw [← charFun_apply_real, charFun_intervalNoise (hr j)])

end D5.S3.Fourier.Concentration.UniformPerturbationEuclidean
