/- GID: D5/S3/Zeros/Endpoints/FirstLiCoefficientNormalization
   generality: I
   mirror-B: D5/B/S3/Zeros/Endpoints/FirstLiCoefficientNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The first Li coefficient normalizes the completed-zeta logarithmic derivative at one. -/

import D5.S3.Zeros.Endpoints.XiEndpointValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex
open D5.S3.Zeros.CompletedZeta
open D5.S3.Zeros.Endpoints.XiEndpointValues
open scoped BigOperators

namespace D5.S3.Zeros.Endpoints.FirstLiCoefficientNormalization

/-- The explicit first Li coefficient is the logarithmic derivative of the
canonical xi reading at one, and its reciprocal normalizes that value to one. -/
theorem first_li_coefficient_normalization :
    let firstLiCoefficient : ℝ :=
      1 + Real.eulerMascheroniConstant / 2 -
        Real.log (2 * Real.sqrt Real.pi)
    deriv xiReading 1 / xiReading 1 = (firstLiCoefficient : ℂ) ∧
      (1 / (firstLiCoefficient : ℂ)) *
        (deriv xiReading 1 / xiReading 1) = 1 := by
  dsimp only
  have hLogFourPi :
      Real.log (4 * Real.pi) / 2 =
        Real.log (2 * Real.sqrt Real.pi) := by
    calc
      Real.log (4 * Real.pi) / 2 =
          (Real.log 4 + Real.log Real.pi) / 2 := by
            rw [Real.log_mul (by norm_num) (ne_of_gt Real.pi_pos)]
      _ = (2 * Real.log 2 + Real.log Real.pi) / 2 := by
            rw [show (4 : ℝ) = 2 * 2 by norm_num,
              Real.log_mul (by norm_num) (by norm_num)]
            ring
      _ = Real.log 2 + Real.log Real.pi / 2 := by ring
      _ = Real.log 2 + Real.log (Real.sqrt Real.pi) := by
            rw [Real.log_sqrt Real.pi_pos.le]
      _ = Real.log (2 * Real.sqrt Real.pi) := by
            rw [Real.log_mul (by norm_num)
              (ne_of_gt (Real.sqrt_pos.2 Real.pi_pos))]
  have hGamma :
      (11 / 20 : ℝ) < Real.eulerMascheroniConstant := by
    have hGammaApprox :=
      Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 20
    have hLogTwentyOne : Real.log 21 < (3047 / 1000 : ℝ) := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have hSummable :=
        (NormedSpace.expSeries_div_hasSum_exp (3047 / 1000 : ℝ)).summable
      have hPartialBound :=
        hSummable.sum_le_tsum (Finset.range 14) (fun i hi => by positivity)
      rw [(NormedSpace.expSeries_div_hasSum_exp
        (3047 / 1000 : ℝ)).tsum_eq] at hPartialBound
      rw [← Real.exp_eq_exp_ℝ] at hPartialBound
      have hPartial :
          (21 : ℝ) <
            ∑ i ∈ Finset.range 14,
              (3047 / 1000 : ℝ) ^ i / i.factorial := by
        norm_num
      exact hPartial.trans_le hPartialBound
    norm_num [Real.eulerMascheroniSeq, harmonic] at hGammaApprox
    linarith
  have hLogBound :
      Real.log (4 * Real.pi) < (51 / 20 : ℝ) := by
    rw [Real.log_lt_iff_lt_exp (by positivity)]
    have hSummable :=
      (NormedSpace.expSeries_div_hasSum_exp (51 / 20 : ℝ)).summable
    have hPartialBound :=
      hSummable.sum_le_tsum (Finset.range 10) (fun i hi => by positivity)
    rw [(NormedSpace.expSeries_div_hasSum_exp
      (51 / 20 : ℝ)).tsum_eq] at hPartialBound
    rw [← Real.exp_eq_exp_ℝ] at hPartialBound
    have hPi := Real.pi_lt_d4
    norm_num at hPartialBound hPi ⊢
    calc
      4 * Real.pi < 4 * (3927 / 1250 : ℝ) :=
        mul_lt_mul_of_pos_left hPi (by norm_num)
      _ < 29366922070115351 / 2293760000000000 := by norm_num
      _ ≤ Real.exp (51 / 20) := hPartialBound
  have hFirstPositive :
      0 < 1 + Real.eulerMascheroniConstant / 2 -
        Real.log (2 * Real.sqrt Real.pi) := by
    rw [← hLogFourPi]
    linarith
  have hCompletedValue :
      completedRiemannZeta₀ 1 =
        ((1 + Real.eulerMascheroniConstant / 2 -
          Real.log (2 * Real.sqrt Real.pi) : ℝ) : ℂ) := by
    rw [completedRiemannZeta₀_one]
    rw [show (4 : ℂ) * Real.pi =
      ((4 * Real.pi : ℝ) : ℂ) by norm_num]
    rw [← Complex.ofReal_log
      (by positivity : 0 ≤ (4 * Real.pi : ℝ))]
    push_cast
    have hLogFourPiComplex :
        ((Real.log (4 * Real.pi) : ℂ) / 2) =
          (Real.log (2 * Real.sqrt Real.pi) : ℂ) := by
      exact_mod_cast hLogFourPi
    rw [show ((Real.eulerMascheroniConstant : ℂ) -
      Real.log (4 * Real.pi)) / 2 =
        Real.eulerMascheroniConstant / 2 -
          Real.log (4 * Real.pi) / 2 by ring]
    rw [hLogFourPiComplex]
    ring
  have hDerivative :
      deriv xiReading 1 = (1 / 2 : ℂ) * completedRiemannZeta₀ 1 := by
    unfold xiReading
    convert HasDerivAt.deriv
      (((((hasDerivAt_id (𝕜 := ℂ) (1 : ℂ)).mul
        ((hasDerivAt_id (𝕜 := ℂ) (1 : ℂ)).sub
          (hasDerivAt_const (𝕜 := ℂ) (1 : ℂ) 1))).mul
        differentiable_completedZeta₀.differentiableAt.hasDerivAt).add_const
          1).const_mul (1 / 2 : ℂ)) using 1 <;>
      norm_num
  have hRatio :
      deriv xiReading 1 / xiReading 1 =
        ((1 + Real.eulerMascheroniConstant / 2 -
          Real.log (2 * Real.sqrt Real.pi) : ℝ) : ℂ) := by
    calc
      deriv xiReading 1 / xiReading 1 =
          completedRiemannZeta₀ 1 := by
            rw [hDerivative, xi_reading_endpoint_values.2]
            ring
      _ = ((1 + Real.eulerMascheroniConstant / 2 -
          Real.log (2 * Real.sqrt Real.pi) : ℝ) : ℂ) := hCompletedValue
  refine ⟨hRatio, ?_⟩
  rw [hRatio]
  exact one_div_mul_cancel (Complex.ofReal_ne_zero.mpr hFirstPositive.ne')

#print axioms first_li_coefficient_normalization

end D5.S3.Zeros.Endpoints.FirstLiCoefficientNormalization
