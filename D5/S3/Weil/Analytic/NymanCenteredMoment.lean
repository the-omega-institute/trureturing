/- GID: D5/S3/Weil/Analytic/NymanCenteredMoment
   generality: I
   mirror-B: none(waiver:nyman-centered-prime-analysis)
   mirror-E: none(waiver:nyman-centered-prime-analysis)
   anchors: []
   utility: none
   digest: The centered prime dilation sum has an absolutely convergent zero Mellin moment. -/

import D5.S3.Weil.Analytic.NymanCenteredBoundary
import D5.S3.Weil.Analytic.NymanCenteredPrimeDirichlet
import Mathlib.NumberTheory.LSeries.Dirichlet

/-! The arithmetic Abel limit identifies the absolutely convergent moment. -/

set_option autoImplicit false

noncomputable section

open ArithmeticFunction Filter MeasureTheory Set
open scoped ArithmeticFunction.Moebius Topology

namespace NymanCenteredMoment

open NymanPrimeDilations NymanCenteredReciprocal NymanCenteredBoundary
open NymanCenteredPrimeDirichlet NymanDilationTransform
open NymanFixedRationalKernel (b b_zero_off continuous_b)

private theorem coe_centeredPrimeConvolution (n : ℕ) :
    (((centeredPrimeCoefficient * (μ : ArithmeticFunction ℝ)) n : ℝ) : ℂ) =
      (centeredPrimeCoefficientComplex * (μ : ArithmeticFunction ℂ)) n := by
  have hcast (k : ℕ) : centeredPrimeCoefficientComplex k = (centeredPrimeCoefficient k : ℂ) :=
    rfl
  simp only [ArithmeticFunction.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul,
    ArithmeticFunction.intCoe_apply, Complex.ofReal_intCast, hcast]

private theorem centered_mellin_factorization {s : ℂ} (hs : 1 < s.re) :
    mellin (fun x => (centeredPrimeDilations x : ℂ)) (-s) =
      LSeries (fun n => (centeredPrimeCoefficientComplex * (μ : ArithmeticFunction ℂ)) n) s *
        mellin (fun x => (b x : ℂ)) s := by
  have hsum : LSeriesSummable
      (fun n => (centeredPrimeCoefficientComplex * (μ : ArithmeticFunction ℂ)) n) s :=
    LSeriesSummable_mul (f := centeredPrimeCoefficientComplex) (g := (μ : ArithmeticFunction ℂ))
      (centeredPrimeCoefficient_lSeriesSummable hs) (LSeriesSummable_moebius_iff.mpr hs)
  rw [← mellin_comp_inv]
  calc
    _ = mellin (dilatedSum
        (fun n => (centeredPrimeCoefficientComplex * (μ : ArithmeticFunction ℂ)) n)
        (fun x => (b x : ℂ))) s := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [centeredPrimeDilations_inv_eq_dilatedSum ht]
      simp only [coe_centeredPrimeConvolution]
    _ = _ := mellin_dilatedSum
      (ArithmeticFunction.map_zero
        (f := centeredPrimeCoefficientComplex * (μ : ArithmeticFunction ℂ)))
      (Complex.continuous_ofReal.comp continuous_b) (fun x hx => by simp [b_zero_off x hx]) hsum

private theorem mellin_neg_one_eq_zero :
    mellin (fun x => (centeredPrimeDilations x : ℂ)) (-1) = 0 := by
  have hkernel := continuous_mellin_kernel (Complex.continuous_ofReal.comp continuous_b)
    (fun x hx => by simp [b_zero_off x hx])
  have hkernelLimit : Tendsto (fun σ : ℝ => mellin (fun x => (b x : ℂ)) (σ : ℂ))
      (𝓝[>] (1 : ℝ)) (𝓝 (mellin (fun x => (b x : ℂ)) ((1 : ℝ) : ℂ))) :=
    ((hkernel.comp Complex.continuous_ofReal).tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  have hzero := tendsto_centeredPrimeConvolution_lSeries.mul hkernelLimit
  have hlimit : Tendsto
      (fun σ : ℝ => mellin (fun x => (centeredPrimeDilations x : ℂ)) (-(σ : ℂ)))
      (𝓝[>] (1 : ℝ)) (𝓝 0) := by
    rw [← zero_mul (mellin (fun x => (b x : ℂ)) ((1 : ℝ) : ℂ))]
    apply hzero.congr'
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact (centered_mellin_factorization (by simpa using (Set.mem_Ioi.mp hσ))).symm
  exact tendsto_nhds_unique tendsto_mellin_neg_from_right hlimit

/-- The centered prime dilations have zero ordinary Mellin moment at exponent `-1`. -/
theorem integral_centeredPrime_weighted_eq_zero :
    (∫ x in Ioi (1 : ℝ), centeredPrimeDilations x / x ^ 2) = 0 := by
  have hpoint (x : ℝ) (_hx : x ∈ Ioi (0 : ℝ)) :
      (x : ℂ) ^ ((-1 : ℂ) - 1) • (centeredPrimeDilations x : ℂ) =
        ((centeredPrimeDilations x / x ^ 2 : ℝ) : ℂ) := by
    rw [show (-1 : ℂ) - 1 = -(2 : ℂ) by norm_num, Complex.cpow_neg, Complex.cpow_two,
      smul_eq_mul, Complex.ofReal_div, Complex.ofReal_pow, div_eq_inv_mul]
  have hz := mellin_neg_one_eq_zero
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi hpoint, integral_complex_ofReal] at hz
  have hset : (∫ x in Ioi (0 : ℝ), centeredPrimeDilations x / x ^ 2) =
      ∫ x in Ioi (1 : ℝ), centeredPrimeDilations x / x ^ 2 := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    · exact fun _ hx => zero_lt_one.trans (mem_Ioi.mp hx)
    · intro x hx
      rw [centeredPrimeDilations_eq_zero_of_le_one (le_of_not_gt hx.2), zero_div]
  exact hset.symm.trans (Complex.ofReal_eq_zero.mp hz)

end NymanCenteredMoment
