/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/LaguerreSevenHalfSynthesisCharge
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:analytic-synthesis)
   anchors: []
   utility: none
   digest: Actual Mellin integration of weighted synthesis equals coefficient charge. -/
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.LaguerreSevenHalfWeightedSynthesis
import D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4.ReflectedGaussianCoefficientCore
import Mathlib.MeasureTheory.Integral.Bochner.L1

/-! The central Mellin integral is evaluated on the constructed physical image.
No original-domain surjectivity or Laguerre completeness is presumed. -/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

namespace FiniteGaussianCap4.LaguerreSevenHalf.WeightedSynthesis

/-- Integration of the actual second coordinate against its central Mellin measure. -/
def mellinIntegral : PhysicalSpace →L[ℝ] ℝ :=
  (L1.integralCLM (α := ℝ) (E := ℝ) (μ := mellinMeasure)).comp
    (ContinuousLinearMap.snd ℝ (Lp ℝ 2 graphMeasure) (Lp ℝ 1 mellinMeasure))

private theorem feature_single (n : ℕ) (a x : ℝ) :
    finiteFeature (Finsupp.single n a) x =
      (a / coefficientWeight n) * centralPsi x (2 * n) := by
  classical
  have h : finitePolynomial (Finsupp.single n a) =
      Polynomial.C (a / coefficientWeight n) * psiPolynomial (2 * n) := by
    by_cases ha : a = 0
    · simp [ha, finitePolynomial, finiteCoefficients]
    · simp [finitePolynomial, finiteCoefficients, ha]
  simp only [finiteFeature, h, physicalPolynomial, Polynomial.eval_mul,
    Polynomial.eval_C, psiPolynomial, centralPsi, phi]
  ring

private theorem feature_single_memLp (n : ℕ) (a : ℝ) :
    MemLp (finiteFeature (Finsupp.single n a)) 1 mellinMeasure := by
  rw [memLp_one_iff_integrable]
  have hm : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ (5 / 4 : ℝ))) := by fun_prop
  apply (integrable_withDensity_iff_integrable_smul' hm
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  apply ((integrable_centralPsi (2 * n)).const_mul (a / coefficientWeight n)).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hx.le _), smul_eq_mul, feature_single]
  ring

private theorem mellinIntegral_single (n : ℕ) (a : ℝ) :
    mellinIntegral (finiteSynthesis (Finsupp.single n a)) =
      (a / coefficientWeight n) * normalizedCentralMellin (2 * n) := by
  change L1.integralCLM ((finiteSynthesis (Finsupp.single n a)).2) = _
  rw [← L1.integral_eq, L1.integral_eq_integral]
  have he : ((finiteSynthesis (Finsupp.single n a)).2 : ℝ → ℝ) =ᵐ[mellinMeasure]
      finiteFeature (Finsupp.single n a) :=
    MemLp.coeFn_toLp (feature_single_memLp n a)
  rw [integral_congr_ae he]
  have hm : Measurable (fun x : ℝ => ENNReal.ofReal (x ^ (5 / 4 : ℝ))) := by fun_prop
  rw [mellinMeasure, integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  calc
    _ = ∫ x in Ioi (0 : ℝ), (a / coefficientWeight n) *
        (x ^ (5 / 4 : ℝ) * centralPsi x (2 * n)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [ENNReal.toReal_ofReal (Real.rpow_nonneg hx.le _), smul_eq_mul, feature_single]
      ring
    _ = _ := integral_const_mul _ _

/-- The continuous physical central Mellin integral is exactly the actual coefficient charge. -/
theorem synthesis_mellin_charge (w : Coeff) :
    mellinIntegral (synthesis w) = normalizedCentralMellin 0 *
      RHGaussianDilationCore.coeffCharge RHGaussianDilationCore.actualCentralChargeVector w := by
  have hs := mellinIntegral.hasSum (synthesis_hasSum w)
  simp only [mellinIntegral_single] at hs
  have hc := lp.hasSum_inner (𝕜 := ℝ) RHGaussianDilationCore.actualCentralChargeVector w
  have hcs : HasSum (fun n => RHGaussianDilationCore.actualCentralChargeVector n * w n)
      (RHGaussianDilationCore.coeffCharge RHGaussianDilationCore.actualCentralChargeVector w) := by
    simpa only [RHGaussianDilationCore.coeffCharge, innerSL_apply_apply, Real.inner_apply] using hc
  apply hs.unique
  convert hcs.mul_left (normalizedCentralMellin 0) using 1
  funext n
  change w n / coefficientWeight n * normalizedCentralMellin (2 * n) =
    normalizedCentralMellin 0 *
      ((RHGaussianDilationCore.actualCentralZ n / RHGaussianDilationCore.coeffWeight n) * w n)
  unfold RHGaussianDilationCore.actualCentralZ coefficientWeight RHGaussianDilationCore.coeffWeight
  field_simp [(normalizedCentralMellin_even_pos 0).ne',
    show (n : ℝ) + 1 ≠ 0 by positivity]
  <;> ring

end FiniteGaussianCap4.LaguerreSevenHalf.WeightedSynthesis
