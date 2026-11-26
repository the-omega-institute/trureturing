/- GID: D5/S3/Quantum/Analysis/RefinedBMV/Tracial/SimplexBarycenter
   generality: G
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A conditional simplex comparison for shifted matrix-word kernels. -/

import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.MeanInequalities

namespace RefinedBMV.Tracial

open MeasureTheory Set

/-- The expected exponential of an affine simplex kernel dominates the
exponential at its barycenter. The weights may come from any probability law. -/
theorem exp_sum_barycenter_le {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (w : Ω → ι → ℝ)
    (a : ι → ℝ) (hw : ∀ i, Integrable (fun ω ↦ w ω i) μ)
    (hExp : Integrable (fun ω ↦ Real.exp (∑ i, a i * w ω i)) μ) :
    Real.exp (∑ i, a i * ∫ ω, w ω i ∂μ) ≤
      ∫ ω, Real.exp (∑ i, a i * w ω i) ∂μ := by
  have hterm (i : ι) : Integrable (fun ω ↦ a i * w ω i) μ := (hw i).const_mul _
  have hsum : Integrable (fun ω ↦ ∑ i, a i * w ω i) μ :=
    integrable_finsetSum _ fun i _ ↦ hterm i
  have hmean : (∫ ω, (∑ i, a i * w ω i) ∂μ) = ∑ i, a i * ∫ ω, w ω i ∂μ := by
    rw [integral_finsetSum _ (fun i _ ↦ hterm i)]
    simp only [integral_const_mul]
  have h := ConvexOn.map_integral_le convexOn_exp Real.continuous_exp.continuousOn
    isClosed_univ (Filter.Eventually.of_forall fun _ ↦ mem_univ _) hsum hExp
  simpa only [hmean] using h

/-- A random simplex weight gives a power-mean kernel above the geometric
kernel evaluated at its mean weight. The exponent may be below one. -/
theorem geometric_barycenter_le_power_mean {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (w : Ω → ι → ℝ) (x : ι → ℝ) (p : ℝ)
    (hp : 0 ≤ p) (hx : ∀ i, 0 < x i)
    (hw : ∀ᵐ ω ∂μ, (∀ i, 0 ≤ w ω i) ∧ (∑ i, w ω i) = 1)
    (hwInt : ∀ i, Integrable (fun ω ↦ w ω i) μ)
    (hInt : Integrable (fun ω ↦ (∑ i, w ω i * x i) ^ p) μ) :
    (∏ i, x i ^ (p * ∫ ω, w ω i ∂μ)) ≤
      ∫ ω, (∑ i, w ω i * x i) ^ p ∂μ := by
  classical
  let a (i : ι) := p * Real.log (x i)
  have heval (v : ι → ℝ) : Real.exp (∑ i, a i * v i) = ∏ i, x i ^ (p * v i) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro i _
    rw [Real.rpow_def_of_pos (hx i)]
    congr 1
    unfold a
    ring
  have hpoint : ∀ᵐ ω ∂μ,
      Real.exp (∑ i, a i * w ω i) ≤ (∑ i, w ω i * x i) ^ p := by
    filter_upwards [hw] with ω hω
    rw [heval, show (∏ i, x i ^ (p * w ω i)) = (∏ i, x i ^ w ω i) ^ p by
      rw [← Real.finsetProd_rpow _ _ (fun i _ ↦ Real.rpow_nonneg (hx i).le _) _]
      apply Finset.prod_congr rfl
      intro i _
      rw [← Real.rpow_mul (hx i).le, mul_comm p]]
    apply Real.rpow_le_rpow (Finset.prod_nonneg fun i _ ↦ Real.rpow_nonneg (hx i).le _) _ hp
    exact Real.geom_mean_le_arith_mean_weighted _ _ _ (fun i _ ↦ hω.1 i) hω.2
      (fun i _ ↦ (hx i).le)
  have hsumInt : Integrable (fun ω ↦ ∑ i, a i * w ω i) μ :=
    integrable_finsetSum _ fun i _ ↦ (hwInt i).const_mul _
  have hexpMeas : AEStronglyMeasurable (fun ω ↦ Real.exp (∑ i, a i * w ω i)) μ :=
    Real.continuous_exp.comp_aestronglyMeasurable hsumInt.aestronglyMeasurable
  have hexpInt : Integrable (fun ω ↦ Real.exp (∑ i, a i * w ω i)) μ :=
    hInt.mono' hexpMeas (hpoint.mono fun ω h ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)] using h)
  calc
    _ = Real.exp (∑ i, a i * ∫ ω, w ω i ∂μ) := (heval _).symm
    _ ≤ ∫ ω, Real.exp (∑ i, a i * w ω i) ∂μ :=
      exp_sum_barycenter_le μ w a hwInt hexpInt
    _ ≤ _ := integral_mono_ae hexpInt hInt hpoint

#print axioms exp_sum_barycenter_le
#print axioms geometric_barycenter_le_power_mean

end RefinedBMV.Tracial
