/- GID: D5/S3/Combinatorics/Graph/Chordal/EuclideanChordalGaussian
   generality: G
   mirror-B: none(waiver:covered-by-hilbert-clique-phase-reversal-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A homogeneous Gaussian averaging kernel -/

import OmegaBuild.Commands
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.LinearAlgebra.Center
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Tactic

compile_only_with_mathlib

/-! Omega original.

 # A homogeneous Gaussian averaging kernel

The kernel `exp (-‖x‖²) x / ‖x‖` reduces the reconstruction coefficient to
`dimension * (first absolute coordinate moment) / (first radial moment)`.
-/

open MeasureTheory Set Real Module
open scoped RealInnerProductSpace

namespace SimpleGraph.EuclideanChordal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def radialMoment (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : ℝ :=
  ∫ y : E, ‖y‖ * exp (-‖y‖ ^ 2)

noncomputable def gaussianKernel (y : E) : E := (exp (-‖y‖ ^ 2) / ‖y‖) • y

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem gaussianKernel_zero : gaussianKernel (0 : E) = 0 := by
  simp [gaussianKernel]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_gaussianKernel_le (y : E) : ‖gaussianKernel y‖ ≤ exp (-‖y‖ ^ 2) := by
  by_cases hy : y = 0
  · simp [hy]
  · simp [gaussianKernel, norm_smul, norm_ne_zero_iff.mpr hy]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem gaussianKernel_isometry (L : E ≃ₗᵢ[ℝ] E) (y : E) :
    gaussianKernel (L y) = L (gaussianKernel y) := by
  simp [gaussianKernel]

theorem measurable_gaussianKernel : Measurable (gaussianKernel : E → E) := by
  unfold gaussianKernel
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_mul_inner_kernel (y z : E) :
    ‖y‖ * |⟪gaussianKernel y, z⟫| = |⟪y, z⟫| * exp (-‖y‖ ^ 2) := by
  by_cases hy : y = 0
  · simp [hy]
  · rw [gaussianKernel, real_inner_smul_left, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ exp (-‖y‖ ^ 2) / ‖y‖)]
    field_simp

/-- The radial first moment is integrable in every positive finite dimension. -/
theorem integrable_radial [Nontrivial E] :
    Integrable (fun y : E => ‖y‖ * exp (-‖y‖ ^ 2)) := by
  change Integrable ((fun r : ℝ => r * exp (-r ^ 2)) ∘ (fun y : E => ‖y‖))
  rw [Function.comp_def, integrable_fun_norm_addHaar (volume : Measure E) (f := fun r : ℝ => r * exp (-r ^ 2))]
  have hn := finrank_pos (R := ℝ) (M := E)
  have hh := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num)
    (s := (finrank ℝ E : ℝ)) (by have : (0 : ℝ) ≤ finrank ℝ E := Nat.cast_nonneg _; linarith)
  apply hh.congr_fun _ measurableSet_Ioi
  intro x hx
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← pow_succ, Nat.sub_add_cancel hn]
  simp only [rpow_natCast, neg_mul, one_mul]

/-- An integrable function of at most linear growth can be averaged against the kernel. -/
theorem integrable_kernel_mul [Nontrivial E] (f : E → ℝ) (hf : Measurable f)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ y, |f y| ≤ B * ‖y‖) :
    Integrable (fun y => f y • gaussianKernel y) := by
  apply (integrable_radial.const_mul B).mono' (hf.smul measurable_gaussianKernel).aestronglyMeasurable
  filter_upwards with y
  change ‖f y • gaussianKernel y‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs]
  calc
    |f y| * ‖gaussianKernel y‖ ≤ (B * ‖y‖) * exp (-‖y‖ ^ 2) :=
      mul_le_mul (hbound y) (norm_gaussianKernel_le y) (norm_nonneg _) (by positivity)
    _ = B * (‖y‖ * exp (-‖y‖ ^ 2)) := by ring

private theorem integrable_linear_kernel [Nontrivial E] (x : E) :
    Integrable (fun y => ⟪x, y⟫ • gaussianKernel y) :=
  integrable_kernel_mul _ (by fun_prop) (norm_nonneg _) (fun y => abs_real_inner_le_norm _ _)

/-- The linear moment map used by the averaging construction. -/
noncomputable def gaussianMomentMap [Nontrivial E] : E →ₗ[ℝ] E where
  toFun x := ∫ y, ⟪x, y⟫ • gaussianKernel y
  map_add' x z := by
    simp_rw [inner_add_left, add_smul]
    exact integral_add (integrable_linear_kernel x) (integrable_linear_kernel z)
  map_smul' r x := by
    simp_rw [real_inner_smul_left, mul_smul]
    exact integral_smul r _

theorem gaussianMomentMap_isometry [Nontrivial E] (L : E ≃ₗᵢ[ℝ] E) (x : E) :
    gaussianMomentMap (L x) = L (gaussianMomentMap x) := by
  change (∫ y, ⟪L x, y⟫ • gaussianKernel y) = L (∫ y, ⟪x, y⟫ • gaussianKernel y)
  have hh := L.measurePreserving.integral_comp L.toHomeomorph.measurableEmbedding
    (fun y => ⟪L x, y⟫ • gaussianKernel y)
  calc
    _ = ∫ y, ⟪L x, L y⟫ • gaussianKernel (L y) := hh.symm
    _ = ∫ y, L (⟪x, y⟫ • gaussianKernel y) := by
      apply integral_congr_ae
      filter_upwards with y
      simp
    _ = _ := L.toLinearIsometry.integral_comp_comm _

private theorem integral_inner_right {F : E → E} (hF : Integrable F) (z : E) :
    (∫ y, ⟪F y, z⟫) = ⟪∫ y, F y, z⟫ := by
  simpa only [real_inner_comm] using (integral_inner (𝕜 := ℝ) hF z)

private theorem gaussianMomentMap_scalar [Nontrivial E] :
    ∃ c : ℝ, gaussianMomentMap (E := E) = c • (1 : E →ₗ[ℝ] E) := by
  apply LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent
  intro x
  let K := ℝ ∙ x
  have hfix : K.reflection (gaussianMomentMap x) = gaussianMomentMap x := by
    rw [← gaussianMomentMap_isometry, K.reflection_mem_subspace_eq_self
      (Submodule.mem_span_singleton_self x)]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((K.reflection_eq_self_iff _).mp hfix)
  rw [← hc]
  intro h
  have hh := (LinearIndependent.pair_iff.mp h) (-c) 1
    (by simp)
  exact one_ne_zero hh.2

/-- Rotation symmetry and the trace identify the reproducing moment exactly. -/
theorem gaussianMomentMap_eq [Nontrivial E] (x : E) :
    gaussianMomentMap x = (radialMoment E / (finrank ℝ E : ℝ)) • x := by
  obtain ⟨c, hc⟩ := gaussianMomentMap_scalar (E := E)
  let b := stdOrthonormalBasis ℝ E
  have htrace : (finrank ℝ E : ℝ) * c = radialMoment E := by
    calc
      (finrank ℝ E : ℝ) * c = ∑ i, ⟪gaussianMomentMap (b i), b i⟫ := by
        simp [hc, b, real_inner_smul_left, mul_comm]
      _ = ∑ i, ∫ y, ⟪⟪b i, y⟫ • gaussianKernel y, b i⟫ := by
        congr 1
        ext i
        exact (integral_inner_right (integrable_linear_kernel (b i)) (b i)).symm
      _ = ∫ y, ∑ i, ⟪⟪b i, y⟫ • gaussianKernel y, b i⟫ := by
        rw [integral_finsetSum]
        intro i _
        exact (integrable_linear_kernel (b i)).inner_const (b i)
      _ = radialMoment E := by
        apply integral_congr_ae
        filter_upwards with y
        simp only [real_inner_smul_left, gaussianKernel]
        rw [show (∑ i, ⟪b i, y⟫ * (exp (-‖y‖ ^ 2) / ‖y‖ * ⟪y, b i⟫)) =
          (exp (-‖y‖ ^ 2) / ‖y‖) * ∑ i, ⟪y, b i⟫ ^ 2 by
            simp_rw [real_inner_comm (b _) y, pow_two, Finset.mul_sum]; congr 1; ext; ring]
        rw [b.sum_sq_inner_left]
        by_cases hy : y = 0
        · simp [hy]
        · field_simp
  have hn : (finrank ℝ E : ℝ) ≠ 0 := by exact_mod_cast (finrank_pos (R := ℝ) (M := E)).ne'
  have he : c = radialMoment E / (finrank ℝ E : ℝ) := by apply (eq_div_iff hn).2; linarith
  simp [hc, he]

/-- The absolute first projection moment depends only on the length of the direction. -/
theorem absoluteMoment_eq (e : E) (he : ‖e‖ = 1) (z : E) :
    (∫ y : E, |⟪y, z⟫| * exp (-‖y‖ ^ 2)) =
      ‖z‖ * ∫ y : E, |⟪y, e⟫| * exp (-‖y‖ ^ 2) := by
  let L : E ≃ₗᵢ[ℝ] E := (ℝ ∙ (z - ‖z‖ • e))ᗮ.reflection
  have hL : L z = ‖z‖ • e := Submodule.reflection_sub (v := z) (w := ‖z‖ • e) (by simp [norm_smul, he])
  have hh := L.measurePreserving.integral_comp L.toHomeomorph.measurableEmbedding
    (fun y => |⟪y, L z⟫| * exp (-‖y‖ ^ 2))
  have heq : (∫ y : E, |⟪y, z⟫| * exp (-‖y‖ ^ 2)) =
      ∫ y : E, |⟪y, ‖z‖ • e⟫| * exp (-‖y‖ ^ 2) := by
    rw [← hL, ← hh]
    apply integral_congr_ae
    filter_upwards with y
    simp
  rw [heq]
  simp_rw [real_inner_smul_right, abs_mul, abs_norm, mul_assoc]
  exact integral_const_mul _ _

theorem integrable_absolute_projection [Nontrivial E] (z : E) :
    Integrable (fun y : E => |⟪y, z⟫| * exp (-‖y‖ ^ 2)) := by
  apply (integrable_radial.const_mul ‖z‖).mono' (by fun_prop)
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    |⟪y, z⟫| * exp (-‖y‖ ^ 2) ≤ (‖y‖ * ‖z‖) * exp (-‖y‖ ^ 2) := by
      gcongr
      exact abs_real_inner_le_norm _ _
    _ = ‖z‖ * (‖y‖ * exp (-‖y‖ ^ 2)) := by ring

/-- Averaging any continuous scalar selection of linear growth gives a vector potential.
The only dimension-dependent data are two explicitly evaluable Gaussian moments. -/
theorem gaussian_averaging [Nontrivial E] {V : Type*} (g : V → V → E)
    (f : E → V → ℝ) (hf : ∀ v, Continuous fun y => f y v)
    {B : ℝ} (hB : 0 ≤ B) (hgrowth : ∀ y v, |f y v| ≤ B * ‖y‖)
    (A : V → V → Prop) {M : ℝ} (hM : 0 ≤ M)
    (herror : ∀ y a b, A a b → |f y b - f y a - ⟪g a b, y⟫| ≤ M * ‖y‖)
    (e : E) (he : ‖e‖ = 1) (hJ : 0 < radialMoment E) :
    ∃ q : V → E, ∀ a b, A a b →
      ‖q b - q a - g a b‖ ≤
        ((finrank ℝ E : ℝ) / radialMoment E *
          (∫ y : E, |⟪y, e⟫| * exp (-‖y‖ ^ 2))) * M := by
  let R : ℝ := (finrank ℝ E : ℝ) / radialMoment E
  have hR : 0 ≤ R := div_nonneg (Nat.cast_nonneg _) hJ.le
  let q (v : V) := R • ∫ y, f y v • gaussianKernel y
  have hfi (v : V) := integrable_kernel_mul (fun y => f y v) (hf v).measurable hB
    (fun y => hgrowth y v)
  have hrep (x : E) : R • gaussianMomentMap x = x := by
    rw [gaussianMomentMap_eq, smul_smul]
    have hn : (finrank ℝ E : ℝ) ≠ 0 := by exact_mod_cast (finrank_pos (R := ℝ) (M := E)).ne'
    have hh : R * (radialMoment E / (finrank ℝ E : ℝ)) = 1 := by
      dsimp [R]
      field_simp
    rw [hh, one_smul]
  refine ⟨q, fun a b hab => ?_⟩
  let F (y : E) := f y b - f y a - ⟪g a b, y⟫
  have hFi : Integrable (fun y => F y • gaussianKernel y) := by
    simp_rw [F, sub_smul]
    exact ((hfi b).sub (hfi a)).sub (integrable_linear_kernel (g a b))
  let r := q b - q a - g a b
  have hr : r = R • ∫ y, F y • gaussianKernel y := by
    simp_rw [F, sub_smul]
    rw [integral_sub (f := fun y => f y b • gaussianKernel y - f y a • gaussianKernel y)
        (g := fun y => ⟪g a b, y⟫ • gaussianKernel y) ((hfi b).sub (hfi a)) (integrable_linear_kernel (g a b)),
      integral_sub (hfi b) (hfi a), smul_sub, smul_sub]
    change r = q b - q a - R • gaussianMomentMap (g a b)
    rw [hrep]
  have hint : |⟪r, r⟫| ≤ R * (M * (‖r‖ *
      ∫ y : E, |⟪y, e⟫| * exp (-‖y‖ ^ 2))) := by
    calc
      |⟪r, r⟫| = R * |∫ y, ⟪F y • gaussianKernel y, r⟫| := by
        nth_rw 1 [hr]
        rw [real_inner_smul_left, abs_mul, abs_of_nonneg hR, ← integral_inner_right hFi]
      _ ≤ R * ∫ y, |⟪F y • gaussianKernel y, r⟫| := by
        gcongr
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun y => ⟪F y • gaussianKernel y, r⟫)
      _ ≤ R * ∫ y, M * (|⟪y, r⟫| * exp (-‖y‖ ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hR
        apply integral_mono (by simpa only [Real.norm_eq_abs] using (hFi.inner_const (𝕜 := ℝ) r).norm)
          ((integrable_absolute_projection r).const_mul M)
        intro y
        change |⟪F y • gaussianKernel y, r⟫| ≤ _
        rw [real_inner_smul_left, abs_mul]
        calc
          |F y| * |⟪gaussianKernel y, r⟫| ≤ (M * ‖y‖) * |⟪gaussianKernel y, r⟫| :=
            mul_le_mul_of_nonneg_right (herror y a b hab) (abs_nonneg _)
          _ = M * (|⟪y, r⟫| * exp (-‖y‖ ^ 2)) := by
            rw [mul_assoc, norm_mul_inner_kernel]
      _ = _ := by rw [integral_const_mul, absoluteMoment_eq e he]
  have hsq : ‖r‖ ^ 2 ≤ (R * (∫ y : E, |⟪y, e⟫| * exp (-‖y‖ ^ 2)) * M) * ‖r‖ := by
    rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg ‖r‖)] at hint
    nlinarith only [hint]

  change ‖r‖ ≤ _
  change ‖r‖ ≤ R * (∫ y : E, |⟪y, e⟫| * exp (-‖y‖ ^ 2)) * M
  by_cases hr0 : ‖r‖ = 0
  · rw [hr0]
    exact mul_nonneg (mul_nonneg hR (integral_nonneg (fun y => by positivity))) hM
  · have hn := lt_of_le_of_ne (norm_nonneg r) (Ne.symm hr0)
    nlinarith

end SimpleGraph.EuclideanChordal
