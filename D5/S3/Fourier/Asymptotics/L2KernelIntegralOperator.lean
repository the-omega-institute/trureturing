/- GID: D5/S3/Fourier/Asymptotics/L2KernelIntegralOperator
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/L2KernelIntegralOperator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Integral.Prod]
   utility: none
   digest: L2 complex kernels define bounded integral operators contractively. -/

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Tactic

open MeasureTheory Filter
open scoped ENNReal NNReal ComplexConjugate

namespace D5.S3.Fourier.Asymptotics.L2KernelIntegralOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Square-integrable kernels on arbitrary sigma-finite measure spaces define bounded
complex integral operators, linearly and contractively in the kernel. The integral
formula includes actual section integrability and holds for the quotient representatives. -/
theorem result {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν] :
    ∃ A : Lp ℂ 2 (μ.prod ν) →L[ℂ] (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ),
      ‖A‖ ≤ 1 ∧ ∀ (k : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 ν),
        (∀ᵐ x ∂μ, Integrable (fun y => k (x, y) * f y) ν) ∧
        (∀ᵐ x ∂μ, (A k f) x = ∫ y, k (x, y) * f y ∂ν) ∧
        ‖A k f‖ ≤ ‖k‖ * ‖f‖ := by
  classical
  have hmake (k : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
      ∃ g : Lp ℂ 2 μ,
        (∀ᵐ x ∂μ, Integrable (fun y => k (x, y) * f y) ν) ∧
        (∀ᵐ x ∂μ, g x = ∫ y, k (x, y) * f y ∂ν) ∧
        ‖g‖ ≤ ‖k‖ * ‖f‖ := by
    have hk2 : Integrable (fun p => ‖k p‖ ^ 2) (μ.prod ν) :=
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable k)).mp (Lp.memLp k)
    have hsecs : ∀ᵐ x ∂μ, MemLp (fun y => k (x, y)) 2 ν := by
      filter_upwards [hk2.prod_right_ae, (Lp.aestronglyMeasurable k).prodMk_left] with x hx hm
      exact (memLp_two_iff_integrable_sq_norm hm).mpr hx
    have hint : ∀ᵐ x ∂μ, Integrable (fun y => k (x, y) * f y) ν := by
      filter_upwards [hsecs] with x hx
      exact hx.integrable_mul (Lp.memLp f)
    have hfnorm : (∫ y, ‖f y‖ ^ 2 ∂ν) = ‖f‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
        ← integral_re (L2.integrable_inner f f)]
      simp only [inner_self_eq_norm_sq]
    have hknorm : (∫ p, ‖k p‖ ^ 2 ∂μ.prod ν) = ‖k‖ ^ 2 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
        ← integral_re (L2.integrable_inner k k)]
      simp only [inner_self_eq_norm_sq]
    let u : X → ℂ := fun x => ∫ y, k (x, y) * f y ∂ν
    have hu : AEStronglyMeasurable u μ :=
      ((Lp.aestronglyMeasurable k).mul (Lp.aestronglyMeasurable f).comp_snd).integral_prod_right'
    have hb : ∀ᵐ x ∂μ, ‖u x‖ ^ 2 ≤ (∫ y, ‖k (x, y)‖ ^ 2 ∂ν) * ‖f‖ ^ 2 := by
      filter_upwards [hsecs] with x hx
      have hc := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
        (by simpa using hx) (by simpa using Lp.memLp f)
      have hn : ‖u x‖ ≤ Real.sqrt (∫ y, ‖k (x, y)‖ ^ 2 ∂ν) * ‖f‖ := by
        refine (norm_integral_le_integral_norm _).trans ?_
        simpa only [norm_mul, Real.rpow_two, ← Real.sqrt_eq_rpow,
          hfnorm, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg f)] using hc
      have hnon : 0 ≤ ∫ y, ‖k (x, y)‖ ^ 2 ∂ν := integral_nonneg (fun _ => sq_nonneg _)
      have hs := Real.sq_sqrt hnon
      have hp := sq_le_sq₀ (norm_nonneg (u x))
        (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg f)) |>.mpr hn
      nlinarith
    have hbound : Integrable (fun x => (∫ y, ‖k (x, y)‖ ^ 2 ∂ν) * ‖f‖ ^ 2) μ :=
      hk2.integral_prod_left.mul_const _
    have hu2 : Integrable (fun x => ‖u x‖ ^ 2) μ := by
      apply hbound.mono' (hu.norm.pow 2)
      filter_upwards [hb] with x hx
      simpa only [Pi.pow_apply, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖u x‖)] using hx
    have hmem : MemLp u 2 μ := (memLp_two_iff_integrable_sq_norm hu).mpr hu2
    let g : Lp ℂ 2 μ := hmem.toLp u
    have hg : (g : X → ℂ) =ᵐ[μ] u := hmem.coeFn_toLp
    refine ⟨g, hint, hg, ?_⟩
    have hgnorm : ‖g‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂μ := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
        ← integral_re (L2.integrable_inner g g)]
      simp only [inner_self_eq_norm_sq]
      exact integral_congr_ae (hg.fun_comp (fun z => ‖z‖ ^ 2))
    have hi := integral_mono_ae hu2 hbound hb
    rw [integral_mul_const, ← integral_prod _ hk2, hknorm, ← hgnorm] at hi
    apply (sq_le_sq₀ (norm_nonneg g) (mul_nonneg (norm_nonneg k) (norm_nonneg f))).mp
    simpa only [mul_pow] using hi
  choose T hInt hRep hNorm using hmake
  have hAddK (k l : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
      T (k + l) f = T k f + T l f := by
    apply Lp.ext
    filter_upwards [hRep (k + l) f, hRep k f, hRep l f,
      Lp.coeFn_add (T k f) (T l f), Measure.ae_ae_of_ae_prod (Lp.coeFn_add k l),
      hInt k f, hInt l f] with x ha hb hc hd he hi hj
    rw [ha, hd, Pi.add_apply, hb, hc, ← integral_add hi hj]
    apply integral_congr_ae
    filter_upwards [he] with y hy
    simp only [hy, Pi.add_apply, add_mul]
  have hSmulK (c : ℂ) (k : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
      T (c • k) f = c • T k f := by
    apply Lp.ext
    filter_upwards [hRep (c • k) f, hRep k f, Lp.coeFn_smul c (T k f),
      Measure.ae_ae_of_ae_prod (Lp.coeFn_smul c k)] with x ha hb hc hd
    rw [ha, hc, Pi.smul_apply, hb, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [hd] with y hy
    simp only [hy, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hAddF (k : Lp ℂ 2 (μ.prod ν)) (f g : Lp ℂ 2 ν) :
      T k (f + g) = T k f + T k g := by
    apply Lp.ext
    filter_upwards [hRep k (f + g), hRep k f, hRep k g,
      Lp.coeFn_add (T k f) (T k g), hInt k f, hInt k g] with x ha hb hc hd hi hj
    rw [ha, hd, Pi.add_apply, hb, hc, ← integral_add hi hj]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f g] with y hy
    simp only [hy, Pi.add_apply, mul_add]
  have hSmulF (c : ℂ) (k : Lp ℂ 2 (μ.prod ν)) (f : Lp ℂ 2 ν) :
      T k (c • f) = c • T k f := by
    apply Lp.ext
    filter_upwards [hRep k (c • f), hRep k f, Lp.coeFn_smul c (T k f)] with x ha hb hc
    rw [ha, hc, Pi.smul_apply, hb, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c f] with y hy
    simp only [hy, Pi.smul_apply, smul_eq_mul]
    ring
  let B : Lp ℂ 2 (μ.prod ν) →ₗ[ℂ] (Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 μ) :=
    LinearMap.mk₂ ℂ T hAddK hSmulK hAddF hSmulF
  have hB : ∀ k f, ‖B k f‖ ≤ 1 * ‖k‖ * ‖f‖ := by
    intro k f
    simpa only [B, LinearMap.mk₂_apply, one_mul] using hNorm k f
  refine ⟨B.mkContinuous₂ 1 hB, B.mkContinuous₂_norm_le (by norm_num) hB, ?_⟩
  intro k f
  exact ⟨hInt k f, hRep k f, hNorm k f⟩

end D5.S3.Fourier.Asymptotics.L2KernelIntegralOperator
