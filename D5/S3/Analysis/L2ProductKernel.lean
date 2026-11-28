/- GID: D5/S3/Analysis/L2ProductKernel
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-shear-obstruction4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Separated complex kernels define isometric copies of the one-variable Hilbert space when the second factor has unit norm. -/

import OmegaBuild.Commands
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-!
Omega original.

Separated complex kernels define isometric copies of the one-variable Hilbert space
when the second factor has unit norm. These copies are orthogonal for orthogonal
second factors, yielding an L² product kernel from square-summable Hilbert basis data.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace ComplexConjugate

namespace Omega

variable {X ι : Type*} [MeasurableSpace X] (μ : Measure X)

private theorem rankKernel_memLp (f g : Lp ℂ 2 μ) :
    MemLp (fun z : X × X ↦ f z.1 * star (g z.2)) 2 (μ.prod μ) := by
  have hf := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)
  have hg := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).1 (Lp.memLp g)
  have hm : AEStronglyMeasurable (fun z : X × X ↦ f z.1 * star (g z.2)) (μ.prod μ) :=
    (Lp.aestronglyMeasurable f).comp_fst.mul (Lp.memLp g).star.aestronglyMeasurable.comp_snd
  exact (memLp_two_iff_integrable_sq_norm hm).2 (by
    simpa only [norm_mul, norm_star, mul_pow] using hf.mul_prod hg)

/-- The product kernel of the rank-one pairing with second vector `g`. -/
def rankKernel (f g : Lp ℂ 2 μ) : Lp ℂ 2 (μ.prod μ) :=
  (rankKernel_memLp μ f g).toLp (fun z ↦ f z.1 * star (g z.2))

theorem rankKernel_ae (f g : Lp ℂ 2 μ) :
    (rankKernel μ f g : X × X → ℂ) =ᵐ[μ.prod μ] fun z ↦ f z.1 * star (g z.2) :=
  (rankKernel_memLp μ f g).coeFn_toLp

variable [SFinite μ]

private theorem rankKernel_inner (f g f' g' : Lp ℂ 2 μ) :
    ⟪rankKernel μ f g, rankKernel μ f' g'⟫_ℂ = ⟪f, f'⟫_ℂ * ⟪g', g⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def f f', L2.inner_def g' g, ← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards [rankKernel_ae μ f g, rankKernel_ae μ f' g'] with z hz hz'
  rw [hz, hz']
  simp only [RCLike.inner_apply', map_mul]
  change star (f z.1) * star (star (g z.2)) * (f' z.1 * star (g' z.2)) =
    (star (f z.1) * f' z.1) * (star (g' z.2) * g z.2)
  rw [star_star]
  ring

private def rankKernelIsometry (g : Lp ℂ 2 μ) (hg : ‖g‖ = 1) :
    Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 (μ.prod μ) where
  toFun f := rankKernel μ f g
  map_add' f f' := by
    apply Lp.ext
    filter_upwards [rankKernel_ae μ (f + f') g, rankKernel_ae μ f g, rankKernel_ae μ f' g,
      Lp.coeFn_add (rankKernel μ f g) (rankKernel μ f' g),
      (quasiMeasurePreserving_fst (ν := μ)).ae (Lp.coeFn_add f f')] with z hsum hf hf' hright hleft
    rw [hsum, hright, hleft, Pi.add_apply, Pi.add_apply, hf, hf', add_mul]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [rankKernel_ae μ (c • f) g, rankKernel_ae μ f g,
      Lp.coeFn_smul c (rankKernel μ f g),
      (quasiMeasurePreserving_fst (ν := μ)).ae (Lp.coeFn_smul c f)] with z hsmul hf hright hleft
    rw [RingHom.id_apply, hsmul, hright, hleft, Pi.smul_apply, Pi.smul_apply, hf]
    exact mul_assoc _ _ _
  norm_map' f := by
    have h := rankKernel_inner μ f g f g
    simp only [inner_self_eq_norm_sq_to_K, hg] at h
    have hs : ‖rankKernel μ f g‖ ^ 2 = ‖f‖ ^ 2 * (1 : ℝ) ^ 2 := by exact_mod_cast h
    have hsq : ‖rankKernel μ f g‖ ^ 2 = ‖f‖ ^ 2 := by
      simpa only [one_pow, mul_one] using hs
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

/-- Square-summable images of a Hilbert basis yield an L² kernel with the associated pairings. -/
theorem exists_l2_kernel_of_summable_basis (b : HilbertBasis ι ℂ (Lp ℂ 2 μ))
    (v : ι → Lp ℂ 2 μ) (hv : Summable (fun i ↦ ‖v i‖ ^ 2)) :
    ∃ k : Lp ℂ 2 (μ.prod μ), ∀ f g : Lp ℂ 2 μ,
      ⟪rankKernel μ f g, k⟫_ℂ = ∑' i, ⟪f, v i⟫_ℂ * ⟪b i, g⟫_ℂ := by
  let V (i : ι) := rankKernelIsometry μ (b i) (b.orthonormal.1 i)
  have hV : OrthogonalFamily ℂ (fun _ : ι ↦ Lp ℂ 2 μ) V := by
    intro i j hij f g
    change ⟪rankKernel μ f (b i), rankKernel μ g (b j)⟫_ℂ = 0
    rw [rankKernel_inner, b.orthonormal.2 hij.symm, mul_zero]
  have hsum : Summable (fun i ↦ rankKernel μ (v i) (b i)) :=
    (hV.summable_iff_norm_sq_summable v).2 hv
  refine ⟨∑' i, rankKernel μ (v i) (b i), fun f g ↦ ?_⟩
  have hpair := hsum.hasSum.mapL (innerSL ℂ (rankKernel μ f g))
  simp only [innerSL_apply_apply, rankKernel_inner] at hpair
  exact hpair.tsum_eq.symm

end Omega
