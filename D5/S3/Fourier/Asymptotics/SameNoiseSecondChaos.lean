/- GID: D5/S3/Fourier/Asymptotics/SameNoiseSecondChaos
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/SameNoiseSecondChaos
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Same-noise second integral on the full symmetric product-measure L2 space. -/

import D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticFourthMoment
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.HasLaw
import Mathlib.Tactic

noncomputable section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter
open scoped ENNReal NNReal RealInnerProductSpace

namespace D5.S3.Fourier.Asymptotics.SameNoiseSecondChaos

set_option autoImplicit false

section Spatial

variable {X : Type*} [MeasurableSpace X]
variable (μ : Measure X) [IsFiniteMeasure μ]

private theorem rankOne_memLp (f g : Lp ℝ 2 μ) :
    MemLp (fun z : X × X => f z.1 * g z.2) 2 (μ.prod μ) := by
  refine (memLp_two_iff_integrable_sq ?_).2 ?_
  · exact (Lp.aestronglyMeasurable f).comp_fst.mul
      (Lp.aestronglyMeasurable g).comp_snd
  · exact ((Lp.memLp f).integrable_sq.mul_prod (Lp.memLp g).integrable_sq).congr
      (Filter.Eventually.of_forall fun z => by ring)

/-- The actual product-measure L² class of a rank-one spatial kernel. -/
def rankOne (f g : Lp ℝ 2 μ) : Lp ℝ 2 (μ.prod μ) :=
  (rankOne_memLp μ f g).toLp (fun z : X × X => f z.1 * g z.2)

theorem rankOne_coe (f g : Lp ℝ 2 μ) :
    rankOne μ f g =ᵐ[μ.prod μ] (fun z : X × X => f z.1 * g z.2) :=
  (rankOne_memLp μ f g).coeFn_toLp

/-- Flip on the actual L² product-measure space. -/
def kernelFlip : Lp ℝ 2 (μ.prod μ) →ₗᵢ[ℝ] Lp ℝ 2 (μ.prod μ) :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.swap (measurePreserving_swap (μ := μ) (ν := μ))

/-- Fixed subspace of the actual flip; no abstract tensor-space substitute. -/
def symmetricKernel : Submodule ℝ (Lp ℝ 2 (μ.prod μ)) :=
  LinearMap.ker ((kernelFlip μ).toLinearMap - LinearMap.id)

private theorem diagonal_mem (f : Lp ℝ 2 μ) :
    rankOne μ f f ∈ symmetricKernel μ := by
  change kernelFlip μ (rankOne μ f f) - rankOne μ f f = 0
  apply sub_eq_zero.mpr
  apply Lp.ext
  have hf := rankOne_coe μ f f
  have hswap := (measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae_eq hf
  have hflip : kernelFlip μ (rankOne μ f f) =ᵐ[μ.prod μ]
      (fun z : X × X => rankOne μ f f (Prod.swap z)) :=
    Lp.coeFn_compMeasurePreserving (rankOne μ f f)
      (measurePreserving_swap (μ := μ) (ν := μ))
  filter_upwards [hflip, hswap, hf] with z hz hs hr
  change rankOne μ f f (Prod.swap z) = f z.2 * f z.1 at hs
  exact hz.trans (hs.trans ((mul_comm _ _).trans hr.symm))

/-- Actual symmetric diagonal generator. -/
def diagonalKernel (f : Lp ℝ 2 μ) : symmetricKernel μ :=
  ⟨rankOne μ f f, diagonal_mem μ f⟩

/-- Finite coefficients interpreted as actual symmetric spatial kernels. -/
def finiteKernelMap : (Lp ℝ 2 μ →₀ ℝ) →ₗ[ℝ] symmetricKernel μ :=
  Finsupp.linearCombination ℝ (diagonalKernel μ)

/-- Fubini factors the inner product of actual rank-one classes. -/
theorem rankOne_inner (f g h k : Lp ℝ 2 μ) :
    ⟪rankOne μ f g, rankOne μ h k⟫ = ⟪f, h⟫ * ⟪g, k⟫ := by
  rw [L2.inner_def, L2.inner_def, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial]
  calc
    (∫ z, rankOne μ h k z * rankOne μ f g z ∂μ.prod μ) =
        ∫ z : X × X, (h z.1 * f z.1) * (k z.2 * g z.2) ∂μ.prod μ := by
      apply integral_congr_ae
      filter_upwards [rankOne_coe μ f g, rankOne_coe μ h k] with z hz hz'
      rw [hz, hz']; ring
    _ = _ := integral_prod_mul (μ := μ) (ν := μ)
      (fun x : X => h x * f x) (fun x : X => k x * g x)

private theorem rankOne_total (k : Lp ℝ 2 (μ.prod μ))
    (hk : ∀ f g : Lp ℝ 2 μ, ⟪rankOne μ f g, k⟫ = 0) : k = 0 := by
  have hi : Integrable k (μ.prod μ) := (Lp.memLp k).integrable (by norm_num)
  have hr (s t : Set X) (hs : MeasurableSet s) (ht : MeasurableSet t) :
      (∫ z in s ×ˢ t, k z ∂μ.prod μ) = 0 := by
    let f : Lp ℝ 2 μ := indicatorConstLp 2 hs (measure_ne_top μ s) 1
    let g : Lp ℝ 2 μ := indicatorConstLp 2 ht (measure_ne_top μ t) 1
    have hf : f =ᵐ[μ] s.indicator (fun _ => (1 : ℝ)) := indicatorConstLp_coeFn
    have hg : g =ᵐ[μ] t.indicator (fun _ => (1 : ℝ)) := indicatorConstLp_coeFn
    have hf' := (quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq hf
    have hg' := (quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq hg
    have he : ⟪rankOne μ f g, k⟫ = ∫ z in s ×ˢ t, k z ∂μ.prod μ := by
      rw [L2.inner_def, ← integral_indicator (hs.prod ht)]
      apply integral_congr_ae
      filter_upwards [rankOne_coe μ f g, hf', hg'] with z hz hzf hzg
      simp only [RCLike.inner_apply, conj_trivial, Function.comp_def] at *
      rw [hz, hzf, hzg]
      by_cases hzs : z.1 ∈ s <;> by_cases hzt : z.2 ∈ t <;>
        simp [Set.mem_prod, hzs, hzt]
    rw [← he]; exact hk f g
  have hu : (∫ z, k z ∂μ.prod μ) = 0 := by
    simpa using hr Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
  have hall (s : Set (X × X)) (hs : MeasurableSet s) :
      (∫ z in s, k z ∂μ.prod μ) = 0 := by
    refine MeasurableSpace.induction_on_inter generateFrom_prod.symm
      isPiSystem_prod ?_ ?_ ?_ ?_ s hs
    · simp
    · rintro _ ⟨a, ha, b, hb, rfl⟩
      exact hr a b ha hb
    · intro t ht hzero
      have h := integral_add_compl ht hi
      rw [hzero, hu, zero_add] at h
      exact h
    · intro f hd hm hz
      rw [integral_iUnion hm hd hi.integrableOn]
      simp [hz]
  apply Lp.ext
  exact (hi.ae_eq_zero_of_forall_setIntegral_eq_zero
    (fun s hs _ => hall s hs)).trans (Lp.coeFn_zero ℝ 2 (μ.prod μ)).symm

private theorem kernelFlip_rankOne (f g : Lp ℝ 2 μ) :
    kernelFlip μ (rankOne μ f g) = rankOne μ g f := by
  apply Lp.ext
  have hf := rankOne_coe μ f g
  have hswap := (measurePreserving_swap (μ := μ) (ν := μ)).quasiMeasurePreserving.ae_eq hf
  have hflip := Lp.coeFn_compMeasurePreserving (rankOne μ f g)
    (measurePreserving_swap (μ := μ) (ν := μ))
  filter_upwards [hflip, hswap, rankOne_coe μ g f] with z hz hs hr
  change rankOne μ f g (Prod.swap z) = f z.2 * g z.1 at hs
  exact hz.trans (hs.trans ((mul_comm _ _).trans hr.symm))

private theorem diagonal_add (f g : Lp ℝ 2 μ) :
    rankOne μ (f + g) (f + g) = rankOne μ f f + rankOne μ f g +
      rankOne μ g f + rankOne μ g g := by
  apply Lp.ext
  have ha := Lp.coeFn_add f g
  have ha1 := (quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq ha
  have ha2 := (quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq ha
  filter_upwards [rankOne_coe μ (f + g) (f + g), rankOne_coe μ f f,
    rankOne_coe μ f g, rankOne_coe μ g f, rankOne_coe μ g g,
    Lp.coeFn_add (rankOne μ f f + rankOne μ f g + rankOne μ g f) (rankOne μ g g),
    Lp.coeFn_add (rankOne μ f f + rankOne μ f g) (rankOne μ g f),
    Lp.coeFn_add (rankOne μ f f) (rankOne μ f g), ha1, ha2] with z h hff hfg hgf hgg h3 h2 h1 ha1 ha2
  simp only [Function.comp_def, Pi.add_apply] at ha1 ha2
  simp only [Pi.add_apply] at h3 h2 h1
  rw [h, h3, h2, h1, hff, hfg, hgf, hgg, ha1, ha2]
  ring

instance symmetricKernel_complete : CompleteSpace (symmetricKernel μ) := by
  let T : Lp ℝ 2 (μ.prod μ) →L[ℝ] Lp ℝ 2 (μ.prod μ) :=
    (kernelFlip μ).toContinuousLinearMap - ContinuousLinearMap.id ℝ _
  have hc : IsClosed (symmetricKernel μ : Set (Lp ℝ 2 (μ.prod μ))) := T.isClosed_ker
  exact hc.completeSpace_coe

/-- The actual diagonal-kernel finite map has dense range in the full symmetric L² space. -/
theorem finiteKernelMap_dense : DenseRange (finiteKernelMap μ) := by
  have hclosure : (LinearMap.range (finiteKernelMap μ)).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro k hk
    have hd (f : Lp ℝ 2 μ) : ⟪rankOne μ f f, k.val⟫ = 0 := by
      have hf : diagonalKernel μ f ∈ LinearMap.range (finiteKernelMap μ) := by
        refine ⟨Finsupp.single f 1, ?_⟩
        simp [finiteKernelMap]
      have h := (Submodule.mem_orthogonal _ k).mp hk (diagonalKernel μ f) hf
      exact h
    have hsym : kernelFlip μ k.val = k.val := by
      have h := k.property
      change kernelFlip μ k.val - k.val = 0 at h
      exact sub_eq_zero.mp h
    have hf (f g : Lp ℝ 2 μ) : ⟪rankOne μ f g, k.val⟫ = ⟪rankOne μ g f, k.val⟫ := by
      have h := (kernelFlip μ).inner_map_map (rankOne μ f g) k.val
      rw [kernelFlip_rankOne μ f g, hsym] at h
      exact h.symm
    have hz : k.val = 0 := rankOne_total μ k.val (by
      intro f g
      have h := hd (f + g)
      rw [diagonal_add μ f g, inner_add_left, inner_add_left, inner_add_left,
        hd f, hd g, ← hf f g] at h
      linarith)
    exact Subtype.ext hz
  rw [DenseRange, dense_iff_closure_eq]
  rw [← LinearMap.coe_range, ← Submodule.topologicalClosure_coe, hclosure]
  rfl


end Spatial

section SameNoise

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
variable (μ : Measure X) [IsFiniteMeasure μ]
variable (P : Measure Ω) [IsProbabilityMeasure P]
variable (W : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 P)
variable (hW : ∀ f : Lp ℝ 2 μ,
  HasLaw (fun ω => W f ω) (gaussianReal 0 (‖f‖ ^ 2).toNNReal) P)

include hW

private theorem gaussian_memLp_four (f : Lp ℝ 2 μ) :
    MemLp (fun ω => W f ω) 4 P := by
  have hm : MemLp id 4 (P.map (fun ω => W f ω)) := by
    rw [(hW f).map_eq]
    exact memLp_id_gaussianReal' 4 (by norm_num)
  simpa only [Function.id_comp] using
    (memLp_map_measure_iff aestronglyMeasurable_id (hW f).aemeasurable).mp hm

private theorem gaussianProduct_memLp (f g : Lp ℝ 2 μ) :
    MemLp (fun ω => W f ω * W g ω) 2 P := by
  letI : ENNReal.HolderTriple 4 4 2 := ⟨by
    have h4 : (4 : ℝ≥0∞)⁻¹ = ((4 : ℝ≥0)⁻¹ : ℝ≥0) :=
      (ENNReal.coe_inv (by norm_num : (4 : ℝ≥0) ≠ 0)).symm
    have h2 : (2 : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0)⁻¹ : ℝ≥0) :=
      (ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0)).symm
    rw [h4, h2, ← ENNReal.coe_add]
    norm_num⟩
  exact (gaussian_memLp_four μ P W hW g).mul'
    (gaussian_memLp_four μ P W hW f)

/-- Actual L²(P) class of the original W's centered square. -/
def centeredSquare (f : Lp ℝ 2 μ) : Lp ℝ 2 P :=
  ((gaussianProduct_memLp μ P W hW f f).sub
    (memLp_const (‖f‖ ^ 2))).toLp
      (fun ω => W f ω * W f ω - ‖f‖ ^ 2)

/-- The same finite coefficients interpreted on the original probability space. -/
def finiteNoiseMap : (Lp ℝ 2 μ →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 P :=
  Finsupp.linearCombination ℝ (centeredSquare μ P W hW)


/-- The actual representative of the centered-square class. -/
theorem centeredSquare_coe (f : Lp ℝ 2 μ) :
    centeredSquare μ P W hW f =ᵐ[P] (fun ω => (W f ω)^2 - ‖f‖^2) := by
  have h := ((gaussianProduct_memLp μ P W hW f f).sub
    (memLp_const (‖f‖ ^ 2))).coeFn_toLp
  filter_upwards [h] with ω hω
  change _ = W f ω * W f ω - ‖f‖^2 at hω
  exact hω.trans (by ring)

/-- Transport the exact scalar supplier along the law of this fixed W. -/
theorem fourthMoment (f : Lp ℝ 2 μ) :
    (∫ ω, (W f ω)^4 ∂P) = 3 * ‖f‖^4 := by
  have hv : (‖f‖ ^ 2).toNNReal = ‖f‖₊ ^ 2 := by
    apply NNReal.eq
    simp [Real.coe_toNNReal _ (sq_nonneg _)]
  have h := CountableGaussianQuadraticFourthMoment.centralMoment_two_mul 0 ‖f‖₊ 2
  have hs : (∫ x : ℝ, x^4 ∂gaussianReal 0 (‖f‖ ^ 2).toNNReal) = 3 * ‖f‖^4 := by
    rw [hv]
    simpa [centralMoment, integral_id_gaussianReal, mul_comm] using h
  exact ((hW f).integral_comp (f := fun x : ℝ => x^4) (by fun_prop)).trans hs

private theorem fourth_integrable (f : Lp ℝ 2 μ) :
    Integrable (fun ω => (W f ω)^4) P := by
  apply ((gaussian_memLp_four μ P W hW f).integrable_norm_pow' (p := 4)).mono'
    ((Lp.aestronglyMeasurable (W f)).pow 4)
  filter_upwards [] with ω
  simp [norm_pow]

omit hW in
private theorem secondMoment (f : Lp ℝ 2 μ) :
    (∫ ω, (W f ω)^2 ∂P) = ‖f‖^2 := by
  have h := real_inner_self_eq_norm_sq (W f)
  rw [L2.inner_def] at h
  simpa [RCLike.inner_apply, conj_trivial, W.norm_map, pow_two] using h

/-- Polarization of scalar fourth moments retains the same W and probability law. -/
theorem squareProductMoment (f g : Lp ℝ 2 μ) :
    (∫ ω, (W f ω * W g ω)^2 ∂P) = ‖f‖^2 * ‖g‖^2 + 2 * ⟪f, g⟫^2 := by
  have ha : (fun ω => W (f + g) ω) =ᵐ[P] (fun ω => W f ω + W g ω) := by
    rw [map_add]; exact Lp.coeFn_add _ _
  have hs : (fun ω => W (f - g) ω) =ᵐ[P] (fun ω => W f ω - W g ω) := by
    rw [map_sub]; exact Lp.coeFn_sub _ _
  have ia : Integrable (fun ω => (W f ω + W g ω)^4) P :=
    (fourth_integrable μ P W hW (f + g)).congr (ha.fun_comp (fun x : ℝ => x^4))
  have is : Integrable (fun ω => (W f ω - W g ω)^4) P :=
    (fourth_integrable μ P W hW (f - g)).congr (hs.fun_comp (fun x : ℝ => x^4))
  have if' := fourth_integrable μ P W hW f
  have ig' := fourth_integrable μ P W hW g
  have ea : (∫ ω, (W f ω + W g ω)^4 ∂P) = 3 * ‖f + g‖^4 :=
    (integral_congr_ae (ha.fun_comp (fun x : ℝ => x^4))).symm.trans
      (fourthMoment μ P W hW (f + g))
  have es : (∫ ω, (W f ω - W g ω)^4 ∂P) = 3 * ‖f - g‖^4 :=
    (integral_congr_ae (hs.fun_comp (fun x : ℝ => x^4))).symm.trans
      (fourthMoment μ P W hW (f - g))
  have hid : 12 * (∫ ω, (W f ω * W g ω)^2 ∂P) =
      (∫ ω, (W f ω + W g ω)^4 ∂P) + (∫ ω, (W f ω - W g ω)^4 ∂P) -
      2 * (∫ ω, (W f ω)^4 ∂P) - 2 * (∫ ω, (W g ω)^4 ∂P) := by
    rw [← integral_const_mul]
    calc
      (∫ ω, 12 * (W f ω * W g ω)^2 ∂P) =
          ∫ ω, ((W f ω + W g ω)^4 + (W f ω - W g ω)^4 -
            2 * (W f ω)^4) - 2 * (W g ω)^4 ∂P := by
        apply integral_congr_ae; filter_upwards [] with ω; ring
      _ = _ := by
        let A : Ω → ℝ := fun ω => (W f ω + W g ω)^4
        let B : Ω → ℝ := fun ω => (W f ω - W g ω)^4
        let C : Ω → ℝ := fun ω => 2 * (W f ω)^4
        let D : Ω → ℝ := fun ω => 2 * (W g ω)^4
        have hA : Integrable A P := by simpa [A] using ia
        have hB : Integrable B P := by simpa [B] using is
        have hC : Integrable C P := by simpa [C] using if'.const_mul 2
        have hD : Integrable D P := by simpa [D] using ig'.const_mul 2
        have hsplit :
            (∫ ω, A ω + B ω - C ω - D ω ∂P) =
              (∫ ω, A ω ∂P) + (∫ ω, B ω ∂P) -
                2 * (∫ ω, (W f ω)^4 ∂P) -
                2 * (∫ ω, (W g ω)^4 ∂P) := by
          have hfun : (fun ω => A ω + B ω - C ω - D ω) =
              ((A + B) - C) - D := by
            funext ω
            dsimp
          calc
            (∫ ω, A ω + B ω - C ω - D ω ∂P) =
                ∫ ω, (((A + B) - C) ω - D ω) ∂P := by
                  apply integral_congr_ae
                  filter_upwards [] with ω
                  exact congrFun hfun ω
            _ = (∫ ω, ((A + B) - C) ω ∂P) - (∫ ω, D ω ∂P) :=
              by simpa only [Pi.sub_apply] using
                (integral_sub ((hA.add hB).sub hC) hD)
            _ = ((∫ ω, (A + B) ω ∂P) - (∫ ω, C ω ∂P)) -
                (∫ ω, D ω ∂P) := by
                  have hh := integral_sub (hA.add hB) hC
                  simpa only [Pi.sub_apply, Pi.add_apply] using
                    congrArg (fun x : ℝ => x - (∫ ω, D ω ∂P)) hh
            _ = ((∫ ω, A ω ∂P) + (∫ ω, B ω ∂P) -
                (∫ ω, C ω ∂P)) - (∫ ω, D ω ∂P) := by
                  have hh := integral_add hA hB
                  simpa only [Pi.add_apply] using
                    congrArg (fun x : ℝ => x - (∫ ω, C ω ∂P) - (∫ ω, D ω ∂P)) hh
            _ = _ := by
              simp [C, D, integral_const, probReal_univ, integral_const_mul]
        simpa [A, B, C, D] using hsplit
  rw [ea, es, fourthMoment μ P W hW f, fourthMoment μ P W hW g] at hid
  have na := norm_add_sq_real f g
  have ns := norm_sub_sq_real f g
  have pa : ‖f + g‖^4 = (‖f‖^2 + 2 * ⟪f, g⟫ + ‖g‖^2)^2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, na]
  have ps : ‖f - g‖^4 = (‖f‖^2 - 2 * ⟪f, g⟫ + ‖g‖^2)^2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, ns]
  rw [pa, ps] at hid
  nlinarith [hid]

/-- Exact centered-square covariance, without a covariance hypothesis. -/
theorem centeredSquare_inner (f g : Lp ℝ 2 μ) :
    ⟪centeredSquare μ P W hW f, centeredSquare μ P W hW g⟫ = 2 * ⟪f, g⟫^2 := by
  have im := (gaussianProduct_memLp μ P W hW f g).integrable_sq
  have iff := (Lp.memLp (W f)).integrable_sq
  have igg := (Lp.memLp (W g)).integrable_sq
  rw [L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial]
  calc
    (∫ ω, centeredSquare μ P W hW g ω * centeredSquare μ P W hW f ω ∂P) =
        ∫ ω, ((W f ω * W g ω)^2 - ‖g‖^2 * (W f ω)^2 -
          ‖f‖^2 * (W g ω)^2) + ‖f‖^2 * ‖g‖^2 ∂P := by
      apply integral_congr_ae
      filter_upwards [centeredSquare_coe μ P W hW f,
        centeredSquare_coe μ P W hW g] with ω hf hg
      rw [hf, hg]; ring
    _ = _ := by
      let A : Ω → ℝ := fun ω => (W f ω * W g ω)^2
      let B : Ω → ℝ := fun ω => ‖g‖^2 * (W f ω)^2
      let C : Ω → ℝ := fun ω => ‖f‖^2 * (W g ω)^2
      let D : Ω → ℝ := fun _ => ‖f‖^2 * ‖g‖^2
      have hA : Integrable A P := by simpa [A] using im
      have hB : Integrable B P := by simpa [B] using iff.const_mul (‖g‖^2)
      have hC : Integrable C P := by simpa [C] using igg.const_mul (‖f‖^2)
      have hD : Integrable D P := by simpa [D] using (integrable_const (‖f‖^2 * ‖g‖^2))
      have hsplit :
          (∫ ω, A ω - B ω - C ω + D ω ∂P) =
            (∫ ω, A ω ∂P) - (∫ ω, B ω ∂P) - (∫ ω, C ω ∂P) +
              (∫ ω, D ω ∂P) := by
        have hfun : (fun ω => A ω - B ω - C ω + D ω) =
            ((A - B) - C) + D := by
          funext ω
          dsimp
        calc
          (∫ ω, A ω - B ω - C ω + D ω ∂P) =
              ∫ ω, (((A - B) - C) ω + D ω) ∂P := by
                apply integral_congr_ae
                filter_upwards [] with ω
                exact congrFun hfun ω
          _ = (∫ ω, ((A - B) - C) ω ∂P) + (∫ ω, D ω ∂P) :=
            by simpa only [Pi.add_apply] using
              (integral_add ((hA.sub hB).sub hC) hD)
          _ = ((∫ ω, (A - B) ω ∂P) - (∫ ω, C ω ∂P)) +
              (∫ ω, D ω ∂P) := by
                have hh := integral_sub (hA.sub hB) hC
                simpa only [Pi.sub_apply, Pi.sub_apply] using
                  congrArg (fun x : ℝ => x + (∫ ω, D ω ∂P)) hh
          _ = ((∫ ω, A ω ∂P) - (∫ ω, B ω ∂P) -
              (∫ ω, C ω ∂P)) + (∫ ω, D ω ∂P) := by
                have hh := integral_sub hA hB
                simpa only [Pi.sub_apply] using
                  congrArg (fun x : ℝ => x - (∫ ω, C ω ∂P) + (∫ ω, D ω ∂P)) hh
      have hAint : (∫ ω, A ω ∂P) = ‖f‖^2 * ‖g‖^2 + 2 * ⟪f, g⟫^2 := by
        simpa [A] using squareProductMoment μ P W hW f g
      have hBint : (∫ ω, B ω ∂P) = ‖g‖^2 * ‖f‖^2 := by
        dsimp [B]
        rw [integral_const_mul, secondMoment μ P W f]
      have hCint : (∫ ω, C ω ∂P) = ‖f‖^2 * ‖g‖^2 := by
        dsimp [C]
        rw [integral_const_mul, secondMoment μ P W g]
      have hDint : (∫ ω, D ω ∂P) = ‖f‖^2 * ‖g‖^2 := by
        simp [D, integral_const, probReal_univ]
      have hh :
          (∫ ω, A ω - B ω - C ω + D ω ∂P) =
            (‖f‖^2 * ‖g‖^2 + 2 * ⟪f, g⟫^2) -
              ‖g‖^2 * ‖f‖^2 - ‖f‖^2 * ‖g‖^2 + ‖f‖^2 * ‖g‖^2 := by
        rw [hsplit, hAint, hBint, hCint, hDint]
      calc
        _ = (‖f‖^2 * ‖g‖^2 + 2 * ⟪f, g⟫^2) -
              ‖g‖^2 * ‖f‖^2 - ‖f‖^2 * ‖g‖^2 + ‖f‖^2 * ‖g‖^2 := by
          simpa [A, B, C, D] using hh
        _ = _ := by ring
      

/-- The finite free-module maps have the exact same Gram matrix up to factor two. -/
theorem finiteGram (c b : Lp ℝ 2 μ →₀ ℝ) :
    ⟪finiteNoiseMap μ P W hW c, finiteNoiseMap μ P W hW b⟫ =
      2 * ⟪finiteKernelMap μ c, finiteKernelMap μ b⟫ := by
  classical
  simp only [finiteNoiseMap, finiteKernelMap, Finsupp.linearCombination_apply,
    Finsupp.sum_inner, Finsupp.inner_sum, real_inner_smul_left, real_inner_smul_right]
  simp only [centeredSquare_inner μ P W hW, Submodule.coe_inner, diagonalKernel,
    rankOne_inner, pow_two]
  simp only [Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro g hg
  ring

/-- Zero-kernel relations vanish on the original probability space. -/
theorem zeroKernel (c : Lp ℝ 2 μ →₀ ℝ) (hc : finiteKernelMap μ c = 0) :
    finiteNoiseMap μ P W hW c = 0 := by
  have h := finiteGram μ P W hW c c
  rw [hc, inner_zero_right, mul_zero, real_inner_self_eq_norm_sq] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (finiteNoiseMap μ P W hW c)])

private theorem finiteBound (c : Lp ℝ 2 μ →₀ ℝ) :
    ‖finiteNoiseMap μ P W hW c‖ ≤ Real.sqrt 2 * ‖finiteKernelMap μ c‖ := by
  have h := finiteGram μ P W hW c c
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  have h2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : 0 ≤ Real.sqrt 2 * ‖finiteKernelMap μ c‖ := by positivity
  nlinarith [norm_nonneg (finiteNoiseMap μ P W hW c)]

/-- The second integral on actual finite diagonal-kernel sums, via the quotient by relations. -/
def finiteSecondIntegral : LinearMap.range (finiteKernelMap μ) →L[ℝ] Lp ℝ 2 P :=
  (finiteNoiseMap μ P W hW).compLeftInverse (finiteKernelMap μ)

/-- Every finite coefficient vector is sent to its same-W centered squares. -/
theorem finiteSecondIntegral_apply (c : Lp ℝ 2 μ →₀ ℝ) :
    finiteSecondIntegral μ P W hW
      ⟨finiteKernelMap μ c, LinearMap.mem_range_self _ c⟩ = finiteNoiseMap μ P W hW c := by
  exact LinearMap.compLeftInverse_apply_of_bdd _ _
    ⟨Real.sqrt 2, finiteBound μ P W hW⟩ c _ rfl

/-- The continuous same-W second integral on all actual symmetric product-space kernels. -/
def secondIntegral : symmetricKernel μ →L[ℝ] Lp ℝ 2 P :=
  (finiteNoiseMap μ P W hW).extendOfNorm (finiteKernelMap μ)

private theorem secondIntegral_apply (c : Lp ℝ 2 μ →₀ ℝ) :
    secondIntegral μ P W hW (finiteKernelMap μ c) = finiteNoiseMap μ P W hW c :=
  LinearMap.extendOfNorm_eq (finiteKernelMap_dense μ)
    ⟨Real.sqrt 2, finiteBound μ P W hW⟩ c

private theorem secondIntegral_diagonal (f : Lp ℝ 2 μ) :
    secondIntegral μ P W hW (diagonalKernel μ f) = centeredSquare μ P W hW f := by
  simpa [finiteKernelMap, finiteNoiseMap] using
    secondIntegral_apply μ P W hW (Finsupp.single f 1)

private theorem secondIntegral_inner (k l : symmetricKernel μ) :
    ⟪secondIntegral μ P W hW k, secondIntegral μ P W hW l⟫ = 2 * ⟪k, l⟫ := by
  refine (finiteKernelMap_dense μ).induction_on₂
    (p := fun k l => ⟪secondIntegral μ P W hW k, secondIntegral μ P W hW l⟫ = 2 * ⟪k, l⟫)
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_ k l
  intro c b
  rw [secondIntegral_apply, secondIntegral_apply]
  exact finiteGram μ P W hW c b

private theorem secondIntegral_norm (k : symmetricKernel μ) :
    ‖secondIntegral μ P W hW k‖ = Real.sqrt 2 * ‖k‖ := by
  have h := secondIntegral_inner μ P W hW k k
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  have hs : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
  have he : (Real.sqrt 2 * ‖k‖)^2 = 2 * ‖k‖^2 := by rw [mul_pow, hs]
  have hn : 0 ≤ Real.sqrt 2 * ‖k‖ := by positivity
  nlinarith [norm_nonneg (secondIntegral μ P W hW k)]

omit hW in
private theorem inner_one_integral (Z : Lp ℝ 2 P) :
    ⟪(memLp_const (1 : ℝ) (p := 2) (μ := P)).toLp (fun _ => 1), Z⟫ = ∫ ω, Z ω ∂P := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(memLp_const (1 : ℝ) (p := 2) (μ := P)).coeFn_toLp] with ω hω
  simp only [RCLike.inner_apply, conj_trivial]
  rw [hω, mul_one]

private theorem centeredSquare_mean (f : Lp ℝ 2 μ) :
    (∫ ω, centeredSquare μ P W hW f ω ∂P) = 0 := by
  calc
    _ = ∫ ω, (W f ω)^2 - ‖f‖^2 ∂P := integral_congr_ae (centeredSquare_coe μ P W hW f)
    _ = (∫ ω, (W f ω)^2 ∂P) - ∫ _ : Ω, ‖f‖^2 ∂P :=
      integral_sub (Lp.memLp (W f)).integrable_sq (integrable_const _)
    _ = 0 := by rw [secondMoment μ P W f]; simp

private theorem secondIntegral_mean (k : symmetricKernel μ) :
    (∫ ω, secondIntegral μ P W hW k ω ∂P) = 0 := by
  rw [← inner_one_integral P]
  refine (finiteKernelMap_dense μ).induction_on k
    (p := fun k => ⟪(memLp_const (1 : ℝ) (p := 2) (μ := P)).toLp (fun _ => 1),
      secondIntegral μ P W hW k⟫ = 0)
    (isClosed_eq (by fun_prop) continuous_const) ?_
  intro c
  rw [secondIntegral_apply]
  classical
  simp only [finiteNoiseMap, Finsupp.linearCombination_apply, Finsupp.inner_sum,
    real_inner_smul_right]
  simp only [inner_one_integral P, centeredSquare_mean μ P W hW,
    mul_zero, Finsupp.sum, Finset.sum_const_zero]

private theorem secondIntegral_unique (J : symmetricKernel μ →L[ℝ] Lp ℝ 2 P)
    (hJ : ∀ f : Lp ℝ 2 μ, J (diagonalKernel μ f) = centeredSquare μ P W hW f) :
    J = secondIntegral μ P W hW := by
  apply ContinuousLinearMap.ext
  intro k
  refine (finiteKernelMap_dense μ).induction_on k
    (p := fun k => J k = secondIntegral μ P W hW k)
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro c
  rw [secondIntegral_apply]
  classical
  simp only [finiteKernelMap, finiteNoiseMap, Finsupp.linearCombination_apply,
    map_finsuppSum, map_smul, hJ]

/-- The extension has the original mean, covariance, exact norm, and uniqueness on the same W. -/
theorem secondIntegral_characterization :
    (∀ k : symmetricKernel μ, (∫ ω, secondIntegral μ P W hW k ω ∂P) = 0) ∧
    (∀ k l : symmetricKernel μ,
      ⟪secondIntegral μ P W hW k, secondIntegral μ P W hW l⟫ = 2 * ⟪k, l⟫) ∧
    (∀ k : symmetricKernel μ, ‖secondIntegral μ P W hW k‖ = Real.sqrt 2 * ‖k‖) ∧
    (∀ J : symmetricKernel μ →L[ℝ] Lp ℝ 2 P,
      (∀ f : Lp ℝ 2 μ, J (diagonalKernel μ f) = centeredSquare μ P W hW f) →
      J = secondIntegral μ P W hW) :=
  ⟨secondIntegral_mean μ P W hW, secondIntegral_inner μ P W hW,
    secondIntegral_norm μ P W hW, secondIntegral_unique μ P W hW⟩

/-- Symmetrization as an actual symmetric product-measure class. -/
def symmetrizedKernel (f g : Lp ℝ 2 μ) : symmetricKernel μ :=
  (1 / 2 : ℝ) • (diagonalKernel μ (f + g) - diagonalKernel μ f - diagonalKernel μ g)

/-- The extension sends symmetrized products to the original centered W products. -/
theorem secondIntegral_product (f g : Lp ℝ 2 μ) :
    ((symmetrizedKernel μ f g).val =ᵐ[μ.prod μ]
      (fun z : X × X => (f z.1 * g z.2 + g z.1 * f z.2) / 2)) ∧
    (secondIntegral μ P W hW (symmetrizedKernel μ f g) =ᵐ[P]
      (fun ω => W f ω * W g ω - ⟪f, g⟫)) := by
  constructor
  · have he : (symmetrizedKernel μ f g).val =
        (1 / 2 : ℝ) • (rankOne μ f g + rankOne μ g f) := by
      change (1 / 2 : ℝ) • (rankOne μ (f + g) (f + g) -
        rankOne μ f f - rankOne μ g g) = _
      rw [diagonal_add μ f g]
      congr 1
      abel
    rw [he]
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ) (rankOne μ f g + rankOne μ g f),
      Lp.coeFn_add (rankOne μ f g) (rankOne μ g f), rankOne_coe μ f g,
      rankOne_coe μ g f] with z hsm hadd hfg hgf
    simp only [Pi.smul_apply, smul_eq_mul] at hsm
    simp only [Pi.add_apply] at hadd
    rw [hsm, hadd, hfg, hgf]
    ring
  · have he : secondIntegral μ P W hW (symmetrizedKernel μ f g) =
        (1 / 2 : ℝ) • (centeredSquare μ P W hW (f + g) -
          centeredSquare μ P W hW f - centeredSquare μ P W hW g) := by
      simp only [symmetrizedKernel, map_smul, map_sub, secondIntegral_diagonal]
    rw [he]
    have ha : (fun ω => W (f + g) ω) =ᵐ[P] (fun ω => W f ω + W g ω) := by
      rw [map_add]; exact Lp.coeFn_add _ _
    filter_upwards [Lp.coeFn_smul (1 / 2 : ℝ)
        (centeredSquare μ P W hW (f + g) - centeredSquare μ P W hW f - centeredSquare μ P W hW g),
      Lp.coeFn_sub (centeredSquare μ P W hW (f + g) - centeredSquare μ P W hW f)
        (centeredSquare μ P W hW g),
      Lp.coeFn_sub (centeredSquare μ P W hW (f + g)) (centeredSquare μ P W hW f),
      centeredSquare_coe μ P W hW (f + g), centeredSquare_coe μ P W hW f,
      centeredSquare_coe μ P W hW g, ha] with ω hsm hsub hsub' hsum hf hg ha
    simp only [Pi.smul_apply, smul_eq_mul] at hsm
    simp only [Pi.sub_apply] at hsub hsub'
    rw [hsm, hsub, hsub', hsum, hf, hg, ha, norm_add_sq_real]
    ring

end SameNoise

section Frequency

variable (μ : Measure ℝ) [IsFiniteMeasure μ]

private theorem cos_memLp (v : ℝ) :
    MemLp (fun x : ℝ => Real.cos ((Real.pi / 2) * v * x)) 2 μ := by
  apply MemLp.of_bound (by fun_prop) 1
  refine ae_of_all _ fun x => ?_
  simpa [Real.norm_eq_abs] using Real.abs_cos_le_one ((Real.pi / 2) * v * x)

private theorem sin_memLp (v : ℝ) :
    MemLp (fun x : ℝ => Real.sin ((Real.pi / 2) * v * x)) 2 μ := by
  apply MemLp.of_bound (by fun_prop) 1
  refine ae_of_all _ fun x => ?_
  simpa [Real.norm_eq_abs] using Real.abs_sin_le_one ((Real.pi / 2) * v * x)

/-- The original cosine frequency at omega = pi/2. -/
def cosineVector (v : ℝ) : Lp ℝ 2 μ :=
  (cos_memLp μ v).toLp (fun x => Real.cos ((Real.pi / 2) * v * x))

/-- The original sine frequency at omega = pi/2. -/
def sineVector (v : ℝ) : Lp ℝ 2 μ :=
  (sin_memLp μ v).toLp (fun x => Real.sin ((Real.pi / 2) * v * x))

/-- The constant vector retains the actual unnormalized spatial mass. -/
def oneVector : Lp ℝ 2 μ := (memLp_const (1 : ℝ)).toLp (fun _ => 1)

private theorem cosineVector_coe (v : ℝ) : cosineVector μ v =ᵐ[μ]
    (fun x => Real.cos ((Real.pi / 2) * v * x)) := (cos_memLp μ v).coeFn_toLp

private theorem sineVector_coe (v : ℝ) : sineVector μ v =ᵐ[μ]
    (fun x => Real.sin ((Real.pi / 2) * v * x)) := (sin_memLp μ v).coeFn_toLp

private theorem oneVector_coe : oneVector μ =ᵐ[μ] (fun _ => (1 : ℝ)) :=
  (memLp_const (1 : ℝ)).coeFn_toLp

private theorem norm_sq_integral (f : Lp ℝ 2 μ) : ‖f‖^2 = ∫ x, (f x)^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp [RCLike.inner_apply, conj_trivial, pow_two]

/-- Trigonometric centering cancels with the original mass, including mass zero. -/
theorem frequency_energy (v : ℝ) :
    ‖cosineVector μ v‖^2 + ‖sineVector μ v‖^2 = ‖oneVector μ‖^2 := by
  rw [norm_sq_integral, norm_sq_integral, norm_sq_integral,
    ← integral_add (Lp.memLp _).integrable_sq (Lp.memLp _).integrable_sq]
  apply integral_congr_ae
  filter_upwards [cosineVector_coe μ v, sineVector_coe μ v, oneVector_coe μ] with x hc hs h1
  rw [hc, hs, h1]
  simpa [add_comm] using Real.sin_sq_add_cos_sq ((Real.pi / 2) * v * x)

/-- The actual finite coefficients of cos(omega*v*(x-y))-1. -/
def frequencyCoefficients (v : ℝ) : Lp ℝ 2 μ →₀ ℝ :=
  Finsupp.single (cosineVector μ v) 1 + Finsupp.single (sineVector μ v) 1 -
    Finsupp.single (oneVector μ) 1

/-- An actual finite symmetric kernel in the range of the diagonal map. -/
def frequencyKernel (v : ℝ) : LinearMap.range (finiteKernelMap μ) :=
  ⟨finiteKernelMap μ (frequencyCoefficients μ v), LinearMap.mem_range_self _ _⟩

/-- The quotient-range kernel is the actual cosine difference on product measure. -/
theorem frequencyKernel_coe (v : ℝ) :
    (frequencyKernel μ v).val.val =ᵐ[μ.prod μ]
      (fun z : ℝ × ℝ => Real.cos ((Real.pi / 2) * v * (z.1 - z.2)) - 1) := by
  have he : (frequencyKernel μ v).val.val =
      rankOne μ (cosineVector μ v) (cosineVector μ v) +
      rankOne μ (sineVector μ v) (sineVector μ v) - rankOne μ (oneVector μ) (oneVector μ) := by
    simp [frequencyKernel, frequencyCoefficients, finiteKernelMap, diagonalKernel]
  rw [he]
  have hc1 := (quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq (cosineVector_coe μ v)
  have hc2 := (quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq (cosineVector_coe μ v)
  have hs1 := (quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq (sineVector_coe μ v)
  have hs2 := (quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq (sineVector_coe μ v)
  have h11 := (quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq (oneVector_coe μ)
  have h12 := (quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq (oneVector_coe μ)
  have hc1' : (fun z : ℝ × ℝ => cosineVector μ v z.1) =ᵐ[μ.prod μ]
      (fun z => Real.cos ((Real.pi / 2) * v * z.1)) := by
    simpa [Function.comp_def] using hc1
  have hc2' : (fun z : ℝ × ℝ => cosineVector μ v z.2) =ᵐ[μ.prod μ]
      (fun z => Real.cos ((Real.pi / 2) * v * z.2)) := by
    simpa [Function.comp_def] using hc2
  have hs1' : (fun z : ℝ × ℝ => sineVector μ v z.1) =ᵐ[μ.prod μ]
      (fun z => Real.sin ((Real.pi / 2) * v * z.1)) := by
    simpa [Function.comp_def] using hs1
  have hs2' : (fun z : ℝ × ℝ => sineVector μ v z.2) =ᵐ[μ.prod μ]
      (fun z => Real.sin ((Real.pi / 2) * v * z.2)) := by
    simpa [Function.comp_def] using hs2
  have h11' : (fun z : ℝ × ℝ => oneVector μ z.1) =ᵐ[μ.prod μ]
      (fun _ => (1 : ℝ)) := by
    simpa [Function.comp_def] using h11
  have h12' : (fun z : ℝ × ℝ => oneVector μ z.2) =ᵐ[μ.prod μ]
      (fun _ => (1 : ℝ)) := by
    simpa [Function.comp_def] using h12
  have hsub' :
      (fun z : ℝ × ℝ =>
        (rankOne μ (cosineVector μ v) (cosineVector μ v) +
          rankOne μ (sineVector μ v) (sineVector μ v) -
          rankOne μ (oneVector μ) (oneVector μ)) z) =ᵐ[μ.prod μ]
        (fun z : ℝ × ℝ =>
          (rankOne μ (cosineVector μ v) (cosineVector μ v) +
            rankOne μ (sineVector μ v) (sineVector μ v)) z -
            rankOne μ (oneVector μ) (oneVector μ) z) :=
    Lp.coeFn_sub _ _
  have hadd' :
      (fun z : ℝ × ℝ =>
        (rankOne μ (cosineVector μ v) (cosineVector μ v) +
          rankOne μ (sineVector μ v) (sineVector μ v)) z) =ᵐ[μ.prod μ]
        (fun z : ℝ × ℝ =>
          rankOne μ (cosineVector μ v) (cosineVector μ v) z +
            rankOne μ (sineVector μ v) (sineVector μ v) z) :=
    Lp.coeFn_add _ _
  filter_upwards [hsub', hadd',
    rankOne_coe μ (cosineVector μ v) (cosineVector μ v),
    rankOne_coe μ (sineVector μ v) (sineVector μ v),
    rankOne_coe μ (oneVector μ) (oneVector μ), hc1', hc2', hs1', hs2', h11', h12']
    with z hsub hadd hrc hrs hr1 hc1 hc2 hs1 hs2 h11 h12
  rw [hsub, hadd, hrc, hrs, hr1, hc1, hc2, hs1, hs2, h11, h12]
  rw [mul_sub, Real.cos_sub]
  ring

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]
variable (W : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 P)
variable (hW : ∀ f : Lp ℝ 2 μ,
  HasLaw (fun ω => W f ω) (gaussianReal 0 (‖f‖ ^ 2).toNNReal) P)

include hW

/-- The finite second integral is the actual same-W |F(v)|^2-Y^2 representative. -/
theorem finiteFrequency_sameNoise (v : ℝ) :
    finiteSecondIntegral μ P W hW (frequencyKernel μ v) =ᵐ[P]
      (fun ω => (W (cosineVector μ v) ω)^2 + (W (sineVector μ v) ω)^2 -
        (W (oneVector μ) ω)^2) := by
  have he : finiteSecondIntegral μ P W hW (frequencyKernel μ v) =
      centeredSquare μ P W hW (cosineVector μ v) +
      centeredSquare μ P W hW (sineVector μ v) - centeredSquare μ P W hW (oneVector μ) := by
    rw [frequencyKernel, finiteSecondIntegral_apply]
    simp [frequencyCoefficients, finiteNoiseMap]
  rw [he]
  
  have hsub' :
      (fun ω : Ω =>
        (centeredSquare μ P W hW (cosineVector μ v) +
          centeredSquare μ P W hW (sineVector μ v) -
          centeredSquare μ P W hW (oneVector μ)) ω) =ᵐ[P]
        (fun ω : Ω =>
          (centeredSquare μ P W hW (cosineVector μ v) +
            centeredSquare μ P W hW (sineVector μ v)) ω -
            centeredSquare μ P W hW (oneVector μ) ω) :=
    Lp.coeFn_sub _ _
  have hadd' :
      (fun ω : Ω =>
        (centeredSquare μ P W hW (cosineVector μ v) +
          centeredSquare μ P W hW (sineVector μ v)) ω) =ᵐ[P]
        (fun ω : Ω =>
          centeredSquare μ P W hW (cosineVector μ v) ω +
            centeredSquare μ P W hW (sineVector μ v) ω) :=
    Lp.coeFn_add _ _
  filter_upwards [hsub', hadd',
    centeredSquare_coe μ P W hW (cosineVector μ v),
    centeredSquare_coe μ P W hW (sineVector μ v),
    centeredSquare_coe μ P W hW (oneVector μ)] with ω hsub hadd hc hs h1
  rw [hsub, hadd, hc, hs, h1]
  have h := frequency_energy μ v
  linarith

end Frequency

end D5.S3.Fourier.Asymptotics.SameNoiseSecondChaos
