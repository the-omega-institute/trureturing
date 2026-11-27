/- GID: D5/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/NullDiamondKernelHS
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Square-integrable kernels induce Hilbert–Schmidt operators on complex L². -/

import OmegaBuild.Commands
import D5.S3.Quantum.Analysis.NullConeGravity.QuarterPowerSqrtHilbertSchmidt
import D5.S3.Quantum.Analysis.TraceClass.HilbertSchmidt
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! The integral realization of square-integrable complex kernels and its sharp norm bounds. -/

noncomputable section

open Filter HilbertSchmidt MeasureTheory MeasureTheory.Measure
open D5.S3.Quantum.Analysis.NullConeGravity.QuarterPowerSqrtHilbertSchmidt
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace NullConeGravity

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

private theorem lp_norm_sq {f : X → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [ENNReal.toReal_ofReal (by positivity), show (2 : ℝ)⁻¹ = 1 / 2 by norm_num,
    ← Real.sqrt_eq_rpow, Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]

private theorem lp_norm_sq_integral (f : Lp ℂ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← lp_norm_sq μ (Lp.memLp f), Lp.toLp_coeFn]

private theorem kernel_sq_integrable {K : X × X → ℂ} (hK : MemLp K 2 (μ.prod μ)) :
    Integrable (fun p => ‖K p‖ ^ 2) (μ.prod μ) :=
  (memLp_two_iff_integrable_sq_norm hK.aestronglyMeasurable).1 hK

variable [SFinite μ]

private theorem kernel_section_memLp {K : X × X → ℂ} (hK : MemLp K 2 (μ.prod μ)) :
    ∀ᵐ x ∂μ, MemLp (fun y => K (x, y)) 2 μ := by
  filter_upwards [hK.aestronglyMeasurable.prodMk_left, (kernel_sq_integrable μ hK).prod_right_ae]
    with x hmeas hint
  exact (memLp_two_iff_integrable_sq_norm hmeas).2 hint

private theorem kernel_mass_integrable {K : X × X → ℂ} (hK : MemLp K 2 (μ.prod μ)) :
    Integrable (fun x => ∫ y, ‖K (x, y)‖ ^ 2 ∂μ) μ := by
  have hint := kernel_sq_integrable μ hK
  simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using
    ((integrable_prod_iff hint.aestronglyMeasurable).1 hint).2

private def kernelEval (K : X × X → ℂ) (f : Lp ℂ 2 μ) (x : X) : ℂ :=
  ∫ y, K (x, y) * f y ∂μ

omit [SFinite μ] in
private theorem section_inner {k : X → ℂ} (hk : MemLp k 2 μ) (f : Lp ℂ 2 μ) :
    ⟪hk.star.toLp (star k), f⟫_ℂ = ∫ y, k y * f y ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hk.star.coeFn_toLp] with y hy
  rw [RCLike.inner_apply', hy]
  simp

omit [SFinite μ] in
private theorem section_norm {k : X → ℂ} (hk : MemLp k 2 μ) :
    ‖hk.star.toLp (star k)‖ ^ 2 = ∫ y, ‖k y‖ ^ 2 ∂μ := by
  rw [lp_norm_sq]
  simp

private theorem kernelEval_sq_le {K : X × X → ℂ} (hK : MemLp K 2 (μ.prod μ)) (f : Lp ℂ 2 μ) :
    ∀ᵐ x ∂μ, ‖kernelEval μ K f x‖ ^ 2 ≤ (∫ y, ‖K (x, y)‖ ^ 2 ∂μ) * ‖f‖ ^ 2 := by
  filter_upwards [kernel_section_memLp μ hK] with x hx
  rw [kernelEval, ← section_inner μ hx f, ← section_norm μ hx, ← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 (norm_inner_le_norm _ _)

private theorem kernelEval_memLp {K : X × X → ℂ} (hK : MemLp K 2 (μ.prod μ)) (f : Lp ℂ 2 μ) :
    MemLp (kernelEval μ K f) 2 μ := by
  have hmeas : AEStronglyMeasurable (kernelEval μ K f) μ :=
    (hK.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f).comp_snd).integral_prod_right'
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  apply ((kernel_mass_integrable μ hK).mul_const (‖f‖ ^ 2)).mono'
    ((hmeas.norm).pow 2)
  filter_upwards [kernelEval_sq_le μ hK f] with x hx
  change ‖‖kernelEval μ K f x‖ ^ 2‖ ≤ _
  simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using hx

private def kernelLinear (K : X × X → ℂ) (hK : MemLp K 2 (μ.prod μ)) :
    Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := (kernelEval_memLp μ hK f).toLp (kernelEval μ K f)
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(kernelEval_memLp μ hK (f + g)).coeFn_toLp, Lp.coeFn_add
        ((kernelEval_memLp μ hK f).toLp (kernelEval μ K f))
        ((kernelEval_memLp μ hK g).toLp (kernelEval μ K g)),
      (kernelEval_memLp μ hK f).coeFn_toLp, (kernelEval_memLp μ hK g).coeFn_toLp,
      kernel_section_memLp μ hK] with x hsum houtput hf hg hx
    rw [hsum, houtput]
    change kernelEval μ K (f + g) x = _ + _
    rw [hf, hg]
    simp only [kernelEval, ← section_inner μ hx, inner_add_right]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(kernelEval_memLp μ hK (c • f)).coeFn_toLp, Lp.coeFn_smul c
        ((kernelEval_memLp μ hK f).toLp (kernelEval μ K f)),
      (kernelEval_memLp μ hK f).coeFn_toLp, kernel_section_memLp μ hK] with x hscaled houtput hf hx
    simp only [RingHom.id_apply]
    rw [hscaled, houtput]
    change kernelEval μ K (c • f) x = c • _
    rw [hf]
    simp only [kernelEval, ← section_inner μ hx, inner_smul_right, smul_eq_mul]

private theorem kernelLinear_bound (K : X × X → ℂ) (hK : MemLp K 2 (μ.prod μ)) (f : Lp ℂ 2 μ) :
    ‖kernelLinear μ K hK f‖ ≤ Real.sqrt (∫ p, ‖K p‖ ^ 2 ∂(μ.prod μ)) * ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
  rw [show ‖kernelLinear μ K hK f‖ ^ 2 = ∫ x, ‖kernelEval μ K f x‖ ^ 2 ∂μ from
    lp_norm_sq μ (kernelEval_memLp μ hK f), mul_pow, Real.sq_sqrt (integral_nonneg fun p => sq_nonneg _),
    integral_prod _ (kernel_sq_integrable μ hK), ← integral_mul_const]
  exact integral_mono_ae
    ((memLp_two_iff_integrable_sq_norm (kernelEval_memLp μ hK f).aestronglyMeasurable).1
      (kernelEval_memLp μ hK f))
    ((kernel_mass_integrable μ hK).mul_const _) (kernelEval_sq_le μ hK f)

/-- A square-integrable kernel acting on complex L² by integration in its second argument. -/
def integralKernelOp (K : X × X → ℂ) (hK : MemLp K 2 (μ.prod μ)) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (kernelLinear μ K hK).mkContinuous _ (kernelLinear_bound μ K hK)

/-- The operator realizes the section integrals almost everywhere. -/
theorem integralKernelOp_ae (K : X × X → ℂ) (hK : MemLp K 2 (μ.prod μ)) (f : Lp ℂ 2 μ) :
    (integralKernelOp μ K hK f : X → ℂ) =ᵐ[μ] fun x => ∫ y, K (x, y) * f y ∂μ :=
  (kernelEval_memLp μ hK f).coeFn_toLp

/-- The operator norm is bounded by the L² norm of the kernel. -/
theorem integralKernelOp_norm_le (K : X × X → ℂ) (hK : MemLp K 2 (μ.prod μ)) :
    ‖integralKernelOp μ K hK‖ ≤ Real.sqrt (∫ p, ‖K p‖ ^ 2 ∂(μ.prod μ)) :=
  (kernelLinear μ K hK).mkContinuous_norm_le (Real.sqrt_nonneg _) (kernelLinear_bound μ K hK)

private theorem kernel_basis_sum_le (K : X × X → ℂ) (hK : MemLp K 2 (μ.prod μ))
    {ι : Type*} (b : HilbertBasis ι ℂ (Lp ℂ 2 μ)) (s : Finset ι) :
    ∑ i ∈ s, ‖integralKernelOp μ K hK (b i)‖ ^ 2 ≤ ∫ p, ‖K p‖ ^ 2 ∂(μ.prod μ) := by
  classical
  let v : ι → Lp ℂ 2 μ := fun i => integralKernelOp μ K hK (b i)
  have hv (i : ι) : Integrable (fun x => ‖v i x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (v i))).1 (Lp.memLp (v i))
  calc
    _ = ∫ x, ∑ i ∈ s, ‖v i x‖ ^ 2 ∂μ := by
      rw [integral_finsetSum s (fun i _ => hv i)]
      exact Finset.sum_congr rfl fun i _ => lp_norm_sq_integral μ (v i)
    _ ≤ ∫ x, ∫ y, ‖K (x, y)‖ ^ 2 ∂μ ∂μ := by
      apply integral_mono_ae (integrable_finsetSum s (fun i _ => hv i)) (kernel_mass_integrable μ hK)
      have heq : ∀ᵐ x ∂μ, ∀ i ∈ s, v i x = kernelEval μ K (b i) x :=
        s.eventually_all.mpr fun i _ => integralKernelOp_ae μ K hK (b i)
      filter_upwards [heq, kernel_section_memLp μ hK] with x hx hsec
      change (∑ i ∈ s, ‖v i x‖ ^ 2) ≤ _
      let u := hsec.star.toLp (star (fun y => K (x, y)))
      calc
        _ = ∑ i ∈ s, ‖⟪b i, u⟫_ℂ‖ ^ 2 := Finset.sum_congr rfl fun i hi => by
          rw [hx i hi, kernelEval, ← section_inner μ hsec (b i), norm_inner_symm]
        _ ≤ ‖u‖ ^ 2 := b.orthonormal.sum_inner_products_le u
        _ = _ := section_norm μ hsec
    _ = _ := (integral_prod _ (kernel_sq_integrable μ hK)).symm

/-- The integrable kernel induces a Hilbert–Schmidt operator. -/
theorem integralKernelOp_hilbertSchmidt (K : X × X → ℂ) (hK : MemLp K 2 (μ.prod μ)) :
    IsHilbertSchmidt (integralKernelOp μ K hK) := by
  obtain ⟨w, b, _⟩ := exists_hilbertBasis ℂ (Lp ℂ 2 μ)
  exact ⟨w, b, summable_of_sum_le (fun _ => sq_nonneg _) (kernel_basis_sum_le μ K hK b)⟩

/-- The squared Hilbert–Schmidt norm is at most the squared L² norm of the kernel. -/
theorem integralKernelOp_hsSq_le (K : X × X → ℂ) (hK : MemLp K 2 (μ.prod μ)) :
    hsSq (integralKernelOp μ K hK) (integralKernelOp_hilbertSchmidt μ K hK) ≤
      ∫ p, ‖K p‖ ^ 2 ∂(μ.prod μ) := by
  unfold hsSq
  exact Real.tsum_le_of_sum_le (fun _ => sq_nonneg _)
    (kernel_basis_sum_le μ K hK (exists_hilbertBasis ℂ (Lp ℂ 2 μ)).choose_spec.choose)

private theorem memLp_conj_swap {K : X × X → ℂ} (hK : MemLp K 2 (μ.prod μ)) :
    MemLp (fun p : X × X => conj (K (p.2, p.1))) 2 (μ.prod μ) :=
  hK.star.comp_measurePreserving measurePreserving_swap

omit [SFinite μ] in
private theorem memLp_separated (f g : Lp ℂ 2 μ) :
    MemLp (fun p : X × X => conj (f p.1) * g p.2) 2 (μ.prod μ) := by
  have hf := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)
  have hg := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
  have hm : AEStronglyMeasurable (fun p : X × X => conj (f p.1) * g p.2) (μ.prod μ) :=
    (Lp.memLp f).star.aestronglyMeasurable.comp_fst.mul (Lp.aestronglyMeasurable g).comp_snd
  refine (memLp_two_iff_integrable_sq_norm hm).mpr ?_
  simpa only [norm_mul, Complex.norm_conj, mul_pow] using hf.mul_prod hg

/-- The (L^2) pairing with the integral operator is a product integral. -/
theorem integralKernelOp_inner (K : X × X → ℂ) (hK : MemLp K 2 (μ.prod μ))
    (f g : Lp ℂ 2 μ) :
    ⟪f, integralKernelOp μ K hK g⟫_ℂ = ∫ p, conj (f p.1) * K p * g p.2 ∂(μ.prod μ) := by
  have hp : Integrable (fun p : X × X => conj (f p.1) * K p * g p.2) (μ.prod μ) := by
    convert hK.integrable_mul (memLp_separated μ f g) using 1
    ext p
    simp only [Pi.mul_apply]
    ring
  rw [L2.inner_def, integral_prod _ hp]
  refine integral_congr_ae ?_
  filter_upwards [integralKernelOp_ae μ K hK g] with x hx
  rw [RCLike.inner_apply', hx, ← integral_const_mul]
  simp only [mul_assoc]

/-- Changing a kernel on a product-null set preserves its operator. -/
theorem integralKernelOp_congr_ae {K K' : X × X → ℂ}
    (hK : MemLp K 2 (μ.prod μ)) (hK' : MemLp K' 2 (μ.prod μ))
    (he : K =ᵐ[μ.prod μ] K') :
    integralKernelOp μ K hK = integralKernelOp μ K' hK' := by
  ext1 f
  apply Lp.ext
  filter_upwards [integralKernelOp_ae μ K hK f, integralKernelOp_ae μ K' hK' f,
    ae_ae_of_ae_prod he] with x hx hx' he'
  rw [hx, hx']
  apply integral_congr_ae
  filter_upwards [he'] with y hy
  rw [hy]

/-- Transposition and complex conjugation of the kernel give the Hilbert adjoint. -/
theorem integralKernelOp_adjoint (K : X × X → ℂ) (hK : MemLp K 2 (μ.prod μ)) :
    (integralKernelOp μ K hK).adjoint =
      integralKernelOp μ (fun p => conj (K (p.2, p.1))) (memLp_conj_swap μ hK) := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro f g
  calc
    _ = conj ⟪g, integralKernelOp μ _ (memLp_conj_swap μ hK) f⟫_ℂ := (inner_conj_symm _ _).symm
    _ = _ := by
      rw [integralKernelOp_inner μ,
        integralKernelOp_inner μ, ← integral_conj]
      trans ∫ p : X × X, conj (conj (g p.2) * conj (K p) * f p.1) ∂(μ.prod μ)
      · exact (integral_prod_swap
          (fun p : X × X => conj (conj (g p.1) * conj (K (p.2, p.1)) * f p.2))).symm
      · apply integral_congr_ae
        exact Eventually.of_forall fun p => by
          simp only [map_mul, starRingEnd_apply, star_star]
          ring

private def complexMul : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.lsmul ℂ ℂ

/-- Multiplication by an essentially bounded function on complex (L^2). -/
def mulOp (g : X → ℂ) (hg : MemLp g ∞ μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  complexMul.holderL μ ∞ 2 2 (hg.toLp g)

omit [SFinite μ] in
theorem mulOp_ae (g : X → ℂ) (hg : MemLp g ∞ μ) (f : Lp ℂ 2 μ) :
    (mulOp μ g hg f : X → ℂ) =ᵐ[μ] fun x => g x * f x := by
  have he := complexMul.coeFn_holder (r := 2) (hg.toLp g) f
  filter_upwards [he, hg.coeFn_toLp] with x hx hgx
  simpa only [mulOp, ContinuousLinearMap.holderL_apply_apply,
    complexMul, ContinuousLinearMap.lsmul_apply, smul_eq_mul, hgx] using hx

omit [SFinite μ] in
private theorem memLp_top_comp {g : X → ℂ} (hg : MemLp g ∞ μ) {v : X × X → X}
    (hv : QuasiMeasurePreserving v (μ.prod μ) μ) :
    MemLp (g ∘ v) ∞ (μ.prod μ) := by
  have htop : eLpNormEssSup g μ < ∞ := by
    simpa only [eLpNorm_exponent_top hg.aestronglyMeasurable] using hg.eLpNorm_lt_top
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp htop
  exact memLp_top_of_bound (hg.aestronglyMeasurable.comp_quasiMeasurePreserving hv) C
    (hv.ae (show ∀ᵐ x ∂μ, ‖g x‖ ≤ (C : ℝ) from hC))

omit [SFinite μ] in
private theorem memLp_weighted_kernel {K : X × X → ℂ} (hK : MemLp K 2 (μ.prod μ))
    {g h : X → ℂ} (hg : MemLp g ∞ μ) (hh : MemLp h ∞ μ) :
    MemLp (fun p : X × X => g p.1 * K p * h p.2) 2 (μ.prod μ) := by
  have hg' := memLp_top_comp μ hg (quasiMeasurePreserving_fst (ν := μ))
  have hh' := memLp_top_comp μ hh (quasiMeasurePreserving_snd (μ := μ))
  exact (hg'.mul hK : MemLp ((g ∘ Prod.fst) * K) 2 (μ.prod μ)).mul hh'

/-- Left and right multiplication weight the first and second variables of the kernel. -/
theorem integralKernelOp_mulOp_both (K : X × X → ℂ) (hK : MemLp K 2 (μ.prod μ))
    (g h : X → ℂ) (hg : MemLp g ∞ μ) (hh : MemLp h ∞ μ) :
    mulOp μ g hg ∘L integralKernelOp μ K hK ∘L mulOp μ h hh =
      integralKernelOp μ (fun p => g p.1 * K p * h p.2) (memLp_weighted_kernel μ hK hg hh) := by
  ext1 f
  apply Lp.ext
  filter_upwards [mulOp_ae μ g hg (integralKernelOp μ K hK (mulOp μ h hh f)),
    integralKernelOp_ae μ K hK (mulOp μ h hh f),
    integralKernelOp_ae μ _ (memLp_weighted_kernel μ hK hg hh) f] with x hx hk hw
  change mulOp μ g hg (integralKernelOp μ K hK (mulOp μ h hh f)) x = _
  rw [hx, hk, hw, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [mulOp_ae μ h hh f] with y hy
  rw [hy]
  ring

end NullConeGravity
