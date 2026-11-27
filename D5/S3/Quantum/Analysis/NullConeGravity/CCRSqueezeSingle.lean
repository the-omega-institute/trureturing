/- GID: D5/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/CCRSqueezeSingle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A normalized one-mode squeezed vacuum and its Weyl characteristic function. -/

import D5.S3.Quantum.Analysis.NullConeGravity.CCRFockOccupation
import D5.S3.Quantum.Analysis.NullConeGravity.CCRFockWeyl
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
The coherent isometry identifies the occupation model of one mode with
complex square-integrable functions on the real line. A dilation of the
vacuum Gaussian gives the squeezed vector.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex MeasureTheory
open scoped ComplexConjugate FourierTransform InnerProductSpace

namespace D5.S3.Quantum.Analysis.NullConeGravity.CCRSqueezeSingle

open CCRFockOccupation CCRFockWeyl

/-- The one-particle basis consisting of the complex number one. -/
def singleModeBasis : HilbertBasis Unit ℂ ℂ :=
  HilbertBasis.mk (orthonormal_subsingleton_iff.mpr (fun _ => norm_one (α := ℂ)))
    (v := fun _ => (1 : ℂ)) (by
      have h : (1 : ℂ) ∈ Submodule.span ℂ (Set.range (fun _ : Unit => (1 : ℂ))) :=
        Submodule.subset_span ⟨(), rfl⟩
      intro z _
      exact Submodule.le_topologicalClosure _
        (by simpa only [smul_eq_mul, mul_one] using (Submodule.span ℂ _).smul_mem z h))

@[simp] theorem singleModeBasis_apply (i : Unit) : singleModeBasis i = 1 := by
  unfold singleModeBasis
  rw [HilbertBasis.coe_mk]

@[simp] theorem singleModeBasis_repr (z : ℂ) (i : Unit) : singleModeBasis.repr z i = z := by
  rw [HilbertBasis.repr_apply_apply, singleModeBasis_apply]
  simp [RCLike.inner_apply]

private abbrev Line := Lp ℂ 2 (volume : Measure ℝ)

private def packetFn (a : ℝ) (b d : ℂ) (q : ℝ) : ℂ :=
  exp (-(a : ℂ) / 2 * (q : ℂ) ^ 2 + b * q + d)

private theorem packet_mem (a : ℝ) (ha : 0 < a) (b d : ℂ) :
    MemLp (packetFn a b d) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (by unfold packetFn; fun_prop)).mpr
  refine (integrable_cexp_quadratic' (b := -(a : ℂ)) (by simpa) (2 * b.re)
    (2 * d.re)).norm.congr ?_
  filter_upwards with q
  simp only [packetFn, norm_exp, ← Real.exp_nat_mul]
  congr 1
  simp [mul_re, pow_two]
  ring

private def packet (a : ℝ) (ha : 0 < a) (b d : ℂ) : Line :=
  (packet_mem a ha b d).toLp _

private theorem packet_inner (a A : ℝ) (ha : 0 < a) (hA : 0 < A) (b d B D : ℂ) :
    ⟪packet a ha b d, packet A hA B D⟫_ℂ =
      (Real.sqrt (Real.pi / ((a + A) / 2)) : ℂ) *
        exp (conj d + D + (conj b + B) ^ 2 / (2 * ((a : ℂ) + A))) := by
  rw [L2.inner_def]
  calc
    _ = ∫ q : ℝ, exp (-(((a + A) / 2 : ℝ) : ℂ) * (q : ℂ) ^ 2 +
        (conj b + B) * q + (conj d + D)) := by
      apply integral_congr_ae
      filter_upwards [(packet_mem a ha b d).coeFn_toLp, (packet_mem A hA B D).coeFn_toLp]
        with q hq hQ
      change ⟪((packet_mem a ha b d).toLp _) q, ((packet_mem A hA B D).toLp _) q⟫_ℂ = _
      rw [hq, hQ]
      simp only [RCLike.inner_apply, packetFn, ← exp_conj, ← exp_add,
        map_add, map_mul, map_div₀, map_neg, map_pow, map_ofNat, conj_ofReal, ofReal_add,
        ofReal_div, ofReal_ofNat]
      congr 1
      ring
    _ = _ := by
      rw [integral_cexp_quadratic (by simp; positivity), neg_neg, ← ofReal_div,
        Real.sqrt_eq_rpow, ofReal_cpow (by positivity)]
      push_cast
      congr 2
      rw [show (4 : ℂ) * -((↑a + ↑A) / 2) = -(2 * (↑a + ↑A)) by ring, div_neg]
      ring

private def gaussianScale : ℝ := (Real.sqrt (Real.sqrt Real.pi))⁻¹

private theorem gaussianScale_sq : gaussianScale ^ 2 * Real.sqrt Real.pi = 1 := by
  rw [gaussianScale, inv_pow, Real.sq_sqrt (by positivity), inv_mul_cancel₀ (by positivity)]

private theorem scaled_sqrt (k : ℝ) :
    gaussianScale ^ 2 * Real.sqrt (Real.pi / k) = (Real.sqrt k)⁻¹ := by
  rw [Real.sqrt_div Real.pi_pos.le, div_eq_mul_inv, ← mul_assoc, gaussianScale_sq, one_mul]

private def coherent (w : ℂ) : Line :=
  (gaussianScale : ℂ) • packet 1 one_pos ((Real.sqrt 2 : ℂ) * w) (-w ^ 2 / 2)

private theorem coherent_inner (z w : ℂ) :
    ⟪coherent z, coherent w⟫_ℂ = exp ⟪z, w⟫_ℂ := by
  rw [coherent, coherent, inner_smul_left, inner_smul_right]
  change (conj (gaussianScale : ℂ)) * ((gaussianScale : ℂ) * _) = _
  rw [conj_ofReal, packet_inner]
  norm_num only [show (1 + 1) / 2 = (1 : ℝ) by norm_num, div_one, ofReal_one]
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hc : (gaussianScale : ℂ) * (gaussianScale : ℂ) * (Real.sqrt Real.pi : ℂ) = 1 := by
    rw [← sq]
    exact_mod_cast gaussianScale_sq
  rw [← mul_assoc, ← mul_assoc, hc, one_mul]
  congr 1
  simp only [map_div₀, map_neg, map_pow, map_mul, map_ofNat, conj_ofReal, RCLike.inner_apply]
  rw [← mul_add, mul_pow, hs]
  ring

private theorem coherent_total (g : Line) (h : ∀ w, ⟪coherent w, g⟫_ℂ = 0) : g = 0 := by
  let f : ℝ → ℂ := fun q => packetFn 1 0 0 q * g q
  have hf : Integrable f := (packet_mem 1 one_pos 0 0).integrable_mul (Lp.memLp g)
  have hfourier (t : ℝ) : 𝓕 f t = 0 := by
    let w : ℂ := (2 * Real.pi * t / Real.sqrt 2 : ℝ) * I
    have hq (q : ℝ) : conj (packetFn 1 ((Real.sqrt 2 : ℂ) * w) (-w ^ 2 / 2) q) =
        exp (conj (-w ^ 2 / 2)) *
          (exp ((-2 * Real.pi * q * t : ℝ) * I) * packetFn 1 0 0 q) := by
      have hs : (Real.sqrt 2 : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by positivity)
      simp only [w, packetFn, ← exp_conj, ← exp_add, map_add, map_mul, map_div₀, map_neg,
        map_pow, map_ofNat, conj_ofReal, conj_I, ofReal_one, map_one]
      push_cast
      congr 1
      field_simp [hs]
      ring
    have hv := h w
    rw [coherent, inner_smul_left] at hv
    change conj (gaussianScale : ℂ) * _ = 0 at hv
    rw [conj_ofReal, L2.inner_def] at hv
    have he : (∫ q : ℝ, ⟪packet 1 one_pos ((Real.sqrt 2 : ℂ) * w) (-w ^ 2 / 2) q, g q⟫_ℂ) =
        exp (conj (-w ^ 2 / 2)) * 𝓕 f t := by
      rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [(packet_mem 1 one_pos ((Real.sqrt 2 : ℂ) * w) (-w ^ 2 / 2)).coeFn_toLp]
        with q hq'
      change ⟪((packet_mem 1 one_pos _ _).toLp _) q, g q⟫_ℂ = _
      rw [hq', RCLike.inner_apply, hq]
      simp [f, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    rw [he, ← mul_assoc, mul_eq_zero] at hv
    exact hv.resolve_left (mul_ne_zero (ofReal_ne_zero.mpr (by unfold gaussianScale; positivity)) (exp_ne_zero _))
  have hz : f =ᵐ[volume] 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable
    intro u hu huc
    let ψ : SchwartzMap ℝ ℂ :=
      (huc.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hu)
    let φ : SchwartzMap ℝ ℂ := 𝓕⁻ ψ
    have hφ : 𝓕 φ = ψ := FourierTransform.fourier_fourierInv_eq ψ
    have hswap :
        (∫ t : ℝ, φ t • 𝓕 f t) = ∫ q : ℝ, 𝓕 φ q • f q := by
      simpa [SchwartzMap.fourier_coe, Real.fourier_eq, VectorFourier.fourierIntegral,
        Real.inner_apply, smul_eq_mul, mul_comm] using!
        VectorFourier.integral_bilin_fourierIntegral_eq_flip
          (f := f) (g := (φ : ℝ → ℂ)) (.mul ℂ ℂ) (L := innerₗ ℝ)
          (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
          Real.continuous_fourierChar continuous_inner hf (φ.integrable (μ := volume))
    simpa [hfourier, hφ, ψ, Function.comp_apply, Complex.real_smul] using hswap.symm
  apply Lp.ext
  filter_upwards [hz, Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with q hq hq'
  exact (mul_eq_zero.mp hq).resolve_left (exp_ne_zero _) |>.trans hq'.symm

private theorem coherent_dense : Dense (Submodule.span ℂ (Set.range coherent) : Set Line) := by
  let K := Submodule.span ℂ (Set.range coherent)
  change Dense (K : Set Line)
  rw [dense_iff_closure_eq, ← K.topologicalClosure_coe,
    ← Submodule.top_coe (R := ℂ), SetLike.coe_set_eq, K.topologicalClosure_eq_top_iff]
  refine le_antisymm (fun g hg => ?_) bot_le
  rw [Submodule.mem_bot]
  apply coherent_total g
  intro w
  have hw : coherent w ∈ K := Submodule.subset_span ⟨w, rfl⟩
  exact Submodule.inner_right_of_mem_orthogonal hw hg

private theorem coherent_linear_norm (c : ℂ →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ coherent c‖ =
      ‖Finsupp.linearCombination ℂ (fockExponential singleModeBasis) c‖ := by
  have h : ⟪Finsupp.linearCombination ℂ coherent c, Finsupp.linearCombination ℂ coherent c⟫_ℂ =
      ⟪Finsupp.linearCombination ℂ (fockExponential singleModeBasis) c,
        Finsupp.linearCombination ℂ (fockExponential singleModeBasis) c⟫_ℂ := by
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, coherent_inner, fockExponential_inner]
  simp only [inner_self_eq_norm_sq_to_K] at h
  have hn : ‖Finsupp.linearCombination ℂ coherent c‖ ^ 2 =
      ‖Finsupp.linearCombination ℂ (fockExponential singleModeBasis) c‖ ^ 2 := by exact_mod_cast h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hn

private def gaussianModel : BosonFock Unit ≃ₗᵢ[ℂ] Line :=
  (LinearEquiv.refl ℂ (ℂ →₀ ℂ)).extendOfIsometry
    (Finsupp.linearCombination ℂ (fockExponential singleModeBasis))
    (Finsupp.linearCombination ℂ coherent)
    (by simpa only [DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination]
      using fockExponential_dense_span singleModeBasis)
    (by simpa only [DenseRange, ← LinearMap.coe_range, Finsupp.range_linearCombination]
      using coherent_dense)
    coherent_linear_norm

private theorem gaussianModel_exponential (w : ℂ) :
    gaussianModel (fockExponential singleModeBasis w) = coherent w := by
  unfold gaussianModel
  simpa only [LinearEquiv.refl_apply, Finsupp.linearCombination_single, one_smul] using
    LinearEquiv.extendOfIsometry_eq (LinearEquiv.refl ℂ (ℂ →₀ ℂ))
      (Finsupp.linearCombination ℂ (fockExponential singleModeBasis))
      (Finsupp.linearCombination ℂ coherent) _ _ coherent_linear_norm (Finsupp.single w 1)

private def width (r : ℝ) : ℝ := Real.exp (2 * r)
private theorem width_pos (r : ℝ) : 0 < width r := Real.exp_pos _
private def amplitude (r : ℝ) : ℝ := gaussianScale * Real.sqrt (Real.exp r)

private def gaussian (r : ℝ) : Line :=
  (amplitude r : ℂ) • packet (width r) (width_pos r) 0 0

private theorem sqrt_width (r : ℝ) : Real.sqrt (width r) = Real.exp r := by
  rw [width, show 2 * r = r + r by ring, Real.exp_add, ← sq,
    Real.sqrt_sq (Real.exp_pos r).le]

private theorem gaussian_prefactor (r : ℝ) :
    amplitude r ^ 2 * Real.sqrt (Real.pi / width r) = 1 := by
  rw [amplitude, mul_pow, Real.sq_sqrt (Real.exp_pos r).le, mul_right_comm, scaled_sqrt,
    sqrt_width, inv_mul_cancel₀ (Real.exp_ne_zero r)]

private theorem gaussian_zero : gaussian 0 = coherent 0 := by
  simp [gaussian, coherent, width, amplitude]

/-- Pullback of the normalized Gaussian of width `exp (2 * r)` under the coherent isometry. -/
def squeezeVacuum (r : ℝ) : BosonFock Unit := gaussianModel.symm (gaussian r)

theorem squeezeVacuum_zero : squeezeVacuum 0 = fockVacuum Unit := by
  apply gaussianModel.injective
  rw [squeezeVacuum, LinearIsometryEquiv.apply_symm_apply, gaussian_zero,
    ← fockExponential_zero singleModeBasis, gaussianModel_exponential]

theorem squeezeVacuum_norm (r : ℝ) : ‖squeezeVacuum r‖ = 1 := by
  have h : ⟪gaussian r, gaussian r⟫_ℂ = 1 := by
    rw [gaussian, inner_smul_left, inner_smul_right]
    change conj (amplitude r : ℂ) * ((amplitude r : ℂ) * _) = _
    rw [conj_ofReal, packet_inner]
    simp only [map_zero, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero,
      exp_zero, mul_one]
    rw [show (width r + width r) / 2 = width r by ring, ← mul_assoc, ← sq]
    exact_mod_cast gaussian_prefactor r
  rw [squeezeVacuum, LinearIsometryEquiv.norm_map]
  have hn : ‖gaussian r‖ ^ 2 = 1 := by
    rw [@norm_sq_eq_re_inner ℂ, h]
    rfl
  exact (sq_eq_one_iff.mp hn).resolve_right (by linarith [norm_nonneg (gaussian r)])

theorem squeezeVacuum_vacuum_inner (r : ℝ) :
    ⟪fockVacuum Unit, squeezeVacuum r⟫_ℂ = ((1 / Real.sqrt (Real.cosh r) : ℝ) : ℂ) := by
  rw [← gaussianModel.inner_map_map, squeezeVacuum, LinearIsometryEquiv.apply_symm_apply,
    ← fockExponential_zero singleModeBasis, gaussianModel_exponential]
  rw [← gaussian_zero, gaussian, gaussian, inner_smul_left, inner_smul_right]
  change conj (amplitude 0 : ℂ) * ((amplitude r : ℂ) * _) = _
  rw [conj_ofReal, packet_inner]
  simp only [map_zero, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero,
    exp_zero, mul_one]
  have hw : (1 + width r) / 2 = Real.exp r * Real.cosh r := by
    rw [width, Real.cosh_eq, Real.exp_neg, show 2 * r = r + r by ring, Real.exp_add]
    field_simp [Real.exp_ne_zero]
    ring
  simp only [← ofReal_mul]
  apply congrArg ofReal
  rw [show width 0 = 1 by simp [width], hw, amplitude, amplitude,
    Real.exp_zero, Real.sqrt_one, mul_one]
  rw [show gaussianScale * (gaussianScale * Real.sqrt (Real.exp r) *
      Real.sqrt (Real.pi / (Real.exp r * Real.cosh r))) =
    Real.sqrt (Real.exp r) * (gaussianScale ^ 2 *
      Real.sqrt (Real.pi / (Real.exp r * Real.cosh r))) by ring,
    scaled_sqrt, Real.sqrt_mul (Real.exp_pos r).le]
  field_simp [show Real.sqrt (Real.exp r) ≠ 0 by positivity,
    show Real.sqrt (Real.cosh r) ≠ 0 by positivity]

private def shiftedSlope (a : ℝ) (z : ℂ) : ℂ :=
  (Real.sqrt 2 : ℂ) * ((a : ℂ) * z.re + I * z.im)

private def shiftedOffset (a : ℝ) (z : ℂ) : ℂ :=
  -(a : ℂ) * (z.re : ℂ) ^ 2 - I * z.re * z.im

private def shiftedGaussian (r : ℝ) (z : ℂ) : Line :=
  (amplitude r : ℂ) • packet (width r) (width_pos r)
    (shiftedSlope (width r) z) (shiftedOffset (width r) z)

private theorem sqrt_two_sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)

private theorem norm_sq_complex (z : ℂ) : (‖z‖ : ℂ) ^ 2 =
    (z.re : ℂ) ^ 2 + (z.im : ℂ) ^ 2 := by
  exact_mod_cast (Complex.sq_norm z).trans (by rw [Complex.normSq_apply]; ring)

private theorem coherent_shift (r : ℝ) (z w : ℂ) :
    ⟪coherent w, shiftedGaussian r z⟫_ℂ =
      ⟪exp (-(‖-z‖ : ℂ) ^ 2 / 2 - ⟪-z, w⟫_ℂ) • coherent (-z + w), gaussian r⟫_ℂ := by
  rw [inner_smul_left, coherent, coherent, shiftedGaussian, gaussian]
  simp only [inner_smul_left, inner_smul_right, packet_inner]
  change (amplitude r : ℂ) * (conj (gaussianScale : ℂ) * (_ * exp _)) =
    conj (exp _) * ((amplitude r : ℂ) * (conj (gaussianScale : ℂ) * (_ * exp _)))
  rw [← exp_conj]
  simp only [conj_ofReal, add_zero, ofReal_one]
  rw [mul_left_comm (exp _), mul_left_comm (exp _), mul_left_comm (exp _), ← exp_add]
  congr 4
  let a : ℝ := width r
  change conj (-w ^ 2 / 2) + shiftedOffset a z +
      (conj ((Real.sqrt 2 : ℂ) * w) + shiftedSlope a z) ^ 2 / (2 * ((1 : ℂ) + a)) =
    conj (-(‖-z‖ : ℂ) ^ 2 / 2 - ⟪-z, w⟫_ℂ) + (conj (-(-z + w) ^ 2 / 2) +
      conj ((Real.sqrt 2 : ℂ) * (-z + w)) ^ 2 / (2 * ((1 : ℂ) + a)))
  have hden : (1 : ℂ) + (a : ℂ) ≠ 0 := by
    rw [← ofReal_one, ← ofReal_add]
    exact ofReal_ne_zero.mpr (by dsimp [a]; positivity [width_pos r])
  simp only [shiftedSlope, shiftedOffset, norm_neg, norm_sq_complex, RCLike.inner_apply,
    map_sub, map_div₀, map_neg, map_add, map_mul, map_pow, map_ofNat, conj_ofReal,
    Complex.conj_conj]
  have hc : conj z = z.re - (z.im : ℂ) * I := by
    apply Complex.ext <;> simp [mul_re, mul_im]
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
  generalize z.re = x at hc hz ⊢
  generalize z.im = y at hc hz ⊢
  rw [hc, hz]
  field_simp [hden]
  ring_nf
  simp only [sqrt_two_sq, I_sq]
  ring

private theorem gaussianModel_weyl (r : ℝ) (z : ℂ) :
    gaussianModel (fockWeyl singleModeBasis z (squeezeVacuum r)) = shiftedGaussian r z := by
  rw [← sub_eq_zero]
  apply coherent_total
  intro w
  rw [inner_sub_right, sub_eq_zero]
  conv_lhs => rw [← gaussianModel_exponential w, gaussianModel.inner_map_map]
  let W := fockWeyl singleModeBasis z
  have h := W.symm.inner_map_eq_flip (fockExponential singleModeBasis w) (squeezeVacuum r)
  rw [LinearIsometryEquiv.symm_symm] at h
  change ⟪fockExponential singleModeBasis w, W (squeezeVacuum r)⟫_ℂ = _
  rw [← h, show W.symm = fockWeyl singleModeBasis (-z) from fockWeyl_symm _ _,
    fockWeyl_exponential, ← gaussianModel.inner_map_map, map_smul, gaussianModel_exponential,
    squeezeVacuum, LinearIsometryEquiv.apply_symm_apply]
  exact (coherent_shift r z w).symm

theorem squeezeVacuum_weyl_inner (r : ℝ) (z : ℂ) :
    ⟪squeezeVacuum r, fockWeyl singleModeBasis z (squeezeVacuum r)⟫_ℂ =
      exp (-((Real.exp (2 * r) * z.re ^ 2 + Real.exp (-2 * r) * z.im ^ 2 : ℝ) : ℂ) / 2) := by
  rw [← gaussianModel.inner_map_map, gaussianModel_weyl, squeezeVacuum,
    LinearIsometryEquiv.apply_symm_apply, gaussian, shiftedGaussian, inner_smul_left, inner_smul_right]
  change conj (amplitude r : ℂ) * ((amplitude r : ℂ) * _) = _
  rw [conj_ofReal, packet_inner]
  simp only [map_zero, zero_add]
  rw [show (width r + width r) / 2 = width r by ring, ← mul_assoc, ← mul_assoc, ← sq]
  rw [show (amplitude r : ℂ) ^ 2 * (Real.sqrt (Real.pi / width r) : ℂ) = 1 by
    exact_mod_cast gaussian_prefactor r, one_mul]
  congr 1
  have h : (width r : ℂ) ≠ 0 := ofReal_ne_zero.mpr (width_pos r).ne'
  rw [show -2 * r = -(2 * r) by ring, Real.exp_neg]
  change shiftedOffset (width r) z +
    shiftedSlope (width r) z ^ 2 / (2 * ((width r : ℂ) + width r)) =
      -((width r * z.re ^ 2 + (width r)⁻¹ * z.im ^ 2 : ℝ) : ℂ) / 2
  push_cast
  rw [shiftedSlope, mul_pow, sqrt_two_sq, shiftedOffset]
  field_simp [h]
  ring_nf
  rw [I_sq]
  ring

end D5.S3.Quantum.Analysis.NullConeGravity.CCRSqueezeSingle
