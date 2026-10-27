/- GID: D5/S3/Weil/ZetaGamma/FormCore/SourceGammaOffDiagonal
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:actual-reflected-resolvent-kernel)
   anchors: []
   utility: none
   digest: Actual L1 reflected Fourier cross and signed resolvent resonance kernels. -/

/- Actual L1 cross, exponential-absolute-value resolvent, self-convolution
double pole, and signed resonance kernel suppliers for the same actual Gamma
source. Standalone admission is not claimed for organizational helpers.
Only the original literal source Fourier owner is imported. The private
halfline and zeroExtension below use the same definition bodies as the
retained quarter source. The entire quarter graph background is not
an import prerequisite. The residual L1 family remains in its canonical
Archimedean owner and is not duplicated here. -/

import D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiLacunaryProfile
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal

open MeasureTheory Set Filter
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open scoped Topology ComplexConjugate FourierTransform Convolution

private abbrev halfline : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
private def zeroExtension (u : ℝ → ℂ) : ℝ → ℂ := (Ioi (0 : ℝ)).indicator u

open MeasureTheory Set Filter
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open scoped Topology ComplexConjugate FourierTransform

/-- The actual operator kernel: the normalization is 1/(2*pi), not the
unitary normalization of a single Fourier transform. -/
def actualL1MultiplierKernel (p : ℝ → ℂ) (z : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ ξ : ℝ, sourcePhase (-ξ) z * p ξ

private def crossIntegrand (p u : ℝ → ℂ) (ξ : ℝ) (z : ℝ × ℝ) : ℂ :=
  sourcePhase (-ξ) (z.1 + z.2) *
    (p ξ * ((starRingEnd ℂ) (u z.1) * u z.2))

private theorem unitary_zero_extension_integral (u : ℝ → ℂ) (ξ : ℝ) :
    unitarySourceFourier (zeroExtension u) ξ =
      (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)⁻¹) *
        ∫ s : ℝ, sourcePhase ξ s * u s ∂halfline := by
  rw [unitarySourceFourier_eq_integral]
  congr 1
  change (∫ s : ℝ, sourcePhase ξ s * (Ioi (0 : ℝ)).indicator u s) =
    ∫ s : ℝ in Ioi 0, sourcePhase ξ s * u s
  rw [← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  exact Eventually.of_forall fun s => by
    by_cases hs : s ∈ Ioi (0 : ℝ)
    · simp only [Set.indicator_of_mem hs]
    · simp only [Set.indicator_of_notMem hs, mul_zero]

private theorem sourcePhase_conj_add (ξ s t : ℝ) :
    (starRingEnd ℂ) (sourcePhase ξ s) * sourcePhase (-ξ) t =
      sourcePhase (-ξ) (s + t) := by
  unfold sourcePhase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal,
    Complex.ofReal_neg, Complex.ofReal_add]
  ring

private theorem unitary_factor_square :
    ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)⁻¹) ^ 2) =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) := by
  have hS : ((Real.sqrt (2 * Real.pi) : ℂ) ^ 2) = ((2 * Real.pi : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  rw [inv_pow, hS]

private theorem crossIntegrand_integrable
    {p u : ℝ → ℂ} (hp : Integrable p volume) (hu : Integrable u halfline) :
    Integrable (fun z : ℝ × (ℝ × ℝ) => crossIntegrand p u z.1 z.2)
      (volume.prod (halfline.prod halfline)) := by
  have hconj : Integrable (fun s : ℝ => (starRingEnd ℂ) (u s)) halfline := by
    simpa using (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hu
  have hpair : Integrable (fun z : ℝ × ℝ =>
      (starRingEnd ℂ) (u z.1) * u z.2) (halfline.prod halfline) :=
    hconj.mul_prod hu
  have hbase : Integrable (fun z : ℝ × (ℝ × ℝ) =>
      p z.1 * ((starRingEnd ℂ) (u z.2.1) * u z.2.2))
      (volume.prod (halfline.prod halfline)) := hp.mul_prod hpair
  have hphase : Continuous (fun z : ℝ × (ℝ × ℝ) =>
      sourcePhase (-z.1) (z.2.1 + z.2.2)) := by
    unfold sourcePhase
    fun_prop
  apply hbase.mono
    (hphase.aestronglyMeasurable.mul hbase.aestronglyMeasurable)
  exact Eventually.of_forall fun z => by
    simp only [Pi.mul_apply, crossIntegrand, norm_mul, sourcePhase_norm, one_mul, le_refl]

private theorem pointwise_cross_integral (p u : ℝ → ℂ) (ξ : ℝ) :
    p ξ * (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
        unitarySourceFourier (zeroExtension u) (-ξ) =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ∫ z : ℝ × ℝ, crossIntegrand p u ξ z ∂halfline.prod halfline := by
  let N : ℂ := (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)⁻¹)
  have hN : (starRingEnd ℂ) N = N := by simp [N]
  have hN2 : N ^ 2 = (((2 * Real.pi : ℝ) : ℂ)⁻¹) := unitary_factor_square
  calc
    _ = N ^ 2 * (p ξ *
        ((∫ s : ℝ, (starRingEnd ℂ) (sourcePhase ξ s * u s) ∂halfline) *
          (∫ t : ℝ, sourcePhase (-ξ) t * u t ∂halfline))) := by
      rw [unitary_zero_extension_integral, unitary_zero_extension_integral,
        map_mul, hN, ← integral_conj]
      ring
    _ = N ^ 2 * (p ξ *
        ∫ z : ℝ × ℝ,
          (starRingEnd ℂ) (sourcePhase ξ z.1 * u z.1) *
            (sourcePhase (-ξ) z.2 * u z.2) ∂halfline.prod halfline) := by
      rw [integral_prod_mul
        (fun s : ℝ => (starRingEnd ℂ) (sourcePhase ξ s * u s))
        (fun t : ℝ => sourcePhase (-ξ) t * u t)]
    _ = N ^ 2 * ∫ z : ℝ × ℝ,
        p ξ * ((starRingEnd ℂ) (sourcePhase ξ z.1 * u z.1) *
          (sourcePhase (-ξ) z.2 * u z.2)) ∂halfline.prod halfline := by
      rw [integral_const_mul]
    _ = N ^ 2 * ∫ z : ℝ × ℝ, crossIntegrand p u ξ z
        ∂halfline.prod halfline := by
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        simp only [crossIntegrand, map_mul]
        rw [← sourcePhase_conj_add]
        ring
    _ = _ := by rw [hN2]

private theorem inner_cross_integral (p u : ℝ → ℂ) (z : ℝ × ℝ) :
    (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        (∫ ξ : ℝ, crossIntegrand p u ξ z) =
      actualL1MultiplierKernel p (z.1 + z.2) *
        ((starRingEnd ℂ) (u z.1) * u z.2) := by
  calc
    _ = (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ((∫ ξ : ℝ, sourcePhase (-ξ) (z.1 + z.2) * p ξ) *
          ((starRingEnd ℂ) (u z.1) * u z.2)) := by
      congr 1
      rw [← integral_mul_const]
      apply integral_congr_ae
      exact Eventually.of_forall fun ξ => by
        unfold crossIntegrand
        ring
    _ = _ := by unfold actualL1MultiplierKernel; ring

/-- Actual spectral/physical reflected-cross identity for every literal
L1 multiplier and half-line L1 source. Absolute product integrability is
proved before Fubini; no desired energy or kernel identity is a premise.
The conclusion retains the literal negative-frequency Fourier value
of the same zero-extended source. -/
theorem actual_l1_reflected_unitary_cross_kernel
    {p u : ℝ → ℂ} (hp : Integrable p volume) (hu : Integrable u halfline) :
    Integrable (fun ξ : ℝ =>
      p ξ * (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
        unitarySourceFourier (zeroExtension u) (-ξ)) volume ∧
    Integrable (fun z : ℝ × ℝ =>
      actualL1MultiplierKernel p (z.1 + z.2) *
        ((starRingEnd ℂ) (u z.1) * u z.2)) (halfline.prod halfline) ∧
    (∫ ξ : ℝ,
      p ξ * (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
        unitarySourceFourier (zeroExtension u) (-ξ)) =
      ∫ z : ℝ × ℝ,
        actualL1MultiplierKernel p (z.1 + z.2) *
          ((starRingEnd ℂ) (u z.1) * u z.2) ∂halfline.prod halfline := by
  have hH := crossIntegrand_integrable hp hu
  have hSpec : Integrable (fun ξ : ℝ =>
      p ξ * (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
        unitarySourceFourier (zeroExtension u) (-ξ)) volume := by
    apply (hH.integral_prod_left.const_mul
      (((2 * Real.pi : ℝ) : ℂ)⁻¹)).congr
    exact Eventually.of_forall fun ξ => (pointwise_cross_integral p u ξ).symm
  have hPhys : Integrable (fun z : ℝ × ℝ =>
      actualL1MultiplierKernel p (z.1 + z.2) *
        ((starRingEnd ℂ) (u z.1) * u z.2)) (halfline.prod halfline) := by
    apply (hH.integral_prod_right.const_mul
      (((2 * Real.pi : ℝ) : ℂ)⁻¹)).congr
    exact Eventually.of_forall fun z => inner_cross_integral p u z
  refine ⟨hSpec, hPhys, ?_⟩
  calc
    _ = (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ∫ ξ : ℝ, ∫ z : ℝ × ℝ, crossIntegrand p u ξ z
          ∂halfline.prod halfline := by
      simp_rw [pointwise_cross_integral]
      rw [integral_const_mul]
    _ = (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ∫ z : ℝ × ℝ, (∫ ξ : ℝ, crossIntegrand p u ξ z)
          ∂halfline.prod halfline := by
      congr 1
      exact integral_integral_swap hH
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => inner_cross_integral p u z

open MeasureTheory Set Filter
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open scoped Topology ComplexConjugate FourierTransform Convolution

def actualResolventKernel (a z : ℝ) : ℂ :=
  (Real.exp (-a * |z|) : ℂ) / ((2 * a : ℝ) : ℂ)

def actualResolventSymbol (a ξ : ℝ) : ℂ :=
  (((ξ ^ 2 + a ^ 2)⁻¹ : ℝ) : ℂ)

private theorem actualResolventKernel_continuous (a : ℝ) :
    Continuous (actualResolventKernel a) := by
  unfold actualResolventKernel
  fun_prop

private theorem actualResolventKernel_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (actualResolventKernel a) volume := by
  have hn : IntegrableOn (actualResolventKernel a) (Iic (0 : ℝ)) := by
    have hi : Integrable (fun z : ℝ => (Real.exp (a * z) : ℂ))
        (volume.restrict (Iic (0 : ℝ))) := (integrableOn_exp_mul_Iic ha 0).ofReal
    apply (hi.div_const ((2 * a : ℝ) : ℂ)).congr
    filter_upwards [ae_restrict_mem measurableSet_Iic] with z hz
    change z ≤ 0 at hz
    simp only [actualResolventKernel, abs_of_nonpos hz, neg_mul_neg]
  have hp : IntegrableOn (actualResolventKernel a) (Ioi (0 : ℝ)) := by
    have hi : Integrable (fun z : ℝ => (Real.exp (-a * z) : ℂ))
        (volume.restrict (Ioi (0 : ℝ))) :=
      (integrableOn_exp_mul_Ioi (by linarith : -a < 0) 0).ofReal
    apply (hi.div_const ((2 * a : ℝ) : ℂ)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    change 0 < z at hz
    simp only [actualResolventKernel, abs_of_pos hz]
  simpa only [Iic_union_Ioi, integrableOn_univ] using hn.union hp

private theorem actualResolventSymbol_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (actualResolventSymbol a) volume := by
  have h := (integrable_inv_one_add_mul_sq (inv_ne_zero ha.ne')).const_mul
    ((a ^ 2)⁻¹)
  have hreal : Integrable (fun ξ : ℝ => (ξ ^ 2 + a ^ 2)⁻¹) volume := by
    apply h.congr
    exact Eventually.of_forall fun ξ => by
      have hd : 1 + (a⁻¹ * ξ) ^ 2 ≠ 0 := by positivity
      have hd2 : ξ ^ 2 + a ^ 2 ≠ 0 := by positivity
      field_simp [ha.ne', hd, hd2]
      <;> ring
  exact hreal.ofReal

private theorem resolvent_left_phase {a ξ t : ℝ} (ht : t ≤ 0) :
    Complex.exp (((-2 * Real.pi * t * ξ : ℝ) : ℂ) * Complex.I) *
        actualResolventKernel a t =
      Complex.exp (((a : ℂ) - Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ)) * t) /
        ((2 * a : ℝ) : ℂ) := by
  unfold actualResolventKernel
  rw [abs_of_nonpos ht, neg_mul_neg, Complex.ofReal_exp,
    ← mul_div_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

private theorem resolvent_right_phase {a ξ t : ℝ} (ht : 0 < t) :
    Complex.exp (((-2 * Real.pi * t * ξ : ℝ) : ℂ) * Complex.I) *
        actualResolventKernel a t =
      Complex.exp ((((-a : ℝ) : ℂ) -
        Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ)) * (t : ℂ)) /
        ((2 * a : ℝ) : ℂ) := by
  unfold actualResolventKernel
  rw [abs_of_pos ht, Complex.ofReal_exp, ← mul_div_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

/-- Computes the actual raw cycles-frequency transform from two absolutely
integrable half-line exponentials. No Fourier inversion is assumed. -/
private theorem actualResolventKernel_fourier {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    𝓕 (actualResolventKernel a) ξ =
      actualResolventSymbol a (2 * Real.pi * ξ) := by
  let m : ℂ := (a : ℂ) - Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ)
  let n : ℂ := ((-a : ℝ) : ℂ) - Complex.I * ((2 * Real.pi * ξ : ℝ) : ℂ)
  have hm : 0 < m.re := by simpa [m] using ha
  have hn : n.re < 0 := by simpa [n] using (neg_neg_of_pos ha)
  have hm0 : m ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp only [Complex.zero_re] at this
    linarith
  have hn0 : n ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp only [Complex.zero_re] at this
    linarith
  have hleft : IntegrableOn (fun t : ℝ =>
      Complex.exp (((-2 * Real.pi * t * ξ : ℝ) : ℂ) * Complex.I) *
        actualResolventKernel a t) (Iic 0) := by
    apply ((integrableOn_exp_mul_complex_Iic hm 0).div_const
      ((2 * a : ℝ) : ℂ)).congr
    filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    exact (resolvent_left_phase ht).symm
  have hright : IntegrableOn (fun t : ℝ =>
      Complex.exp (((-2 * Real.pi * t * ξ : ℝ) : ℂ) * Complex.I) *
        actualResolventKernel a t) (Ioi 0) := by
    apply ((integrableOn_exp_mul_complex_Ioi hn 0).div_const
      ((2 * a : ℝ) : ℂ)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (resolvent_right_phase ht).symm
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  calc
    _ = (∫ t : ℝ in Iic 0, Complex.exp (m * t) / ((2 * a : ℝ) : ℂ)) +
        (∫ t : ℝ in Ioi 0, Complex.exp (n * t) / ((2 * a : ℝ) : ℂ)) := by
      rw [← intervalIntegral.integral_Iic_add_Ioi hleft hright]
      congr 1
      · apply setIntegral_congr_fun measurableSet_Iic
        intro t ht
        exact resolvent_left_phase ht
      · apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact resolvent_right_phase ht
    _ = (1 / m - 1 / n) / ((2 * a : ℝ) : ℂ) := by
      simp_rw [div_eq_mul_inv, integral_mul_const]
      rw [integral_exp_mul_complex_Iic hm 0, integral_exp_mul_complex_Ioi hn 0]
      simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
      ring
    _ = actualResolventSymbol a (2 * Real.pi * ξ) := by
      let D : ℂ := (((2 * Real.pi * ξ) ^ 2 + a ^ 2 : ℝ) : ℂ)
      have hD : D ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
      have hC : ((2 * a : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (by positivity)
      have hmn : m * n = -D := by
        calc
          m * n = -(a : ℂ) ^ 2 +
              Complex.I ^ 2 * (((2 * Real.pi * ξ : ℝ) : ℂ) ^ 2) := by
            dsimp only [m, n]
            push_cast
            ring
          _ = -D := by
            rw [Complex.I_sq]
            dsimp only [D]
            push_cast
            ring
      have hsub : n - m = -((2 * a : ℝ) : ℂ) := by
        dsimp only [m, n]
        push_cast
        ring
      unfold actualResolventSymbol
      rw [Complex.ofReal_inv]
      change (1 / m - 1 / n) / ((2 * a : ℝ) : ℂ) = D⁻¹
      rw [div_sub_div 1 1 hm0 hn0, one_mul, mul_one, hmn, hsub]
      field_simp [hD, hC]
      <;> ring

/-- Exact inverse operator kernel with the normalization used by the
actual reflected-cross theorem. All integrability is paid first. -/
theorem actual_resolvent_inverse_kernel {a : ℝ} (ha : 0 < a) (z : ℝ) :
    Integrable (actualResolventSymbol a) volume ∧
    actualL1MultiplierKernel (actualResolventSymbol a) z =
      actualResolventKernel a z := by
  have hG := actualResolventKernel_integrable ha
  have hP := actualResolventSymbol_integrable ha
  have hFG : Integrable (𝓕 (actualResolventKernel a)) volume := by
    apply (hP.comp_mul_left' (by positivity : (2 * Real.pi : ℝ) ≠ 0)).congr
    exact Eventually.of_forall fun ξ => (actualResolventKernel_fourier ha ξ).symm
  have hInv : 𝓕⁻ (𝓕 (actualResolventKernel a)) (-z) =
      actualResolventKernel a (-z) :=
    hG.fourierInv_fourier_eq hFG (actualResolventKernel_continuous a).continuousAt
  have hScale := Measure.integral_comp_mul_left
    (fun ξ : ℝ => sourcePhase (-ξ) z * actualResolventSymbol a ξ) (2 * Real.pi)
  have hScale' :
      (∫ ξ : ℝ, sourcePhase (-(2 * Real.pi * ξ)) z *
        actualResolventSymbol a (2 * Real.pi * ξ)) =
      actualL1MultiplierKernel (actualResolventSymbol a) z := by
    simpa only [abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi)),
      Complex.real_smul, smul_eq_mul, Complex.ofReal_inv,
      actualL1MultiplierKernel] using hScale
  have hInv' :
      (∫ ξ : ℝ, sourcePhase (-(2 * Real.pi * ξ)) z *
        actualResolventSymbol a (2 * Real.pi * ξ)) =
      actualResolventKernel a (-z) := by
    rw [Real.fourierInv_eq'] at hInv
    simp only [smul_eq_mul, Real.inner_apply] at hInv
    convert hInv using 1
    apply integral_congr_ae
    exact Eventually.of_forall fun ξ => by
      dsimp only
      rw [actualResolventKernel_fourier ha]
      unfold sourcePhase
      congr 1
      push_cast
      ring
  refine ⟨hP, hScale'.symm.trans ?_⟩
  simpa only [actualResolventKernel, abs_neg] using hInv'

private theorem halfline_pair_positive :
    ∀ᵐ z : ℝ × ℝ ∂halfline.prod halfline, 0 < z.1 ∧ 0 < z.2 := by
  simpa only [halfline, Measure.prod_restrict, Set.mem_prod, Set.mem_Ioi] using
    (ae_restrict_mem (μ := volume.prod volume)
      (measurableSet_Ioi.prod measurableSet_Ioi))

private theorem literalLaplace_l1 {a : ℝ} (ha : 0 < a)
    {u : ℝ → ℂ} (hu : Integrable u halfline) :
    Integrable (fun t : ℝ => (Real.exp (-a * t) : ℂ) * u t) halfline := by
  have hm : Continuous (fun t : ℝ => (Real.exp (-a * t) : ℂ)) := by fun_prop
  apply hu.mono (hm.aestronglyMeasurable.mul hu.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  simp only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos (-a * t))]
  calc
    Real.exp (-a * t) * ‖u t‖ ≤ 1 * ‖u t‖ :=
      mul_le_mul_of_nonneg_right
        (Real.exp_le_one_iff.2 (by nlinarith : -a * t ≤ 0)) (norm_nonneg _)
    _ = ‖u t‖ := one_mul _

/-- The actual resolvent reflected cross is a literal Laplace norm-square.
All source/spectral integrals are established, with no L2 or graph premise. -/
theorem actual_resolvent_reflected_cross_laplace_square
    {a : ℝ} (ha : 0 < a) {u : ℝ → ℂ} (hu : Integrable u halfline) :
    Integrable (fun t : ℝ => (Real.exp (-a * t) : ℂ) * u t) halfline ∧
    Integrable (fun ξ : ℝ =>
      actualResolventSymbol a ξ *
        (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
          unitarySourceFourier (zeroExtension u) (-ξ)) volume ∧
    (∫ ξ : ℝ,
      actualResolventSymbol a ξ *
        (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
          unitarySourceFourier (zeroExtension u) (-ξ)) =
      (Complex.normSq (∫ t : ℝ, (Real.exp (-a * t) : ℂ) * u t ∂halfline) : ℂ) /
        ((2 * a : ℝ) : ℂ) := by
  have hp := actualResolventSymbol_integrable ha
  obtain ⟨hSpec, _, hCross⟩ := actual_l1_reflected_unitary_cross_kernel hp hu
  refine ⟨literalLaplace_l1 ha hu, hSpec, hCross.trans ?_⟩
  calc
    _ = ∫ z : ℝ × ℝ,
        (((starRingEnd ℂ) ((Real.exp (-a * z.1) : ℂ) * u z.1) *
          ((Real.exp (-a * z.2) : ℂ) * u z.2)) / ((2 * a : ℝ) : ℂ))
          ∂halfline.prod halfline := by
      apply integral_congr_ae
      filter_upwards [halfline_pair_positive] with z hz
      rw [(actual_resolvent_inverse_kernel ha (z.1 + z.2)).2]
      have he : Real.exp (-a * (z.1 + z.2)) =
          Real.exp (-a * z.1) * Real.exp (-a * z.2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      simp only [actualResolventKernel, abs_of_pos (add_pos hz.1 hz.2),
        he, Complex.ofReal_mul, map_mul, Complex.conj_ofReal]
      ring
    _ = (Complex.normSq (∫ t : ℝ, (Real.exp (-a * t) : ℂ) * u t ∂halfline) : ℂ) /
        ((2 * a : ℝ) : ℂ) := by
      simp_rw [div_eq_mul_inv]
      rw [integral_mul_const, integral_prod_mul
        (fun t : ℝ => (starRingEnd ℂ) ((Real.exp (-a * t) : ℂ) * u t))
        (fun t : ℝ => (Real.exp (-a * t) : ℂ) * u t),
        integral_conj, ← Complex.normSq_eq_conj_mul_self]

/- The actual self-convolution is computed on three absolutely integrable
regions. This supplies the resonant double pole without differentiation of
a parameter under an integral. -/

private theorem exp_abs_self_convolution_nonnegative
    {a z : ℝ} (ha : 0 < a) (hz : 0 ≤ z) :
    (∫ t : ℝ, Real.exp (-a * |t|) * Real.exp (-a * |z - t|)) =
      Real.exp (-a * z) * (z + a⁻¹) := by
  let l : ℝ → ℝ := (Iic (0 : ℝ)).indicator
    (fun t => Real.exp (-a * z) * Real.exp ((2 * a) * t))
  let m : ℝ → ℝ := (Ioc (0 : ℝ) z).indicator
    (fun _ => Real.exp (-a * z))
  let r : ℝ → ℝ := (Ioi z).indicator
    (fun t => Real.exp (a * z) * Real.exp ((-2 * a) * t))
  have hL : Integrable l volume :=
    (integrable_indicator_iff measurableSet_Iic).2
      ((integrableOn_exp_mul_Iic (by positivity : 0 < 2 * a) 0).const_mul _)
  have hM : Integrable m volume :=
    (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp))
  have hR : Integrable r volume :=
    (integrable_indicator_iff measurableSet_Ioi).2
      ((integrableOn_exp_mul_Ioi (by linarith : -2 * a < 0) z).const_mul _)
  have heq : (fun t : ℝ => Real.exp (-a * |t|) * Real.exp (-a * |z - t|)) =
      fun t => l t + m t + r t := by
    funext t
    by_cases ht0 : t ≤ 0
    · have hzt : 0 ≤ z - t := by linarith
      have htL : t ∈ Iic (0 : ℝ) := ht0
      have htM : t ∉ Ioc (0 : ℝ) z := by
        rintro ⟨ht, _⟩
        linarith
      have htR : t ∉ Ioi z := not_lt.mpr (le_trans ht0 hz)
      simp only [l, m, r, Set.indicator_of_mem htL, Set.indicator_of_notMem htM,
        Set.indicator_of_notMem htR, add_zero, abs_of_nonpos ht0, abs_of_nonneg hzt]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    · have ht : 0 < t := lt_of_not_ge ht0
      by_cases htz : t ≤ z
      · have hzt : 0 ≤ z - t := by linarith
        have htL : t ∉ Iic (0 : ℝ) := ht0
        have htM : t ∈ Ioc (0 : ℝ) z := ⟨ht, htz⟩
        have htR : t ∉ Ioi z := not_lt.mpr htz
        simp only [l, m, r, Set.indicator_of_notMem htL,
          Set.indicator_of_mem htM, Set.indicator_of_notMem htR, zero_add, add_zero,
          abs_of_pos ht, abs_of_nonneg hzt]
        rw [← Real.exp_add]
        congr 1
        ring
      · have htz' : z < t := lt_of_not_ge htz
        have hzt : z - t < 0 := by linarith
        have htL : t ∉ Iic (0 : ℝ) := ht0
        have htM : t ∉ Ioc (0 : ℝ) z := by
          rintro ⟨_, htz⟩
          linarith
        have htR : t ∈ Ioi z := htz'
        simp only [l, m, r, Set.indicator_of_notMem htL,
          Set.indicator_of_notMem htM, Set.indicator_of_mem htR, zero_add,
          abs_of_pos ht, abs_of_neg hzt]
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
  have hLi : (∫ t : ℝ, l t) = Real.exp (-a * z) / (2 * a) := by
    dsimp [l]
    rw [integral_indicator measurableSet_Iic, integral_const_mul,
      integral_exp_mul_Iic (by positivity : 0 < 2 * a) 0]
    simp only [mul_zero, Real.exp_zero]
    field_simp [ha.ne']
    <;> ring
  have hMi : (∫ t : ℝ, m t) = z * Real.exp (-a * z) := by
    dsimp [m]
    rw [integral_indicator measurableSet_Ioc, setIntegral_const,
      Real.volume_real_Ioc_of_le hz, sub_zero, smul_eq_mul]
  have hRi : (∫ t : ℝ, r t) = Real.exp (-a * z) / (2 * a) := by
    dsimp [r]
    rw [integral_indicator measurableSet_Ioi, integral_const_mul,
      integral_exp_mul_Ioi (by linarith : -2 * a < 0) z]
    have he : Real.exp (a * z) * Real.exp ((-2 * a) * z) =
        Real.exp (-a * z) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = (Real.exp (a * z) * Real.exp ((-2 * a) * z)) / (2 * a) := by
        field_simp [ha.ne']
        <;> ring
      _ = Real.exp (-a * z) / (2 * a) := by rw [he]
  rw [heq, integral_add (f := fun t : ℝ => l t + m t) (g := r)
    (hL.add hM) hR, integral_add hL hM, hLi, hMi, hRi]
  field_simp [ha.ne']
  <;> ring

private theorem actualResolventKernel_self_convolution_nonnegative
    {a z : ℝ} (ha : 0 < a) (hz : 0 ≤ z) :
    (actualResolventKernel a ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        actualResolventKernel a) z =
      ((Real.exp (-a * z) * (1 + a * z) / (4 * a ^ 3) : ℝ) : ℂ) := by
  rw [convolution_mul]
  calc
    _ = ∫ t : ℝ,
        ((Real.exp (-a * |t|) * Real.exp (-a * |z - t|) /
          (4 * a ^ 2) : ℝ) : ℂ) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        unfold actualResolventKernel
        push_cast
        field_simp [Complex.ofReal_ne_zero.mpr ha.ne']
        <;> ring
    _ = (((∫ t : ℝ, Real.exp (-a * |t|) * Real.exp (-a * |z - t|)) /
          (4 * a ^ 2) : ℝ) : ℂ) := by
      rw [integral_complex_ofReal, integral_div]
    _ = _ := by
      rw [exp_abs_self_convolution_nonnegative ha hz]
      congr 1
      field_simp [ha.ne']
      <;> ring

private theorem actualResolventKernel_self_convolution_even (a z : ℝ) :
    (actualResolventKernel a ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        actualResolventKernel a) (-z) =
      (actualResolventKernel a ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
        actualResolventKernel a) z := by
  rw [convolution_mul, convolution_mul]
  calc
    _ = ∫ t : ℝ, actualResolventKernel a (-t) *
        actualResolventKernel a (-z - (-t)) :=
      (integral_neg_eq_self (fun t : ℝ => actualResolventKernel a t *
        actualResolventKernel a (-z - t)) volume).symm
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        have hzt : -z - (-t) = -(z - t) := by ring
        simp only [actualResolventKernel, hzt, abs_neg]

def actualDoubleResolventKernel (a z : ℝ) : ℂ :=
  ((Real.exp (-a * |z|) * (1 + a * |z|) / (4 * a ^ 3) : ℝ) : ℂ)

/-- The resonant double-pole kernel is the actual self-convolution, on
both signs of the real line, not a fitted pointwise surrogate. -/
private theorem actualResolventKernel_self_convolution {a : ℝ} (ha : 0 < a) :
    (actualResolventKernel a ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
      actualResolventKernel a) = actualDoubleResolventKernel a := by
  funext z
  rcases le_or_gt 0 z with hz | hz
  · simpa only [actualDoubleResolventKernel, abs_of_nonneg hz] using
      actualResolventKernel_self_convolution_nonnegative ha hz
  · have he := actualResolventKernel_self_convolution_nonnegative ha (le_of_lt (neg_pos.mpr hz))
    rw [actualResolventKernel_self_convolution_even a z] at he
    simpa only [actualDoubleResolventKernel, abs_of_neg hz] using he

private theorem actualResolventSymbol_sq_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun ξ : ℝ => actualResolventSymbol a ξ ^ 2) volume := by
  have hP := actualResolventSymbol_integrable ha
  have hm : Continuous (fun ξ : ℝ => actualResolventSymbol a ξ ^ 2) := by
    have hden : Continuous (fun ξ : ℝ => ξ ^ 2 + a ^ 2) := by fun_prop
    have hreal : Continuous (fun ξ : ℝ => (ξ ^ 2 + a ^ 2)⁻¹) :=
      hden.inv₀ (fun ξ => ne_of_gt
        (add_pos_of_nonneg_of_pos (sq_nonneg ξ) (sq_pos_of_pos ha)))
    exact (Complex.continuous_ofReal.comp hreal).pow 2
  apply (hP.norm.const_mul ((a ^ 2)⁻¹)).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun ξ => by
    have hr0 : 0 ≤ (ξ ^ 2 + a ^ 2)⁻¹ := by positivity
    have hr : (ξ ^ 2 + a ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le (sq_pos_of_pos ha)
          (by nlinarith : a ^ 2 ≤ ξ ^ 2 + a ^ 2))
    change ‖(((ξ ^ 2 + a ^ 2)⁻¹ : ℝ) : ℂ) ^ 2‖ ≤
      (a ^ 2)⁻¹ * ‖(((ξ ^ 2 + a ^ 2)⁻¹ : ℝ) : ℂ)‖
    rw [norm_pow, Complex.norm_of_nonneg hr0]
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hr hr0

private theorem actualResolventKernel_norm_le {a : ℝ} (ha : 0 < a) (z : ℝ) :
    ‖actualResolventKernel a z‖ ≤ (2 * a)⁻¹ := by
  have hd : 0 < 2 * a := by positivity
  have he : Real.exp (-a * |z|) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [abs_nonneg z])
  simp only [actualResolventKernel, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_of_pos hd]
  simpa only [one_div] using div_le_div_of_nonneg_right he hd.le

/-- Consumed Fourier-inversion helper. The actual transform equality is
a paid argument from the concrete resolvent/convolution calculation;
the eventual Gamma theorem does not assume its desired kernel identity. -/
private theorem actual_inverse_kernel_of_raw_transform
    {f p : ℝ → ℂ} (hf : Integrable f volume) (hfc : Continuous f)
    (hp : Integrable p volume)
    (hFT : ∀ ξ : ℝ, 𝓕 f ξ = p (2 * Real.pi * ξ)) (z : ℝ) :
    actualL1MultiplierKernel p z = f (-z) := by
  have hFp : Integrable (𝓕 f) volume := by
    apply (hp.comp_mul_left' (by positivity : (2 * Real.pi : ℝ) ≠ 0)).congr
    exact Eventually.of_forall fun ξ => (hFT ξ).symm
  have hInv : 𝓕⁻ (𝓕 f) (-z) = f (-z) :=
    hf.fourierInv_fourier_eq hFp hfc.continuousAt
  have hScale := Measure.integral_comp_mul_left
    (fun ξ : ℝ => sourcePhase (-ξ) z * p ξ) (2 * Real.pi)
  have hScale' :
      (∫ ξ : ℝ, sourcePhase (-(2 * Real.pi * ξ)) z * p (2 * Real.pi * ξ)) =
      actualL1MultiplierKernel p z := by
    simpa only [abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < 2 * Real.pi)),
      Complex.real_smul, smul_eq_mul, Complex.ofReal_inv,
      actualL1MultiplierKernel] using hScale
  rw [← hScale']
  rw [Real.fourierInv_eq'] at hInv
  simp only [smul_eq_mul, Real.inner_apply] at hInv
  convert hInv using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun ξ => by
    dsimp only
    rw [hFT ξ]
    unfold sourcePhase
    congr 1
    push_cast
    ring

/-- Exact actual double-pole inverse kernel, obtained by an actual L1
self-convolution and Fourier inversion. No parameter differentiation. -/
private theorem actual_double_resolvent_inverse_kernel
    {a : ℝ} (ha : 0 < a) (z : ℝ) :
    Integrable (fun ξ : ℝ => actualResolventSymbol a ξ ^ 2) volume ∧
    actualL1MultiplierKernel (fun ξ : ℝ => actualResolventSymbol a ξ ^ 2) z =
      actualDoubleResolventKernel a z := by
  let f : ℝ → ℂ := actualResolventKernel a ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
    actualResolventKernel a
  have hG := actualResolventKernel_integrable ha
  have hf : Integrable f volume := hG.integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ) hG
  have hGb : BddAbove (Set.range (fun z : ℝ => ‖actualResolventKernel a z‖)) := by
    refine ⟨(2 * a)⁻¹, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact actualResolventKernel_norm_le ha z
  have hfc : Continuous f := BddAbove.continuous_convolution_right_of_integrable
    (ContinuousLinearMap.mul ℂ ℂ) hGb hG (actualResolventKernel_continuous a)
  have hP := actualResolventSymbol_sq_integrable ha
  have hFT (ξ : ℝ) : 𝓕 f ξ = actualResolventSymbol a (2 * Real.pi * ξ) ^ 2 := by
    dsimp [f]
    rw [Real.fourier_mul_convolution_eq hG hG, actualResolventKernel_fourier ha]
    ring
  refine ⟨hP, ?_⟩
  rw [actual_inverse_kernel_of_raw_transform hf hfc hP hFT z]
  dsimp [f]
  rw [actualResolventKernel_self_convolution ha]
  simp only [actualDoubleResolventKernel, abs_neg]

private theorem phase_mul_l1 {p : ℝ → ℂ} (hp : Integrable p volume) (z : ℝ) :
    Integrable (fun ξ : ℝ => sourcePhase (-ξ) z * p ξ) volume := by
  have hm : Continuous (fun ξ : ℝ => sourcePhase (-ξ) z) := by
    unfold sourcePhase
    fun_prop
  apply hp.mono (hm.aestronglyMeasurable.mul hp.aestronglyMeasurable)
  exact Eventually.of_forall fun ξ => by
    simp only [Pi.mul_apply, norm_mul, sourcePhase_norm, one_mul, le_refl]

private theorem actual_kernel_sub_const_mul
    {p q : ℝ → ℂ} (hp : Integrable p volume) (hq : Integrable q volume)
    (c d : ℂ) (z : ℝ) :
    actualL1MultiplierKernel (fun ξ => c * p ξ - d * q ξ) z =
      c * actualL1MultiplierKernel p z - d * actualL1MultiplierKernel q z := by
  unfold actualL1MultiplierKernel
  have he : (fun ξ : ℝ => sourcePhase (-ξ) z * (c * p ξ - d * q ξ)) =
      fun ξ => c * (sourcePhase (-ξ) z * p ξ) -
        d * (sourcePhase (-ξ) z * q ξ) := by
    funext ξ
    ring
  rw [he, integral_sub ((phase_mul_l1 hp z).const_mul c)
    ((phase_mul_l1 hq z).const_mul d), integral_const_mul, integral_const_mul]
  ring

def actualResonantSymbol (a ξ : ℝ) : ℂ :=
  ((ξ ^ 2 / (a * (ξ ^ 2 + a ^ 2) ^ 2) : ℝ) : ℂ)

/-- The actual resonance retains its signed linear kernel. This is the
n=1 summand at a=5/4 in the original quarter residual. -/
theorem actual_resonant_inverse_kernel {a : ℝ} (ha : 0 < a) (z : ℝ) :
    Integrable (actualResonantSymbol a) volume ∧
    actualL1MultiplierKernel (actualResonantSymbol a) z =
      ((Real.exp (-a * |z|) * (1 - a * |z|) / (4 * a ^ 2) : ℝ) : ℂ) := by
  have hp := actualResolventSymbol_integrable ha
  have hq := actualResolventSymbol_sq_integrable ha
  have heq : actualResonantSymbol a =
      fun ξ : ℝ => ((a : ℂ)⁻¹) * actualResolventSymbol a ξ -
        (a : ℂ) * actualResolventSymbol a ξ ^ 2 := by
    funext ξ
    have hd : (ξ ^ 2 + a ^ 2 : ℝ) ≠ 0 := by positivity
    unfold actualResonantSymbol actualResolventSymbol
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr ha.ne',
      Complex.ofReal_ne_zero.mpr hd]
    <;> ring
  have hi : Integrable (actualResonantSymbol a) volume := by
    rw [heq]
    exact (hp.const_mul _).sub (hq.const_mul _)
  refine ⟨hi, ?_⟩
  rw [heq, actual_kernel_sub_const_mul hp hq,
    (actual_resolvent_inverse_kernel ha z).2,
    (actual_double_resolvent_inverse_kernel ha z).2]
  unfold actualResolventKernel actualDoubleResolventKernel
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr ha.ne']
  <;> ring

/-- Actual resonance cross, before moment compression. It is a genuine
L1/Fubini identity on the original literal source, not a sign premise. -/
theorem actual_resonant_reflected_cross_kernel
    {a : ℝ} (ha : 0 < a) {u : ℝ → ℂ} (hu : Integrable u halfline) :
    Integrable (fun ξ : ℝ =>
      actualResonantSymbol a ξ *
        (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
          unitarySourceFourier (zeroExtension u) (-ξ)) volume ∧
    (∫ ξ : ℝ,
      actualResonantSymbol a ξ *
        (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
          unitarySourceFourier (zeroExtension u) (-ξ)) =
      ∫ z : ℝ × ℝ,
        ((Real.exp (-a * (z.1 + z.2)) * (1 - a * (z.1 + z.2)) /
            (4 * a ^ 2) : ℝ) : ℂ) *
          ((starRingEnd ℂ) (u z.1) * u z.2) ∂halfline.prod halfline := by
  obtain ⟨hSpec, _, hCross⟩ := actual_l1_reflected_unitary_cross_kernel
    (actual_resonant_inverse_kernel ha 0).1 hu
  refine ⟨hSpec, hCross.trans ?_⟩
  apply integral_congr_ae
  filter_upwards [halfline_pair_positive] with z hz
  rw [(actual_resonant_inverse_kernel ha (z.1 + z.2)).2,
    abs_of_pos (add_pos hz.1 hz.2)]

private theorem firstMoment_weight_bound {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    t * Real.exp (-a * t) ≤ a⁻¹ := by
  have hx : a * t ≤ Real.exp (a * t) := by
    linarith [Real.add_one_le_exp (a * t)]
  have hPay := mul_le_mul_of_nonneg_right hx (le_of_lt (Real.exp_pos (-a * t)))
  have hExp : Real.exp (a * t) * Real.exp (-a * t) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hExp] at hPay
  rw [← one_div]
  apply (le_div_iff₀ ha).2
  nlinarith [hPay]

private theorem literalFirstLaplaceMoment_l1 {a : ℝ} (ha : 0 < a)
    {u : ℝ → ℂ} (hu : Integrable u halfline) :
    Integrable (fun t : ℝ => (t : ℂ) * (Real.exp (-a * t) : ℂ) * u t)
      halfline := by
  have hm : Continuous (fun t : ℝ => (t : ℂ) * (Real.exp (-a * t) : ℂ)) := by
    fun_prop
  apply (hu.norm.const_mul a⁻¹).mono'
    (hm.aestronglyMeasurable.mul hu.aestronglyMeasurable)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  simp only [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ht, abs_of_pos (Real.exp_pos _)]
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right (firstMoment_weight_bound ha ht) (norm_nonneg (u t))

/-- Moment compression of the actual resonant cross. The first moment's
actual L1 domain is supplied inside this theorem, rather than assumed.
The coefficient -1/(2a) retains the resonant mixed term. -/
theorem actual_resonant_reflected_cross_laplace_moment
    {a : ℝ} (ha : 0 < a) {u : ℝ → ℂ} (hu : Integrable u halfline) :
    Integrable (fun t : ℝ => (t : ℂ) * (Real.exp (-a * t) : ℂ) * u t) halfline ∧
    (∫ ξ : ℝ,
      actualResonantSymbol a ξ *
        (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
          unitarySourceFourier (zeroExtension u) (-ξ)).re =
      Complex.normSq (∫ t : ℝ, (Real.exp (-a * t) : ℂ) * u t ∂halfline) /
          (4 * a ^ 2) -
        (((starRingEnd ℂ) (∫ t : ℝ, (Real.exp (-a * t) : ℂ) * u t ∂halfline)) *
          (∫ t : ℝ, (t : ℂ) * (Real.exp (-a * t) : ℂ) * u t ∂halfline)).re /
            (2 * a) := by
  let L : ℝ → ℂ := fun t => (Real.exp (-a * t) : ℂ) * u t
  let T : ℝ → ℂ := fun t => (t : ℂ) * (Real.exp (-a * t) : ℂ) * u t
  have hL : Integrable L halfline := literalLaplace_l1 ha hu
  have hT : Integrable T halfline := literalFirstLaplaceMoment_l1 ha hu
  have hLc : Integrable (fun t => (starRingEnd ℂ) (L t)) halfline := by
    simpa using (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hL
  have hTc : Integrable (fun t => (starRingEnd ℂ) (T t)) halfline := by
    simpa using (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hT
  have hLL := (hLc.mul_prod hL).div_const ((4 * a ^ 2 : ℝ) : ℂ)
  have hMix : Integrable (fun z : ℝ × ℝ =>
      ((starRingEnd ℂ) (T z.1) * L z.2 +
        (starRingEnd ℂ) (L z.1) * T z.2) / ((4 * a : ℝ) : ℂ))
      (halfline.prod halfline) :=
    ((hTc.mul_prod hL).add (hLc.mul_prod hT)).div_const ((4 * a : ℝ) : ℂ)
  have hCross := (actual_resonant_reflected_cross_kernel ha hu).2
  have hComplex :
      (∫ ξ : ℝ,
        actualResonantSymbol a ξ *
          (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
            unitarySourceFourier (zeroExtension u) (-ξ)) =
        (Complex.normSq (∫ t : ℝ, L t ∂halfline) : ℂ) / ((4 * a ^ 2 : ℝ) : ℂ) -
          (((starRingEnd ℂ) (∫ t : ℝ, T t ∂halfline)) *
              (∫ t : ℝ, L t ∂halfline) +
            ((starRingEnd ℂ) (∫ t : ℝ, L t ∂halfline)) *
              (∫ t : ℝ, T t ∂halfline)) / ((4 * a : ℝ) : ℂ) := by
    rw [hCross]
    calc
      _ = ∫ z : ℝ × ℝ,
          ((starRingEnd ℂ) (L z.1) * L z.2) / ((4 * a ^ 2 : ℝ) : ℂ) -
            (((starRingEnd ℂ) (T z.1) * L z.2 +
              (starRingEnd ℂ) (L z.1) * T z.2) / ((4 * a : ℝ) : ℂ))
                ∂halfline.prod halfline := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          have he : Real.exp (-a * (z.1 + z.2)) =
              Real.exp (-a * z.1) * Real.exp (-a * z.2) := by
            rw [← Real.exp_add]
            congr 1
            ring
          simp only [L, T, he, Complex.ofReal_mul, map_mul, Complex.conj_ofReal]
          push_cast
          field_simp [Complex.ofReal_ne_zero.mpr ha.ne']
          <;> ring
      _ = _ := by
        rw [integral_sub hLL hMix]
        simp_rw [integral_div]
        rw [integral_add (hTc.mul_prod hL) (hLc.mul_prod hT)]
        rw [integral_prod_mul (fun t : ℝ => (starRingEnd ℂ) (L t)) L,
          integral_prod_mul (fun t : ℝ => (starRingEnd ℂ) (T t)) L,
          integral_prod_mul (fun t : ℝ => (starRingEnd ℂ) (L t)) T]
        simp_rw [integral_conj]
        rw [← Complex.normSq_eq_conj_mul_self]
  refine ⟨hT, ?_⟩
  rw [hComplex]
  simp only [Complex.sub_re, Complex.div_ofReal_re, Complex.ofReal_re, Complex.add_re,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  dsimp [L, T]
  ring

end D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal
