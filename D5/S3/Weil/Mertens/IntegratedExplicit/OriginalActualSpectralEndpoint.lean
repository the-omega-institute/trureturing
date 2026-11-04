/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/OriginalActualSpectralEndpoint
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Absolute Fourier Fubini and the actual endpoint close the original signed J identity. -/

/-
Copyright (c) 2026. Released under Apache 2.0.

Mathlib suppliers are imported under Apache 2.0, retaining upstream notices:
Integral/Prod (Floris van Doorn, copyright 2020),
Bochner/ContinuousLinearMap and Function/LocallyIntegrable. No upstream proof
body is copied. The angular inverse integral is consumed exclusively from
OriginalAngularResolvent.angular_resolvent, with its exact factor 1/(2*pi).

The only restrictions on atoms below are a finite type, nodes in [0,D],
and zero total mass. There is no positivity, distinctness, nonemptiness,
positive-energy, parity, Fourier-integrability or endpoint hypothesis.
-/
import D5.S3.Weil.Mertens.IntegratedExplicit.OriginalActualFourier
import D5.S3.Weil.Mertens.IntegratedExplicit.OriginalAngularResolvent
import D5.S3.Weil.Mertens.IntegratedExplicit.OriginalTestRegularity
import D5.S3.Weil.Mertens.IntegratedExplicit.OriginalSignedJ
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

/-! Absolute Fourier Fubini, the actual spectral endpoint, and the original J identity. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators Topology ComplexConjugate

namespace OriginalActualSpectralEndpoint

open D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open OriginalActualFourier

abbrev pairMeasure : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume

def weight (w : ℝ) : ℝ := (1 + 4 * w ^ 2)⁻¹
def resolvent (s w : ℝ) : ℂ := phase w s / ((1 + 4 * w ^ 2 : ℝ) : ℂ)
def coefficient (A : ℝ → ℂ) (p : ℝ × ℝ) : ℂ := A p.1 * conj (A p.2)
def decay (s : ℝ) : ℝ := Real.exp (-|s| / 2)
def triple (A : ℝ → ℂ) (t w : ℝ) (p : ℝ × ℝ) : ℂ :=
  coefficient A p * resolvent (t - p.1 + p.2) w
def frequencyIntegrand (A : ℝ → ℂ) (t w : ℝ) : ℂ :=
  resolvent t w * ((‖Ahat A w‖ ^ 2 : ℝ) : ℂ)
def fourierPair (A : ℝ → ℂ) (w : ℝ) (p : ℝ × ℝ) : ℂ :=
  coefficient A p * phase (-w) (p.1 - p.2)

lemma denominator_pos (w : ℝ) : 0 < 1 + 4 * w ^ 2 := by positivity

lemma weight_integrable : Integrable weight := by
  have he : weight = fun w : ℝ => (1 + (2 * w) ^ 2)⁻¹ := by
    funext w
    unfold weight
    congr 1
    ring
  rw [he]
  exact integrable_inv_one_add_mul_sq (by norm_num : (2 : ℝ) ≠ 0)

lemma resolvent_norm (s w : ℝ) : ‖resolvent s w‖ = weight w := by
  simp only [resolvent, norm_div, phase_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (denominator_pos w), one_div, weight]

lemma resolvent_integrable (s : ℝ) : Integrable (resolvent s) := by
  change Integrable (fun w : ℝ =>
    Complex.exp (Complex.I * (w : ℂ) * (s : ℂ)) / ((1 + 4 * w ^ 2 : ℝ) : ℂ))
  exact (OriginalAngularResolvent.angular_resolvent s).1

lemma normalized_resolvent (s : ℝ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ)) * (∫ w : ℝ, resolvent s w) =
      (decay s : ℂ) / 4 := by
  simpa only [resolvent, phase, decay] using (OriginalAngularResolvent.angular_resolvent s).2

lemma conjugate_integrable {μ : Measure ℝ} {A : ℝ → ℂ}
    (hAm : Measurable A) (hA : Integrable A μ) : Integrable (fun u => conj (A u)) μ := by
  apply hA.norm.mono' (Complex.continuous_conj.measurable.comp hAm).aestronglyMeasurable
  exact ae_of_all _ fun u => (Complex.norm_conj (A u)).le

lemma coefficient_integrable {A : ℝ → ℂ} (hAm : Measurable A) (hA : Integrable A) :
    Integrable (coefficient A) pairMeasure :=
  hA.mul_prod (conjugate_integrable hAm hA)

lemma coefficient_norm (A : ℝ → ℂ) (p : ℝ × ℝ) :
    ‖coefficient A p‖ = ‖A p.1‖ * ‖A p.2‖ := by
  simp only [coefficient, norm_mul, Complex.norm_conj]

lemma coefficient_re_swap (A : ℝ → ℂ) (p : ℝ × ℝ) :
    (coefficient A p.swap).re = (coefficient A p).re := by
  simp only [coefficient, Prod.fst_swap, Prod.snd_swap, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  ring

lemma fourierPair_eq_product (A : ℝ → ℂ) (w : ℝ) (p : ℝ × ℝ) :
    fourierPair A w p =
      (A p.1 * phase (-w) p.1) * conj (A p.2 * phase (-w) p.2) := by
  have hp : phase (-w) (p.1 - p.2) = phase (-w) p.1 * phase w p.2 := by
    rw [sub_eq_add_neg, phase_add, ← phase_neg_left]
    simp only [neg_neg]
  unfold fourierPair coefficient
  rw [hp, map_mul, phase_conj]
  simp only [neg_neg]
  ring

lemma fourierPair_integrable {A : ℝ → ℂ} (hAm : Measurable A) (hA : Integrable A) (w : ℝ) :
    Integrable (fourierPair A w) pairMeasure := by
  have hm : Measurable (fun u : ℝ => A u * phase (-w) u) := by
    unfold phase
    fun_prop
  have hi := (transform_integrable hA w).mul_prod
    (conjugate_integrable hm (transform_integrable hA w))
  exact hi.congr (ae_of_all _ fun p => (fourierPair_eq_product A w p).symm)

lemma Ahat_normSq_eq_pair {A : ℝ → ℂ} (hAm : Measurable A)
    (hA : Integrable A) (w : ℝ) :
    ((‖Ahat A w‖ ^ 2 : ℝ) : ℂ) =
      ∫ p : ℝ × ℝ, fourierPair A w p ∂pairMeasure := by
  rw [integral_prod (fourierPair A w) (fourierPair_integrable hAm hA w)]
  simp_rw [fourierPair_eq_product, integral_const_mul, integral_mul_const, integral_conj]
  change ((‖Ahat A w‖ ^ 2 : ℝ) : ℂ) = Ahat A w * conj (Ahat A w)
  simpa only [Complex.ofReal_pow] using (Complex.mul_conj' (Ahat A w)).symm

lemma triple_norm (A : ℝ → ℂ) (t w : ℝ) (p : ℝ × ℝ) :
    ‖triple A t w p‖ = weight w * (‖A p.1‖ * ‖A p.2‖) := by
  rw [triple, norm_mul, coefficient_norm, resolvent_norm]
  ring

/-- Absolute integrability on frequency times the whole spatial square.
The dominating function is exactly weight(w)*|A(u)|*|A(v)|. -/
theorem triple_integrable {A : ℝ → ℂ} (hAm : Measurable A) (hA : Integrable A) (t : ℝ) :
    Integrable (fun z : ℝ × (ℝ × ℝ) => triple A t z.1 z.2)
      ((volume : Measure ℝ).prod pairMeasure) := by
  have hb := weight_integrable.mul_prod (hA.norm.mul_prod hA.norm)
  apply hb.mono' ?_ (ae_of_all _ fun z => (triple_norm A t z.1 z.2).le)
  have hm : Measurable (fun z : ℝ × (ℝ × ℝ) => triple A t z.1 z.2) := by
    unfold triple coefficient resolvent phase
    fun_prop
  exact hm.aestronglyMeasurable

/-- Expansion of the literal modulus square of the literal L1 transform.
Only products of two independent L1 functions are integrated here. -/
lemma pair_expansion {A : ℝ → ℂ} (hAm : Measurable A)
    (hA : Integrable A) (t w : ℝ) :
    (∫ p : ℝ × ℝ, triple A t w p ∂pairMeasure) = frequencyIntegrand A t w := by
  have he (p : ℝ × ℝ) : triple A t w p =
      resolvent t w *
        ((A p.1 * phase (-w) p.1) * conj (A p.2 * phase (-w) p.2)) := by
    have hp : phase w (t - p.1 + p.2) =
        phase w t * phase (-w) p.1 * phase w p.2 := by
      rw [sub_eq_add_neg, phase_add, phase_add, ← phase_neg_left]
    unfold triple coefficient resolvent
    rw [hp, map_mul, phase_conj]
    simp only [neg_neg]
    ring
  simp_rw [he, ← fourierPair_eq_product]
  rw [integral_const_mul, ← Ahat_normSq_eq_pair hAm hA w]
  rfl

lemma frequencyIntegrand_integrable {A : ℝ → ℂ} (hA : Integrable A) (t : ℝ) :
    Integrable (frequencyIntegrand A t) := by
  have hm : AEStronglyMeasurable
      (fun w => ((‖Ahat A w‖ ^ 2 : ℝ) : ℂ)) volume := by
    have hc : Continuous (fun w => ((‖Ahat A w‖ ^ 2 : ℝ) : ℂ)) := by
      have := Ahat_continuous hA
      fun_prop
    exact hc.aestronglyMeasurable
  apply (resolvent_integrable t).mul_bdd hm
  exact ae_of_all _ fun w => by
    change ‖((‖Ahat A w‖ ^ 2 : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖Ahat A w‖)]
    have hb := Ahat_bound hA w
    simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) hb

lemma decay_nonneg (s : ℝ) : 0 ≤ decay s := (Real.exp_pos _).le
lemma decay_le_one (s : ℝ) : decay s ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  linarith [abs_nonneg s]

lemma spatial_integrable {A : ℝ → ℂ} (hAm : Measurable A) (hA : Integrable A)
    (t : ℝ) : Integrable
      (fun p : ℝ × ℝ => coefficient A p * (decay (t - p.1 + p.2) : ℂ)) pairMeasure := by
  apply (coefficient_integrable hAm hA).mul_bdd
  · have hc : Continuous (fun p : ℝ × ℝ => (decay (t - p.1 + p.2) : ℂ)) := by
      unfold decay
      fun_prop
    exact hc.aestronglyMeasurable
  · exact ae_of_all _ fun p => by
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (decay_nonneg _)] using decay_le_one (t - p.1 + p.2)

/-- The legitimate frequency/space interchange, followed by the existing
angular supplier. No parity of rho is involved. -/
theorem complex_resolvent_identity {A : ℝ → ℂ} (hAm : Measurable A)
    (hA : Integrable A) (t : ℝ) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ)) * (∫ w : ℝ, frequencyIntegrand A t w) =
      (∫ p : ℝ × ℝ, coefficient A p * (decay (t - p.1 + p.2) : ℂ)
        ∂pairMeasure) / 4 := by
  calc
    _ = (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        (∫ w : ℝ, ∫ p : ℝ × ℝ, triple A t w p ∂pairMeasure) := by
      simp only [pair_expansion hAm hA]
    _ = (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        (∫ p : ℝ × ℝ, (∫ w : ℝ, triple A t w p) ∂pairMeasure) := by
      rw [integral_integral_swap (triple_integrable hAm hA t)]
    _ = ∫ p : ℝ × ℝ, (((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        (∫ w : ℝ, triple A t w p) ∂pairMeasure := by rw [integral_const_mul]
    _ = ∫ p : ℝ × ℝ, coefficient A p *
        (decay (t - p.1 + p.2) : ℂ) / 4 ∂pairMeasure := by
      apply integral_congr_ae
      exact ae_of_all _ fun p => by
        dsimp only
        unfold triple
        rw [integral_const_mul]
        calc
          _ = coefficient A p *
              ((((1 / (2 * Real.pi) : ℝ) : ℂ)) *
                (∫ w : ℝ, resolvent (t - p.1 + p.2) w)) := by ring
          _ = _ := by rw [normalized_resolvent]; ring
    _ = _ := integral_div _ _

/-- Change of measure is for actual ENNReal.ofReal density, not an abstract L2 measure. -/
lemma spectralS_density {A : ℝ → ℂ} (hA : Integrable A) (t : ℝ) :
    OriginalTestRegularity.spectralS (rho A) t =
      ∫ w : ℝ, density A w * OriginalTestRegularity.spectralKernel t w := by
  unfold OriginalTestRegularity.spectralS rho
  rw [integral_withDensity_eq_integral_toReal_smul
    (density_continuous hA).measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (density_nonneg _ _), smul_eq_mul]

lemma spectralS_eq_complex_real {A : ℝ → ℂ} (hA : Integrable A) (t : ℝ) :
    OriginalTestRegularity.spectralS (rho A) t =
      ((((1 / (2 * Real.pi) : ℝ) : ℂ)) *
        (∫ w : ℝ, frequencyIntegrand A t w)).re := by
  have hre := Complex.reCLM.integral_comp_comm
    ((frequencyIntegrand_integrable hA t).const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ)))
  simp only [Complex.reCLM_apply] at hre
  rw [spectralS_density hA t, ← integral_const_mul, ← hre]
  apply integral_congr_ae
  exact ae_of_all _ fun w => by
    change density A w * OriginalTestRegularity.spectralKernel t w =
      ((((1 / (2 * Real.pi) : ℝ) : ℂ)) * frequencyIntegrand A t w).re
    have he : (((1 / (2 * Real.pi) : ℝ) : ℂ)) * frequencyIntegrand A t w =
        phase w t * ((density A w / (1 + 4 * w ^ 2) : ℝ) : ℂ) := by
      unfold frequencyIntegrand resolvent density
      push_cast
      ring
    rw [he]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      phase_re]
    unfold OriginalTestRegularity.spectralKernel
    ring

lemma spatial_real {A : ℝ → ℂ} (hAm : Measurable A) (hA : Integrable A) (t : ℝ) :
    (∫ p : ℝ × ℝ, coefficient A p * (decay (t - p.1 + p.2) : ℂ)
      ∂pairMeasure).re =
    ∫ p : ℝ × ℝ, (coefficient A p).re * decay (t - p.1 + p.2) ∂pairMeasure := by
  have hre := Complex.reCLM.integral_comp_comm (spatial_integrable hAm hA t)
  simp only [Complex.reCLM_apply] at hre
  rw [← hre]
  change (∫ p : ℝ × ℝ, (coefficient A p * (decay (t - p.1 + p.2) : ℂ)).re
    ∂pairMeasure) = _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- Real part plus the u/v swap supplies the requested sign of the lag.
This works for complex A whose Fourier density need not be even. -/
theorem spectral_convolution {A : ℝ → ℂ} (hAm : Measurable A)
    (hA : Integrable A) (t : ℝ) :
    OriginalTestRegularity.spectralS (rho A) t =
      (∫ p : ℝ × ℝ, (coefficient A p).re * decay (t + p.1 - p.2)
        ∂pairMeasure) / 4 := by
  rw [spectralS_eq_complex_real hA t, complex_resolvent_identity hAm hA t,
    show (4 : ℂ) = ((4 : ℝ) : ℂ) from rfl,
    Complex.div_ofReal_re, spatial_real hAm hA t]
  congr 1
  rw [← integral_prod_swap
    (fun p : ℝ × ℝ => (coefficient A p).re * decay (t - p.1 + p.2))]
  apply integral_congr_ae
  exact ae_of_all _ fun p => by
    dsimp only
    rw [coefficient_re_swap]
    congr 2
    change t - p.2 + p.1 = t + p.1 - p.2
    ring

lemma spatial_real_integrable {A : ℝ → ℂ} (hAm : Measurable A)
    (hA : Integrable A) (t : ℝ) : Integrable
      (fun p : ℝ × ℝ => (coefficient A p).re * decay (t + p.1 - p.2)) pairMeasure := by
  have hs := (spatial_integrable hAm hA t).re.swap
  apply hs.congr
  exact ae_of_all _ fun p => by
    change (coefficient A p.swap * (decay (t - p.2 + p.1) : ℂ)).re = _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, coefficient_re_swap]
    congr 2
    change t - p.2 + p.1 = t + p.1 - p.2
    ring

/-- The L1 spectral resolvent is the exponential convolution of the literal
complex correlation. Complex correlation slices are integrable only almost
everywhere; no L2 hypothesis or symmetry of the Fourier density is needed. -/
theorem spectral_correlation_convolution {A : ℝ → ℂ} (hAm : Measurable A)
    (hA : Integrable A) (t : ℝ) :
    OriginalTestRegularity.spectralS (rho A) t =
      (1 / 4) * ∫ s : ℝ, Real.exp (-|t - s| / 2) *
        (∫ u : ℝ, star (A (u + s)) * A u).re := by
  let T : ℝ × ℝ → ℝ × ℝ := fun p => (p.2, p.2 + p.1)
  have hT : MeasurePreserving T pairMeasure pairMeasure :=
    measurePreserving_prod_add_swap volume volume
  let F : ℝ × ℝ → ℝ := fun p => (coefficient A p).re * decay (t + p.1 - p.2)
  have hF : Integrable F pairMeasure := spatial_real_integrable hAm hA t
  have hFT : Integrable (F ∘ T) pairMeasure := hT.integrable_comp_of_integrable hF
  have hCT : Integrable (coefficient A ∘ T) pairMeasure :=
    hT.integrable_comp_of_integrable (coefficient_integrable hAm hA)
  have hmap : (∫ p, F p ∂pairMeasure) = ∫ p, F (T p) ∂pairMeasure := by
    have hm : AEStronglyMeasurable F (Measure.map T pairMeasure) :=
      hT.map_eq.symm ▸ hF.aestronglyMeasurable
    simpa only [hT.map_eq] using integral_map hT.measurable.aemeasurable hm
  have hslice : ∀ᵐ s : ℝ, Integrable (fun u : ℝ => star (A (u + s)) * A u) := by
    filter_upwards [hCT.prod_right_ae] with s hs
    simpa only [Function.comp_def, T, coefficient, mul_comm, Complex.star_def] using hs
  have hprod := integral_prod (F ∘ T) hFT
  change (∫ p, F (T p) ∂pairMeasure) = ∫ s : ℝ, ∫ u : ℝ, F (T (s, u)) at hprod
  rw [spectral_convolution hAm hA t, hmap, hprod]
  have he : (∫ s : ℝ, ∫ u : ℝ, F (T (s, u))) =
      ∫ s : ℝ, Real.exp (-|t - s| / 2) *
        (∫ u : ℝ, star (A (u + s)) * A u).re := by
    apply integral_congr_ae
    filter_upwards [hslice] with s hs
    have hre := Complex.reCLM.integral_comp_comm hs
    simp only [Complex.reCLM_apply] at hre
    have hp (u : ℝ) : F (T (s, u)) =
        Real.exp (-|t - s| / 2) * (star (A (u + s)) * A u).re := by
      dsimp [F, T, coefficient, decay]
      rw [show t + u - (u + s) = t - s by ring]
      simp only [Complex.star_def, mul_comm]
    simp_rw [hp]
    rw [integral_const_mul, hre]
  rw [he]
  ring

variable {ι : Type*} [Fintype ι]

/-- Original finite atoms, actual Lebesgue restrictions, all real lags. -/
theorem actual_spectral_square (x : ι → ℝ) (a : ι → ℂ) (ha : ∑ i, a i = 0)
    {D : ℝ} (hx : ∀ i, x i ∈ Icc 0 D) (t : ℝ) :
    OriginalTestRegularity.spectralS (rho («prefix» x a)) t =
      (1 / 4) * ∫ u : ℝ in Icc 0 D, ∫ v : ℝ in Icc 0 D,
        (conj («prefix» x a v) * «prefix» x a u).re *
          Real.exp (-|t + u - v| / 2) := by
  let A := «prefix» x a
  have hm : Measurable A := prefix_measurable x a
  have hi : Integrable A := (prefix_L1_L2 x a ha D (fun i => (hx i).2)).1
  let F : ℝ × ℝ → ℝ := fun p => (coefficient A p).re * decay (t + p.1 - p.2)
  have hF : Integrable F pairMeasure := spatial_real_integrable hm hi t
  have hwindow : (Icc 0 D).indicator A = A := prefix_eq_zero_extension x a ha hx
  have hout (u : ℝ) (hu : u ∉ Icc 0 D) : A u = 0 := by
    rw [← congrFun hwindow u, indicator_of_notMem hu]
  have hzero (p : ℝ × ℝ) (hp : p ∉ (Icc 0 D) ×ˢ (Icc 0 D)) : F p = 0 := by
    by_cases hu : p.1 ∈ Icc 0 D
    · have hv : p.2 ∉ Icc 0 D := fun hv => hp ⟨hu, hv⟩
      change (A p.1 * conj (A p.2)).re * _ = 0
      rw [hout p.2 hv]
      simp
    · change (A p.1 * conj (A p.2)).re * _ = 0
      rw [hout p.1 hu]
      simp
  have hr : (∫ p : ℝ × ℝ, F p ∂pairMeasure) =
      ∫ u : ℝ in Icc 0 D, ∫ v : ℝ in Icc 0 D, F (u, v) := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    exact setIntegral_prod F hF.integrableOn
  rw [spectral_convolution hm hi t]
  change (∫ p : ℝ × ℝ, F p ∂pairMeasure) / 4 = _
  rw [hr]
  have he (u v : ℝ) : F (u, v) =
      (conj («prefix» x a v) * «prefix» x a u).re * Real.exp (-|t + u - v| / 2) := by
    dsimp [F, coefficient, A, decay]
    rw [mul_comm (conj _) _]
  simp_rw [he]
  ring

/-- Closed-window weighted moments. Lebesgue endpoint atoms have measure zero. -/
def Iplus (A : ℝ → ℂ) (D : ℝ) : ℂ :=
  ∫ u : ℝ in Icc 0 D, (Real.exp (u / 2) : ℂ) * A u
def Iminus (A : ℝ → ℂ) (D : ℝ) : ℂ :=
  ∫ u : ℝ in Icc 0 D, (Real.exp (-u / 2) : ℂ) * A u
def Z (A : ℝ → ℂ) (D : ℝ) : ℝ := (conj (Iplus A D) * Iminus A D).re

lemma weighted_integrableOn {A : ℝ → ℂ} (hA : Integrable A) (D k : ℝ) :
    IntegrableOn (fun u : ℝ => (Real.exp (k * u) : ℂ) * A u) (Icc 0 D) := by
  have hc : Continuous (fun u : ℝ => (Real.exp (k * u) : ℂ)) := by fun_prop
  exact ((hA.integrableOn).mul_continuousOn hc.continuousOn isCompact_Icc).congr
    (ae_of_all _ fun u => mul_comm _ _)

lemma endpoint_phase {D u v : ℝ} (hD : 0 ≤ D)
    (hu : u ∈ Icc 0 D) (hv : v ∈ Icc 0 D) :
    decay (D + u - v) = Real.exp (-D / 2) * Real.exp (-u / 2) * Real.exp (v / 2) := by
  have hs : 0 ≤ D + u - v := by linarith [hu.1, hv.2]
  unfold decay
  rw [abs_of_nonneg hs]
  have he : -(D + u - v) / 2 = (-D / 2 + -u / 2) + v / 2 := by ring
  rw [he, Real.exp_add, Real.exp_add]

/-- Factor the actual closed square. The sign of the lag gives Iminus(u)
and conjugate(Iplus(v)); commuting the two scalar factors gives exactly Z. -/
lemma endpoint_square_factor {A : ℝ → ℂ} (hAm : Measurable A) (hA : Integrable A)
    {D : ℝ} (hD : 0 ≤ D) :
    (∫ u : ℝ in Icc 0 D, ∫ v : ℝ in Icc 0 D,
      (conj (A v) * A u).re * Real.exp (-|D + u - v| / 2)) =
        Real.exp (-D / 2) * Z A D := by
  let square : Set (ℝ × ℝ) := (Icc 0 D) ×ˢ (Icc 0 D)
  let H : ℝ × ℝ → ℂ := fun p => coefficient A p * (decay (D + p.1 - p.2) : ℂ)
  have hplus : IntegrableOn (fun u : ℝ => (Real.exp (u / 2) : ℂ) * A u) (Icc 0 D) := by
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using weighted_integrableOn hA D (1 / 2)
  have hminus : IntegrableOn (fun u : ℝ => (Real.exp (-u / 2) : ℂ) * A u) (Icc 0 D) := by
    simpa only [div_eq_mul_inv, neg_mul, mul_neg, one_mul, mul_comm] using
      weighted_integrableOn hA D (-1 / 2)
  have hpm : Measurable (fun u : ℝ => (Real.exp (u / 2) : ℂ) * A u) := by fun_prop
  have hproduct := hminus.mul_prod (conjugate_integrable hpm hplus)
  have hH' : Integrable H pairMeasure := by
    apply (coefficient_integrable hAm hA).mul_bdd
    · have hc : Continuous (fun p : ℝ × ℝ => (decay (D + p.1 - p.2) : ℂ)) := by
        unfold decay
        fun_prop
      exact hc.aestronglyMeasurable
    · exact ae_of_all _ fun p => by
        simpa only [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (decay_nonneg _)] using decay_le_one (D + p.1 - p.2)
  have hfactor : (∫ p : ℝ × ℝ in square, H p ∂pairMeasure) =
      (Real.exp (-D / 2) : ℂ) * (Iminus A D * conj (Iplus A D)) := by
    calc
      _ = ∫ p : ℝ × ℝ in square, (Real.exp (-D / 2) : ℂ) *
          (((Real.exp (-p.1 / 2) : ℂ) * A p.1) *
            conj ((Real.exp (p.2 / 2) : ℂ) * A p.2)) ∂pairMeasure := by
        apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
        intro p hp
        have he := endpoint_phase hD hp.1 hp.2
        dsimp [H]
        rw [he]
        simp only [coefficient, Complex.ofReal_mul, map_mul, Complex.conj_ofReal]
        ring
      _ = _ := by
        rw [integral_const_mul, ← Measure.prod_restrict,
          integral_prod _ hproduct]
        simp_rw [integral_const_mul, integral_mul_const, integral_conj]
        rfl
  have hr : (∫ p : ℝ × ℝ in square, H p ∂pairMeasure).re =
      ∫ p : ℝ × ℝ in square,
        (conj (A p.2) * A p.1).re * Real.exp (-|D + p.1 - p.2| / 2) ∂pairMeasure := by
    have hre := Complex.reCLM.integral_comp_comm (hH'.integrableOn (s := square))
    simp only [Complex.reCLM_apply] at hre
    rw [← hre]
    change (∫ p : ℝ × ℝ in square, (H p).re ∂pairMeasure) = _
    apply setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc)
    intro p _
    dsimp [H, coefficient, decay]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.conj_re, Complex.conj_im]
    ring
  have hi : IntegrableOn
      (fun p : ℝ × ℝ => (conj (A p.2) * A p.1).re *
        Real.exp (-|D + p.1 - p.2| / 2)) square pairMeasure := by
    exact (hH'.re.integrableOn).congr (ae_of_all _ fun p => by
      dsimp [H, coefficient, decay]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
        Complex.conj_re, Complex.conj_im]
      ring)
  rw [← setIntegral_prod _ hi, ← hr, hfactor]
  unfold Z
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.conj_re, Complex.conj_im]
  ring

/-- Actual spectral endpoint, not a conditional endpoint adapter. -/
theorem actual_spectral_endpoint (x : ι → ℝ) (a : ι → ℂ) (ha : ∑ i, a i = 0)
    {D : ℝ} (hD : 0 ≤ D) (hx : ∀ i, x i ∈ Icc 0 D) :
    OriginalTestRegularity.spectralS (rho («prefix» x a)) D =
      Real.exp (-D / 2) * Z («prefix» x a) D / 4 := by
  rw [actual_spectral_square x a ha hx D,
    endpoint_square_factor (prefix_measurable x a)
      (prefix_L1_L2 x a ha D (fun i => (hx i).2)).1 hD]
  ring

def originalTest (x : ι → ℝ) (a : ι → ℂ) (t : ℝ) : ℝ :=
  OriginalTestRegularity.c x a t - OriginalTestRegularity.spectralS (rho («prefix» x a)) t

/-- This supplies the previously undischarged `hend`, using the actual Ahat/rho. -/
theorem original_test_endpoint (x : ι → ℝ) (a : ι → ℂ) (ha : ∑ i, a i = 0)
    {D : ℝ} (hD : 0 ≤ D) (hx : ∀ i, x i ∈ Icc 0 D) :
    originalTest x a D = -Real.exp (-D / 2) * Z («prefix» x a) D / 4 := by
  rw [originalTest, OriginalTestRegularity.c_at_D x a ha hx,
    actual_spectral_endpoint x a ha hD hx]
  ring

theorem original_test_ac (x : ι → ℝ) (a : ι → ℂ) (ha : ∑ i, a i = 0)
    {D : ℝ} (hx : ∀ i, x i ∈ Icc 0 D) :
    AbsolutelyContinuousOnInterval (originalTest x a) 0 D := by
  letI : IsFiniteMeasure (rho («prefix» x a)) := actual_rho_finite x a ha D (fun i => (hx i).2)
  exact (OriginalTestRegularity.c_ac x a ha 0 D).sub
    (OriginalTestRegularity.spectralS_ac (rho («prefix» x a)) 0 D)

/-- Direct original-J consumer: the derivative is the actual a.e. derivative.
No caller-supplied endpoint, integrability or finite-measure premise remains. -/
theorem actual_fullR_eq_original_J (x : ι → ℝ) (a : ι → ℂ) (ha : ∑ i, a i = 0)
    {D : ℝ} (hD : 0 ≤ D) (hx : ∀ i, x i ∈ Icc 0 D) :
    OriginalSignedJ.fullR D (Z («prefix» x a) D) (originalTest x a) =
      -2 * Real.eulerMascheroniConstant * originalTest x a 0 -
        OriginalSignedJ.J D (originalTest x a) (deriv (originalTest x a)) := by
  have hf := original_test_ac x a ha hx
  apply OriginalSignedJ.fullR_eq_original_J hD hf
  · filter_upwards [hf.ae_differentiableAt] with t ht htD
    exact (ht htD).hasDerivAt
  · exact original_test_endpoint x a ha hD hx

end OriginalActualSpectralEndpoint
