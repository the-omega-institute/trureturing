/- GID: D5/S3/Weil/ZetaBridge/SalemIntegralUniqueness
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/SalemIntegralUniqueness
   mirror-E: none(waiver:infinite-domain-analytic-theorem)
   anchors: [mathlib/module/Mathlib.Analysis.MellinTransform]
   utility: none
   digest: Salem integral uniqueness for bounded completed-measurable functions. -/
import D5.S3.Weil.ZetaBridge.FermiMellin
import D5.S3.Fourier.SmoothConvolutionUniqueness
import D5.S3.Analytic.Dilation.MellinDilationFlow
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Complex.CauchyIntegral

open Complex Filter MeasureTheory Set
open scoped FourierTransform Topology ContDiff
set_option autoImplicit false
namespace D5.S3.Weil.ZetaBridge.SalemIntegralUniqueness
noncomputable section
open FermiMellin D5.S3.Analytic.Dilation.MellinDilationFlow

/-- The positive Salem kernel in logarithmic coordinates. -/
def salemKernel (δ u : ℝ) : ℂ :=
  ((Real.exp (δ * u) / (Real.exp (Real.exp u) + 1) : ℝ) : ℂ)

private lemma exp_cpow_real (u a : ℝ) :
    (Real.exp u : ℂ) ^ (a : ℂ) = (Real.exp (u * a) : ℂ) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
    ← ofReal_log (Real.exp_pos u).le, Real.log_exp, ← ofReal_mul, ofReal_exp]

private theorem salem_kernel_integrable (δ : ℝ) (hδ : 0 < δ) :
    Integrable (salemKernel δ) := by
  have h := fermi_mellin_integrable 1 (by norm_num) (δ : ℂ) hδ
  have hc := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun u (_ : u ∈ (univ : Set ℝ)) => (Real.hasDerivAt_exp u).hasDerivWithinAt)
    Real.exp_injective.injOn (fun t : ℝ => (t : ℂ)^((δ : ℂ)-1) / ((Real.exp t : ℂ)+1))
  rw [image_univ, Real.range_exp] at hc
  simp only [one_mul] at h
  have hi := hc.mp h
  simp only [integrableOn_univ, abs_of_pos (Real.exp_pos _), Complex.real_smul,
    ← ofReal_one, ← ofReal_sub, exp_cpow_real] at hi
  convert hi using 1
  funext u
  simp only [salemKernel, ofReal_div, ofReal_add, ofReal_one, ← mul_div_assoc,
    ← ofReal_mul, ← Real.exp_add]
  congr 2
  congr 1
  ring

private theorem fourier_salem_kernel_eq_mellin (δ ξ : ℝ) :
    𝓕 (salemKernel δ) ξ = ∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ ((δ : ℂ) - 1 + I * ((-2 * Real.pi * ξ : ℝ) : ℂ)) /
        ((Real.exp t : ℂ) + 1) := by
  have h := mellin_eq_fourier_on_dilation_flow
    (fun t : ℝ => 1 / ((Real.exp t : ℂ) + 1))
    ((δ : ℂ) + I * ((-2 * Real.pi * ξ : ℝ) : ℂ))
  simp only [mellin, smul_eq_mul, mul_one_div] at h
  rw [show (δ : ℂ) + I * ((-2 * Real.pi * ξ : ℝ) : ℂ) - 1 =
    (δ : ℂ) - 1 + I * ((-2 * Real.pi * ξ : ℝ) : ℂ) by ring] at h
  rw [h, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with u
  simp only [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im, mul_zero,
    zero_mul, sub_zero, add_zero, add_im, mul_im, zero_add,
    one_mul, Real.inner_apply, salemKernel, ofReal_div, ofReal_add,
    ofReal_one, smul_eq_mul, Complex.real_smul, mul_one_div]
  congr 2; push_cast; ring

private def salemProduct (s : ℂ) : ℂ :=
  Gamma s * (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

private theorem salemProduct_contDiffOn :
    ContDiffOn ℝ ∞ salemProduct {s : ℂ | 0 < s.re ∧ s.re < 1} := by
  apply ContDiffOn.restrict_scalars ℝ (𝕜' := ℂ)
  apply DifferentiableOn.contDiffOn
  · intro s hs
    have hg := differentiableAt_Gamma s (fun n he => by
      have hr := congrArg Complex.re he
      simp only [neg_re, natCast_re] at hr
      have := Nat.cast_nonneg (α := ℝ) n
      linarith [hs.1])
    have hz := differentiableAt_riemannZeta (s := s) (by
      intro he; have hr := congrArg Complex.re he; simp only [one_re] at hr
      linarith [hs.2])
    exact ((hg.mul ((differentiableAt_const (1 : ℂ)).sub
      (((differentiableAt_const (1 : ℂ)).sub differentiableAt_id).const_cpow
        (Or.inl (by norm_num : (2 : ℂ) ≠ 0))))).mul hz).differentiableWithinAt
  · exact (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_re continuous_const)

private theorem salem_kernel_fourier_contDiff (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ContDiff ℝ ∞ (𝓕 (salemKernel δ)) := by
  have hc : ContDiff ℝ ∞ (fun ξ : ℝ => (δ : ℂ) + I * ((-2 * Real.pi * ξ : ℝ) : ℂ)) := by
    exact contDiff_const.add (contDiff_const.mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)))
  have h := salemProduct_contDiffOn.comp_contDiff hc (fun ξ => by simpa using And.intro hδ hδ1)
  convert h using 1
  funext ξ
  rw [fourier_salem_kernel_eq_mellin]
  have he : (δ : ℂ) - 1 + I * ((-2 * Real.pi * ξ : ℝ) : ℂ) =
      ((δ : ℂ) + I * ((-2 * Real.pi * ξ : ℝ) : ℂ)) - 1 := by ring
  rw [he]
  have hp := fermi_mellin_eq_of_ne_one 1 (by norm_num)
    ((δ : ℂ) + I * ((-2 * Real.pi * ξ : ℝ) : ℂ)) (by simpa using hδ)
    (by intro he; have hr := congrArg Complex.re he; simp at hr; linarith)
  simpa [salemProduct, Function.comp_def] using hp


/-- Positive logarithmic coordinates and translation, for totalized integrals. -/
theorem salem_integral_eq_convolution (δ y : ℝ) (f : ℝ → ℂ) :
    (∫ t : ℝ in Ioi 0, ((t ^ (δ - 1) : ℝ) : ℂ) * f t /
      ((Real.exp (Real.exp y * t) : ℂ) + 1)) =
    (Real.exp (-δ * y) : ℂ) *
      (∫ u : ℝ, salemKernel δ u * f (Real.exp (u - y))) := by
  have h := mellin_eq_fourier_on_dilation_flow
    (fun t : ℝ => f t / ((Real.exp (Real.exp y * t) : ℂ) + 1)) (δ : ℂ)
  have hp : (∫ t : ℝ in Ioi 0, ((t ^ (δ - 1) : ℝ) : ℂ) * f t /
      ((Real.exp (Real.exp y * t) : ℂ) + 1)) =
      mellin (fun t : ℝ => f t / ((Real.exp (Real.exp y * t) : ℂ) + 1)) (δ : ℂ) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [smul_eq_mul]
    rw [Complex.ofReal_cpow ht.le]
    push_cast
    ring
  rw [hp, h]
  simp only [ofReal_im, zero_mul, ofReal_zero, exp_zero, one_smul, ofReal_re,
    Complex.real_smul]
  rw [← integral_sub_right_eq_self (fun v : ℝ =>
    (Real.exp (δ*v) : ℂ) * (f (Real.exp v) /
      ((Real.exp (Real.exp y * Real.exp v) : ℂ) + 1))) y,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  simp only [salemKernel, ofReal_div, ofReal_add, ofReal_one,
    ← Real.exp_add, show y + (u-y) = u by ring]
  rw [show δ * (u-y) = -δ*y + δ*u by ring, Real.exp_add, ofReal_mul]
  ring

private theorem nullMeasurable_iff_aestronglyMeasurable_complex (f : ℝ → ℂ) :
    NullMeasurable f (volume.restrict (Ioi 0)) ↔
      AEStronglyMeasurable f (volume.restrict (Ioi 0)) := by
  rw [aestronglyMeasurable_iff_nullMeasurable_separable]
  exact ⟨fun h => ⟨h, univ, .of_separableSpace univ, Eventually.of_forall (fun _ => mem_univ _)⟩,
    And.left⟩

private theorem quasiMeasurePreserving_exp_neg :
    Measure.QuasiMeasurePreserving (fun v : ℝ => Real.exp (-v)) volume
      (volume.restrict (Ioi 0)) := by
  refine ⟨by fun_prop, Measure.AbsolutelyContinuous.mk ?_⟩
  intro s hs hs0
  rw [Measure.map_apply (by fun_prop) hs]
  rw [Measure.restrict_apply hs] at hs0
  have hi := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (f := fun t : ℝ => -Real.log t) (s := s ∩ Ioi 0)
    (fun t ht => ((Real.differentiableAt_log ht.2.ne').neg).differentiableWithinAt) hs0
  apply measure_mono_null _ hi
  intro v hv
  exact ⟨Real.exp (-v), ⟨hv, Real.exp_pos _⟩, by simp⟩

private theorem quasiMeasurePreserving_neg_log :
    Measure.QuasiMeasurePreserving (fun t : ℝ => -Real.log t)
      (volume.restrict (Ioi 0)) volume := by
  refine ⟨by fun_prop, Measure.AbsolutelyContinuous.mk ?_⟩
  intro s hs hs0
  rw [Measure.map_apply (by fun_prop) hs,
    Measure.restrict_apply ((by fun_prop : Measurable (fun t : ℝ => -Real.log t)) hs)]
  have hi := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (f := fun v : ℝ => Real.exp (-v))
    (by fun_prop : DifferentiableOn ℝ (fun v : ℝ => Real.exp (-v)) s) hs0
  apply measure_mono_null _ hi
  intro t ht
  exact ⟨-Real.log t, ht.1, by simpa using Real.exp_log ht.2⟩

private theorem salem_pullback_aestronglyMeasurable (f : ℝ → ℂ)
    (hf : NullMeasurable f (volume.restrict (Ioi 0))) :
    AEStronglyMeasurable (fun v => f (Real.exp (-v))) volume :=
  ((nullMeasurable_iff_aestronglyMeasurable_complex f).mp hf).comp_quasiMeasurePreserving
    quasiMeasurePreserving_exp_neg

private theorem salem_pullback_ae_zero_iff (f : ℝ → ℂ) :
    (∀ᵐ v ∂volume, f (Real.exp (-v)) = 0) ↔
      (∀ᵐ t ∂volume.restrict (Ioi 0), f t = 0) := by
  constructor
  · intro h
    filter_upwards [quasiMeasurePreserving_neg_log.ae h,
      ae_restrict_mem measurableSet_Ioi] with t ht htpos
    simpa [Real.exp_log htpos] using ht
  · exact quasiMeasurePreserving_exp_neg.ae


private theorem original_integrand_integrable (δ x : ℝ) (hδ : 0 < δ) (hx : 0 < x)
    (f : ℝ → ℂ) (hf : NullMeasurable f (volume.restrict (Ioi 0)))
    (B : ℝ) (hb : ∀ t, 0 < t → ‖f t‖ ≤ B) :
    IntegrableOn (fun t => ((t^(δ-1) : ℝ):ℂ)*f t/((Real.exp (x*t):ℂ)+1)) (Ioi 0) := by
  have h := (fermi_mellin_integrable x hx (δ : ℂ) hδ).mul_bdd
    ((nullMeasurable_iff_aestronglyMeasurable_complex f).mp hf)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hb t ht)
  apply h.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Complex.ofReal_cpow ht.le]
  push_cast
  ring

private theorem salem_convolution_integrable (δ y : ℝ) (hδ : 0 < δ)
    (f : ℝ → ℂ) (hf : NullMeasurable f (volume.restrict (Ioi 0)))
    (B : ℝ) (hb : ∀ t, 0 < t → ‖f t‖ ≤ B) :
    Integrable (fun u => salemKernel δ u * f (Real.exp (u-y))) := by
  have hm := (salem_pullback_aestronglyMeasurable f hf).comp_quasiMeasurePreserving
    (Measure.measurePreserving_sub_left volume y).quasiMeasurePreserving
  apply (salem_kernel_integrable δ hδ).mul_bdd (by
    convert hm using 1
    funext u
    simp)
    (Eventually.of_forall (fun u => hb _ (Real.exp_pos _)))

/-- Completing the source sigma algebra preserves its Bochner integral. -/
private theorem completion_integral_eq (μ : Measure ℝ) (f : ℝ → ℂ)
    (hf : AEStronglyMeasurable f μ) :
    (∫ t : NullMeasurableSpace ℝ μ, f t ∂μ.completion) = ∫ t : ℝ, f t ∂μ := by
  have hm : (inferInstance : MeasurableSpace ℝ) ≤
      (inferInstance : MeasurableSpace (NullMeasurableSpace ℝ μ)) :=
    fun _ hs => hs.nullMeasurableSet
  have ht : μ.completion.trim hm = μ := by
    apply @Measure.ext ℝ _
    intro s hs
    exact trim_measurableSet_eq hm hs
  dsimp only [NullMeasurableSpace] at hm ht ⊢
  have hh : AEStronglyMeasurable f (μ.completion.trim hm) := by
    dsimp only [NullMeasurableSpace] at *
    rwa [ht]
  have h := integral_trim_ae (β := ℝ) (μ := μ.completion) hm (f := f) hh
  simpa only [ht] using h

/-- Convergent transport, with the original integral on the completed measure. -/
private theorem salem_integrable_transport (δ y : ℝ) (hδ : 0 < δ)
    (f : ℝ → ℂ) (hf : NullMeasurable f (volume.restrict (Ioi 0)))
    (B : ℝ) (hb : ∀ t, 0 < t → ‖f t‖ ≤ B) :
    (IntegrableOn (fun t => ((t^(δ-1):ℝ):ℂ)*f t/
        ((Real.exp (Real.exp y*t):ℂ)+1)) (Ioi 0) ∧
      Integrable (fun u => salemKernel δ u*f (Real.exp (u-y)))) ∧
    (∫ t : NullMeasurableSpace ℝ (volume.restrict (Ioi 0)),
      (fun t : ℝ => ((t^(δ-1):ℝ):ℂ)*f t/((Real.exp (Real.exp y*t):ℂ)+1)) t
        ∂(volume.restrict (Ioi 0)).completion) =
      (Real.exp (-δ*y):ℂ) * ∫ u, salemKernel δ u*f (Real.exp (u-y)) := by
  have hi := original_integrand_integrable δ (Real.exp y) hδ (Real.exp_pos _) f hf B hb
  refine ⟨⟨hi, salem_convolution_integrable δ y hδ f hf B hb⟩, ?_⟩
  rw [completion_integral_eq _ _ hi.aestronglyMeasurable]
  exact salem_integral_eq_convolution δ y f

private def salemCharacter (γ t : ℝ) : ℂ :=
  Complex.exp (I * (γ : ℂ) * (Real.log t : ℂ))


private theorem salem_character_witness (δ γ : ℝ) (hδ : 0 < δ)
    (hz : (∫ t : ℝ in Ioi 0, (t:ℂ)^((δ:ℂ)-1+I*(γ:ℂ))/((Real.exp t:ℂ)+1)) = 0) :
    NullMeasurable (salemCharacter γ) (volume.restrict (Ioi 0)) ∧
    (∀ t, ‖salemCharacter γ t‖ = 1) ∧
    (¬ ∀ᵐ t ∂volume.restrict (Ioi 0), salemCharacter γ t = 0) ∧
    (∀ x, 0 < x →
      IntegrableOn (fun t : ℝ => ((t^(δ-1):ℝ):ℂ)*salemCharacter γ t/
        ((Real.exp (x*t):ℂ)+1)) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0,
        ((t^(δ-1):ℝ):ℂ)*salemCharacter γ t/((Real.exp (x*t):ℂ)+1)) = 0) := by
  have hm : Measurable (salemCharacter γ) := by unfold salemCharacter; fun_prop
  have hn (t : ℝ) : ‖salemCharacter γ t‖ = 1 := by
    simp [salemCharacter, Complex.norm_exp]
  have hnon : ¬ ∀ᵐ t ∂volume.restrict (Ioi 0), salemCharacter γ t = 0 := by
    intro h
    have hfalse : ∀ᵐ t : ℝ ∂volume.restrict (Ioi 0), False := h.mono (fun t ht => by
      have := hn t; rw [ht, norm_zero] at this; norm_num at this)
    have hm0 := (Filter.eventually_false_iff_eq_bot.mp hfalse)
    have hz0 := ae_eq_bot.mp hm0
    have hi : (volume.restrict (Ioi (0 : ℝ))) (Ioc 1 2) = 1 := by
      rw [Measure.restrict_apply measurableSet_Ioc, inter_eq_left.mpr]
      · norm_num
      · intro t ht; exact lt_trans (by norm_num) ht.1
    rw [hz0] at hi
    simp at hi
  refine ⟨hm.nullMeasurable, hn, hnon, ?_⟩
  intro x hx
  refine ⟨original_integrand_integrable δ x hδ hx _ hm.nullMeasurable 1
    (fun t _ => (hn t).le), ?_⟩
  let s : ℂ := (δ : ℂ) + I*(γ : ℂ)
  have he (t : ℝ) (ht : 0 < t) :
      ((t^(δ-1) : ℝ) : ℂ)*salemCharacter γ t = (t : ℂ)^(s-1) := by
    rw [Complex.ofReal_cpow ht.le, salemCharacter,
      cpow_def_of_ne_zero (ofReal_ne_zero.mpr ht.ne'),
      cpow_def_of_ne_zero (ofReal_ne_zero.mpr ht.ne'), ← Complex.exp_add,
      ← ofReal_log ht.le]
    congr 1
    dsimp [s]
    push_cast
    ring
  have hM : mellin (fun t : ℝ => 1 / ((Real.exp t : ℂ)+1)) s = 0 := by
    simpa only [mellin, smul_eq_mul, mul_one_div, s,
      show (δ : ℂ)+I*(γ : ℂ)-1 = (δ : ℂ)-1+I*(γ : ℂ) by ring] using hz
  calc
    _ = mellin (fun t : ℝ => 1 / ((Real.exp (x*t) : ℂ)+1)) s := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simp only [smul_eq_mul, mul_one_div]
      rw [he t ht]
    _ = (x : ℂ)^(-s) * mellin (fun t : ℝ => 1 / ((Real.exp t : ℂ)+1)) s := by
      simpa only [smul_eq_mul] using
        mellin_comp_mul_left (fun t : ℝ => 1 / ((Real.exp t : ℂ)+1)) s hx
    _ = 0 := by rw [hM, mul_zero]

/-- The original bounded, completed-Lebesgue-measurable uniqueness criterion. -/
theorem salem_bounded_measurable_uniqueness_iff_rh :
    RiemannHypothesis ↔ ∀ δ : ℝ, (1 / 2 : ℝ) < δ → δ < 1 →
      ∀ f : ℝ → ℂ, NullMeasurable f (volume.restrict (Ioi 0)) →
      (∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 < t → ‖f t‖ ≤ B) →
      (∀ x : ℝ, 0 < x → (∫ t : ℝ in Ioi 0,
        ((t ^ (δ - 1) : ℝ) : ℂ) * f t / ((Real.exp (x * t) : ℂ) + 1)) = 0) →
      ∀ᵐ t ∂volume.restrict (Ioi 0), f t = 0 := by
  constructor
  · intro hRH δ hlo hhi f hf hb hz
    have hδ : 0 < δ := by linarith
    apply (salem_pullback_ae_zero_iff f).mp
    apply D5.S3.Fourier.SmoothConvolutionUniqueness.ae_eq_zero_of_smooth_fourier_convolution_eq_zero
      (salem_kernel_integrable δ hδ) (salem_kernel_fourier_contDiff δ hδ hhi)
    · intro ξ
      rw [fourier_salem_kernel_eq_mellin]
      exact salem_mellin_nonvanishing_iff_rh.mpr hRH δ hlo hhi _
    · exact salem_pullback_aestronglyMeasurable f hf
    · obtain ⟨B, hB, hb⟩ := hb
      exact ⟨B, hB, fun y => hb _ (Real.exp_pos _)⟩
    · intro y
      obtain ⟨B, _, hB⟩ := hb
      have hc := salem_integrable_transport δ y hδ f hf B hB
      have ht := hc.2
      rw [completion_integral_eq _ _ hc.1.1.aestronglyMeasurable,
        hz _ (Real.exp_pos _)] at ht
      have hn : (Real.exp (-δ*y) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.exp_ne_zero _)
      have hzero := (mul_eq_zero.mp ht.symm).resolve_left hn
      simpa only [neg_sub] using hzero
  · intro h
    apply salem_mellin_nonvanishing_iff_rh.mp
    intro δ hlo hhi γ hz
    obtain ⟨hm, hn, hnon, he⟩ := salem_character_witness δ γ (by linarith) hz
    exact hnon (h δ hlo hhi (salemCharacter γ) hm
      ⟨1, by norm_num, fun t _ => (hn t).le⟩ (fun x hx => (he x hx).2))

end
end D5.S3.Weil.ZetaBridge.SalemIntegralUniqueness
