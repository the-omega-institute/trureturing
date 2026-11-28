/- GID: D5/S3/Analysis/FourierTestSeparation
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-profile-fourier4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourier uniqueness for integrable functions and separation by Lipschitz tests. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
Omega original.

Fourier uniqueness for integrable functions and separation by Lipschitz tests.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory MeasureTheory.Measure Set
open scoped FourierTransform NNReal Topology

namespace Omega

/-- An integrable function with zero Fourier transform vanishes almost everywhere. -/
theorem ae_eq_zero_of_fourier_eq_zero {f : ℝ → ℂ} (hf : Integrable f)
    (hz : (𝓕 f : ℝ → ℂ) = 0) : f =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable
  intro g hg hgc
  let psi := (hgc.comp_left (g := Complex.ofReal) Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hg)
  let q : SchwartzMap ℝ ℂ := 𝓕⁻ psi
  have hq : 𝓕 (q : ℝ → ℂ) = (fun x => (g x : ℂ)) := by
    rw [← SchwartzMap.fourier_coe, FourierTransform.fourier_fourierInv_eq]
    rfl
  have hflip := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (f := f) (g := (q : ℝ → ℂ)) (.mul ℂ ℂ)
    (L := innerₗ ℝ) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    Real.continuous_fourierChar continuous_inner hf q.integrable
  have heq : (∫ ξ, 𝓕 f ξ * q ξ) = ∫ x, f x * 𝓕 (q : ℝ → ℂ) x := by
    simpa [Real.fourier_eq, VectorFourier.fourierIntegral, Real.inner_apply, mul_comm]
      using hflip
  rw [hz, hq] at heq
  simpa [Complex.real_smul, mul_comm] using heq.symm

open Metric in
/-- Integrable complex functions are separated by bounded Lipschitz functions. -/
theorem ae_eq_zero_of_lipschitz_pairing {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {μ : Measure X} {f : X → ℂ}
    (hf : Integrable f μ)
    (h : ∀ g : X → ℂ, (∃ K : ℝ≥0, LipschitzWith K g) →
      (∀ x, ‖g x‖ ≤ 1) → ∫ x, f x * g x ∂μ = 0) : f =ᵐ[μ] 0 := by
  have hclosed (s : Set X) (hs : IsClosed s) : (∫ x in s, f x ∂μ) = 0 := by
    let δ (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
    have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
    let g (n : ℕ) (x : X) : ℂ := ((thickenedIndicator (hδ n) s x : ℝ≥0) : ℝ)
    have hLip (n : ℕ) :
        LipschitzWith (δ n).toNNReal⁻¹ (g n) := by
      have hc : LipschitzWith 1 (fun x : ℝ≥0 => ((x : ℝ) : ℂ)) :=
        LipschitzWith.of_dist_le_mul fun x y => by
          rw [Complex.isometry_ofReal.dist_eq, NNReal.coe_one, one_mul,
            NNReal.dist_eq, Real.dist_eq]
      simpa only [g, Function.comp_def, one_mul] using
        hc.comp (lipschitzWith_thickenedIndicator (hδ n) s)
    have hb (n : ℕ) (x : X) : ‖g n x‖ ≤ 1 := by
      dsimp only [g]
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact_mod_cast thickenedIndicator_le_one (hδ n) s x
    have ht := thickenedIndicator_tendsto_indicator_closure hδ
      (show Tendsto δ atTop (𝓝 0) from tendsto_one_div_add_atTop_nhds_zero_nat) s
    rw [hs.closure_eq, tendsto_pi_nhds] at ht
    have hlim (x : X) : Tendsto (fun n => g n x) atTop
        (𝓝 (s.indicator (fun _ => (1 : ℂ)) x)) := by
      have hc : Continuous (fun x : ℝ≥0 => ((x : ℝ) : ℂ)) :=
        Complex.continuous_ofReal.comp NNReal.continuous_coe
      have hh := hc.continuousAt.tendsto.comp (ht x)
      by_cases hx : x ∈ s <;> simpa [g, hx, Function.comp_def] using hh
    have hlim' : Tendsto (fun n => ∫ x, f x * g n x ∂μ) atTop
        (𝓝 (∫ x, f x * s.indicator (fun _ => (1 : ℂ)) x ∂μ)) :=
      tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
        (.of_forall fun n => hf.aestronglyMeasurable.mul (hLip n).continuous.aestronglyMeasurable)
        (.of_forall fun n => .of_forall fun x => by
          rw [norm_mul]
          exact mul_le_of_le_one_right (norm_nonneg _) (hb n x))
        hf.norm (.of_forall fun x => (hlim x).const_mul _)
    simp_rw [fun n => h (g n) ⟨_, hLip n⟩ (hb n)] at hlim'
    have hz := tendsto_nhds_unique hlim' tendsto_const_nhds
    rw [← integral_indicator hs.measurableSet]
    exact (integral_congr_ae (.of_forall fun x => by
      by_cases hx : x ∈ s <;> simp [hx])).trans hz
  have hset (s : Set X) (hs : MeasurableSet s) : (∫ x in s, f x ∂μ) = 0 := by
    induction s, hs using MeasurableSpace.induction_on_inter
      ((BorelSpace.measurable_eq (α := X)).trans (borel_eq_generateFrom_isClosed (α := X)))
      isPiSystem_isClosed with
    | empty => simp
    | basic s hs => exact hclosed s hs
    | compl s hs ih =>
      rw [setIntegral_compl hs hf, ← setIntegral_univ, hclosed univ isClosed_univ, ih, sub_zero]
    | iUnion s hd hs ih =>
      rw [integral_iUnion hs hd hf.integrableOn]
      simp [ih]
  exact hf.ae_eq_zero_of_forall_setIntegral_eq_zero (fun s hs _ => hset s hs)


private theorem fourier_translate (f : ℝ → ℂ) (t ξ : ℝ) :
    𝓕 (f ∘ fun x => x + t) ξ =
      Complex.exp (((2 * Real.pi * t * ξ : ℝ) : ℂ) * Complex.I) * 𝓕 f ξ := by
  simpa [Real.fourier_eq, VectorFourier.fourierIntegral, Real.inner_apply,
    Real.fourierChar_apply, Circle.smul_def, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
    congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar
      (volume : Measure ℝ) (innerₗ ℝ) f t) ξ

private theorem fourier_dilate (f : ℝ → ℂ) {d : ℝ} (hd : 0 < d) (ξ : ℝ) :
    𝓕 (f ∘ fun x => d * x) ξ = (d⁻¹ : ℝ) • 𝓕 f (d⁻¹ * ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  conv_rhs => rw [← abs_of_pos (inv_pos.mpr hd), ← Measure.integral_comp_mul_left]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Function.comp_apply, abs_of_pos (inv_pos.mpr hd)]
  rw [show -2 * Real.pi * (d * x) * (d⁻¹ * ξ) = -2 * Real.pi * x * ξ by
    field_simp [hd.ne']]

/-- Translations and dilations of a compact test with nonzero integral separate
a weighted frequency pairing on the real line. -/
theorem ae_eq_zero_of_weighted_fourier_pairing {W g f : ℝ → ℂ} {c : ℝ}
    (hc : c ≠ 0) (hW : ∀ᵐ ξ : ℝ, W ξ ≠ 0)
    (hf : Integrable f) (h₀ : (∫ x : ℝ, f x) ≠ 0)
    (hi : ∀ n : ℕ, Integrable (fun ξ => g ξ * W ξ *
      𝓕 (f ∘ fun x : ℝ => ((n : ℝ) + 1) * x) (c * ξ)))
    (hz : ∀ (n : ℕ) (t : ℝ), (∫ ξ : ℝ, g ξ * W ξ *
      𝓕 ((f ∘ fun x : ℝ => ((n : ℝ) + 1) * x) ∘ fun x => x + t) (c * ξ)) = 0) :
    g =ᵐ[volume] 0 := by
  have heq (n : ℕ) : ∀ᵐ ξ : ℝ, g ξ * W ξ *
      𝓕 (f ∘ fun x : ℝ => ((n : ℝ) + 1) * x) (c * ξ) = 0 := by
    apply ae_eq_zero_of_fourier_eq_zero (hi n)
    funext η
    rw [Pi.zero_apply, Real.fourier_real_eq_integral_exp_smul, ← hz n (-η / c)]
    apply integral_congr_ae
    filter_upwards with ξ
    rw [fourier_translate]
    have he : 2 * Real.pi * (-η / c) * (c * ξ) = -2 * Real.pi * ξ * η := by
      field_simp [hc]
    rw [he]
    simp only [smul_eq_mul]
    ring
  have hnz : 𝓕 f (0 : ℝ) ≠ 0 := by
    simpa [Real.fourier_real_eq_integral_exp_smul] using h₀
  have hcont : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf
  filter_upwards [hW, ae_all_iff.2 heq] with ξ hξ hzξ
  by_contra h
  have hz' (n : ℕ) : 𝓕 f (((n : ℝ) + 1)⁻¹ * (c * ξ)) = 0 := by
    have hd : 0 < (n : ℝ) + 1 := by positivity
    have hzn := hzξ n
    rw [fourier_dilate f hd, mul_eq_zero, smul_eq_zero] at hzn
    exact (hzn.resolve_left (mul_ne_zero h hξ)).resolve_left (inv_ne_zero hd.ne')
  have ht : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * (c * ξ)) atTop (𝓝 0) := by
    simpa only [one_div, zero_mul] using
      tendsto_one_div_add_atTop_nhds_zero_nat.mul_const (c * ξ)
  have hb := hcont.continuousAt.tendsto.comp ht
  refine hnz (tendsto_nhds_unique hb ?_)
  simpa only [Function.comp_def, hz'] using (tendsto_const_nhds (x := (0 : ℂ)))


/-- Vanishing against every angular Lipschitz test on almost every slice
implies vanishing for the product measure. -/
theorem ae_eq_zero_of_lipschitz_slice_pairing {A X : Type*} [MeasurableSpace A]
    [MetricSpace X] [CompactSpace X] [SecondCountableTopology X] [MeasurableSpace X]
    [BorelSpace X] {μ : Measure A} {σ : Measure X} [SFinite σ] {f : A × X → ℂ}
    (hm : AEStronglyMeasurable f (μ.prod σ))
    (hi : ∀ᵐ a ∂μ, Integrable (fun x => f (a, x)) σ)
    (hz : ∀ g : C(X, ℂ), (∃ K : ℝ≥0, LipschitzWith K g) →
      ∀ᵐ a ∂μ, ∫ x, f (a, x) * g x ∂σ = 0) :
    f =ᵐ[μ.prod σ] 0 := by
  let L := {g : C(X, ℂ) | ∃ K : ℝ≥0, LipschitzWith K g}
  obtain ⟨s, hs, hd⟩ := TopologicalSpace.exists_countable_dense L
  have : Countable s := hs.to_subtype
  have hz' (g : s) : ∀ᵐ a ∂μ, ∫ x, f (a, x) * (g : L).val x ∂σ = 0 :=
    hz _ (g : L).property
  have hz'' : ∀ᵐ a ∂μ, ∀ᵐ x ∂σ, f (a, x) = 0 := by
    filter_upwards [hi, ae_all_iff.2 hz'] with a ha haz
    let pairing (g : C(X, ℂ)) := ∫ x, f (a, x) * g x ∂σ
    have hint (g : C(X, ℂ)) : Integrable (fun x => f (a, x) * g x) σ := by
      apply (ha.norm.mul_const ‖g‖).mono' (ha.aestronglyMeasurable.mul
        g.continuous.aestronglyMeasurable)
      filter_upwards with x
      change ‖f (a, x) * g x‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm g x) (norm_nonneg _)
    have hcont : Continuous pairing := by
      let B : ℝ≥0 := ⟨∫ x, ‖f (a, x)‖ ∂σ, integral_nonneg (fun x => norm_nonneg _)⟩
      apply (show LipschitzWith B pairing from LipschitzWith.of_dist_le_mul ?_).continuous
      intro g h
      dsimp only [pairing, B]
      rw [dist_eq_norm, ← integral_sub (hint g) (hint h)]
      simp_rw [← mul_sub]
      apply (norm_integral_le_integral_norm _).trans
      rw [dist_eq_norm]
      change (∫ x, ‖f (a, x) * (g x - h x)‖ ∂σ) ≤
        (∫ x, ‖f (a, x)‖ ∂σ) * ‖g - h‖
      rw [← integral_mul_const]
      apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
        (ha.norm.mul_const _)
      filter_upwards with x
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        (ContinuousMap.norm_coe_le_norm (g - h) x) (norm_nonneg _)
    have hall (g : L) : pairing g.val = 0 := by
      have hcl : IsClosed {g : L | pairing g.val = 0} :=
        isClosed_eq (hcont.comp continuous_subtype_val) continuous_const
      exact closure_minimal (fun y hy => haz ⟨y, hy⟩) hcl (hd g)
    refine ae_eq_zero_of_lipschitz_pairing ha (fun g hg _ => ?_)
    exact hall ⟨⟨g, hg.choose_spec.continuous⟩, hg⟩
  have hrep := ae_ae_of_ae_prod hm.ae_eq_mk
  have hzero : ∀ᵐ p ∂μ.prod σ, hm.mk f p = 0 := by
    rw [ae_prod_iff_ae_ae (measurableSet_eq_fun hm.stronglyMeasurable_mk.measurable measurable_const)]
    filter_upwards [hz'', hrep] with a ha hrep'
    filter_upwards [ha, hrep'] with x hx hxe
    exact hxe.symm.trans hx
  filter_upwards [hzero, hm.ae_eq_mk] with p hp hpe
  exact hpe.trans hp


/-- Parseval pairing of an integrable function against a Schwartz test.
The Schwartz factor ensures integrability on the frequency side. -/
theorem integral_fourier_inner_test {f : ℝ → ℂ} (hf : Integrable f)
    (g : SchwartzMap ℝ ℂ) :
    (∫ x, star (g x) * f x) = ∫ ξ, star (𝓕 g ξ) * 𝓕 f ξ := by
  let q : SchwartzMap ℝ ℂ := 𝓕 g
  have hflip := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip
    (f := f) (g := (q : ℝ → ℂ)) (innerSL ℂ)
    (L := innerₗ ℝ) (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    Real.continuous_fourierChar continuous_inner hf q.integrable
  have hconj := congrArg (starRingEnd ℂ) hflip
  simp only [← integral_conj] at hconj
  have hi (x : ℝ) :
      VectorFourier.fourierIntegral Real.fourierChar volume (-(innerₗ ℝ).flip) q x = g x := by
    have hh : (innerₗ ℝ : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ).flip = innerₗ ℝ := by
      apply LinearMap.ext
      intro u
      apply LinearMap.ext
      intro v
      simp [Real.inner_apply, mul_comm]
    rw [hh]
    change 𝓕⁻ (q : ℝ → ℂ) x = g x
    rw [← SchwartzMap.fourierInv_coe]
    exact congrFun (congrArg DFunLike.coe (FourierTransform.fourierInv_fourier_eq g)) x
  have hF (ξ : ℝ) :
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ) f ξ = 𝓕 f ξ := rfl
  simp only [innerSL_apply_apply, RCLike.inner_apply, map_mul, starRingEnd_apply, star_star,
    hF, hi] at hconj
  simpa [q, mul_comm] using hconj.symm

end Omega

