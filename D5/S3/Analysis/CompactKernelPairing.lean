/- GID: D5/S3/Analysis/CompactKernelPairing
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-weak-boundary4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two integrations by parts for a smooth kernel against compact tests in an open interval, with transport to logistic coordinates. -/

import OmegaBuild.Commands
import D5.S3.Analysis.LogisticCoordinate
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod

/-!
Omega original.

Two integrations by parts for a smooth kernel against compact tests in an open
interval, with transport to logistic coordinates.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set Function
open scoped Topology

namespace Omega

/-- A complex kernel analytic on the positive real axis, tested at a positive
multiple of the coordinate product, is twice continuously differentiable there. -/
theorem contDiffOn_mul_of_real_product {a : ℝ} (ha : 0 < a) {F : ℂ → ℂ}
    (hF : ∀ q : ℝ, 0 < q → AnalyticAt ℂ F q) :
    ContDiffOn ℝ 2 (fun p : ℝ × ℝ => ((p.1 * p.2 : ℝ) : ℂ) *
      F (((a * p.1 * p.2 : ℝ) : ℂ))) (Ioi 0 ×ˢ Ioi 0) := by
  intro p hp
  have hu : 0 < p.1 := hp.1
  have hv : 0 < p.2 := hp.2
  have hq : ContDiff ℝ 2 (fun p : ℝ × ℝ => a * p.1 * p.2) :=
    (contDiff_const.mul contDiff_fst).mul contDiff_snd
  have hqC := Complex.ofRealCLM.contDiff.comp hq
  have hprod : ContDiff ℝ 2 (fun p : ℝ × ℝ => p.1 * p.2) := contDiff_fst.mul contDiff_snd
  have hprodC := Complex.ofRealCLM.contDiff.comp hprod
  have hanalytic : AnalyticAt ℂ F ((a * p.1 * p.2 : ℝ) : ℂ) := hF _ (by positivity)
  exact (hprodC.contDiffAt.mul
    ((hanalytic.restrictScalars (𝕜 := ℝ)).contDiffAt.comp p hqC.contDiffAt)).contDiffWithinAt

private def unitMeasure : Measure ℝ := volume.restrict (Ioo 0 1)

private local instance : IsFiniteMeasure unitMeasure := by
  unfold unitMeasure
  infer_instance

private def quadrant : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioi 0

private theorem open_quadrant : IsOpen quadrant :=
  isOpen_Ioi.prod isOpen_Ioi

private def partialLeft (K : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  deriv (fun u => K (u, p.2)) p.1

private def partialRight (K : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  deriv (fun v => K (p.1, v)) p.2

private theorem partialLeft_smooth {K : ℝ × ℝ → ℂ} {n m : WithTop ℕ∞}
    (hK : ContDiffOn ℝ n K quadrant) (hn : 1 ≤ n) (hm : m + 1 ≤ n) :
    ContDiffOn ℝ m (partialLeft K) quadrant := by
  have he (p : ℝ × ℝ) (hp : p ∈ quadrant) :
      partialLeft K p = fderiv ℝ K p (1, 0) := by
    have hd := ((hK.differentiableOn (ne_of_gt (zero_lt_one.trans_le hn))).differentiableAt
      (open_quadrant.mem_nhds hp)).hasFDerivAt
    have hpair : HasDerivAt (fun u : ℝ => (u, p.2)) (1, 0) p.1 :=
      (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
    exact (hd.comp_hasDerivAt p.1 hpair).deriv
  exact ((hK.fderiv_of_isOpen open_quadrant hm).clm_apply contDiffOn_const).congr he

private theorem partialRight_continuous {K : ℝ × ℝ → ℂ}
    (hK : ContDiffOn ℝ 1 K quadrant) : ContinuousOn (partialRight K) quadrant := by
  have he (p : ℝ × ℝ) (hp : p ∈ quadrant) :
      partialRight K p = fderiv ℝ K p (0, 1) := by
    have hd := ((hK.differentiableOn one_ne_zero).differentiableAt
      (open_quadrant.mem_nhds hp)).hasFDerivAt
    have hpair : HasDerivAt (fun v : ℝ => (p.1, v)) (0, 1) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    exact (hd.comp_hasDerivAt p.2 hpair).deriv
  exact ((hK.continuousOn_fderiv_of_isOpen open_quadrant le_rfl).clm_apply
    continuousOn_const).congr he

private theorem compact_of_unit_support {f : ℝ → ℂ}
    (hf : tsupport f ⊆ Ioo 0 1) : HasCompactSupport f :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) (hf.trans Ioo_subset_Icc_self)

private theorem weighted_pair_integrable {K : ℝ × ℝ → ℂ} (hK : ContinuousOn K quadrant)
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hf₀ : tsupport f ⊆ Ioo 0 1) (hg₀ : tsupport g ⊆ Ioo 0 1) :
    Integrable (fun p : ℝ × ℝ => f p.1 * K p * g p.2) ((volume : Measure ℝ).prod volume) := by
  have hsub : tsupport f ×ˢ tsupport g ⊆ quadrant :=
    prod_mono (hf₀.trans fun _ h => h.1) (hg₀.trans fun _ h => h.1)
  have hc : ContinuousOn (fun p : ℝ × ℝ => f p.1 * K p * g p.2) (tsupport f ×ˢ tsupport g) :=
    (((hf.comp continuous_fst).continuousOn).mul (hK.mono hsub)).mul
      (hg.comp continuous_snd).continuousOn
  apply (hc.integrableOn_compact ((compact_of_unit_support hf₀).prod
    (compact_of_unit_support hg₀))).integrable_of_forall_notMem_eq_zero
  intro p hp
  by_cases h₁ : p.1 ∈ tsupport f
  · have h₂ : p.2 ∉ tsupport g := fun h => hp ⟨h₁, h⟩
    rw [image_eq_zero_of_notMem_tsupport h₂, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport h₁, zero_mul, zero_mul]

private theorem integral_weighted_pair_restrict (K : ℝ × ℝ → ℂ) {f g : ℝ → ℂ}
    (hf₀ : tsupport f ⊆ Ioo 0 1) (hg₀ : tsupport g ⊆ Ioo 0 1) :
    (∫ p : ℝ × ℝ, f p.1 * K p * g p.2 ∂(unitMeasure.prod unitMeasure)) =
      ∫ p : ℝ × ℝ, f p.1 * K p * g p.2 ∂((volume : Measure ℝ).prod volume) := by
  rw [unitMeasure, Measure.prod_restrict]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  by_cases h₁ : p.1 ∈ Ioo (0 : ℝ) 1
  · have h₂ : p.2 ∉ tsupport g := fun h => hp ⟨h₁, hg₀ h⟩
    rw [image_eq_zero_of_notMem_tsupport h₂, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport (fun h => h₁ (hf₀ h)), zero_mul, zero_mul]

private theorem mul_deriv_integral {f k : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hf₀ : tsupport f ⊆ Ioo 0 1) (hk : ContDiffOn ℝ 1 k (Ioi 0)) :
    (∫ u : ℝ, deriv f u * k u) = -(∫ u : ℝ, f u * deriv k u) := by
  have hc := compact_of_unit_support hf₀
  have hfs : tsupport (deriv f) ⊆ tsupport f := tsupport_deriv_subset
  have hsub : tsupport f ⊆ Ioi (0 : ℝ) := hf₀.trans fun _ h => h.1
  have h : ∀ {a b : ℝ → ℂ}, ContinuousOn a (tsupport f) →
      ContinuousOn b (tsupport f) → (tsupport a ⊆ tsupport f ∨ tsupport b ⊆ tsupport f) →
      Integrable (a * b) := by
    intro a b ha hb hab
    apply ((ha.mul hb).integrableOn_compact hc).integrable_of_forall_notMem_eq_zero
    intro u hu
    rcases hab with ha' | hb'
    · simp [image_eq_zero_of_notMem_tsupport (fun h => hu (ha' h))]
    · simp [image_eq_zero_of_notMem_tsupport (fun h => hu (hb' h))]
  have hfd := hf.continuous_deriv le_rfl
  have hkd := (hk.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).mono hsub
  have hkc := hk.continuousOn.mono hsub
  have hp : HasCompactSupport (k * f) := hc.mul_left
  have ht : Tendsto (k * f) (cocompact ℝ) (𝓝 0) := hp.is_zero_at_infty
  have hparts := MeasureTheory.integral_mul_deriv_eq_deriv_mul
    (fun u hu => ((hk.differentiableOn one_ne_zero).differentiableAt
      (isOpen_Ioi.mem_nhds (hsub hu))).hasDerivAt)
    (fun u _ => (hf.differentiable one_ne_zero u).hasDerivAt)
    (h hkc hfd.continuousOn (Or.inr hfs))
    (h hkd hf.continuous.continuousOn (Or.inr (Subset.refl _)))
    (ht.mono_left atBot_le_cocompact) (ht.mono_left atTop_le_cocompact)
  simpa only [sub_zero, zero_sub, Pi.mul_apply, mul_comm] using hparts

private theorem sliceLeft_smooth {K : ℝ × ℝ → ℂ} (hK : ContDiffOn ℝ 1 K quadrant)
    {v : ℝ} (hv : 0 < v) : ContDiffOn ℝ 1 (fun u => K (u, v)) (Ioi 0) :=
  hK.comp ((contDiff_id.prodMk contDiff_const).contDiffOn) (fun _ hu => ⟨hu, hv⟩)

private theorem sliceRight_smooth {K : ℝ × ℝ → ℂ} (hK : ContDiffOn ℝ 1 K quadrant)
    {u : ℝ} (hu : 0 < u) : ContDiffOn ℝ 1 (fun v => K (u, v)) (Ioi 0) :=
  hK.comp ((contDiff_const.prodMk contDiff_id).contDiffOn) (fun _ hv => ⟨hu, hv⟩)

private theorem compact_kernel_parts {K : ℝ × ℝ → ℂ} {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hf₀ : tsupport f ⊆ Ioo 0 1) (hg₀ : tsupport g ⊆ Ioo 0 1)
    (hK : ContDiffOn ℝ 2 K quadrant) :
    (∫ p : ℝ × ℝ, deriv f p.1 * K p * deriv g p.2 ∂(unitMeasure.prod unitMeasure)) =
      ∫ p : ℝ × ℝ, f p.1 * partialRight (partialLeft K) p * g p.2
        ∂(unitMeasure.prod unitMeasure) := by
  have hf' := tsupport_deriv_subset.trans hf₀
  have hg' := tsupport_deriv_subset.trans hg₀
  have hK₁ : ContDiffOn ℝ 1 (partialLeft K) quadrant :=
    partialLeft_smooth hK (by norm_num) (by norm_num)
  have hK₂ := partialRight_continuous hK₁
  let μ : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume
  let A : ℝ × ℝ → ℂ := fun p => deriv f p.1 * K p * deriv g p.2
  let B : ℝ × ℝ → ℂ := fun p => f p.1 * partialLeft K p * deriv g p.2
  let C : ℝ × ℝ → ℂ := fun p => f p.1 * partialRight (partialLeft K) p * g p.2
  have hA : Integrable A μ := weighted_pair_integrable hK.continuousOn
    (hf.continuous_deriv le_rfl) (hg.continuous_deriv le_rfl) hf' hg'
  have hB : Integrable B μ := weighted_pair_integrable hK₁.continuousOn
    hf.continuous (hg.continuous_deriv le_rfl) hf₀ hg'
  have hC : Integrable C μ := weighted_pair_integrable hK₂ hf.continuous hg.continuous hf₀ hg₀
  rw [integral_weighted_pair_restrict K hf' hg',
    integral_weighted_pair_restrict (partialRight (partialLeft K)) hf₀ hg₀]
  change (∫ p, A p ∂μ) = ∫ p, C p ∂μ
  have hAB : (∫ p, A p ∂μ) = -(∫ p, B p ∂μ) := by
    rw [integral_prod_symm A hA, integral_prod_symm B hB, ← integral_neg]
    apply integral_congr_ae
    filter_upwards with v
    by_cases hv : 0 < v
    · simp only [A, B, integral_mul_const, ← neg_mul]
      rw [mul_deriv_integral hf hf₀ (sliceLeft_smooth (hK.of_le (by norm_num)) hv)]
      rfl
    · have hz : deriv g v = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => hv (hg' h).1
      simp [A, B, hz]
  have hBC : (∫ p, B p ∂μ) = -(∫ p, C p ∂μ) := by
    rw [integral_prod B hB, integral_prod C hC, ← integral_neg]
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : 0 < u
    · simp only [B, C, mul_assoc, integral_const_mul, ← mul_neg]
      simp_rw [mul_comm (partialLeft K (u, _)) (deriv g _),
        mul_comm (partialRight (partialLeft K) (u, _)) (g _)]
      rw [mul_deriv_integral hg hg₀ (sliceRight_smooth hK₁ hu)]
      rfl
    · have hz : f u = 0 :=
        image_eq_zero_of_notMem_tsupport fun h => hu (hf₀ h).1
      simp [B, C, hz]
  rw [hAB, hBC, neg_neg]

/-- Two integrations by parts and two logistic substitutions turn the derivative
pairing into the pairing against the mixed derivative of the affine kernel. -/
theorem integral_compact_pairing_eq_logistic {b : ℝ} (hb : 0 < b)
    {K : ℝ × ℝ → ℂ} {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hf₀ : tsupport f ⊆ Ioo 0 1) (hg₀ : tsupport g ⊆ Ioo 0 1)
    (hK : ContDiffOn ℝ 2 K (Ioi 0 ×ˢ Ioi 0)) :
    (∫ p : ℝ × ℝ, star (deriv f p.1) * K p * deriv g p.2
      ∂((volume.restrict (Ioo (0 : ℝ) 1)).prod (volume.restrict (Ioo (0 : ℝ) 1)))) =
      ∫ s : ℝ, ∫ t : ℝ, star (f (logistic b s)) *
        (((b * (logistic b s * (1 - logistic b s)) : ℝ) : ℂ) *
          ((b * (logistic b t * (1 - logistic b t)) : ℝ) : ℂ) *
          deriv (fun v => deriv (fun u => K (u, v)) (logistic b s)) (logistic b t)) *
        g (logistic b t) := by
  let fc : ℝ → ℂ := fun u => star (f u)
  have hfc : ContDiff ℝ 1 fc := Complex.conjCLE.toContinuousLinearMap.contDiff.comp hf
  have hfc₀ : tsupport fc ⊆ Ioo 0 1 := by
    have he : support fc = support f := by ext u; simp [fc, mem_support]
    change closure (support fc) ⊆ _
    rw [he]
    exact hf₀
  have hfd (u : ℝ) : deriv fc u = star (deriv f u) :=
    (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt u
      (hf.differentiable one_ne_zero u).hasDerivAt).deriv
  simp_rw [← hfd]
  change (∫ p : ℝ × ℝ, deriv fc p.1 * K p * deriv g p.2 ∂(unitMeasure.prod unitMeasure)) = _
  rw [compact_kernel_parts hfc hg hfc₀ hg₀ hK]
  let C : ℝ × ℝ → ℂ := fun p => fc p.1 * partialRight (partialLeft K) p * g p.2
  have hK₁ : ContDiffOn ℝ 1 (partialLeft K) quadrant :=
    partialLeft_smooth hK (by norm_num) (by norm_num)
  have hC : Integrable C (unitMeasure.prod unitMeasure) := by
    rw [unitMeasure, Measure.prod_restrict]
    exact (weighted_pair_integrable (partialRight_continuous hK₁)
      hfc.continuous hg.continuous hfc₀ hg₀).integrableOn
  change (∫ p, C p ∂(unitMeasure.prod unitMeasure)) = _
  rw [integral_prod C hC]
  unfold unitMeasure
  rw [integral_logistic_substitution hb]
  apply integral_congr_ae
  filter_upwards with s
  rw [integral_logistic_substitution hb, Complex.real_smul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  rw [Complex.real_smul]
  dsimp only [C, fc, partialRight, partialLeft]
  ring

end Omega
