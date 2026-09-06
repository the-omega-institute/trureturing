/- GID: D5/S3/Observer/HilbertGeometry/HilbertPathFundamentalTheorem
   generality: G
   mirror-B: D5/B/S3/Observer/HilbertGeometry/HilbertPathFundamentalTheorem
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hilbert AC paths have actual derivatives and pointwise Bochner reconstruction. -/

import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
Absolute continuity gives a separable closed span of the interval image even
in a nonseparable ambient Hilbert space. On a countable Hilbert basis, scalar
derivatives satisfy finite Bessel bounds dominated by signed variation.
Their square-summable orthogonal series is a measurable L1 velocity. Scalar
FTC and coordinate separation reconstruct every point; differentiating its
Bochner primitive then supplies actual strong derivatives.

Consumer: absolutely_continuous_subspace_action_minimum_unique (qdo-v1,
theorem 36.26). This module supplies the analytic prerequisite only. The
extended quadratic action, lower bound, affine attainment and pointwise
uniqueness remain downstream. AC alone does not imply finite quadratic energy.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

namespace D5.S3.Observer.HilbertGeometry.HilbertPathFundamentalTheorem

private theorem ac_lipschitz_comp {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : ℝ → X} {g : X → Y} {a b : ℝ} {K : NNReal}
    (hf : AbsolutelyContinuousOnInterval f a b) (hg : LipschitzWith K g) :
    AbsolutelyContinuousOnInterval (g ∘ f) a b := by
  have hlim : Tendsto (fun E => (K : ℝ) *
      ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2))
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (𝓝 ((K : ℝ) * 0)) :=
    tendsto_const_nhds.mul hf
  apply squeeze_zero (fun E => ?_) (fun E => ?_) (by simpa only [mul_zero] using hlim)
  · exact Finset.sum_nonneg (fun _ _ => dist_nonneg)
  · simp only [Function.comp_apply, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hg.dist_le_mul _ _)

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem finite_coordinate_derivative_bound {f : ℝ → H} {g : ℝ → ℝ}
    {v : ι → H} (hv : Orthonormal ℝ v) {t : ℝ}
    (hc : ∀ i, DifferentiableAt ℝ (fun x => ⟪v i, f x⟫_ℝ) t)
    (hg : DifferentiableAt ℝ g t)
    (hfg : ∀ᶠ y in 𝓝 t, ‖f y - f t‖ ≤ ‖g y - g t‖) (s : Finset ι) :
    ∑ i ∈ s, ‖deriv (fun x => ⟪v i, f x⟫_ℝ) t‖ ^ 2 ≤ ‖deriv g t‖ ^ 2 := by
  have hlim := tendsto_finsetSum s (fun i _ => (hc i).hasDerivAt.tendsto_slope.norm.pow 2)
  apply le_of_tendsto_of_tendsto hlim (hg.hasDerivAt.tendsto_slope.norm.pow 2)
  filter_upwards [hfg.filter_mono nhdsWithin_le_nhds] with y hy
  have hB := hv.sum_inner_products_le (s := s) (slope f t y)
  have hN : ‖slope f t y‖ ≤ ‖slope g t y‖ := by
    simpa only [slope, vsub_eq_sub, norm_smul] using
      mul_le_mul_of_nonneg_left hy (norm_nonneg ((y - t)⁻¹))
  have hcoord : ∀ i, ⟪v i, slope f t y⟫_ℝ = slope (fun x => ⟪v i, f x⟫_ℝ) t y := by
    intro i
    simp only [slope, vsub_eq_sub, inner_smul_right, inner_sub_right, smul_eq_mul]
  simp only [hcoord] at hB
  exact hB.trans (pow_le_pow_left₀ (norm_nonneg _) hN 2)

private theorem assemble_velocity [CompleteSpace H] (b : HilbertBasis ι ℝ H)
    {d : ι → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ s : Finset ι, ∑ i ∈ s, ‖d i‖ ^ 2 ≤ C ^ 2) :
    ∃ v : H, (∀ i, ⟪b i, v⟫_ℝ = d i) ∧ ‖v‖ ≤ C ∧
      HasSum (fun i => d i • b i) v := by
  have hmem : Memℓp d 2 := memℓp_gen' (C := C ^ 2) (by simpa using hd)
  let z : lp (fun _ : ι => ℝ) 2 := ⟨d, hmem⟩
  refine ⟨b.repr.symm z, ?_, ?_, b.hasSum_repr_symm z⟩
  · intro i
    rw [← b.repr_apply_apply, b.repr.apply_symm_apply]
  · rw [b.repr.symm.norm_map]
    exact lp.norm_le_of_forall_sum_le (by norm_num) hC (by simpa [z] using hd)

-- Same variation identities as the immutable integrability owner's private helper.
omit [InnerProductSpace ℝ H] in
private theorem increment_le_variation {f : ℝ → H} {a b u v : ℝ}
    (hf : BoundedVariationOn f (uIcc a b))
    (hu : u ∈ uIcc a b) (hv : v ∈ uIcc a b) :
    ‖f v - f u‖ ≤
      ‖variationOnFromTo f (uIcc a b) a v - variationOnFromTo f (uIcc a b) a u‖ := by
  wlog huv : u ≤ v generalizing u v
  · simpa only [norm_sub_rev] using this hv hu (le_of_not_ge huv)
  rw [variationOnFromTo.sub_right hf.locallyBoundedVariationOn (by simp) hv hu,
    Real.norm_of_nonneg (variationOnFromTo.nonneg_of_le _ _ huv),
    variationOnFromTo.eq_of_le _ _ huv, ← dist_eq_norm]
  exact (hf.mono inter_subset_left).dist_le ⟨hv, huv, le_rfl⟩ ⟨hu, le_rfl, huv⟩

private noncomputable def coordinateVelocity (b : HilbertBasis ι ℝ H) (f : ℝ → H) (t : ℝ) : H :=
  ∑' i, deriv (fun x => ⟪b i, f x⟫_ℝ) t • b i

private theorem coordinateVelocity_ae [CompleteSpace H] [Countable ι]
    (basis : HilbertBasis ι ℝ H) {f : ℝ → H} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    ∀ᵐ t : ℝ, t ∈ uIcc a b →
      (∀ i, ⟪basis i, coordinateVelocity basis f t⟫_ℝ =
        deriv (fun x => ⟪basis i, f x⟫_ℝ) t) ∧
      ‖coordinateVelocity basis f t‖ ≤ ‖deriv (variationOnFromTo f (uIcc a b) a) t‖ := by
  let V := variationOnFromTo f (uIcc a b) a
  have hV : MonotoneOn V (uIcc a b) :=
    variationOnFromTo.monotoneOn hf.boundedVariationOn.locallyBoundedVariationOn (by simp)
  have hc : ∀ i, AbsolutelyContinuousOnInterval (fun x => ⟪basis i, f x⟫_ℝ) a b :=
    fun i => ac_lipschitz_comp hf (innerSL ℝ (basis i)).lipschitz
  filter_upwards [ae_all_iff.mpr (fun i => (hc i).ae_differentiableAt),
    hV.ae_differentiableWithinAt_of_mem,
    show ∀ᵐ t : ℝ, t ≠ min a b by simp [ae_iff, measure_singleton],
    show ∀ᵐ t : ℝ, t ≠ max a b by simp [ae_iff, measure_singleton]] with t ht hvt hta htb hmem
  have htnhds : uIcc a b ∈ 𝓝 t :=
    Icc_mem_nhds (lt_of_le_of_ne hmem.1 hta.symm) (lt_of_le_of_ne hmem.2 htb)
  have hbound := finite_coordinate_derivative_bound basis.orthonormal
    (fun i => ht i hmem) ((hvt hmem).differentiableAt htnhds)
    (show ∀ᶠ y in 𝓝 t, ‖f y - f t‖ ≤ ‖V y - V t‖ from
      Filter.Eventually.mono htnhds (fun y hy =>
        increment_le_variation hf.boundedVariationOn hmem hy))
  obtain ⟨v, hv, hn, hs⟩ := assemble_velocity basis (norm_nonneg (deriv V t)) hbound
  have heq : coordinateVelocity basis f t = v := hs.tsum_eq
  exact heq ▸ ⟨hv, hn⟩

private theorem coordinateVelocity_integrable [CompleteSpace H]
    [SecondCountableTopology H] [Countable ι]
    (basis : HilbertBasis ι ℝ H) {f : ℝ → H} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    IntervalIntegrable (coordinateVelocity basis f) volume a b := by
  borelize H
  have hm : Measurable (coordinateVelocity basis f) :=
    Measurable.tsum (fun i => (measurable_deriv _).smul measurable_const)
  have hV : MonotoneOn (variationOnFromTo f (uIcc a b) a) (uIcc a b) :=
    variationOnFromTo.monotoneOn hf.boundedVariationOn.locallyBoundedVariationOn (by simp)
  apply hV.intervalIntegrable_deriv.mono_fun hm.aestronglyMeasurable
  rw [EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [coordinateVelocity_ae basis hf] with t ht hmem
  exact (ht (uIoc_subset_uIcc hmem)).2

private theorem integral_coordinateVelocity [CompleteSpace H]
    [SecondCountableTopology H] [Countable ι]
    (basis : HilbertBasis ι ℝ H) {f : ℝ → H} {a b t : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (ht : t ∈ uIcc a b) :
    ∫ x in a..t, coordinateVelocity basis f x = f t - f a := by
  have hsub : uIcc a t ⊆ uIcc a b := uIcc_subset_uIcc (left_mem_uIcc) ht
  have hint := (coordinateVelocity_integrable basis hf).mono_set hsub
  apply basis.repr.injective
  apply lp.ext
  funext i
  simp only [HilbertBasis.repr_apply_apply]
  change (innerSL ℝ (basis i)) (∫ x in a..t, coordinateVelocity basis f x) = _
  rw [← (innerSL ℝ (basis i)).intervalIntegral_comp_comm hint]
  have heq : ∫ x in a..t, (innerSL ℝ (basis i)) (coordinateVelocity basis f x) =
      ∫ x in a..t, deriv (fun y => ⟪basis i, f y⟫_ℝ) x := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [coordinateVelocity_ae basis hf] with x hx hmem
    exact (hx (hsub (uIoc_subset_uIcc hmem))).1 i
  rw [heq]
  have hci : AbsolutelyContinuousOnInterval (fun y => ⟪basis i, f y⟫_ℝ) a t :=
    ac_lipschitz_comp (hf.mono hsub) (innerSL ℝ (basis i)).lipschitz
  simpa only [inner_sub_right] using hci.integral_deriv_eq_sub

/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Minimal source port from AIQ-Kitware/aiq-dkps-formalization,
ef157afc71c3866cb608111ef61462516330ef56,
ForTauCeti/Analysis/InnerProductSpace/SeparableOrthonormal.lean.
Modified here: namespace and visibility; only the four countability results.
The complete upstream license and third-party notice are retained below.
Upstream pins Lean v4.34.0-rc1 and Mathlib 72f9c607bb3a3e3a9fbe2a0513c7c79f998b9944;
this repository pins v4.33.0, so a dependency cannot share its toolchain.
Retirement: replace this private port by direct imports when this repository's
pinned Mathlib contains equivalent countable orthonormal-basis declarations.
-/
namespace CountableBasisPort

private theorem countable_of_pairwise_dist_le {M : Type*} [MetricSpace M]
    [TopologicalSpace.SeparableSpace M] {s : Set M} {δ : ℝ} (hδ : 0 < δ)
    (h : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → δ ≤ dist x y) : s.Countable := by
  classical
  obtain ⟨t, htc, htd⟩ := TopologicalSpace.exists_countable_dense M
  have hchoice : ∀ x : M, ∃ y, y ∈ t ∧ dist x y < δ / 2 := fun x =>
    Metric.mem_closure_iff.mp (htd x) (δ / 2) (by positivity)
  choose g hgt hgd using hchoice
  refine Set.MapsTo.countable_of_injOn (f := g) (fun x _ => hgt x) ?_ htc
  intro x hx y hy hxy
  by_contra hne
  have hlt : dist x y < δ := by
    calc dist x y ≤ dist x (g x) + dist (g x) y := dist_triangle _ _ _
      _ = dist x (g x) + dist y (g y) := by rw [hxy, dist_comm (g y) y]
      _ < δ / 2 + δ / 2 := add_lt_add (hgd x) (hgd y)
      _ = δ := by ring
  exact absurd (h x hx y hy hne) (not_le.mpr hlt)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

private theorem dist_eq_sqrt_two_of_orthonormal {s : Set E}
    (h : Orthonormal 𝕜 ((↑) : s → E)) {x y : E} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) :
    dist x y = Real.sqrt 2 := by
  have hne : (⟨x, hx⟩ : s) ≠ ⟨y, hy⟩ := by
    simpa [Subtype.ext_iff] using hxy
  have hinner : (inner 𝕜 x y : 𝕜) = 0 := h.2 hne
  have hnx : ‖x‖ = 1 := h.1 ⟨x, hx⟩
  have hny : ‖y‖ = 1 := h.1 ⟨y, hy⟩
  have hsq : ‖x - y‖ ^ 2 = 2 := by
    rw [@norm_sub_sq 𝕜, hinner, hnx, hny]
    norm_num
  have hnn : 0 ≤ ‖x - y‖ := norm_nonneg _
  rw [dist_eq_norm]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2, hsq, hnn]

private theorem countable_of_orthonormal
    [TopologicalSpace.SeparableSpace E] {s : Set E}
    (h : Orthonormal 𝕜 ((↑) : s → E)) : s.Countable := by
  refine countable_of_pairwise_dist_le (δ := 1) one_pos ?_
  intro x hx y hy hxy
  rw [dist_eq_sqrt_two_of_orthonormal h hx hy hxy]
  nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]

private theorem exists_countable_hilbertBasis [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] :
    ∃ (w : Set E) (_b : HilbertBasis w 𝕜 E), w.Countable := by
  obtain ⟨w, b, hb⟩ := exists_hilbertBasis 𝕜 E
  refine ⟨w, b, countable_of_orthonormal (𝕜 := 𝕜) ?_⟩
  have := b.orthonormal
  rwa [hb] at this

end CountableBasisPort

private theorem exists_integrable_velocity [CompleteSpace H]
    {f : ℝ → H} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    ∃ v : ℝ → H, IntervalIntegrable v volume a b ∧
      ∀ t ∈ uIcc a b, ∫ x in a..t, v x = f t - f a := by
  let S : Submodule ℝ H := (Submodule.span ℝ (f '' uIcc a b)).topologicalClosure
  have hsep : TopologicalSpace.IsSeparable (S : Set H) :=
    (hf.continuousOn.isSeparable_image
      (TopologicalSpace.IsSeparable.of_separableSpace _)).span.closure
  let : TopologicalSpace.SeparableSpace S := hsep.separableSpace
  have hmem : ∀ t ∈ uIcc a b, f t ∈ S := fun t ht =>
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨t, ht, rfl⟩)
  let g : ℝ → S := S.orthogonalProjectionOnto ∘ f
  have hg : AbsolutelyContinuousOnInterval g a b :=
    ac_lipschitz_comp hf S.orthogonalProjectionOnto.lipschitz
  obtain ⟨w, basis, hw⟩ := CountableBasisPort.exists_countable_hilbertBasis (𝕜 := ℝ) (E := S)
  let : Countable w := hw.to_subtype
  let v := coordinateVelocity basis g
  have hv : IntervalIntegrable v volume a b := coordinateVelocity_integrable basis hg
  refine ⟨fun t => S.subtypeL (v t), ?_, ?_⟩
  · exact ⟨S.subtypeL.integrable_comp hv.1, S.subtypeL.integrable_comp hv.2⟩
  · intro t ht
    rw [S.subtypeL.intervalIntegral_comp_comm (hv.mono_set (uIcc_subset_uIcc left_mem_uIcc ht))]
    rw [show ∫ x in a..t, v x = g t - g a from integral_coordinateVelocity basis hg ht]
    simp only [map_sub]
    change S.starProjection (f t) - S.starProjection (f a) = f t - f a
    rw [Submodule.starProjection_eq_self_iff.mpr (hmem t ht),
      Submodule.starProjection_eq_self_iff.mpr (hmem a left_mem_uIcc)]

private theorem exists_integrable_velocity_hasDerivAt [CompleteSpace H]
    {f : ℝ → H} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    ∃ v : ℝ → H, IntervalIntegrable v volume a b ∧
      (∀ t ∈ uIcc a b, ∫ x in a..t, v x = f t - f a) ∧
      ∀ᵐ t : ℝ, t ∈ uIcc a b → HasDerivAt f (v t) t := by
  obtain ⟨v, hv, hpoint⟩ := exists_integrable_velocity hf
  refine ⟨v, hv, hpoint, ?_⟩
  filter_upwards [hv.ae_hasDerivAt_integral,
    show ∀ᵐ t : ℝ, t ≠ min a b by simp [ae_iff, measure_singleton],
    show ∀ᵐ t : ℝ, t ≠ max a b by simp [ae_iff, measure_singleton]] with t ht hta htb hmem
  have htnhds : uIcc a b ∈ 𝓝 t :=
    Icc_mem_nhds (lt_of_le_of_ne hmem.1 hta.symm) (lt_of_le_of_ne hmem.2 htb)
  apply ((ht hmem a left_mem_uIcc).add_const (f a)).congr_of_eventuallyEq
  filter_upwards [htnhds] with x hx
  simp only [hpoint x hx, sub_add_cancel]

/-- Every absolutely continuous Hilbert path has its actual totalized derivative
almost everywhere on the interval, with no ambient separability assumption. -/
theorem absolutely_continuous_interval_ae_hasDerivAt [CompleteSpace H]
    {f : ℝ → H} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    ∀ᵐ t : ℝ, t ∈ uIcc a b → HasDerivAt f (deriv f t) t := by
  obtain ⟨v, _, _, hder⟩ := exists_integrable_velocity_hasDerivAt hf
  filter_upwards [hder] with t ht hmem
  exact (ht hmem).deriv ▸ ht hmem

/-- The Bochner integral of the derivative reconstructs every point of an
absolutely continuous Hilbert path, including both interval endpoints. -/
theorem absolutely_continuous_interval_integral_deriv_eq_sub [CompleteSpace H]
    {f : ℝ → H} {a b t : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (ht : t ∈ uIcc a b) :
    ∫ x in a..t, deriv f x = f t - f a := by
  obtain ⟨v, _, hpoint, hder⟩ := exists_integrable_velocity_hasDerivAt hf
  rw [← hpoint t ht]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hder] with x hx hmem
  exact (hx (uIcc_subset_uIcc left_mem_uIcc ht (uIoc_subset_uIcc hmem))).deriv

end D5.S3.Observer.HilbertGeometry.HilbertPathFundamentalTheorem

/-
Upstream LICENSE, retained verbatim:

                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "{}"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright 2026 "Kitware Inc"

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

Upstream vendor/lean/NOTICE.md, retained verbatim for the notice trail.
No vendor/lean source reference is included in this minimal port:

# Third-party notices

The files under `vendor/lean/` are source references, not linked build dependencies.

## Lean community / Mathlib

Selected excerpts from Mathlib at the project-pinned revision.
Copyright is retained by the named upstream authors and Mathlib contributors.
Licensed under the Apache License, Version 2.0.
See `LICENSES/Apache-2.0.txt` and `manifest.toml`.

## Jacob Barr / jbarrcfl mathlib4 fork

Copyright (c) 2026 Jacob Barr.
Licensed under the Apache License, Version 2.0.
See `LICENSES/Apache-2.0.txt` and `manifest.toml`.

## Yuanhe Zhang, Jason D. Lee, Fanghui Liu / lean-stat-learning-theory

Copyright (c) 2026 Yuanhe Zhang.
Licensed under the Apache License, Version 2.0.
See `LICENSES/Apache-2.0.txt` and `manifest.toml`.

## Dronmong / drifting-identifiability

Copyright (c) 2026 Dronmong.
Licensed under the MIT License.
See `LICENSES/MIT.txt` and `manifest.toml`.
-/
