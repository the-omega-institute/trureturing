/- GID: D5/S3/Quantum/Foundation/OriginalStateCover
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalStateCover
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Original states lie between a pure point and its entire exclusion ball. -/

import D5.S3.Quantum.Foundation.OriginalWidthContact
import D5.S3.Quantum.Foundation.MixedExclusionGeometry
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Convex.Intrinsic

/-! Affine diameters and complete exclusion-ball decompositions on the original carriers. -/

noncomputable section
open Set Filter Topology

namespace D5.S3.Quantum.Foundation.OriginalStateCover

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces

private theorem support_positive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : Set E} (hzero : (0 : E) ∈ interior L) (f : E →L[ℝ] ℝ) (hf : f ≠ 0)
    {v : E} (hmax : ∀ w ∈ L, f w ≤ f v) : 0 < f v := by
  by_contra! hn
  have hle (w : E) : f w ≤ 0 := by
    have ht : ∀ᶠ t : ℝ in 𝓝 0, t • w ∈ L :=
      (continuous_id.smul continuous_const).continuousAt.preimage_mem_nhds
        (by simpa using mem_interior_iff_mem_nhds.mp hzero)
    obtain ⟨t, htpos, htw⟩ := ht.exists_gt
    have hh := (hmax _ htw).trans hn
    rw [map_smul, smul_eq_mul] at hh
    exact nonpos_of_mul_nonpos_right hh htpos
  apply hf
  ext w
  have hh := hle (-w)
  simp only [map_neg] at hh
  exact le_antisymm (hle w) (by linarith)

/-- A maximal reflected copy of a compact body touches a supporting hyperplane;
the paired point minimizes the same functional on the whole body. -/
theorem centered_affine_diameter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : Set E} (hcompact : IsCompact L) (hconvex : Convex ℝ L)
    (hzero : (0 : E) ∈ interior L) (hnonzero : ∃ z ∈ L, z ≠ 0) :
    ∃ (t : ℝ) (z : E) (f : E →L[ℝ] ℝ),
      0 < t ∧ z ∈ L ∧ (-t) • z ∈ L ∧
      0 < f ((-t) • z) ∧ f z < 0 ∧
      (∀ w ∈ L, f z ≤ f w) ∧ (∀ w ∈ L, f w ≤ f ((-t) • z)) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hzero)
  obtain ⟨R, hR, hbound⟩ := hcompact.isBounded.exists_pos_norm_le
  let T : Set ℝ := {t | 0 ≤ t ∧ ∀ z ∈ L, (-t) • z ∈ L}
  have hsmall : r / (2 * R) ∈ T := by
    refine ⟨(div_pos hr (by positivity)).le, ?_⟩
    intro z hz
    apply hball
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_neg, abs_of_pos (div_pos hr (by positivity))]
    calc
      r / (2 * R) * ‖z‖ ≤ r / (2 * R) * R :=
        mul_le_mul_of_nonneg_left (hbound z hz) (by positivity)
      _ = r / 2 := by field_simp; ring
      _ < r := by linarith
  have hclosed : IsClosed T := by
    apply isClosed_Ici.inter
    apply isClosed_setOf_forall
    intro z
    apply isClosed_setOf_forall
    intro _
    exact hcompact.isClosed.preimage (continuous_neg.smul continuous_const)
  obtain ⟨w, hw, hw0⟩ := hnonzero
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hTbound : T ⊆ Icc 0 (R / ‖w‖) := by
    intro t ht
    refine ⟨ht.1, (le_div_iff₀ hnw).mpr ?_⟩
    have hh := hbound _ (ht.2 w hw)
    simpa only [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg ht.1] using hh
  have hTcompact : IsCompact T := isCompact_Icc.of_isClosed_subset hclosed hTbound
  obtain ⟨t, ht, hmax⟩ := hTcompact.exists_isMaxOn ⟨_, hsmall⟩ continuous_id.continuousOn
  have htpos : 0 < t := (div_pos hr (by positivity)).trans_le (hmax hsmall)
  have hcontact : ∃ z ∈ L, (-t) • z ∉ interior L := by
    by_contra! hall
    have hevent : ∀ᶠ s : ℝ in 𝓝 t, ∀ z ∈ L, (-s) • z ∈ interior L := by
      apply hcompact.eventually_forall_of_forall_eventually
      intro z hz
      exact ((continuous_neg.comp continuous_fst).smul continuous_snd).continuousAt
        .preimage_mem_nhds (isOpen_interior.mem_nhds (hall z hz))
    obtain ⟨s, hst, hs⟩ := hevent.exists_gt
    have hsT : s ∈ T := ⟨htpos.le.trans hst.le,
      fun z hz => interior_subset (hs z hz)⟩
    exact (not_lt_of_ge (hmax hsT)) hst
  obtain ⟨z, hz, hznot⟩ := hcontact
  obtain ⟨f, hf, hsupport⟩ := geometric_hahn_banach_of_nonempty_interior_point
    hconvex hznot ⟨0, hzero⟩
  have hfpos := support_positive hzero f hf hsupport
  have hfz : f z < 0 := by
    simpa only [map_smul, smul_eq_mul] using hfpos
      |> fun hh => by nlinarith
  refine ⟨t, z, f, htpos, hz, ht.2 z hz, hfpos, hfz, ?_, hsupport⟩
  intro a ha
  have hh := hsupport _ (ht.2 a ha)
  simp only [map_smul, smul_eq_mul] at hh
  nlinarith

end D5.S3.Quantum.Foundation.OriginalStateCover
