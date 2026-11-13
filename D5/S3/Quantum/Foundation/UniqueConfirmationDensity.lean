/- GID: D5/S3/Quantum/Foundation/UniqueConfirmationDensity
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/UniqueConfirmationDensity
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Joint original state-effect compactness controls limits of exclusion labels. -/

import D5.S3.Quantum.Foundation.SingleLabelNormalBody
import D5.S3.Quantum.Foundation.MixedExclusionGeometry
import D5.S3.Quantum.Foundation.OriginalWidthContact
import Mathlib.Topology.Sequences

/-! All state and effect carriers below are the original full cone carriers.
No closedness of the pure-state set or weak Pair premise is used. -/

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace

namespace D5.S3.Quantum.Foundation.UniqueConfirmationDensity

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces
open WholePairBallConfirmation ContinuousFrameSum SingleLabelNormalBody

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- Uniqueness concerns the entire original effect fiber, not the exclusion-label fiber. -/
def UniqueConfirmer (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (p : pure C u) : Prop :=
  ∃ e : V →ₗ[ℝ] ℝ, confirms C u p e ∧
    (∀ z ∈ exclusion C u p, e z = 0) ∧
    ∀ f : V →ₗ[ℝ] ℝ, confirms C u p f →
      (∀ z ∈ exclusion C u p, f z = 0) → f = e

private theorem affine_zero_inside_ball {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E →ᵃ[ℝ] ℝ) (hpos : ∀ z, ‖z‖ ≤ 1 → 0 ≤ f z)
    {z : E} (hz : ‖z‖ < 1) (hfz : f z = 0) : ∀ w, f w = 0 := by
  obtain ⟨v, hv⟩ := affine_riesz f
  have hb := affine_nonneg_bound (fun w hw => by rw [← hv]; exact hpos w hw)
  have h0 : 0 ≤ f 0 := hpos 0 (by simp)
  have hi : -⟪v, z⟫ ≤ ‖v‖ * ‖z‖ := by
    have h := real_inner_le_norm (-v) z
    simpa only [inner_neg_left, norm_neg] using h
  have hvan : f 0 = 0 := by
    have he := hv z
    nlinarith [norm_nonneg v, norm_nonneg z, mul_le_mul_of_nonneg_right hb (norm_nonneg z)]
  have hv0 : v = 0 := norm_le_zero_iff.mp (hvan ▸ hb)
  intro w
  rw [hv, hv0, hvan, inner_zero_left, add_zero]

private theorem zero_on_exclusion_of_zero_interior
    (hB : exclusionBalls C u) (p : pure C u) (f : V →ₗ[ℝ] ℝ)
    (hpos : ∀ z ∈ C, 0 ≤ f z) {x : V}
    (hx : x ∈ intrinsicInterior ℝ (exclusion C u p)) (hfx : f x = 0) :
    ∀ z ∈ exclusion C u p, f z = 0 := by
  obtain ⟨b⟩ := hB p
  rw [MixedExclusionGeometry.chart_intrinsic p b] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hf := affine_zero_inside_ball (f.toAffineMap.comp b.param)
    (fun w hw => hpos _ (b.whole ▸ mem_image_of_mem b.param (by simpa using hw)).1.1)
    (by simpa using hz) hfx
  intro y hy
  obtain ⟨w, _, rfl⟩ := b.whole.symm ▸ hy
  exact hf w

/-- Incidence points converging to the relative interior of D(p) force the full
original pure-label sequence to converge to p, even when P is not closed. -/
theorem original_label_tendsto
    (hc : IsClosed (C : Set V)) (hs : ∀ z ∈ C, z ≠ 0 → 0 < u z)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hinj : Function.Injective (fun p : pure C u => exclusion C u p))
    (p : pure C u) {x : V} (hx : x ∈ intrinsicInterior ℝ (exclusion C u p))
    (pn : ℕ → pure C u) (xn : ℕ → V)
    (hxn : ∀ n, xn n ∈ exclusion C u (pn n))
    (hlim : Tendsto xn atTop (𝓝 x)) :
    Tendsto (fun n => (pn n : V)) atTop (𝓝 (p : V)) := by
  classical
  have hall := (exclusion_ball_faces hc hs hg hB).1
  choose e he hz using fun n => (hall (pn n)).2.2.2.2.2.2
  let ec (n : ℕ) : V →L[ℝ] ℝ := (e n).toContinuousLinearMap
  let se (n : ℕ) : V × (V →L[ℝ] ℝ) := (pn n, ec n)
  have hmem (n : ℕ) : se n ∈ base C u ×ˢ effects C u := ⟨pure_mem (pn n), (he n).1⟩
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨⟨s, f⟩, ⟨hsK, hf⟩, ms, hms, hsf⟩ :=
    ((base_compact hc hs).prod (effects_compact hs hg)).tendsto_subseq (fun n => hmem (ns n))
  have hslim : Tendsto (fun n => (pn (ns (ms n)) : V)) atTop (𝓝 s) := hsf.fst
  have hflim : Tendsto (fun n => ec (ns (ms n))) atTop (𝓝 f) := hsf.snd
  have hxlim : Tendsto (fun n => xn (ns (ms n))) atTop (𝓝 x) :=
    hlim.comp (hns.comp hms.tendsto_atTop)
  have heval : Continuous (fun z : (V →L[ℝ] ℝ) × V => z.1 z.2) :=
    continuous_fst.clm_apply continuous_snd
  have hfs : f s = 1 := by
    have ht := (heval.tendsto (f, s)).comp (hflim.prodMk_nhds hslim)
    have hh : (fun n => ec (ns (ms n)) (pn (ns (ms n)))) = fun _ : ℕ => (1 : ℝ) := by
      funext n
      exact (he _).2
    simpa only [Function.comp_def, hh] using tendsto_nhds_unique ht tendsto_const_nhds
  have hfx : f x = 0 := by
    have ht := (heval.tendsto (f, x)).comp (hflim.prodMk_nhds hxlim)
    have hh : (fun n => ec (ns (ms n)) (xn (ns (ms n)))) = fun _ : ℕ => (0 : ℝ) := by
      funext n
      exact (show xn (ns (ms n)) ∈ {z | z ∈ base C u ∧ e (ns (ms n)) z = 0}
        from hz _ ▸ hxn _).2
    simpa only [Function.comp_def, hh] using tendsto_nhds_unique ht tendsto_const_nhds
  have hzero := zero_on_exclusion_of_zero_interior hB p f.toLinearMap
    (fun z hz => (hf z hz).1) hx hfx
  have htop := OriginalWidthContact.top_exposed hf
  have hsingle := OriginalWidthContact.top_subsingleton_of_zero_exclusion
    hc hs hg hB hinj hf p hzero
  have hface : {z ∈ base C u | f z = 1} = {s} :=
    hsingle.eq_singleton_of_mem ⟨hsK, hfs⟩
  have hsP : s ∈ pure C u := isExtreme_singleton.mp (hface ▸ htop.isExtreme)
  let q : pure C u := ⟨s, hsP⟩
  have hsub : exclusion C u p ⊆ exclusion C u q := by
    intro z hzD
    exact ⟨hzD.1, f.toLinearMap, ⟨hf, hfs⟩, hzero z hzD⟩
  obtain ⟨bq⟩ := hB q
  have heq := chart_face_eq bq (hall p).2.2.1
    ((hall p).2.2.2.2.1.mono (hall q).2.2.2.2.1.subset hsub) (hall p).1
  have hsp : s = (p : V) := congrArg Subtype.val (hinj heq).symm
  exact ⟨ms, hsp ▸ hslim⟩

end D5.S3.Quantum.Foundation.UniqueConfirmationDensity
