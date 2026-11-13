/- GID: D5/S3/Quantum/Foundation/ReciprocalPureCompactness
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ReciprocalPureCompactness
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Pure-pair reciprocity closes the entire original extreme locus. -/

import D5.S3.Quantum.Foundation.ReciprocalEndpointExposure
import D5.S3.Quantum.Foundation.ExclusionWidthCompactness
import D5.S3.Quantum.Foundation.OriginalWidthContact
import Mathlib.Topology.Sequences

noncomputable section
open Set Filter Topology
namespace D5.S3.Quantum.Foundation.ReciprocalPureCompactness
open CircuitBalancedConfirmation ContinuousFrameSum ReciprocalEndpointExposure
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Pure-endpoint reciprocity closes the entire original extreme locus.
No finite pure decomposition or exclusion-ball hypothesis is used. -/
theorem reciprocal_pure_compact {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p) :
    IsCompact (pure C u) := by
  classical
  have hK := base_compact hc hs
  have hclosed : IsClosed (pure C u) := by
    apply isSeqClosed_iff_isClosed.mp
    intro an x han hax
    have hx : x ∈ base C u := hK.isClosed.mem_of_tendsto hax
      (Eventually.of_forall fun n => pure_mem ⟨an n, han n⟩)
    let F := ExclusionWidthCompactness.confirmingEffects C u x
    have hunit : u.toContinuousLinearMap ∈ F := by
      refine ⟨?_, hx.2⟩
      intro y hy
      refine ⟨?_, le_rfl⟩
      by_cases hz : y = 0
      · simp [hz]
      · exact (hs y hy hz).le
    let : Nonempty F := ⟨⟨u.toContinuousLinearMap, hunit⟩⟩
    let H : Set V := ⋂ f : F, {y ∈ base C u | (f : V →L[ℝ] ℝ) y = 1}
    have hxH : x ∈ H := by
      simp only [H, mem_iInter, mem_ofPred_eq]
      exact fun f => ⟨hx, f.property.2⟩
    have hHface : IsExtreme ℝ (base C u) H := isExtreme_iInter fun f =>
      (OriginalWidthContact.top_exposed f.property.1).isExtreme
    have hHclosed : IsClosed H := isClosed_iInter fun f =>
      hK.isClosed.inter (isClosed_eq (f : V →L[ℝ] ℝ).continuous continuous_const)
    have hHcompact : IsCompact H := hK.of_isClosed_subset hHclosed hHface.subset
    obtain ⟨r, hr⟩ := hHcompact.extremePoints_nonempty ⟨x, hxH⟩
    have hrP : r ∈ pure C u := hHface.extremePoints_subset_extremePoints hr
    let q : pure C u := ⟨r, hrP⟩
    obtain ⟨h, hh, _, hf, hsingle, _⟩ := reciprocal_endpoint_exposure hc hs hg q
      (fun b => (hPR q b).le)
    let f := (u - h).toContinuousLinearMap
    choose en hen heq using fun n =>
      ExclusionWidthCompactness.comparison_attained hs hg ⟨an n, han n⟩ r
    obtain ⟨e, he, φ, hφ, helim⟩ := (effects_compact hs hg).tendsto_subseq
      (fun n => (hen n).1)
    have hseq := hax.comp hφ.tendsto_atTop
    have hev : Continuous (fun z : (V →L[ℝ] ℝ) × V => z.1 z.2) := by fun_prop
    have hex : e x = 1 := tendsto_nhds_unique
      ((hev.tendsto (e,x)).comp (helim.prodMk_nhds hseq))
      (by
        change Tendsto (fun n => en (φ n) (an (φ n))) atTop (𝓝 1)
        have he1 : (fun n => en (φ n) (an (φ n))) = fun _ : ℕ => (1 : ℝ) :=
          funext fun n => (hen (φ n)).2
        rw [he1]
        exact tendsto_const_nhds)
    have her : e r = 1 := (mem_iInter.mp hr.1 ⟨e, he, hex⟩).2
    have hle (n : ℕ) : en n r ≤ f (an n) := by
      rw [← heq n, hPR ⟨an n, han n⟩ q]
      change sInf {v | ∃ g : V →ₗ[ℝ] ℝ, confirms C u q g ∧ g (an n) = v} ≤ f (an n)
      exact csInf_le ⟨0, by
        rintro v ⟨g, hg', rfl⟩
        exact (hg'.1 _ (pure_mem ⟨an n, han n⟩).1).1⟩ ⟨u-h, hf, rfl⟩
    have hlimr : Tendsto (fun n => en (φ n) r) atTop (𝓝 (e r)) :=
      (show Continuous (fun g : V →L[ℝ] ℝ => g r) by fun_prop).tendsto e |>.comp helim
    have hfx : 1 ≤ f x := by
      rw [← her]
      exact le_of_tendsto_of_tendsto hlimr (f.continuous.tendsto x |>.comp hseq)
        (Eventually.of_forall fun n => hle (φ n))
    have hfx1 : (u-h) x = 1 := le_antisymm
      (by simpa only [hx.2] using (hf.1 x hx.1).2) hfx
    have hxr : x = r := by
      have hm : x ∈ ({(q : V)} : Set V) := hsingle ▸ ⟨hx, hfx1⟩
      exact hm
    exact hxr ▸ hrP
  exact hK.of_isClosed_subset hclosed (fun x hx => hx.1)


end D5.S3.Quantum.Foundation.ReciprocalPureCompactness
