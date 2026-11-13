/- GID: D5/S3/Quantum/Foundation/OriginalPureCompactness
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalPureCompactness
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Pure reciprocity closes the entire original pure carrier under exclusion-ball geometry. -/

import D5.S3.Quantum.Foundation.OriginalComparisonTopology
import D5.S3.Quantum.Foundation.OriginalStateCover

/-! No injectivity of labels, weak pair axiom, or unit-width condition is assumed. -/

noncomputable section
open Set Filter Topology

namespace D5.S3.Quantum.Foundation.OriginalPureCompactness
open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces OriginalFacePolarity
open ExclusionWidthCompactness OriginalComparisonTopology ReciprocalEndpointExposure

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [Nontrivial V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

private theorem nonpure_decomposition
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    {x : V} (hx : x ∈ base C u) (hn : x ∉ pure C u) :
    ∃ (r : pure C u) (y : V) (λ : ℝ), y ∈ base C u ∧
      0 < λ ∧ λ < 1 ∧ x ≠ (r : V) ∧ x = λ • (r : V) + (1-λ) • y := by
  by_cases hri : x ∈ intrinsicInterior ℝ (base C u)
  · obtain ⟨r⟩ := pure_nonempty hc hs hg
    obtain ⟨a, ha, he⟩ := mem_intrinsicInterior.mp hri
    let : Nonempty (affineSpan ℝ (base C u)) := ⟨a⟩
    let b : affineSpan ℝ (base C u) := ⟨r, subset_affineSpan ℝ _ (pure_mem r)⟩
    have hcont : Continuous (fun t : ℝ => AffineMap.lineMap b a t) :=
      AffineMap.lineMap_continuous
    obtain ⟨t, ht, hmem⟩ := hcont.tendsto' 1 a (AffineMap.lineMap_apply_one b a)
      |>.eventually_mem (mem_interior_iff_mem_nhds.mp ha) |>.exists_gt
    have ht0 : 0 < t := by linarith
    have hline : (AffineMap.lineMap b a t : V) = AffineMap.lineMap (r : V) x t := by
      rw [← he]
      exact (affineSpan ℝ (base C u)).subtype.apply_lineMap b a t
    refine ⟨r, AffineMap.lineMap b a t, 1 - t⁻¹, hmem, ?_, ?_, ?_, ?_⟩
    · exact sub_pos.mpr ((inv_lt_one₀ ht0).mpr ht)
    · linarith [inv_pos.mpr ht0]
    · exact fun h => hn (h.symm ▸ r.property)
    · rw [hline, AffineMap.lineMap_apply_module]
      have hi : t⁻¹ * t = 1 := inv_mul_cancel₀ ht0.ne'
      simp only [sub_sub_cancel, smul_add, smul_smul]
      calc
        x = ((1-t⁻¹) + t⁻¹ * (1-t)) • (r : V) + (t⁻¹*t) • x := by
          have hz : (1-t⁻¹) + t⁻¹ * (1-t) = 0 := by nlinarith [hi]
          rw [hz, hi]; simp
        _ = _ := by module
  · have hfront : x ∈ intrinsicFrontier ℝ (base C u) := by
      rw [← closure_sdiff_intrinsicInterior]; exact ⟨subset_closure hx, hri⟩
    obtain ⟨p, hp⟩ := MixedExclusionGeometry.frontier_covered hc hs hg hfront
    obtain ⟨b⟩ := hB p
    obtain ⟨r, s, λ, _, _, hλ, _, hxλ⟩ :=
      OriginalStateCover.radial_decomposition hc hs hg hB p b hp
    refine ⟨r, s, λ, pure_mem s, ?_, ?_, ?_, hxλ⟩
    · apply lt_of_le_of_ne hλ.1
      intro h
      have he : x = (s : V) := by simpa [← h] using hxλ
      exact hn (he.symm ▸ s.property)
    · apply lt_of_le_of_ne hλ.2
      intro h
      have he : x = (r : V) := by simpa [h] using hxλ
      exact hn (he.symm ▸ r.property)
    · exact fun h => hn (h.symm ▸ r.property)

/-- The entire pure locus is compact under original pure reciprocity and EB.
Neither label injectivity nor a joint-measurement axiom is needed. -/
theorem original_pr_pure_compact
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hPR : ∀ p q : pure C u, comparison C u p q = comparison C u q p) :
    IsCompact (pure C u) := by
  have hK := base_compact hc hs
  obtain ⟨L, hL, hbound⟩ := original_uniform_comparison hs hg
  have hclosed : IsClosed (pure C u) := by
    apply isSeqClosed_iff_isClosed.mp
    intro pn x hpn hconv
    have hx : x ∈ base C u := hK.isClosed.mem_of_tendsto hconv
      (Eventually.of_forall (fun n => pure_mem ⟨pn n, hpn n⟩))
    by_contra hn
    obtain ⟨r, y, λ, hy, hλ, hλ1, hxr, hxλ⟩ := nonpure_decomposition hc hs hg hB hx hn
    have hineq (n : ℕ) : λ * (1 - comparison C u r (pn n)) ≤ L * ‖pn n - x‖ := by
      let p : pure C u := ⟨pn n, hpn n⟩
      obtain ⟨f, hf, hfr⟩ := comparison_attained hs hg p r
      obtain ⟨g, hg', hgg⟩ := comparison_attained hs hg p p
      have hself : comparison C u p p = 1 := hgg.trans hg'.2
      have hnear := hbound p p (pure_mem p) x hx
      rw [hself] at hnear
      have hfx : comparison C u p x ≤ f x := csInf_le
        ⟨0, by rintro z ⟨f', hf', rfl⟩; exact (hf'.1 x hx.1).1⟩
        ⟨f.toLinearMap, hf, rfl⟩
      have hfy : f y ≤ 1 := by simpa [hy.2] using (hf.1 y hy.1).2
      have hfxλ : f x = λ * f r + (1-λ) * f y := by rw [hxλ]; simp
      have hfr' : f r = comparison C u r p := hfr.symm.trans (hPR p r)
      rw [hfr'] at hfxλ
      have hh := (abs_le.mp hnear).2
      have hh' := mul_le_mul_of_nonneg_left hfy (sub_nonneg.mpr hλ1.le)
      change λ * (1 - comparison C u r p) ≤ L * ‖(p : V) - x‖
      nlinarith
    have hLip : LipschitzOnWith ⟨L, hL.le⟩ (comparison C u r) (base C u) := by
      apply LipschitzOnWith.of_dist_le_mul
      intro a ha b hb
      simpa [Real.dist_eq, dist_eq_norm] using hbound r a ha b hb
    have hconvK : Tendsto pn atTop (nhdsWithin x (base C u)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hconv, Eventually.of_forall (fun n => pure_mem ⟨pn n, hpn n⟩)⟩
    have hcompconv := (hLip.continuousOn x hx).tendsto.comp hconvK
    have hnormconv : Tendsto (fun n => L * ‖pn n - x‖) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul ((hconv.sub_const x).norm))
    have hlim : λ * (1 - comparison C u r x) ≤ 0 :=
      le_of_tendsto_of_tendsto (tendsto_const_nhds.mul (tendsto_const_nhds.sub hcompconv))
        hnormconv (Eventually.of_forall hineq)
    obtain ⟨h, _, _, er, hones, _⟩ := reciprocal_endpoint_exposure hc hs hg r
      (fun s => (hPR r s).le)
    have hvalue : comparison C u r x ≤ (u - h) x := by
      exact csInf_le ⟨0, by rintro z ⟨f, hf, rfl⟩; exact (hf.1 x hx.1).1⟩ ⟨_, er, rfl⟩
    have hone : 1 ≤ comparison C u r x := by nlinarith
    have here : (u - h) x = 1 :=
      le_antisymm (by simpa [hx.2] using (er.1 x hx.1).2) (hone.trans hvalue)
    exact hxr (show x ∈ ({(r : V)} : Set V) from hones ▸ ⟨hx, here⟩)
  exact hK.of_isClosed_subset hclosed (fun _ h => h.1)

#print axioms original_pr_pure_compact

end D5.S3.Quantum.Foundation.OriginalPureCompactness
