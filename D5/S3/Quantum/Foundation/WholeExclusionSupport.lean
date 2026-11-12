/- GID: D5/S3/Quantum/Foundation/WholeExclusionSupport
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/WholeExclusionSupport
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Global positivity from vanishing on an entire original exclusion set. -/

import D5.S3.Quantum.Foundation.FacetZeroGluing

/-! A normalization prerequisite for original three-effect completion. -/

noncomputable section

namespace D5.S3.Quantum.Foundation.WholeExclusionSupport

open CircuitBalancedConfirmation FacetZeroGluing

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- An original linear candidate, bounded above by the original unit and equal
to one at an original pure point, is proper if it vanishes on that point's
entire original exclusion set. Positivity is a conclusion, not an input. -/
theorem whole_exclusion_support {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (r : pure C u) (h : V →ₗ[ℝ] ℝ) (hr : h r = 1)
    (hupper : ∀ x ∈ C, h x ≤ u x)
    (hzero : ∀ x ∈ exclusion C u r, h x = 0) : confirms C u r h := by
  have hK := base_compact hclosed hstrict
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn ⟨r, pure_mem r⟩
    h.continuous_of_finiteDimensional.continuousOn
  have hnonneg : 0 ≤ h x := by
    by_contra! hneg
    let c : ℝ := h x
    have hc : c < 0 := hneg
    have hd : 0 < 1 - c := by linarith
    let g : V →ₗ[ℝ] ℝ := (1 - c)⁻¹ • (h - c • u)
    have hgproper : proper C u g := cone_bound hK hstrict (by
      intro p
      have hcp : c ≤ h p := hmin (pure_mem p)
      have hpu : u p = 1 := (pure_mem p).2
      have hpupper : h p ≤ 1 := by simpa only [hpu] using hupper p (pure_mem p).1
      change 0 ≤ (1 - c)⁻¹ * (h p - c * u p) ∧
        (1 - c)⁻¹ * (h p - c * u p) ≤ 1
      rw [hpu, mul_one]
      constructor
      · exact mul_nonneg (inv_nonneg.mpr hd.le) (sub_nonneg.mpr hcp)
      · rw [← div_eq_inv_mul, div_le_one hd]
        linarith)
    have hgr : g r = 1 := by
      simp [g, hr, (pure_mem r).2, ne_of_gt hd]
    have hgx : g x = 0 := by
      simp [g, hx.2, c]
    have hxD : x ∈ exclusion C u r := ⟨hx, g, ⟨hgproper, hgr⟩, hgx⟩
    have hz := hzero x hxD
    linarith
  refine ⟨?_, hr⟩
  intro y hy
  refine ⟨nonneg_on_cone hK hstrict (fun p => hnonneg.trans (hmin (pure_mem p))) y hy,
    hupper y hy⟩

end D5.S3.Quantum.Foundation.WholeExclusionSupport
