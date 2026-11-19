import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPeriodSource
import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourPointChartGluing

/-! Real radial identities determine the overlaps used by the four-point residue proof. -/

open Filter Set
open scoped Topology

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourPointChartGluing

open OriginalFourMPeriodSource (dLip)
open private dLip_neBot dLip_im_ne_zero isOpen_dLip from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPeriodSource

private theorem frequently_eq_of_real_germ {F G : ℂ → ℂ} {x : ℝ}
    (h : ∀ᶠ t : ℝ in 𝓝 x, F (t : ℂ) = G (t : ℂ)) :
    ∃ᶠ z in 𝓝[≠] (x : ℂ), F z = G z := by
  have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] x) (𝓝[≠] (x : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa only [mem_compl_iff, mem_singleton_iff, Complex.ofReal_inj] using ht
  exact ht.frequently (h.filter_mono nhdsWithin_le_nhds).frequently

/-- The real A/B radial identity supplies an accumulation point in the
interior of the original A/B overlap. -/
theorem radial_AB_overlap {A B : ℂ → ℂ} {k : ℤ} {x : ℝ}
    (hx : 0 < x) (hx₁ : x < 1)
    (h : ∀ᶠ t : ℝ in 𝓝 x, A (rA (t : ℂ)) =
      (2 : ℂ) ^ 12 * (t : ℂ) ^ k * B (rB (t : ℂ))) :
    (x : ℂ) ∈ doubleSlit ∧
      (∃ᶠ z in 𝓝[≠] (x : ℂ), A (rA z) = (2 : ℂ) ^ 12 * z ^ k * B (rB z)) := by
  refine ⟨?_, frequently_eq_of_real_germ
    (F := fun z => A (rA z)) (G := fun z => (2 : ℂ) ^ 12 * z ^ k * B (rB z)) h⟩
  simp [doubleSlit, nonpositiveRay, rightRay, not_le.mpr hx, not_le.mpr hx₁]

/-- A local analytic continuation of the D lip that obeys the real
A/D identity supplies an interior overlap in the original physical coordinate. -/
theorem radial_AD_overlap {A D Dlip : ℂ → ℂ} (upperA : Bool) {t : ℝ}
    (hA : AnalyticAt ℂ (fun u => A (1 - u)) (t : ℂ))
    (hDlip : AnalyticAt ℂ Dlip (t : ℂ))
    (hReal : ∀ᶠ s : ℝ in 𝓝 t, A (1 - (s : ℂ)) = Dlip (s : ℂ))
    (hLip : Dlip =ᶠ[𝓝[dLip upperA] (t : ℂ)] D) :
    ∃ y ∈ U_A ∩ U_D, ∃ᶠ z in 𝓝[≠] y, A (rA z) = D (rD z) := by
  have hEq : (fun u => A (1 - u)) =ᶠ[𝓝 (t : ℂ)] Dlip :=
    (hA.frequently_eq_iff_eventually_eq hDlip).mp (frequently_eq_of_real_germ
      (F := fun u => A (1 - u)) (G := Dlip) hReal)
  have h : ∀ᶠ u in 𝓝[dLip upperA] (t : ℂ), A (1 - u) = D u :=
    (hEq.filter_mono nhdsWithin_le_nhds).trans hLip
  have : (𝓝[dLip upperA] (t : ℂ)).NeBot := dLip_neBot upperA t
  obtain ⟨u, he, hu⟩ :=
    ((eventually_eventually_nhdsWithin.mpr h).and self_mem_nhdsWithin).exists
  rw [(isOpen_dLip upperA).nhdsWithin_eq hu] at he
  have hi := dLip_im_ne_zero hu
  have hu₀ : u ≠ 0 := fun hzero => hi (by simp [hzero])
  have hyim : (u⁻¹).im ≠ 0 := by
    rw [Complex.inv_im]
    exact div_ne_zero (neg_ne_zero.mpr hi) (Complex.normSq_pos.mpr hu₀).ne'
  have hyA : u⁻¹ ∈ U_A := by
    rw [U_A_eq]
    rintro (h | h)
    · exact hyim h.1
    · have hOne : u⁻¹ = 1 := mem_singleton_iff.mp h
      exact hyim (by rw [hOne, Complex.one_im])
  have hyD : u⁻¹ ∈ U_D := by
    rw [U_D_eq]
    exact fun h => hyim h.1
  refine ⟨u⁻¹, ⟨hyA, hyD⟩, ?_⟩
  have hinv : Tendsto (fun z : ℂ => z⁻¹) (𝓝 (u⁻¹)) (𝓝 u) := by
    simpa only [inv_inv] using (continuousAt_inv₀ (inv_ne_zero hu₀)).tendsto
  exact ((hinv.eventually he).filter_mono nhdsWithin_le_nhds).frequently

#print axioms radial_AB_overlap
#print axioms radial_AD_overlap

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourPointChartGluing
