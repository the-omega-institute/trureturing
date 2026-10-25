import D5.S3.Geometry.Hyperideal.CFMPSimplexFullFlux435Transient

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped MeasureTheory Interval

namespace CFMPTriangleDivergence435Transient
open CFMPSimplexDirection435Transient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem triangle_directional_y (a : ℝ) (ha : 0 ≤ a) (P D : ℝ × ℝ → E)
    (hP : ContinuousOn P (triangle a)) (hD : ContinuousOn D (triangle a))
    (hd : ∀ x ∈ Ioo (0 : ℝ) a, ∀ y ∈ Ioo (0 : ℝ) (a-x),
      HasDerivAt (fun t : ℝ => P (x,t)) (D (x,y)) y) :
    (∫ z in triangle a, D z) =
      ∫ x in (0 : ℝ)..a, P (x,a-x)-P (x,0) := by
  have hs : MapsTo Prod.swap (triangle a) (triangle a) := by
    intro z hz
    exact ⟨hz.2.1,hz.1,by simpa only [add_comm] using hz.2.2⟩
  have hc : Continuous (Prod.swap : ℝ × ℝ → ℝ × ℝ) := by fun_prop
  rw [← triangle_swap_integral a D]
  exact triangle_directional a ha (fun z => P z.swap) (fun z => D z.swap)
    (hP.comp' hc.continuousOn hs) (hD.comp' hc.continuousOn hs) hd

-- Coordinate fluxes keep the two parametrizations of the diagonal explicit.
theorem triangle_divergence (a : ℝ) (ha : 0 ≤ a)
    (P₀ P₁ D₀ D₁ : ℝ × ℝ → E)
    (hP₀ : ContinuousOn P₀ (triangle a)) (hP₁ : ContinuousOn P₁ (triangle a))
    (hD₀ : ContinuousOn D₀ (triangle a)) (hD₁ : ContinuousOn D₁ (triangle a))
    (hd₀ : ∀ y ∈ Ioo (0 : ℝ) a, ∀ x ∈ Ioo (0 : ℝ) (a-y),
      HasDerivAt (fun t : ℝ => P₀ (t,y)) (D₀ (x,y)) x)
    (hd₁ : ∀ x ∈ Ioo (0 : ℝ) a, ∀ y ∈ Ioo (0 : ℝ) (a-x),
      HasDerivAt (fun t : ℝ => P₁ (x,t)) (D₁ (x,y)) y) :
    (∫ z in triangle a, D₀ z+D₁ z) =
      (∫ y in (0 : ℝ)..a, P₀ (a-y,y)-P₀ (0,y)) +
      (∫ x in (0 : ℝ)..a, P₁ (x,a-x)-P₁ (x,0)) := by
  have hi₀ : IntegrableOn D₀ (triangle a) :=
    ContinuousOn.integrableOn_compact (triangle_compact a) hD₀
  have hi₁ : IntegrableOn D₁ (triangle a) :=
    ContinuousOn.integrableOn_compact (triangle_compact a) hD₁
  change (∫ z in triangle a, (D₀+D₁) z) = _
  rw [integral_add' hi₀ hi₁,triangle_directional a ha P₀ D₀ hP₀ hD₀ hd₀,
    triangle_directional_y a ha P₁ D₁ hP₁ hD₁ hd₁]

end CFMPTriangleDivergence435Transient
