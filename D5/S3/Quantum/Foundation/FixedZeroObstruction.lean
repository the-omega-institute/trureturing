/- GID: D5/S3/Quantum/Foundation/FixedZeroObstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/FixedZeroObstruction
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Original whole-state zero-effect maxima and singleton one-faces. -/

import D5.S3.Quantum.Foundation.ExclusionBallFaces
import Mathlib.Topology.ContinuousMap.Compact

noncomputable section

namespace D5.S3.Quantum.Foundation.FixedZeroObstruction

open CircuitBalancedConfirmation FacetZeroGluing ExclusionBallFaces

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

/-- The original entire zero-confirming effects at a pure label. -/
def zeroEffects (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (t : pure C u) :
    Set (V →ₗ[ℝ] ℝ) := {g | proper C u g ∧ g t = 0}

/-- The original confirmers that vanish on the entire exclusion face. -/
def fullZeroConfirmers (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ) (s : pure C u) :
    Set (V →ₗ[ℝ] ℝ) :=
  {h | confirms C u s h ∧ ∀ x ∈ exclusion C u s, h x = 0}

/-- A global maximum of every actual zero effect is attained at a pure point
of the entire exclusion. The zero effect is included. -/
theorem zero_effect_maximizer
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (t : pure C u) {g : V →ₗ[ℝ] ℝ} (hgt : g ∈ zeroEffects C u t) :
    ∃ v : pure C u, (v : V) ∈ exclusion C u t ∧
      ∀ x ∈ base C u, g x ≤ g v := by
  have hK := base_compact hc hs
  have hD := (exclusion_ball_faces hc hs hg hB).1 t
  by_cases hg0 : g = 0
  · obtain ⟨v, hv⟩ := hD.2.1.extremePoints_nonempty hD.1.nonempty
    exact ⟨⟨v, hD.2.2.2.2.1.extremePoints_subset_extremePoints hv⟩,
      hv.1, by simp [hg0]⟩
  · have hpos : ∃ q : pure C u, 0 < g q := by
      by_contra! hn
      have hz (q : pure C u) : g q = 0 :=
        le_antisymm (hn q) (hgt.1 q (pure_mem q).1).1
      have hk : Submodule.span ℝ (pure C u) ≤ LinearMap.ker g :=
        Submodule.span_le.mpr (fun x hx => hz ⟨x, hx⟩)
      rw [pure_span hK hs hg] at hk
      exact hg0 (LinearMap.ker_eq_top.mp (top_le_iff.mp hk))
    obtain ⟨q, hq⟩ := hpos
    let L := g.toContinuousLinearMap
    obtain ⟨m, hm, hmax⟩ := hK.exists_isMaxOn ⟨q, pure_mem q⟩
      L.continuous.continuousOn
    have hex : IsExposed ℝ (base C u) (L.toExposed (base C u)) :=
      ContinuousLinearMap.toExposed.isExposed
    obtain ⟨v, hv⟩ := (hex.isCompact hK).extremePoints_nonempty ⟨m, hm, hmax⟩
    let vp : pure C u := ⟨v, hex.isExtreme.extremePoints_subset_extremePoints hv⟩
    have hgv : 0 < g v := hq.trans_le (hv.1.2 q (pure_mem q))
    let f : V →ₗ[ℝ] ℝ := (g v)⁻¹ • g
    have hf : confirms C u vp f := by
      refine ⟨cone_bound hK hs ?_, ?_⟩
      · intro r
        change 0 ≤ (g v)⁻¹ * g r ∧ (g v)⁻¹ * g r ≤ 1
        refine ⟨mul_nonneg (inv_nonneg.mpr hgv.le)
          (hgt.1 r (pure_mem r).1).1, ?_⟩
        rw [← div_eq_inv_mul, div_le_one hgv]
        exact hv.1.2 r (pure_mem r)
      · simp [f, vp, hgv.ne']
    have ht : (t : V) ∈ exclusion C u vp :=
      ⟨pure_mem t, f, hf, by simp [f, hgt.2]⟩
    exact ⟨vp, (exclusion_symmetric vp t).mp ht, hv.1.2⟩

/-- Under faithful labels every full zero confirmer has exactly its labelled
singleton as its one-face, even among mixed states. -/
theorem full_zero_one_face
    (hc : IsClosed (C : Set V)) (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hg : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (hInj : Function.Injective (fun p : pure C u => exclusion C u p))
    (s : pure C u) {h : V →ₗ[ℝ] ℝ} (hh : h ∈ fullZeroConfirmers C u s) :
    {x | x ∈ base C u ∧ h x = 1} = {(s : V)} := by
  have geom := (exclusion_ball_faces hc hs hg hB).1
  have hpure (v : pure C u) (hv : h v = 1) : v = s := by
    have hsub : exclusion C u s ⊆ exclusion C u v := by
      intro x hx
      exact ⟨hx.1, h, ⟨hh.1.1, hv⟩, hh.2 x hx⟩
    obtain ⟨b⟩ := hB v
    have he : exclusion C u s = exclusion C u v :=
      chart_face_eq b (geom s).2.2.1
        ((geom s).2.2.2.2.1.mono (geom v).2.2.2.2.1.subset hsub) (geom s).1
    exact (hInj he).symm
  let L := h.toContinuousLinearMap
  let F := L.toExposed (base C u)
  have hex : IsExposed ℝ (base C u) F := ContinuousLinearMap.toExposed.isExposed
  have hF : F = {x | x ∈ base C u ∧ h x = 1} := by
    ext x
    constructor
    · intro hx
      exact ⟨hx.1, le_antisymm
        (by simpa [(pure_mem s).2] using (hh.1.1 x hx.1.1).2)
        (by simpa [hh.1.2] using hx.2 s (pure_mem s))⟩
    · rintro ⟨hx, hx1⟩
      exact ⟨hx, fun y hy => by simpa [hx1, hy.2] using (hh.1.1 y hy.1).2⟩
  have hpoints : F.extremePoints ℝ ⊆ {(s : V)} := by
    intro v hv
    have hvp := hex.isExtreme.extremePoints_subset_extremePoints hv
    have hv1 := (hF ▸ hv.1).2
    exact congrArg Subtype.val (hpure ⟨v, hvp⟩ hv1)
  have hFs : F ⊆ {(s : V)} := by
    rw [← closure_convexHull_extremePoints (hex.isCompact (base_compact hc hs))
      (hex.convex (base_convex C u))]
    exact closure_minimal (convexHull_min hpoints (convex_singleton _)) isClosed_singleton
  rw [← hF]
  exact Set.Subset.antisymm hFs (Set.singleton_subset_iff.mpr
    (hF.symm ▸ (show (s : V) ∈ {x | x ∈ base C u ∧ h x = 1} from ⟨pure_mem s, hh.1.2⟩)))

#print axioms zero_effect_maximizer
#print axioms full_zero_one_face

end D5.S3.Quantum.Foundation.FixedZeroObstruction
