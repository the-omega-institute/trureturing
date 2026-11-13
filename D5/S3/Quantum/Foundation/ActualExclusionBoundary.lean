/- GID: D5/S3/Quantum/Foundation/ActualExclusionBoundary
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/ActualExclusionBoundary
   mirror-E: none(waiver:abstract-convex-geometric-construction)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Intrinsic]
   utility: none
   digest: Whole exclusions cover the actual boundary and detect its boundary midpoints. -/

import D5.S3.Quantum.Foundation.ExclusionBallFaces
import Mathlib.Analysis.Convex.Intrinsic

/-! Relative-boundary geometry of the entire original normalized cone base. -/

noncomputable section
open Set Topology

namespace D5.S3.Quantum.Foundation.ActualExclusionBoundary

open CircuitBalancedConfirmation WeightedRelationConfirmation FacetZeroGluing
open WholePairBallConfirmation ExclusionBallFaces

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}

omit [FiniteDimensional ℝ V] in
private theorem cone_interior_base_interior {x : V} (hx : x ∈ base C u)
    (hi : x ∈ interior (C : Set V)) : x ∈ intrinsicInterior ℝ (base C u) := by
  let A : AffineSubspace ℝ V := ({(1 : ℝ)} : AffineSubspace ℝ ℝ).comap u.toAffineMap
  have hKA : affineSpan ℝ (base C u) ≤ A := affineSpan_le.mpr (by
    intro y hy
    simpa [A] using hy.2)
  have hunit (y : affineSpan ℝ (base C u)) : u y = 1 := by
    have hh := hKA y.property
    simpa [A] using hh
  let a : affineSpan ℝ (base C u) := ⟨x, subset_affineSpan ℝ _ hx⟩
  refine ⟨a, mem_interior_iff_mem_nhds.mpr ?_, rfl⟩
  have hn : {y : affineSpan ℝ (base C u) | (y : V) ∈ C} ∈ nhds a :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      (mem_interior_iff_mem_nhds.mp hi)
  exact Filter.mem_of_superset hn (fun y hy => ⟨hy, hunit y⟩)

private theorem exclusion_boundary
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u)
    (p : pure C u) : exclusion C u p ⊆ intrinsicFrontier ℝ (base C u) := by
  have hK := (base_compact hclosed hstrict).isClosed
  obtain ⟨f, hf, hzero⟩ := (exclusion_ball_faces hclosed hstrict hgen hB).1 p |>.2.2.2.2.2.2
  intro x hx
  rw [← closure_sdiff_intrinsicInterior, hK.closure_eq]
  refine ⟨hx.1, ?_⟩
  rintro ⟨a, ha, he⟩
  let b : affineSpan ℝ (base C u) := ⟨p, subset_affineSpan ℝ _ (pure_mem p)⟩
  have hcont : Continuous (fun t : ℝ => AffineMap.lineMap (k := ℝ) b a t) :=
    AffineMap.lineMap_continuous
  obtain ⟨t, ht, hz⟩ := hcont.tendsto' 1 a (AffineMap.lineMap_apply_one b a) |>.eventually_mem
    (mem_interior_iff_mem_nhds.mp ha) |>.exists_gt
  have hfx : f x = 0 := (hzero ▸ hx).2
  have hbound := (hf.1 _ hz.1).1
  have hval : f ((AffineMap.lineMap (k := ℝ) b a t : affineSpan ℝ (base C u)) : V) =
      1 - t := by
    rw [AffineMap.lineMap_apply]
    change f ((1 - t) • (p : V) + t • (a : V)) = 1 - t
    simp only [map_add, map_smul, smul_eq_mul, he, hfx, hf.2, mul_one, mul_zero, add_zero]
  rw [hval] at hbound
  linarith

private theorem boundary_support_face
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤)
    {x : V} (hx : x ∈ intrinsicFrontier ℝ (base C u)) :
    ∃ F : Set V, x ∈ F ∧ Convex ℝ F ∧ IsExtreme ℝ (base C u) F ∧ F ≠ base C u := by
  have hK := (base_compact hclosed hstrict).isClosed
  have hxK := intrinsicFrontier_subset hK hx
  have hnot : x ∉ interior (C : Set V) := by
    intro hi
    have hii := cone_interior_base_interior hxK hi
    rw [← closure_sdiff_intrinsicInterior, hK.closure_eq] at hx
    exact hx.2 hii
  have hint : (interior (C : Set V)).Nonempty := by
    apply C.convex.interior_nonempty_iff_affineSpan_eq_top.mpr
    rw [affineSpan_eq_span_of_zero_mem (subset_affineSpan ℝ _ C.zero_mem), hgen]
    rfl
  obtain ⟨f, hf, hmax⟩ := geometric_hahn_banach_of_nonempty_interior_point C.convex hnot hint
  have h0 : 0 ≤ f x := by simpa using hmax 0 C.zero_mem
  have h2 := hmax ((2 : ℝ) • x) (C.smul_mem (by norm_num) hxK.1)
  have hfx : f x = 0 := by simp only [map_smul, smul_eq_mul] at h2; linarith
  let F : Set V := f.toExposed (base C u)
  have hext : IsExposed ℝ (base C u) F := ContinuousLinearMap.toExposed.isExposed
  have hxF : x ∈ F := ⟨hxK, fun y hy => by simpa [hfx] using hmax y hy.1⟩
  refine ⟨F, hxF, ?_, hext.isExtreme, ?_⟩
  · exact hext.convex (base_convex C u)
  · intro he
    have hzero (p : pure C u) : f p = 0 := by
      have hpF : (p : V) ∈ F := he.symm ▸ pure_mem p
      exact le_antisymm (by simpa [hfx] using hmax p (pure_mem p).1)
        (by simpa [hfx] using hpF.2 x hxK)
    have hs : Submodule.span ℝ (pure C u) ≤ LinearMap.ker f.toLinearMap :=
      Submodule.span_le.mpr (fun p hp => hzero ⟨p, hp⟩)
    rw [pure_span (base_compact hclosed hstrict) hstrict hgen] at hs
    apply hf
    have heq := LinearMap.ker_eq_top.mp (top_le_iff.mp hs)
    ext y
    exact LinearMap.congr_fun heq y

/-- With the original full effects and variable positive exclusion dimensions,
whole exclusions cover the entire actual relative boundary. Two base points
have a boundary midpoint exactly when they belong to one whole exclusion ball.
No repeated-label, Pair or quotient regularity assumption is used. -/
theorem original_boundary_cover_and_midpoint
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) (hB : exclusionBalls C u) :
    (∀ x ∈ intrinsicFrontier ℝ (base C u), ∃ p : pure C u, x ∈ exclusion C u p) ∧
    ∀ x ∈ base C u, ∀ y ∈ base C u,
      midpoint ℝ x y ∈ intrinsicFrontier ℝ (base C u) ↔
        ∃ p : pure C u, x ∈ exclusion C u p ∧ y ∈ exclusion C u p := by
  have all := exclusion_ball_faces hclosed hstrict hgen hB
  have hcover : ∀ x ∈ intrinsicFrontier ℝ (base C u),
      ∃ p : pure C u, x ∈ exclusion C u p := by
    intro x hx
    obtain ⟨F, hxF, hconv, hface, hproper⟩ := boundary_support_face hclosed hstrict hgen hx
    rcases all.2.1 F ⟨x, hxF⟩ hconv hface hproper with ⟨p, hp⟩ | ⟨p, hp⟩
    · have hxp : x = p := by simpa [hp] using hxF
      have g := all.1 p
      obtain ⟨q, hq⟩ := g.2.1.extremePoints_nonempty g.1.nonempty
      have hqP : q ∈ pure C u := g.2.2.2.2.1.extremePoints_subset_extremePoints hq
      exact ⟨⟨q, hqP⟩, hxp ▸ (exclusion_symmetric p ⟨q, hqP⟩).mp hq.1⟩
    · exact ⟨p, hp ▸ hxF⟩
  refine ⟨hcover, ?_⟩
  intro x hx y hy
  constructor
  · intro hm
    obtain ⟨p, hp⟩ := hcover _ hm
    have hseg : midpoint ℝ x y ∈ openSegment ℝ x y := midpoint_mem_openSegment x y
    have hf := (all.1 p).2.2.2.2.1
    exact ⟨p, hf.left_mem_of_mem_openSegment hx hy hp hseg,
      hf.right_mem_of_mem_openSegment hx hy hp hseg⟩
  · rintro ⟨p, hp, hq⟩
    exact exclusion_boundary hclosed hstrict hgen hB p
      ((all.1 p).2.2.1.midpoint_mem hp hq)

end D5.S3.Quantum.Foundation.ActualExclusionBoundary
