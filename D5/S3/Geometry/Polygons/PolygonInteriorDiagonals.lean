/- GID: D5/S3/Geometry/Polygons/PolygonInteriorDiagonals
   generality: G
   mirror-B: D5/B/S3/Geometry/Polygons/PolygonInteriorDiagonals
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Interior diagonals from an extreme-vertex planar polygon boundary. -/

import D5.S3.Geometry.Polygons.PolygonEarSlideGeometry
import Mathlib.Geometry.Polygon.Basic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Module

namespace D5.S3.Geometry.Polygons.PolygonInteriorDiagonals
open PolygonEarSlide

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ} [NeZero n]

/-- The filled convex hull, with the polygon's actual cyclic edges as its frontier. -/
structure BoundaryModel (poly : Polygon E n) : Prop where
  injective_vertices : Function.Injective poly.vertices
  extreme_vertices : ∀ i, poly i ∈ (convexHull ℝ (range poly.vertices)).extremePoints ℝ
  boundary_eq : poly.boundary ℝ = frontier (convexHull ℝ (range poly.vertices))

/-- Relabelling by the existing ring equivalence preserves the native cyclic successor. -/
def vertex (poly : Polygon E n) (i : ZMod n) : E :=
  poly ((ZMod.finEquiv n).symm i)

private theorem extreme_not_collinear {K : Set E} {a b c : E}
    (ha : a ∈ K.extremePoints ℝ) (hb : b ∈ K.extremePoints ℝ)
    (hc : c ∈ K.extremePoints ℝ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ Collinear ℝ ({a,b,c} : Set E) := by
  intro h
  rcases h.wbtw_or_wbtw_or_wbtw with h | h | h
  · rcases (mem_extremePoints_iff_forall_segment.mp hb).2 a ha.1 c hc.1
      (mem_segment_iff_wbtw.mpr h) with h | h
    · exact hab h
    · exact hbc h.symm
  · rcases (mem_extremePoints_iff_forall_segment.mp hc).2 b hb.1 a ha.1
      (mem_segment_iff_wbtw.mpr h) with h | h
    · exact hbc h
    · exact hac h
  · rcases (mem_extremePoints_iff_forall_segment.mp ha).2 c hc.1 b hb.1
      (mem_segment_iff_wbtw.mpr h) with h | h
    · exact hac h.symm
    · exact hab h.symm

private theorem triple_spans [FiniteDimensional ℝ E] (hdim : finrank ℝ E = 2)
    {K : Set E} {a b c : E} (ha : a ∈ K.extremePoints ℝ)
    (hb : b ∈ K.extremePoints ℝ) (hc : c ∈ K.extremePoints ℝ)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    affineSpan ℝ (range ![a,b,c]) = ⊤ := by
  apply (affineIndependent_iff_not_collinear_set.mpr
    (extreme_not_collinear ha hb hc hab hac hbc)).affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
  simp [hdim]

private theorem interior_nonempty [FiniteDimensional ℝ E] (hdim : finrank ℝ E = 2)
    (hn : 3 ≤ n) {poly : Polygon E n} (hB : BoundaryModel poly) :
    (interior (convexHull ℝ (range poly.vertices))).Nonempty := by
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let c : Fin n := ⟨2, by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; dsimp [a,b] at this; omega
  have hac : a ≠ c := by intro h; have := congrArg Fin.val h; dsimp [a,c] at this; omega
  have hbc : b ≠ c := by intro h; have := congrArg Fin.val h; dsimp [b,c] at this; omega
  have ht := triple_spans hdim (hB.extreme_vertices a) (hB.extreme_vertices b)
    (hB.extreme_vertices c) (hB.injective_vertices.ne hab)
    (hB.injective_vertices.ne hac) (hB.injective_vertices.ne hbc)
  apply interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr
  apply top_unique
  rw [← ht]
  apply affineSpan_mono
  rintro _ ⟨i,rfl⟩
  fin_cases i <;> simp

private theorem common_level_only_two [FiniteDimensional ℝ E] (hdim : finrank ℝ E = 2)
    {K : Set E} {a b c : E} (ha : a ∈ K.extremePoints ℝ)
    (hb : b ∈ K.extremePoints ℝ) (hc : c ∈ K.extremePoints ℝ)
    (hab : a ≠ b) (f : E →L[ℝ] ℝ) (hf : f ≠ 0)
    (habf : f b = f a) (hacf : f c = f a) : c = a ∨ c = b := by
  by_contra! h
  have ht := triple_spans hdim ha hb hc hab h.1.symm h.2.symm
  have heq : f.toLinearMap.toAffineMap = AffineMap.const ℝ E (f a) := by
    apply AffineMap.ext_on ht
    rintro _ ⟨i,rfl⟩
    fin_cases i <;> simp [habf,hacf]
  have hzero : f a = 0 := by
    have := congrArg (fun g : E →ᵃ[ℝ] ℝ => g 0) heq
    simpa using this.symm
  apply hf
  ext x
  have := congrArg (fun g : E →ᵃ[ℝ] ℝ => g x) heq
  simpa [hzero] using this

private theorem maximal_endpoints {K : Set E} {a b z : E}
    (ha : a ∈ K) (hb : b ∈ K) (hz : z ∈ openSegment ℝ a b)
    (f : E →L[ℝ] ℝ) (hmax : ∀ x ∈ K, f x ≤ f z) :
    f a = f z ∧ f b = f z := by
  obtain ⟨s,t,hs,ht,hst,hz⟩ := hz
  have heq := congrArg f hz
  simp only [map_add,map_smul,smul_eq_mul] at heq
  have hfa := hmax a ha
  have hfb := hmax b hb
  constructor <;> nlinarith

private theorem supporting_pair_is_side [FiniteDimensional ℝ E]
    (hdim : finrank ℝ E = 2) {poly : Polygon E n} (hB : BoundaryModel poly)
    {a b : Fin n} (hab : a ≠ b) (f : E →L[ℝ] ℝ) (hf : f ≠ 0)
    (hmax : ∀ x ∈ convexHull ℝ (range poly.vertices), f x ≤ f (poly a))
    (hfb : f (poly b) = f (poly a)) :
    b = finRotate n a ∨ a = finRotate n b := by
  let K := convexHull ℝ (range poly.vertices)
  let z := midpoint ℝ (poly a) (poly b)
  have ha := hB.extreme_vertices a
  have hb := hB.extreme_vertices b
  have hab' := hB.injective_vertices.ne hab
  have hzseg : z ∈ openSegment ℝ (poly a) (poly b) := midpoint_mem_openSegment _ _
  have hzK : z ∈ K := (convex_convexHull ℝ _).openSegment_subset ha.1 hb.1 hzseg
  have hfz : f z = f (poly a) := by
    change f.toLinearMap.toAffineMap (midpoint ℝ (poly a) (poly b)) = _
    rw [AffineMap.map_midpoint]
    simp [hfb]
  have hznot : z ∉ interior K := by
    intro hz
    have hsub : f '' interior K ⊆ Iic (f (poly a)) := by
      rintro _ ⟨x,hx,rfl⟩
      exact hmax x (interior_subset hx)
    have hopen := f.isOpenMap_of_ne_zero hf _ isOpen_interior
    have hi := interior_maximal hsub hopen (mem_image_of_mem f hz)
    rw [interior_Iic] at hi
    exact (lt_irrefl _) (hfz ▸ hi)
  have hzfront : z ∈ frontier K := (mem_frontier_iff_notMem_interior hzK).mpr hznot
  have hzbd : z ∈ poly.boundary ℝ := hB.boundary_eq.symm ▸ hzfront
  obtain ⟨k,hk⟩ := mem_iUnion.mp hzbd
  have hkseg : z ∈ segment ℝ (poly k) (poly (finRotate n k)) := by
    simpa only [Polygon.edgeSet,affineSegment_eq_segment] using hk
  have hzne (l : Fin n) : poly l ≠ z := by
    intro hl
    obtain ⟨h1,h2⟩ := (mem_extremePoints.mp (hB.extreme_vertices l)).2
      (poly a) ha.1 (poly b) hb.1 (hl ▸ hzseg)
    exact hab' (h1.trans h2.symm)
  have hkopen := mem_openSegment_of_ne_left_right (hzne k) (hzne (finRotate n k)) hkseg
  have hmaxz : ∀ x ∈ K, f x ≤ f z := by simpa only [hfz] using hmax
  obtain ⟨hfk,hfk'⟩ := maximal_endpoints (hB.extreme_vertices k).1
    (hB.extreme_vertices (finRotate n k)).1 hkopen f hmaxz
  have hkpair := common_level_only_two hdim ha hb (hB.extreme_vertices k) hab' f hf hfb
    (hfk.trans hfz)
  have hkpair' := common_level_only_two hdim ha hb (hB.extreme_vertices (finRotate n k))
    hab' f hf hfb (hfk'.trans hfz)
  have hkinj := hB.injective_vertices
  rcases hkpair with hk | hk <;> rcases hkpair' with hk' | hk'
  · have : k = finRotate n k := hkinj (hk.trans hk'.symm)
    have hne : finRotate n k ≠ k := by
      rw [finRotate_apply]
      intro he
      have hone : (1 : Fin n) = 0 := add_left_cancel (show k + 1 = k + 0 by simpa using he)
      have := congrArg Fin.val hone
      simp at this
    exact False.elim (hne this.symm)
  · exact Or.inl ((hkinj hk').symm.trans (congrArg (finRotate n) (hkinj hk)))
  · exact Or.inr ((hkinj hk').symm.trans (congrArg (finRotate n) (hkinj hk)))
  · have : poly a = poly b := hk'.symm.trans hk
    exact False.elim (hab' this)

end D5.S3.Geometry.Polygons.PolygonInteriorDiagonals
