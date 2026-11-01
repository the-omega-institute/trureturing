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

/-! Actual cyclic boundary coverage determines the full interior-diagonal universe. -/

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

/-- Relabelling by the canonical equivalence preserves the native cyclic successor. -/
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

omit [NeZero n] in
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

theorem maximal_endpoints {K : Set E} {a b z : E}
    (ha : a ∈ K) (hb : b ∈ K) (hz : z ∈ openSegment ℝ a b)
    (f : E →L[ℝ] ℝ) (hmax : ∀ x ∈ K, f x ≤ f z) :
    f a = f z ∧ f b = f z := by
  obtain ⟨s,t,hs,ht,hst,hz⟩ := hz
  have heq := congrArg f hz
  simp only [map_add,map_smul,smul_eq_mul] at heq
  have hfa := hmax a ha
  have hfb := hmax b hb
  have heq' := congrArg (fun r : ℝ => r * f z) hst
  constructor
  · apply le_antisymm hfa
    by_contra! h
    have := mul_pos hs (sub_pos.mpr h)
    have := mul_nonneg ht.le (sub_nonneg.mpr hfb)
    nlinarith
  · apply le_antisymm hfb
    by_contra! h
    have := mul_pos ht (sub_pos.mpr h)
    have := mul_nonneg hs.le (sub_nonneg.mpr hfa)
    nlinarith

omit [NeZero n] in
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
    have hopen := f.isOpenMap_of_ne_zero hf (interior K) isOpen_interior
    have hi := interior_maximal hsub hopen (mem_image_of_mem f hz)
    rw [interior_Iic] at hi
    exact (lt_irrefl (f (poly a))) (by simpa only [mem_Iio,hfz] using hi)
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
  · have he : z = poly a := by
      rw [hk,hk'] at hkseg
      simpa using hkseg
    exact False.elim (hzne a he.symm)
  · exact Or.inl ((hkinj hk').symm.trans (congrArg (finRotate n) (hkinj hk)))
  · exact Or.inr ((hkinj hk').symm.trans (congrArg (finRotate n) (hkinj hk)))
  · have he : z = poly b := by
      rw [hk,hk'] at hkseg
      simpa using hkseg
    exact False.elim (hzne b he.symm)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem vertex_succ (poly : Polygon E n) (i : ZMod n) :
    vertex poly (i+1) = poly (finRotate n ((ZMod.finEquiv n).symm i)) := by
  simp [vertex,finRotate_apply]

/-- Every native diagonal has its whole open segment in the hull interior, and conversely. -/
theorem isDiagonal_iff_openSegment_subset_interior
    (hdim : finrank ℝ E = 2) (hn : 3 ≤ n) (poly : Polygon E n)
    (hB : BoundaryModel poly) (i j : ZMod n) :
    Carrier.IsDiagonal s(i,j) ↔ vertex poly i ≠ vertex poly j ∧
      openSegment ℝ (vertex poly i) (vertex poly j) ⊆
        interior (convexHull ℝ (range poly.vertices)) := by
  haveI : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by omega)
  let a := (ZMod.finEquiv n).symm i
  let b := (ZMod.finEquiv n).symm j
  have hv : Function.Injective (vertex poly) := hB.injective_vertices.comp (ZMod.finEquiv n).symm.injective
  have hseg : Carrier.IsSegment s(i,j) ↔ i ≠ j := by
    simp [Carrier.IsSegment,Sym2.mk_isDiag_iff]
  constructor
  · rintro ⟨hij,hside⟩
    have hij' : i ≠ j := hseg.mp hij
    refine ⟨hv.ne hij',?_⟩
    intro z hz
    by_contra hznot
    have ha := hB.extreme_vertices a
    have hb := hB.extreme_vertices b
    obtain ⟨f,hf,hmax⟩ := geometric_hahn_banach_of_nonempty_interior_point
      (convex_convexHull ℝ (range poly.vertices)) hznot (interior_nonempty hdim hn hB)
    have hends := maximal_endpoints ha.1 hb.1 hz f hmax
    have hadj := supporting_pair_is_side hdim hB ((ZMod.finEquiv n).symm.injective.ne hij')
      f hf (fun x hx => (hmax x hx).trans_eq hends.1.symm)
      (hends.2.trans hends.1.symm)
    apply hside
    rcases hadj with hadj | hadj
    · have hji : j = i+1 := by
        have := congrArg (ZMod.finEquiv n) hadj
        simpa [a,b,finRotate_apply] using this
      exact ⟨i, by rw [hji]⟩
    · have hij : i = j+1 := by
        have := congrArg (ZMod.finEquiv n) hadj
        simpa [a,b,finRotate_apply] using this
      exact ⟨j, by rw [hij]; exact Sym2.eq_swap⟩
  · rintro ⟨hij,hint⟩
    refine ⟨hseg.mpr (fun h => hij (congrArg (vertex poly) h)),?_⟩
    rintro ⟨k,hk⟩
    have hedge : ∀ k : ZMod n,
        ¬ openSegment ℝ (vertex poly k) (vertex poly (k+1)) ⊆
          interior (convexHull ℝ (range poly.vertices)) := by
      intro k h
      let z := midpoint ℝ (vertex poly k) (vertex poly (k+1))
      have hzint := h (midpoint_mem_openSegment _ _)
      have hzedge : z ∈ poly.edgeSet ℝ ((ZMod.finEquiv n).symm k) := by
        rw [Polygon.edgeSet,affineSegment_eq_segment]
        change z ∈ segment ℝ (vertex poly k) (poly (finRotate n ((ZMod.finEquiv n).symm k)))
        rw [← vertex_succ]
        exact midpoint_mem_segment _ _
      have hzfront : z ∈ frontier (convexHull ℝ (range poly.vertices)) := by
        rw [← hB.boundary_eq]
        exact mem_iUnion.mpr ⟨_,hzedge⟩
      exact (disjoint_left.mp disjoint_interior_frontier) hzint hzfront
    rcases Sym2.eq_iff.mp hk with ⟨hi,hj⟩ | ⟨hi,hj⟩
    · exact hedge k (by simpa only [hi,hj] using hint)
    · exact hedge k (by simpa only [hi,hj,openSegment_symm] using hint)

end D5.S3.Geometry.Polygons.PolygonInteriorDiagonals
