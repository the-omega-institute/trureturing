/- GID: D5/S3/Geometry/Polygons/PolygonFilledBoundary
   generality: G
   mirror-B: D5/B/S3/Geometry/Polygons/PolygonFilledBoundary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Filled convex polygons with genuine corners determine the extreme-vertex boundary model. -/

import D5.S3.Geometry.Polygons.PolygonInteriorDiagonals

/-! The filled-convex, genuine-corner convention uses the actual successor edges. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Module

namespace D5.S3.Geometry.Polygons.PolygonFilledBoundary
open PolygonInteriorDiagonals

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ} [NeZero n]

/-- A filled convex region whose listed genuine corners give its cyclic boundary.
The filled set may have flat sides; it is not assumed to be a strictly convex set. -/
structure FilledModel (poly : Polygon E n) (C : Set E) : Prop where
  compact : IsCompact C
  convex : Convex ℝ C
  interior_nonempty : (interior C).Nonempty
  injective_vertices : Function.Injective poly.vertices
  boundary_eq : poly.boundary ℝ = frontier C
  genuine_corners : poly.HasNondegenerateVertices ℝ

private theorem vertex_mem {poly : Polygon E n} {C : Set E}
    (h : FilledModel poly C) (i : Fin n) : poly i ∈ C := by
  apply h.compact.isClosed.frontier_subset
  rw [← h.boundary_eq]
  apply mem_iUnion.mpr
  refine ⟨i, ?_⟩
  rw [Polygon.edgeSet, affineSegment_eq_segment]
  exact left_mem_segment ℝ _ _

private theorem hull_eq {poly : Polygon E n} {C : Set E}
    (h : FilledModel poly C) : convexHull ℝ (range poly.vertices) = C := by
  let K := convexHull ℝ (range poly.vertices)
  have hKC : K ⊆ C := convexHull_min (by rintro _ ⟨i,rfl⟩; exact vertex_mem h i) h.convex
  apply Subset.antisymm hKC
  intro x hx
  by_contra hxK
  obtain ⟨f,u,hfK,hfx⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ (range poly.vertices))
    ((finite_range poly.vertices).isClosed_convexHull ℝ) hxK
  have hf : f ≠ 0 := by
    intro hz
    have hi := hfK (poly (0 : Fin n)) (subset_convexHull ℝ _ (mem_range_self 0))
    simp only [hz, zero_apply] at hi hfx
    linarith
  obtain ⟨y,hy,hmax⟩ := h.compact.exists_isMaxOn
    (h.interior_nonempty.mono interior_subset) f.continuous.continuousOn
  have hynot : y ∉ interior C := by
    intro hyint
    have hsub : f '' interior C ⊆ Iic (f y) := by
      rintro _ ⟨z,hz,rfl⟩
      exact hmax (interior_subset hz)
    have hopen := f.isOpenMap_of_ne_zero hf (interior C) isOpen_interior
    have hi := interior_maximal hsub hopen (mem_image_of_mem f hyint)
    rw [interior_Iic] at hi
    exact (lt_irrefl (f y)) hi
  have hyfront : y ∈ frontier C := (mem_frontier_iff_notMem_interior hy).mpr hynot
  rw [← h.boundary_eq] at hyfront
  obtain ⟨i,hi⟩ := mem_iUnion.mp hyfront
  have hyK : y ∈ K := by
    apply (convex_convexHull ℝ (range poly.vertices)).segment_subset
      (subset_convexHull ℝ _ (mem_range_self i))
      (subset_convexHull ℝ _ (mem_range_self (finRotate n i)))
    simpa only [Polygon.edgeSet, affineSegment_eq_segment] using hi
  exact (not_lt_of_ge (hmax hx)) ((hfK y hyK).trans hfx)

theorem level_mem_line [FiniteDimensional ℝ E] (hdim : finrank ℝ E = 2)
    {a b x : E} (hab : a ≠ b) (f : E →L[ℝ] ℝ) (hf : f ≠ 0)
    (hfb : f b = f a) (hfx : f x = f a) : x ∈ line[ℝ,a,b] := by
  by_contra hx
  have hnc : ¬ Collinear ℝ ({a,b,x} : Set E) := by
    intro hc
    exact hx (hc.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hab)
  have ht : affineSpan ℝ (range ![a,b,x]) = ⊤ :=
    (affineIndependent_iff_not_collinear_set.mpr hnc).affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr
      (by simp [hdim])
  have heq : f.toLinearMap.toAffineMap = AffineMap.const ℝ E (f a) := by
    apply AffineMap.ext_on ht
    rintro _ ⟨i,rfl⟩
    fin_cases i <;> simp [hfb,hfx]
  have hzero : f a = 0 := by
    have := congrArg (fun g : E →ᵃ[ℝ] ℝ => g 0) heq
    simpa using this.symm
  apply hf
  ext z
  have := congrArg (fun g : E →ᵃ[ℝ] ℝ => g z) heq
  simpa [hzero] using this

private theorem edge_support {poly : Polygon E n} {C : Set E}
    (h : FilledModel poly C) (i : Fin n) :
    ∃ f : E →L[ℝ] ℝ, f ≠ 0 ∧
      (∀ x ∈ C, f x ≤ f (poly i)) ∧ f (poly (finRotate n i)) = f (poly i) := by
  let z := midpoint ℝ (poly i) (poly (finRotate n i))
  have hzedge : z ∈ poly.edgeSet ℝ i := by
    rw [Polygon.edgeSet, affineSegment_eq_segment]
    exact midpoint_mem_segment _ _
  have hzfront : z ∈ frontier C := by
    rw [← h.boundary_eq]
    exact mem_iUnion.mpr ⟨i,hzedge⟩
  have hznot : z ∉ interior C := fun hz =>
    (disjoint_left.mp disjoint_interior_frontier) hz hzfront
  obtain ⟨f,hf,hmax⟩ := geometric_hahn_banach_of_nonempty_interior_point
    h.convex hznot h.interior_nonempty
  obtain ⟨ha,hb⟩ := maximal_endpoints (vertex_mem h i) (vertex_mem h (finRotate n i))
    (midpoint_mem_openSegment _ _) f hmax
  exact ⟨f,hf,fun x hx => (hmax x hx).trans_eq ha.symm,hb.trans ha.symm⟩

private theorem corner_extreme [FiniteDimensional ℝ E] (hdim : finrank ℝ E = 2)
    {poly : Polygon E n} {C : Set E} (h : FilledModel poly C) (i : Fin n) :
    poly (finRotate n i) ∈ C.extremePoints ℝ := by
  let a := poly i
  let b := poly (finRotate n i)
  let c := poly (finRotate n (finRotate n i))
  have hn := h.genuine_corners.three_le
  have htwo : (1 : Fin n) + 1 = 2 := by
    apply Fin.ext
    change (1 % n + 1 % n) % n = 2 % n
    simp [Nat.mod_eq_of_lt (show 1 < n by omega),
      Nat.mod_eq_of_lt (show 2 < n by omega)]
  have hind : AffineIndependent ℝ ![a,b,c] := by
    simpa [a,b,c,finRotate_apply,add_assoc,htwo] using h.genuine_corners i
  have hab : a ≠ b := hind.injective.ne (by decide : (0 : Fin 3) ≠ 1)
  have hbc : b ≠ c := hind.injective.ne (by decide : (1 : Fin 3) ≠ 2)
  obtain ⟨f,hf,hfmax,hfab⟩ := edge_support h i
  obtain ⟨g,hg,hgmax,hgbc⟩ := edge_support h (finRotate n i)
  apply mem_extremePoints_iff_left.mpr
  refine ⟨vertex_mem h _, ?_⟩
  intro x hx y hy hxy
  have hfm : ∀ z ∈ C, f z ≤ f b := fun z hz => (hfmax z hz).trans_eq hfab.symm
  have hgm : ∀ z ∈ C, g z ≤ g b := hgmax
  have hfx := (maximal_endpoints hx hy hxy f hfm).1
  have hgx := (maximal_endpoints hx hy hxy g hgm).1
  have hxline : x ∈ line[ℝ,a,b] := level_mem_line hdim hab f hf hfab (hfx.trans hfab)
  have hxline' : x ∈ line[ℝ,b,c] := level_mem_line hdim hbc g hg hgbc hgx
  by_contra hxb
  have heq : line[ℝ,a,b] = line[ℝ,b,c] := by
    calc
      line[ℝ,a,b] = line[ℝ,b,x] :=
        (affineSpan_pair_eq_of_mem_of_mem_of_ne (right_mem_affineSpan_pair ℝ a b) hxline (Ne.symm hxb)).symm
      _ = line[ℝ,b,c] :=
        affineSpan_pair_eq_of_mem_of_mem_of_ne (left_mem_affineSpan_pair ℝ b c) hxline' (Ne.symm hxb)
  have hc : c ∈ line[ℝ,a,b] := heq.symm ▸ right_mem_affineSpan_pair ℝ b c
  exact (affineIndependent_iff_not_collinear_set.mp hind)
    (by
      convert collinear_insert_of_mem_affineSpan_pair hc using 1
      ext z
      simp only [mem_insert_iff,mem_singleton_iff]
      tauto)

/-- The actual filled region is the vertex hull and its genuine corners give BoundaryModel. -/
theorem boundaryModel_of_filled (hdim : finrank ℝ E = 2)
    (poly : Polygon E n) (C : Set E) (h : FilledModel poly C) :
    C = convexHull ℝ (range poly.vertices) ∧ BoundaryModel poly := by
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_pos (by omega)
  have heq := hull_eq h
  refine ⟨heq.symm,h.injective_vertices,?_,by simpa only [heq] using h.boundary_eq⟩
  intro j
  have hj := corner_extreme hdim h ((finRotate n).symm j)
  simpa only [Equiv.apply_symm_apply,heq] using hj

end D5.S3.Geometry.Polygons.PolygonFilledBoundary
