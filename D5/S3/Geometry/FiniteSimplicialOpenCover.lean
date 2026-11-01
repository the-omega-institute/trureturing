/- GID: D5/S3/Geometry/FiniteSimplicialOpenCover
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteSimplicialOpenCover
   mirror-E: none(waiver:coordinate-topology)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Positive coordinate stars form an open cover with contractible face intersections. -/

import D5.S3.Geometry.FiniteConeCollapse
import Mathlib.Topology.Homotopy.Contractible

/-! The positive coordinate stars of a finite simplicial realization. -/

noncomputable section
open Set Finset Topology
open scoped BigOperators unitInterval ContinuousMap

namespace D5.S3.Geometry.FiniteSimplicialOpenCover
open FiniteConeCollapse
variable {V : Type} [Fintype V] [LinearOrder V]
variable (K : PreAbstractSimplicialComplex V)

/-- The actual finite coordinate carrier, including the empty realization. -/
abbrev Space := ↥(FiniteConeCollapse.realization K)

theorem coordinate_data (x : Space K) :
    (∀ v, 0 ≤ x.val v) ∧ (∑ v, x.val v) = 1 := by
  obtain ⟨s, hs, hx⟩ := (FiniteConeCollapse.realization_mem_iff K x.val).1 x.property
  exact ⟨hx.1, hx.2.1⟩

/-- The real open vertex star. Ghost vertices give empty stars. -/
def vertexOpen (v : V) : Set (Space K) := {x | 0 < x.val v}

theorem isOpen_vertexOpen (v : V) : IsOpen (vertexOpen K v) :=
  isOpen_lt continuous_const ((continuous_apply v).comp continuous_subtype_val)

theorem vertexOpen_cover : ⋃ v, vertexOpen K v = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  have hpos : ∃ v, 0 < x.val v := by
    by_contra h
    push_neg at h
    have hz : ∀ v, x.val v = 0 :=
      fun v => le_antisymm (h v) ((coordinate_data K x).1 v)
    have hsum := (coordinate_data K x).2
    simp only [hz, Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  obtain ⟨v, hv⟩ := hpos
  exact Set.mem_iUnion.mpr ⟨v, hv⟩

/-- Every finite intersection, with the empty intersection equal to the carrier. -/
def intersection (s : Finset V) : Set (Space K) :=
  {x | ∀ v ∈ s, 0 < x.val v}

/-- Positivity forces every chosen vertex to lie in the original support face. -/
theorem intersection_subset_support {s f : Finset V} {x : Space K}
    (hx : x ∈ intersection K s) (hf : x.val ∈ faceSimplex f) : s ⊆ f := by
  intro v hv
  by_contra hvf
  exact (ne_of_gt (hx v hv)) (hf.2.2 v hvf)

theorem face_of_nonempty_intersection {s : Finset V} (hs : s.Nonempty)
    (h : (intersection K s).Nonempty) : s ∈ K := by
  obtain ⟨x, hx⟩ := h
  obtain ⟨f, hf, hxf⟩ := (FiniteConeCollapse.realization_mem_iff K x.val).1 x.property
  exact (K.isRelLowerSet_faces hf).2 (intersection_subset_support K hx hxf) hs

/-- Equal weights on exactly the vertices of `s`. -/
def barycenterCoords (s : Finset V) (v : V) : ℝ :=
  if v ∈ s then 1 / (s.card : ℝ) else 0

theorem barycenterCoords_mem_faceSimplex {s : Finset V} (hs : s.Nonempty) :
    barycenterCoords s ∈ faceSimplex s := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  refine ⟨?_, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ s <;> simp [barycenterCoords, hv, hc.le]
  · have hsum : (∑ v, barycenterCoords s v) = ∑ v ∈ s, barycenterCoords s v := by
      symm
      apply Finset.sum_subset (Finset.subset_univ s)
      intro v hv hvs
      simp [barycenterCoords, hvs]
    rw [hsum]
    calc
      (∑ v ∈ s, barycenterCoords s v) = ∑ _v ∈ s, 1 / (s.card : ℝ) := by
        exact Finset.sum_congr rfl fun v hv => by simp [barycenterCoords, hv]
      _ = 1 := by simp [hc.ne']
  · intro v hv
    simp [barycenterCoords, hv]

/-- A barycenter is constructed only from an actual nonempty face. -/
def barycenter {s : Finset V} (hs : s ∈ K) : Space K :=
  ⟨barycenterCoords s, (FiniteConeCollapse.realization_mem_iff K _).2
    ⟨s, hs, barycenterCoords_mem_faceSimplex (K.isRelLowerSet_faces hs).1⟩⟩

theorem barycenter_mem_intersection {s : Finset V} (hs : s ∈ K) :
    barycenter K hs ∈ intersection K s := by
  intro v hv
  change 0 < barycenterCoords s v
  rw [barycenterCoords, if_pos hv]
  exact one_div_pos.mpr (by exact_mod_cast (K.isRelLowerSet_faces hs).1.card_pos)

/-- No vertices outside the original support face appear during the contraction. -/
theorem segment_mem_original_face {s f : Finset V} (hs : s ∈ K)
    (x : Space K) (hx : x ∈ intersection K s)
    (hxf : x.val ∈ faceSimplex f) (t : I) :
    (fun v => (1 - (t : ℝ)) * x.val v + (t : ℝ) * barycenterCoords s v) ∈
      faceSimplex f := by
  have hsf : s ⊆ f := intersection_subset_support K hx hxf
  have hb : barycenterCoords s ∈ faceSimplex f := by
    refine ⟨(barycenterCoords_mem_faceSimplex (K.isRelLowerSet_faces hs).1).1,
      (barycenterCoords_mem_faceSimplex (K.isRelLowerSet_faces hs).1).2.1, ?_⟩
    intro v hv
    exact (barycenterCoords_mem_faceSimplex (K.isRelLowerSet_faces hs).1).2.2 v
      (fun hvs => hv (hsf hvs))
  have hc : Convex ℝ (faceSimplex f) := by
    rw [faceSimplex_eq_convexHull]
    exact convex_convexHull _ _
  exact hc hxf hb (sub_nonneg.mpr t.property.2) t.property.1 (by ring)

/-- The actual straight-line contraction, valued in the actual intersection. -/
def contractIntersection {s : Finset V} (hs : s ∈ K)
    (t : I) (x : intersection K s) : intersection K s := by
  let y : V → ℝ :=
    fun v => (1 - (t : ℝ)) * x.val.val v + (t : ℝ) * barycenterCoords s v
  have hy : y ∈ FiniteConeCollapse.realization K := by
    obtain ⟨f, hf, hxf⟩ := (FiniteConeCollapse.realization_mem_iff K x.val.val).1 x.val.property
    exact (FiniteConeCollapse.realization_mem_iff K y).2
      ⟨f, hf, segment_mem_original_face K hs x.val x.property hxf t⟩
  refine ⟨⟨y, hy⟩, ?_⟩
  intro v hv
  have hxv : 0 < x.val.val v := x.property v hv
  have hbv : 0 < barycenterCoords s v := barycenter_mem_intersection K hs v hv
  change 0 < (1 - (t : ℝ)) * x.val.val v + (t : ℝ) * barycenterCoords s v
  rcases lt_or_eq_of_le t.property.2 with ht | ht
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht) hxv)
      (mul_nonneg t.property.1 hbv.le)
  · rw [ht]
    simpa using hbv

theorem continuous_contractIntersection {s : Finset V} (hs : s ∈ K) :
    Continuous (fun z : I × intersection K s => contractIntersection K hs z.1 z.2) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  apply continuous_pi
  intro v
  change Continuous (fun z : I × intersection K s =>
    (1 - (z.1 : ℝ)) * z.2.val.val v + (z.1 : ℝ) * barycenterCoords s v)
  have ht : Continuous (fun z : I × intersection K s => (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hx : Continuous (fun z : I × intersection K s => z.2.val.val v) :=
    (continuous_apply v).comp (continuous_subtype_val.comp
      (continuous_subtype_val.comp continuous_snd))
  exact ((continuous_const.sub ht).mul hx).add (ht.mul continuous_const)

/-- This is a homotopy in the intersection, not merely in the ambient vector space. -/
def intersectionContraction {s : Finset V} (hs : s ∈ K) :
    (ContinuousMap.id (intersection K s)).Homotopy
      (ContinuousMap.const _ ⟨barycenter K hs, barycenter_mem_intersection K hs⟩) where
  toFun z := contractIntersection K hs z.1 z.2
  continuous_toFun := continuous_contractIntersection K hs
  map_zero_left x := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    simp [contractIntersection]
  map_one_left x := by
    apply Subtype.ext
    apply Subtype.ext
    funext v
    simp [contractIntersection, barycenter]

theorem contractible_intersection {s : Finset V} (hs : s ∈ K) :
    ContractibleSpace (intersection K s) :=
  (contractible_iff_id_nullhomotopic _).2
    ⟨⟨barycenter K hs, barycenter_mem_intersection K hs⟩,
      ⟨intersectionContraction K hs⟩⟩

end D5.S3.Geometry.FiniteSimplicialOpenCover
