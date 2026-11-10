/- GID: D5/S3/Geometry/FiniteVertexOpenStar
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteVertexOpenStar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Relative open vertex stars in finite coordinate realizations have based contractions. -/
import D5.S3.Geometry.FiniteVertexCylinder
import Mathlib.Topology.Homotopy.Basic

noncomputable section
open Set Finset Topology
open scoped BigOperators ContinuousMap unitInterval

namespace D5.S3.Geometry.FiniteVertexOpenStar
open FiniteConeCollapse FiniteVertexCylinder

variable {V : Type*} [Fintype V] [DecidableEq V]
    (M : PreAbstractSimplicialComplex V) (v : V)

/-- The relative open star in the actual coordinate realization. -/
def star : Set (FiniteVertexCylinder.Space M) := {x | 0 < x.val v}

omit [Fintype V] in
theorem isOpen_star : IsOpen (star M v) :=
  isOpen_lt continuous_const ((continuous_apply v).comp continuous_subtype_val)

omit [Fintype V] in
theorem vertex_mem_star (hv : ({v} : Finset V) ∈ M) :
    vertexPoint M v hv ∈ star M v := by
  simp [star, vertexPoint]

private def segmentVector (t : I) (x : star M v) : V → ℝ :=
  (1 - (t : ℝ)) • x.val.val + (t : ℝ) • Pi.single v 1

private theorem segment_mem (t : I) (x : star M v) : segmentVector M v t x ∈ realization M := by
  obtain ⟨s, hs, hx⟩ := x.val.property
  have hvs : v ∈ s := by
    by_contra hvs
    have hx' := hx
    rw [← faceSimplex_eq_convexHull] at hx'
    have hz := hx'.2.2 v hvs
    have hp := x.property
    change 0 < x.val.val v at hp
    linarith
  have hp : Pi.single v (1 : ℝ) ∈
      convexHull ℝ ((fun w : V => Pi.single w (1 : ℝ)) '' (s : Set V)) :=
    subset_convexHull ℝ _ ⟨v, hvs, rfl⟩
  exact ⟨s, hs, (convex_convexHull ℝ _) hx hp
    (sub_nonneg.mpr t.property.2) t.property.1 (by ring)⟩

private theorem segment_pos (t : I) (x : star M v) :
    0 < segmentVector M v t x v := by
  have hx : 0 < x.val.val v := x.property
  have ht0 := t.property.1
  have ht1 := t.property.2
  change 0 < (1 - (t : ℝ)) * x.val.val v + (t : ℝ) * ((Pi.single v (1 : ℝ) : V → ℝ) v)
  rw [Pi.single_eq_same, mul_one]
  by_cases ht : (t : ℝ) < 1
  · have h := mul_pos (sub_pos.mpr ht) hx
    linarith
  · have ht' : (t : ℝ) = 1 := le_antisymm ht1 (le_of_not_gt ht)
    simp [ht']

/-- A strong contraction of the actual relative open star, fixing its vertex
at every time. This uses convexity of each actual face containing that vertex. -/
def contraction (hv : ({v} : Finset V) ∈ M) :
    (ContinuousMap.id (star M v)).HomotopyRel
      (ContinuousMap.const (star M v)
        (⟨vertexPoint M v hv, vertex_mem_star M v hv⟩ : star M v))
      {⟨vertexPoint M v hv, vertex_mem_star M v hv⟩} where
  toFun z := ⟨⟨segmentVector M v z.1 z.2, segment_mem M v z.1 z.2⟩,
    segment_pos M v z.1 z.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))).add
      ((continuous_subtype_val.comp continuous_fst).smul continuous_const)
  map_zero_left := by intro x; apply Subtype.ext; apply Subtype.ext; simp [segmentVector]
  map_one_left := by intro x; apply Subtype.ext; apply Subtype.ext; simp [segmentVector, vertexPoint]
  prop' := by
    intro t x hx
    have hx' : x = ⟨vertexPoint M v hv, vertex_mem_star M v hv⟩ := hx
    subst x
    apply Subtype.ext
    apply Subtype.ext
    ext w
    change (1 - (t : ℝ)) * ((Pi.single v (1 : ℝ) : V → ℝ) w) +
      (t : ℝ) * ((Pi.single v (1 : ℝ) : V → ℝ) w) = (Pi.single v (1 : ℝ) : V → ℝ) w
    ring

end D5.S3.Geometry.FiniteVertexOpenStar
