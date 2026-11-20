/- GID: D5/S1/Dynamics/Shadowing/FiniteGraphAffineRealization
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/FiniteGraphAffineRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The affine realization of a finite simple graph in the sup metric. -/

import D5.S1.Dynamics.Shadowing.ExactPendantObstruction
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
Each vertex is a coordinate unit vector, and each edge is the closed segment
between its endpoints. Coordinate evaluation controls the sup metric and detects
the open tip of a pendant edge.
-/

open Set

namespace D5.S1.Dynamics.Shadowing.FiniteGraphAffineRealization

noncomputable section

variable {V : Type*} [DecidableEq V]

/-- The standard basis vector at a vertex. -/
def vertexVector (v : V) : V → ℝ := fun i => if i = v then 1 else 0

/-- The affine point at parameter `t` measured from `u` toward `v`. -/
def edgeVector (u v : V) (t : ℝ) : V → ℝ :=
  fun i => (1 - t) * vertexVector u i + t * vertexVector v i

@[simp] theorem edgeVector_left {u v : V} (h : u ≠ v) (t : ℝ) :
    edgeVector u v t u = 1 - t := by
  simp [edgeVector, vertexVector, h]

@[simp] theorem edgeVector_right {u v : V} (h : u ≠ v) (t : ℝ) :
    edgeVector u v t v = t := by
  simp [edgeVector, vertexVector, h.symm]

theorem edgeVector_other {u v i : V} (hu : i ≠ u) (hv : i ≠ v) (t : ℝ) :
    edgeVector u v t i = 0 := by
  simp [edgeVector, vertexVector, hu, hv]

@[simp] theorem edgeVector_zero (u v : V) : edgeVector u v 0 = vertexVector u := by
  funext i
  simp [edgeVector]

@[simp] theorem edgeVector_one (u v : V) : edgeVector u v 1 = vertexVector v := by
  funext i
  simp [edgeVector]

theorem edgeVector_reverse (u v : V) (t : ℝ) :
    edgeVector v u (1 - t) = edgeVector u v t := by
  funext i
  simp only [edgeVector]
  ring

/-- A positive coordinate of an affine edge point must be an endpoint coordinate. -/
theorem endpoint_of_pos {u v i : V} {t : ℝ} (h : 0 < edgeVector u v t i) :
    i = u ∨ i = v := by
  by_contra! hn
  rw [edgeVector_other hn.1 hn.2] at h
  exact (lt_irrefl 0) h

/-- An interior point of a segment determines its edge up to reversal. -/
theorem endpoints_of_interior_eq {u v a b : V} {s t : ℝ}
    (huv : u ≠ v) (hs₀ : 0 < s) (hs₁ : s < 1)
    (he : edgeVector u v s = edgeVector a b t) :
    (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
  have hu : 0 < edgeVector a b t u := by
    rw [← he, edgeVector_left huv]
    exact sub_pos.mpr hs₁
  have hv : 0 < edgeVector a b t v := by
    rw [← he, edgeVector_right huv]
    exact hs₀
  rcases endpoint_of_pos hu with hu | hu <;> rcases endpoint_of_pos hv with hv | hv
  · exact (huv (hu.trans hv.symm)).elim
  · exact Or.inl ⟨hu, hv⟩
  · exact Or.inr ⟨hu, hv⟩
  · exact (huv (hu.trans hv.symm)).elim

variable (G : SimpleGraph V)

/-- The vertices and the closed affine segments of all adjacent pairs. -/
def carrier : Set (V → ℝ) :=
  range vertexVector ∪
    ⋃ e : {e : V × V // G.Adj e.1 e.2},
      range (fun t : Icc (0 : ℝ) 1 => edgeVector e.val.1 e.val.2 t)

/-- The realized graph, with the subspace topology and sup metric for finite `V`. -/
abbrev Space := ↥(carrier G)

/-- The inclusion of a vertex, including isolated vertices. -/
def vertex (v : V) : Space G :=
  ⟨vertexVector v, Or.inl ⟨v, rfl⟩⟩

/-- The closed unit-interval chart of an oriented edge. -/
def edgeChart {u v : V} (h : G.Adj u v) (t : Icc (0 : ℝ) 1) : Space G :=
  ⟨edgeVector u v t, Or.inr (mem_iUnion.mpr ⟨⟨(u, v), h⟩, t, rfl⟩)⟩

/-- Evaluation at a vertex coordinate of the realization. -/
def coord (x : Space G) (i : V) : ℝ := (x : V → ℝ) i

@[simp] theorem coord_edgeChart {u v : V} (h : G.Adj u v) (t : Icc (0 : ℝ) 1) (i : V) :
    coord G (edgeChart G h t) i = edgeVector u v t i := rfl

@[simp] theorem edgeChart_zero {u v : V} (h : G.Adj u v) :
    edgeChart G h ⟨0, le_rfl, zero_le_one⟩ = vertex G u :=
  Subtype.ext (edgeVector_zero u v)

@[simp] theorem edgeChart_one {u v : V} (h : G.Adj u v) :
    edgeChart G h ⟨1, zero_le_one, le_rfl⟩ = vertex G v :=
  Subtype.ext (edgeVector_one u v)

theorem edgeChart_reverse {u v : V} (h : G.Adj u v) (t : Icc (0 : ℝ) 1) :
    edgeChart G h.symm ⟨1 - (t : ℝ), sub_nonneg.mpr t.2.2, sub_le_self _ t.2.1⟩ =
      edgeChart G h t :=
  Subtype.ext (edgeVector_reverse u v t)

theorem continuous_coord (i : V) : Continuous (fun x : Space G => coord G x i) :=
  (continuous_apply i).comp continuous_subtype_val

theorem continuous_edgeVector (u v : V) : Continuous (edgeVector u v) := by
  apply continuous_pi
  intro i
  change Continuous (fun t : ℝ => (1 - t) * vertexVector u i + t * vertexVector v i)
  exact ((continuous_const.sub continuous_id).mul continuous_const).add
    (continuous_id.mul continuous_const)

theorem continuous_edgeChart {u v : V} (h : G.Adj u v) : Continuous (edgeChart G h) :=
  ((continuous_edgeVector u v).comp continuous_subtype_val).subtype_mk _

theorem isCompact_carrier [Finite V] : IsCompact (carrier G) := by
  apply (finite_range vertexVector).isCompact.union
  exact isCompact_iUnion fun e =>
    isCompact_range ((continuous_edgeVector e.val.1 e.val.2).comp continuous_subtype_val)

instance [Finite V] : CompactSpace (Space G) :=
  isCompact_iff_compactSpace.mp (isCompact_carrier G)

section Metric

variable [Fintype V]

/-- The sup distance on one affine edge is the absolute parameter difference. -/
theorem dist_edgeVector {u v : V} (h : u ≠ v) (s t : ℝ) :
    dist (edgeVector u v s) (edgeVector u v t) = |s - t| := by
  apply le_antisymm
  · apply (dist_pi_le_iff (abs_nonneg (s - t))).mpr
    intro i
    by_cases hi : i = u
    · subst i
      rw [edgeVector_left h, edgeVector_left h, Real.dist_eq,
        show 1 - s - (1 - t) = t - s by ring, abs_sub_comm t s]
    · by_cases hj : i = v
      · subst i
        rw [edgeVector_right h, edgeVector_right h, Real.dist_eq]
      · rw [edgeVector_other hi hj, edgeVector_other hi hj, dist_self]
        exact abs_nonneg _
  · simpa only [edgeVector_right h, Real.dist_eq] using
      dist_le_pi_dist (edgeVector u v s) (edgeVector u v t) v

/-- The sup distance between distinct germs based at one vertex is the larger parameter. -/
theorem dist_edgeVector_incident {u v w : V} (huv : u ≠ v) (huw : u ≠ w)
    (hvw : v ≠ w) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    dist (edgeVector u v s) (edgeVector u w t) = max s t := by
  apply le_antisymm
  · apply (dist_pi_le_iff (hs.trans (le_max_left s t))).mpr
    intro i
    by_cases hi : i = u
    · subst i
      rw [edgeVector_left huv, edgeVector_left huw, Real.dist_eq,
        show 1 - s - (1 - t) = t - s by ring, abs_le]
      constructor
      · linarith [le_max_left s t]
      · linarith [le_max_right s t]
    · by_cases hj : i = v
      · subst i
        rw [edgeVector_right huv, edgeVector_other huv.symm hvw, Real.dist_eq, sub_zero,
          abs_of_nonneg hs]
        exact le_max_left _ _
      · by_cases hk : i = w
        · subst i
          rw [edgeVector_other huw.symm hvw.symm, edgeVector_right huw, Real.dist_eq,
            abs_sub_comm 0 t, sub_zero, abs_of_nonneg ht]
          exact le_max_right _ _
        · rw [edgeVector_other hi hj, edgeVector_other hi hk, dist_self]
          exact hs.trans (le_max_left _ _)
  · apply max_le
    · simpa only [edgeVector_right huv, edgeVector_other huv.symm hvw, Real.dist_eq,
        sub_zero, abs_of_nonneg hs] using
        dist_le_pi_dist (edgeVector u v s) (edgeVector u w t) v
    · simpa only [edgeVector_other huw.symm hvw.symm, edgeVector_right huw, Real.dist_eq,
        abs_sub_comm 0 t, sub_zero, abs_of_nonneg ht] using
        dist_le_pi_dist (edgeVector u v s) (edgeVector u w t) w

theorem dist_edgeChart {u v : V} (h : G.Adj u v) (s t : Icc (0 : ℝ) 1) :
    dist (edgeChart G h s) (edgeChart G h t) = |(s : ℝ) - (t : ℝ)| :=
  dist_edgeVector h.ne s t

/-- Each closed edge chart preserves distances. -/
theorem isometry_edgeChart {u v : V} (h : G.Adj u v) : Isometry (edgeChart G h) :=
  Isometry.of_dist_eq fun s t => (dist_edgeChart G h s t).trans (Real.dist_eq _ _).symm

theorem dist_edgeChart_incident {u v w : V} (hv : G.Adj u v) (hw : G.Adj u w)
    (hvw : v ≠ w) (s t : Icc (0 : ℝ) 1) :
    dist (edgeChart G hv s) (edgeChart G hw t) = max (s : ℝ) (t : ℝ) :=
  dist_edgeVector_incident hv.ne hw.ne hvw s.2.1 t.2.1

end Metric

/-- At a vertex with one neighbor the positive coordinate set is its open pendant tip. -/
theorem tip_eq_pos_coord {leaf root : V} (h : G.Adj root leaf)
    (hunique : ∀ w, G.Adj leaf w → w = root) :
    edgeChart G h '' {t | 0 < (t : ℝ)} = {x | 0 < coord G x leaf} := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    change 0 < (t : ℝ) at ht
    change 0 < coord G (edgeChart G h t) leaf
    simpa only [coord_edgeChart, edgeVector_right h.ne] using ht
  · intro hx
    rcases x.property with hxv | hxe
    · obtain ⟨v, hv⟩ := hxv
      have hp : 0 < vertexVector v leaf := by
        change 0 < (x : V → ℝ) leaf at hx
        rwa [← hv] at hx
      have hvl : v = leaf := by
        by_contra hn
        simp [vertexVector, Ne.symm hn] at hp
      subst v
      refine ⟨⟨1, zero_le_one, le_rfl⟩, show (0 : ℝ) < 1 from zero_lt_one, ?_⟩
      rw [edgeChart_one]
      exact Subtype.ext hv
    · obtain ⟨e, t, he⟩ := mem_iUnion.mp hxe
      obtain ⟨⟨u, v⟩, huv⟩ := e
      change G.Adj u v at huv
      change edgeVector u v t = (x : V → ℝ) at he
      have hp : 0 < edgeVector u v t leaf := by
        change 0 < (x : V → ℝ) leaf at hx
        rwa [he]
      rcases endpoint_of_pos hp with hlu | hlv
      · subst u
        have hvr : v = root := hunique v huv
        subst v
        rw [edgeVector_left h.ne.symm] at hp
        let s : Icc (0 : ℝ) 1 := ⟨1 - (t : ℝ), hp.le, sub_le_self _ t.2.1⟩
        refine ⟨s, hp, Subtype.ext ?_⟩
        exact (edgeVector_reverse leaf root t).trans he
      · subst v
        have hur : u = root := hunique u huv.symm
        subst u
        rw [edgeVector_right h.ne] at hp
        exact ⟨t, hp, Subtype.ext he⟩

variable [Fintype V]

/-- A vertex of degree one yields a pendant arc based at its unique neighbor. -/
def pendantArcOfDegreeOne (leaf : V) [Fintype (G.neighborSet leaf)]
    (hdeg : G.degree leaf = 1) : PendantArc (Space G) := by
  classical
  let root := Classical.choose (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg)
  have hroot := Classical.choose_spec (SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdeg)
  have h : G.Adj root leaf := hroot.1.symm
  refine ⟨edgeChart G h, continuous_edgeChart G h, (isometry_edgeChart G h).injective, ?_⟩
  rw [tip_eq_pos_coord G h hroot.2]
  exact isOpen_lt continuous_const (continuous_coord G leaf)

end

end D5.S1.Dynamics.Shadowing.FiniteGraphAffineRealization
