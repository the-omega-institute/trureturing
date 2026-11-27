/- GID: D5/S3/Topology/GraphSubdivisionPositions
   generality: G
   mirror-B: D5/B/S3/Topology/GraphSubdivisionPositions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: Dyadic positions on graph subdivisions preserve original support. -/

import Batteries.Tactic.OpenPrivate
import D5.S3.Geometry.FiniteVertexCylinder
import D5.S3.Topology.GraphSubdivisionIntervals

/-! Dyadic positions on the actual ordinary subdivisions of a finite graph. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Topology.GraphSubdivisionPositions

open BarycentricBaseRigidity (faceImage retainedVertex)
open BarycentricGraphDistance (Face Vertex)
open BarycentricNeighborhoodIteration (iteratedAmbient iteratedSubcomplex)
open GraphSubdivisionIntervals (graph_subdivision_intervals_oriented originalSupport
  originalSupport_mem originalSupport_retained mem_iteratedSubcomplex_iff faceImage_singleton)
open private iterated_point_face from D5.S3.Topology.GraphSubdivisionIntervals
open PathContiguity (intervalComplex)
open D5.S3.Geometry.FiniteConeCollapse (faceSimplex realization_mem_iff)
open D5.S3.Geometry.FiniteAlexanderDualCollapse (simplex)
open D5.S3.Geometry.FiniteVertexCylinder (Space vertexPoint)
open scoped BigOperators

noncomputable section

variable {X : Type} [DecidableEq X]

private def edgeCoordinates (x y : X) (t : ℝ) (w : X) : ℝ :=
  (if w = x then 1 - t else 0) + (if w = y then t else 0)

private theorem edgeCoordinates_simplex [Fintype X] (x y : X) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    edgeCoordinates x y t ∈ faceSimplex {x, y} := by
  refine ⟨fun w => add_nonneg ?_ ?_, ?_, ?_⟩
  · split <;> linarith
  · split <;> linarith
  · simp [edgeCoordinates, Finset.sum_add_distrib, sub_add_cancel]
  · intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hw
    simp [edgeCoordinates, hw.1, hw.2]

private theorem edgeCoordinates_bound (x y w : X) (hx : x ≠ y) (s t : ℝ) :
    |edgeCoordinates x y s w - edgeCoordinates x y t w| ≤ |s - t| := by
  by_cases h₁ : w = x
  · have h₂ : w ≠ y := fun h => hx (h₁.symm.trans h)
    simpa only [edgeCoordinates, ite_eq_left h₁, ite_eq_right h₂, add_zero, sub_sub_sub_cancel_left,
      abs_sub_comm] using (le_refl |s - t|)
  · by_cases h₂ : w = y
    · simp [edgeCoordinates, h₂, hx.symm]
    · simp [edgeCoordinates, h₁, h₂]

/-- In every ordinary subdivision of a graph there are compatible geometric
positions on the original edges. The positions remain in the original
support, and any two in one subdivided face differ by at most its dyadic
mesh in every coordinate. -/
theorem exists_positions [Fintype X] (A : PreAbstractSimplicialComplex X)
    (hdim : ∀ s ∈ A, (s : Finset X).card ≤ 2) (m : ℕ)
    (left right : {e : Face A // e.val.val.card = 2} → Vertex A)
    (horient : ∀ e, e.val.val = {(left e).val, (right e).val} ∧ left e ≠ right e) :
    let P := (iteratedAmbient A m).2
    ∃ pos : Vertex P → Space A,
      (∀ v w, w ∉ originalSupport A m {v.val} → (pos v).val w = 0) ∧
      ∀ (s : Finset _) (_ : s ∈ P) (u v : Vertex P), u.val ∈ s → v.val ∈ s → ∀ w,
        |(pos u).val w - (pos v).val w| ≤ 1 / (2 : ℝ) ^ m := by
  intro P
  obtain ⟨chart, hinj, hend, hfaces, hdisjoint, hcover⟩ :=
    graph_subdivision_intervals_oriented A hdim m left right (fun e =>
      ⟨(horient e).1.trans (by ext w; simp only [Finset.mem_insert, Finset.mem_singleton]),
        (horient e).2⟩)
  let E := {e : Face A // e.val.val.card = 2}
  let N := 2 ^ m
  let I := Vertex (intervalComplex N)
  let t (i : I) : ℝ := (i.val : ℝ) / (N : ℝ)
  have hN : (0 : ℝ) < N := by dsimp [N]; positivity
  have coord (i : I) : 0 ≤ t i ∧ t i ≤ 1 := by
    refine ⟨by dsimp [t]; positivity, (div_le_iff₀ hN).2 ?_⟩
    simpa only [one_mul, Nat.cast_le] using i.property.2.1 _ (Finset.mem_singleton_self _)
  let point (e : E) (i : I) : Space A :=
    ⟨edgeCoordinates (left e).val (right e).val (t i), (realization_mem_iff A _).2
      ⟨{(left e).val, (right e).val}, (horient e).1 ▸ e.val.property,
        edgeCoordinates_simplex _ _ (coord i).1 (coord i).2⟩⟩
  let atVertex (x : Vertex A) : Space A := vertexPoint A x.val x.property
  have atEnd (e : E) (i : I) (he : i.val = 0 ∨ i.val = N) : ∃ x : Vertex A,
      chart e i = retainedVertex m x ∧ point e i = atVertex x := by
    rcases he with h | h
    · refine ⟨left e, (hend e i).1 h, Subtype.ext (funext fun w => ?_)⟩
      simp [point, atVertex, vertexPoint, edgeCoordinates, t, h, Pi.single_apply]
    · refine ⟨right e, (hend e i).2 h, Subtype.ext (funext fun w => ?_)⟩
      simp [point, atVertex, vertexPoint, edgeCoordinates, t, h, ne_of_gt hN, Pi.single_apply]
  have solePoint (u : Vertex P) (x : Vertex A)
      (hs : originalSupport A m {u.val} ⊆ {x.val}) : u = retainedVertex m x := by
    have hp := (mem_iteratedSubcomplex_iff (B := simplex {x.val}) m u.property).2
      ⟨(A.isRelLowerSet_faces (originalSupport_mem m u.property)).1, hs⟩
    exact Subtype.ext (Finset.singleton_injective (iterated_point_face m x hp))
  have supported (e : E) (i : I) : originalSupport A m {(chart e i).val} ⊆ e.val.val := by
    have he := (hfaces e _).2 ⟨{i.val}, i.property, faceImage_singleton (chart e) i⟩
    exact ((mem_iteratedSubcomplex_iff m (chart e i).property).1 he).2
  have agreement (e d : E) (i j : I) (h : chart e i = chart d j) : point e i = point d j := by
    by_cases hi : i.val = 0 ∨ i.val = N
    · by_cases hj : j.val = 0 ∨ j.val = N
      · obtain ⟨x, hx, hpx⟩ := atEnd e i hi
        obtain ⟨y, hy, hpy⟩ := atEnd d j hj
        rw [hx, hy] at h
        have hxy := congrArg (fun v : Vertex P => originalSupport A m {v.val}) h
        simp only [originalSupport_retained, Finset.singleton_inj] at hxy
        rw [hpx, hpy, show x = y from Subtype.ext hxy]
      · have hed := hdisjoint d e j i (fun h => hj (Or.inl h)) (fun h => hj (Or.inr h)) h.symm
        subst d
        rw [hinj e h]
    · have hed := hdisjoint e d i j (fun h => hi (Or.inl h)) (fun h => hi (Or.inr h)) h
      subst d
      rw [hinj e h]
  let onChart (v : Vertex P) : Prop := ∃ a : E × I, chart a.1 a.2 = v
  have isolated (v : Vertex P) (hv : ¬ onChart v) : ∃ x : Vertex A, v = retainedVertex m x := by
    rcases hcover {v.val} v.property with ⟨x, _, he, _⟩ | ⟨e, _, _, _, honto⟩
    · exact ⟨x, Subtype.ext (Finset.singleton_injective he)⟩
    · obtain ⟨i, _, hi⟩ := honto v (Finset.mem_singleton_self _)
      exact (hv ⟨(e, i), hi⟩).elim
  classical
  let pos (v : Vertex P) : Space A :=
    if h : onChart v then point h.choose.1 h.choose.2 else atVertex (isolated v h).choose
  have trace (e : E) (i : I) : pos (chart e i) = point e i := by
    have h : onChart (chart e i) := ⟨(e, i), rfl⟩
    simpa only [pos, dite_eq_left h] using
      agreement h.choose.1 e h.choose.2 i h.choose_spec
  refine ⟨pos, ?_, ?_⟩
  · intro v w hw
    by_cases hv : onChart v
    · obtain ⟨⟨e, i⟩, rfl⟩ := hv
      rw [trace]
      have he := supported e i
      rw [(horient e).1] at he
      have hdistinct : (left e).val ≠ (right e).val :=
        fun h => (horient e).2 (Subtype.ext h)
      by_cases hwl : w = (left e).val
      · have hs : originalSupport A m {(chart e i).val} ⊆ {(right e).val} := by
          intro a ha
          rcases Finset.mem_insert.mp (he ha) with h | h
          · exact (hw ((h.trans hwl.symm) ▸ ha)).elim
          · exact h
        have hh := solePoint _ (right e) hs
        let j : I := ⟨N, by
          change ({N} : Finset ℕ).Nonempty ∧ _ ∧ _
          simp⟩
        have hij := hinj e (hh.trans ((hend e j).2 rfl).symm)
        simp [point, edgeCoordinates, hwl, hdistinct, hdistinct.symm, hij, j, t, ne_of_gt hN]
      · by_cases hwr : w = (right e).val
        · have hs : originalSupport A m {(chart e i).val} ⊆ {(left e).val} := by
            intro a ha
            rcases Finset.mem_insert.mp (he ha) with h | h
            · exact Finset.mem_singleton.mpr h
            · exact (hw ((Finset.mem_singleton.mp h).trans hwr.symm ▸ ha)).elim
          have hh := solePoint _ (left e) hs
          let j : I := ⟨0, by
            change ({0} : Finset ℕ).Nonempty ∧ _ ∧ _
            simp⟩
          have hij := hinj e (hh.trans ((hend e j).1 rfl).symm)
          simp [point, edgeCoordinates, hwr, hdistinct.symm, hij, j, t]
        · simp [point, edgeCoordinates, hwl, hwr]
    · have hx := (isolated v hv).choose_spec
      rw [hx, originalSupport_retained, Finset.mem_singleton] at hw
      simp [pos, hv, atVertex, vertexPoint, Pi.single_apply, hw]
  · intro s hs u v hu hv w
    rcases hcover s hs with ⟨_, _, he, _⟩ | ⟨e, _, ht, _, honto⟩
    · have huv : u = v := Subtype.ext
        ((Finset.mem_singleton.mp (he ▸ hu)).trans (Finset.mem_singleton.mp (he ▸ hv)).symm)
      rw [huv, sub_self, abs_zero]
      positivity
    · obtain ⟨i, hi, rfl⟩ := honto u hu
      obtain ⟨j, hj, rfl⟩ := honto v hv
      rw [trace, trace]
      have hxy : (left e).val ≠ (right e).val := fun h => (horient e).2 (Subtype.ext h)
      refine (edgeCoordinates_bound _ _ w hxy _ _).trans ?_
      change |(i.val : ℝ) / (N : ℝ) - (j.val : ℝ) / (N : ℝ)| ≤ 1 / (2 : ℝ) ^ m
      rw [← sub_div, abs_div, abs_of_pos hN]
      have hcast : (N : ℝ) = (2 : ℝ) ^ m := by simp [N]
      rw [← hcast]
      apply (div_le_div_iff_of_pos_right hN).2
      have h₁ : (i.val : ℝ) ≤ (j.val : ℝ) + 1 := by exact_mod_cast ht.2.2 _ hi _ hj
      have h₂ : (j.val : ℝ) ≤ (i.val : ℝ) + 1 := by exact_mod_cast ht.2.2 _ hj _ hi
      exact abs_le.mpr ⟨by linarith, by linarith⟩

end

end D5.S3.Topology.GraphSubdivisionPositions
