/- GID: D5/S3/Combinatorics/Graph/StaircaseSlab
   generality: G
   mirror-B: none(waiver:covered-by-chordal-banach-exact-strata-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Oriented triangle coordinates in a staircase between consecutive five-vertex cliques. -/

import OmegaBuild.Commands
import D5.S3.Combinatorics.Graph.FiveLaneRouting

compile_only_with_mathlib

/-! Omega original.

Oriented triangle coordinates in a staircase between consecutive five-vertex
cliques. A cross edge from old label i to new label j is present for j ≤ i.
-/

namespace FiveLaneRouting
open Finset
open scoped BigOperators
noncomputable section

abbrev TriangleSide := Label → Current

def SkewCurrent (q : Current) : Prop := ∀ i j, q j i = -q i j

def OldTriangles (o : TriangleSide) : Prop :=
  (∀ j, SkewCurrent (o j)) ∧ ∀ j i k, min i k < j → o j i k = 0

def NewTriangles (n : TriangleSide) : Prop :=
  (∀ i, SkewCurrent (n i)) ∧ ∀ i j k, i < max j k → n i j k = 0

def diagonal (z : Imbalance) : Current := fun i j => if i = j then z i else 0

def crossBoundary (o n : TriangleSide) : Current :=
  fun i j => (∑ k, o j i k) + ∑ k, n i j k

def projectSide (x : TriangleSide) : Current := fun i j => ∑ k, x k i j

theorem projectSide_skew {x : TriangleSide} (hx : ∀ a, SkewCurrent (x a)) :
    SkewCurrent (projectSide x) := by
  intro i j
  simp [projectSide, hx _ i j]

private theorem skew_sum_zero {q : Current} (hq : SkewCurrent q) :
    (∑ i, ∑ j, q i j) = 0 := by
  have h : (∑ i, ∑ j, q i j) = -(∑ i, ∑ j, q i j) := by
    calc
      _ = ∑ i, ∑ j, q j i := sum_comm
      _ = _ := by
        simp only [← sum_neg_distrib]
        apply sum_congr rfl
        intro i _
        exact sum_congr rfl fun j _ => hq i j
  linarith

/-- Summing the staircase boundary at an old vertex removes the new-pair
contributions. The old-pair triangle coordinates route the row demand. -/
theorem old_projection {o n : TriangleSide} (ho : OldTriangles o) (hn : NewTriangles n)
    {z : Imbalance} (h : crossBoundary o n = diagonal z) :
    Routes (projectSide o) z := by
  refine ⟨projectSide_skew ho.1, fun i => ?_⟩
  have hsum := congrArg (fun q : Current => ∑ j, q i j) h
  simp only [crossBoundary, diagonal, sum_ite_eq, mem_univ, ite_true, sum_add_distrib,
    skew_sum_zero (hn.1 i), add_zero] at hsum
  change ∑ k, ∑ j, o j i k = z i
  rwa [sum_comm]

/-- Summing at a new vertex removes the old-pair terms and gives the second
independent routing of the same demand. -/
theorem new_projection {o n : TriangleSide} (ho : OldTriangles o) (hn : NewTriangles n)
    {z : Imbalance} (h : crossBoundary o n = diagonal z) :
    Routes (projectSide n) z := by
  refine ⟨projectSide_skew hn.1, fun j => ?_⟩
  have hsum := congrArg (fun q : Current => ∑ i, q i j) h
  simp only [crossBoundary, diagonal, sum_ite_eq', mem_univ, ite_true, sum_add_distrib,
    skew_sum_zero (ho.1 j), zero_add] at hsum
  change ∑ k, ∑ i, n i j k = z j
  rwa [sum_comm]

def slideOld (q : Current) : TriangleSide :=
  fun j i k => if j = min i k then q i k else 0

def slideNew (q : Current) : TriangleSide :=
  fun i j k => if i = max j k then q j k else 0

theorem slideOld_valid {q : Current} (hq : SkewCurrent q) : OldTriangles (slideOld q) := by
  refine ⟨fun j i k => ?_, fun j i k hj => ?_⟩
  · simp only [slideOld, min_comm k i, hq i k]
    split <;> simp
  · simp [slideOld, hj.ne']

theorem slideNew_valid {q : Current} (hq : SkewCurrent q) : NewTriangles (slideNew q) := by
  refine ⟨fun i j k => ?_, fun i j k hi => ?_⟩
  · simp only [slideNew, max_comm k j, hq j k]
    split <;> simp
  · simp [slideNew, hi.ne]

theorem project_slideOld (q : Current) : projectSide (slideOld q) = q := by
  funext i j
  simp [projectSide, slideOld]

theorem project_slideNew (q : Current) : projectSide (slideNew q) = q := by
  funext i j
  simp [projectSide, slideNew]

/-- A pair route is represented by the two triangles on its canonical
staircase strip. All off-lane cross edges cancel. -/
theorem crossBoundary_slides {q : Current} {z : Imbalance} (h : Routes q z) :
    crossBoundary (slideOld q) (slideNew q) = diagonal z := by
  funext i j
  rcases lt_trichotomy i j with hij | he | hji
  · have ho (k : Label) : j ≠ min i k := (min_le_left i k).trans_lt hij |>.ne'
    have hn (k : Label) : i ≠ max j k := (hij.trans_le (le_max_left j k)).ne
    simp [crossBoundary, slideOld, slideNew, diagonal, hij.ne, ho, hn]
  · subst j
    have hd : q i i = 0 := by linarith [h.1 i i]
    have he (k : Label) :
        (if i = min i k then q i k else 0) + (if i = max i k then q i k else 0) = q i k := by
      rcases lt_trichotomy i k with h | he | h
      · simp [min_eq_left h.le, max_eq_right h.le, h.ne]
      · subst k
        simp [hd]
      · simp [min_eq_right h.le, max_eq_left h.le, h.ne']
    simp only [crossBoundary, slideOld, slideNew, diagonal, ite_true, ← sum_add_distrib, he, h.2 i]
  · have ho (k : Label) : j = min i k ↔ k = j := by
      constructor
      · intro h
        rcases le_total i k with hle | hle
        · exact (hji.ne (h.trans (min_eq_left hle))).elim
        · exact ((min_eq_right hle).symm.trans h.symm)
      · rintro rfl
        exact (min_eq_right hji.le).symm
    have hn (k : Label) : i = max j k ↔ k = i := by
      constructor
      · intro h
        rcases le_total j k with hle | hle
        · exact ((max_eq_right hle).symm.trans h.symm)
        · exact (hji.ne' (h.trans (max_eq_left hle))).elim
      · rintro rfl
        exact (max_eq_right hji.le).symm
    simp only [crossBoundary, slideOld, slideNew, ho, hn, diagonal, hji.ne', ite_false,
      sum_ite_eq', mem_univ, ite_true, h.1 j i, neg_add_cancel]

def sideCost (c : TriangleSide) : ℝ := ∑ k, cost (c k)

def sideCovered (c p : TriangleSide) : Prop := ∀ k, covered (c k) (p k)

theorem projectSide_covered {c p : TriangleSide} (hp : sideCovered c p) :
    covered (projectSide c) (projectSide p) := by
  intro i j
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => hp k i j)

theorem projectSide_cost (c : TriangleSide) : cost (projectSide c) = sideCost c := by
  simp only [cost, projectSide, sideCost, sum_div]
  calc
    (∑ i : Label, ∑ j : Label, ∑ k : Label, c k i j / 2) =
        ∑ i : Label, ∑ k : Label, ∑ j : Label, c k i j / 2 :=
      sum_congr rfl fun _ _ => sum_comm
    _ = _ := sum_comm

theorem slideOld_covered {c q : Current} (h : covered c q) :
    sideCovered (slideOld c) (slideOld q) := by
  intro k i j
  by_cases h' : k = min i j
  · simpa [slideOld, h'] using h i j
  · simp [slideOld, h']

theorem slideNew_covered {c q : Current} (h : covered c q) :
    sideCovered (slideNew c) (slideNew q) := by
  intro k i j
  by_cases h' : k = max i j
  · simpa [slideNew, h'] using h i j
  · simp [slideNew, h']

end
end FiveLaneRouting
