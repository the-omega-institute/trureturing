/- GID: D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Walks/CompleteSubdivisionMetric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Metric]
   utility: none
   digest: Actual shortest distances in the once-subdivision of a complete graph. -/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionMetric

open SimpleGraph

/-- One new vertex for every unordered pair of distinct original vertices. -/
abbrev Midpoint (n : ℕ) := {e : Sym2 (Fin n) // ¬ e.IsDiag}

/-- The full vertex set includes both original vertices and all subdivision vertices. -/
abbrev Vertex (n : ℕ) := Fin n ⊕ Midpoint n

/-- Every original complete-graph edge is replaced by its two incidences. -/
def graph (n : ℕ) : SimpleGraph (Vertex n) where
  Adj x y := match x, y with
    | .inl u, .inr e => u ∈ e.val
    | .inr e, .inl u => u ∈ e.val
    | _, _ => False
  symm.symm x y := by cases x <;> cases y <;> simp
  loopless.irrefl x := by cases x <;> simp

variable {n : ℕ}

/-- The unique midpoint on the original edge with distinct endpoints `u,v`. -/
def subdivisionVertex (u v : Fin n) (h : u ≠ v) : Midpoint n :=
  ⟨s(u,v), by simpa using h⟩

theorem midpoint_swap (u v : Fin n) (h : u ≠ v) :
    subdivisionVertex u v h = subdivisionVertex v u h.symm := by
  apply Subtype.ext
  exact Sym2.eq_swap

@[simp] theorem adj_original_midpoint (u : Fin n) (e : Midpoint n) :
    (graph n).Adj (.inl u) (.inr e) ↔ u ∈ e.val := Iff.rfl

private def originalWalk (u v : Fin n) : (graph n).Walk (.inl u) (.inl v) :=
  if h : u = v then h ▸ .nil else
    .cons (show (graph n).Adj (.inl u) (.inr (subdivisionVertex u v h)) from
      Sym2.mem_mk_left u v)
      (.cons (show (graph n).Adj (.inr (subdivisionVertex u v h)) (.inl v) from
        Sym2.mem_mk_right u v) .nil)

theorem reachable (x y : Vertex n) : (graph n).Reachable x y := by
  have oo (u v : Fin n) : (graph n).Reachable (.inl u) (.inl v) :=
    ⟨originalWalk u v⟩
  have mo (e : Midpoint n) : (graph n).Adj (.inr e) (.inl e.val.out.1) :=
    Sym2.out_fst_mem e.val
  cases x with
  | inl u =>
    cases y with
    | inl v => exact oo u v
    | inr f => exact (oo u f.val.out.1).trans (mo f).symm.reachable
  | inr e =>
    cases y with
    | inl v => exact (mo e).reachable.trans (oo e.val.out.1 v)
    | inr f =>
      exact (mo e).reachable.trans
        ((oo e.val.out.1 f.val.out.1).trans (mo f).symm.reachable)

theorem dist_original_original (u v : Fin n) :
    (graph n).dist (.inl u) (.inl v) = if u = v then 0 else 2 := by
  split_ifs with h
  · subst v; exact SimpleGraph.dist_self
  · have upper := SimpleGraph.dist_le (originalWalk u v)
    have lower := (reachable (.inl u) (.inl v)).one_lt_dist_of_ne_of_not_adj
      (by simpa using h) (by simp [graph])
    simp [originalWalk, h] at upper
    omega

theorem dist_original_midpoint (u : Fin n) (e : Midpoint n) :
    (graph n).dist (.inl u) (.inr e) = if u ∈ e.val then 1 else 3 := by
  classical
  split_ifs with h
  · exact SimpleGraph.dist_eq_one_iff_adj.mpr ((adj_original_midpoint u e).mpr h)
  · have near : (graph n).dist (.inl e.val.out.1) (.inr e) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr (Sym2.out_fst_mem e.val)
    have upper := (reachable (.inl u) (.inl e.val.out.1)).dist_triangle_left (.inr e)
    rw [dist_original_original, near] at upper
    have far : 2 < (graph n).edist (.inl u) (.inr e) := by
      apply SimpleGraph.two_lt_edist_iff.mpr
      refine ⟨by simp, h, ?_⟩
      ext z
      cases z <;> simp [SimpleGraph.mem_commonNeighbors, graph]
    rw [← (reachable (.inl u) (.inr e)).coe_dist_eq_edist] at far
    have lower : 2 < (graph n).dist (.inl u) (.inr e) := by exact_mod_cast far
    split_ifs at upper <;> omega

theorem dist_midpoint_midpoint (e f : Midpoint n) :
    (graph n).dist (.inr e) (.inr f) =
      if e = f then 0 else if ∃ u, u ∈ e.val ∧ u ∈ f.val then 2 else 4 := by
  classical
  split_ifs with heq hmeet
  · subst f; exact SimpleGraph.dist_self
  · have ed : (graph n).edist (.inr e) (.inr f) = 2 := by
      apply SimpleGraph.edist_eq_two_iff.mpr
      refine ⟨by simpa using heq, by simp [graph], ?_⟩
      obtain ⟨u, hu, hf⟩ := hmeet
      exact ⟨.inl u, hu, hf⟩
    rw [← (reachable (.inr e) (.inr f)).coe_dist_eq_edist] at ed
    exact_mod_cast ed
  · have left : (graph n).dist (.inr e) (.inl e.val.out.1) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr (Sym2.out_fst_mem e.val)
    have hf : e.val.out.1 ∉ f.val := fun h =>
      hmeet ⟨_, Sym2.out_fst_mem e.val, h⟩
    have upper := (reachable (.inr e) (.inl e.val.out.1)).dist_triangle_left (.inr f)
    rw [left, dist_original_midpoint, if_neg hf] at upper
    obtain ⟨p, hp⟩ := (reachable (.inr e) (.inr f)).exists_walk_length_eq_dist
    have lower : 4 ≤ p.length := by
      cases p with
      | nil => exact (heq rfl).elim
      | @cons _ z _ hadj q =>
        cases z with
        | inr z => simp [graph] at hadj
        | inl u =>
          have hu : u ∉ f.val := fun h => hmeet ⟨u, hadj, h⟩
          have hq := SimpleGraph.dist_le q
          rw [dist_original_midpoint, if_neg hu] at hq
          simp only [SimpleGraph.Walk.length_cons]
          omega
    omega

end D5.S3.Combinatorics.Graph.Walks.CompleteSubdivisionMetric
