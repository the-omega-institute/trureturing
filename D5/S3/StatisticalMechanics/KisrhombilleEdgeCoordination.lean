/- GID: D5/S3/StatisticalMechanics/KisrhombilleEdgeCoordination
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/KisrhombilleEdgeCoordination
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Simplex inclusion distances from an edge of the triangular lattice. -/

/-
admission_basis: open-problem-resolution (#27078; Proved)
escape_witness: none (external open-problem resolution)
Direct frozen dependencies: KisrhombilleFaceCoordination (Simplex, support, graph,
polygon, polygon_mem, polygon_card, distance, shell_finite);
TeaCoordinationSequence (hexagon, hexagon_mem, hexagon_card);
VertexPositionRatioRefutation (potential_dist).
-/

import D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination
import D5.S3.StatisticalMechanics.TeaCoordinationSequence
import D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation

noncomputable section
open scoped BigOperators

namespace D5.S3.StatisticalMechanics.KisrhombilleEdgeCoordination

open KisrhombilleFaceCoordination (Simplex support graph polygon polygon_mem polygon_card)

/-- The horizontal edge with vertices (0,0) and (1,0). -/
def root : Simplex := (1, 0, 0)

/-- Genuine shortest-walk distance from the specified edge. -/
def distance (s : Simplex) : ℕ := graph.dist root s

/-- The literal coordination sequence. -/
def a (n : ℕ) : ℕ := Set.ncard {s : Simplex | distance s = n}

private def vertexScore (i j : ℤ) : ℤ :=
  max 1 (max (1 - 2*i) (max (2*i - 1) (max (-2*j)
    (max (2*j) (max (1 - 2*(i+j)) (2*(i+j) - 1))))))

private def upScore (i j : ℤ) : ℤ :=
  max 1 (max (-2*i) (max (2*i) (max (-2*j - 1)
    (max (2*j + 1) (max (-2*(i+j)) (2*(i+j)))))))

private def downScore (i j : ℤ) : ℤ :=
  max 1 (max (-2*i) (max (2*i) (max (-2*j - 1)
    (max (2*j + 1) (max (-2*(i+j) - 2) (2*(i+j) + 2))))))

private def score (s : Simplex) : ℤ :=
  let i := s.2.1
  let j := s.2.2
  match s.1 with
  | 0 => vertexScore i j
  | 1 => if i = 0 ∧ j = 0 then 0 else
      1 + min (vertexScore i j) (min (vertexScore (i+1) j)
        (min (upScore i j) (downScore i (j-1))))
  | 2 => 1 + min (vertexScore i j) (min (vertexScore i (j+1))
        (min (upScore i j) (downScore (i-1) j)))
  | 3 => 1 + min (vertexScore (i+1) j) (min (vertexScore i (j+1))
        (min (upScore i j) (downScore i j)))
  | 4 => upScore i j
  | 5 => downScore i j

private lemma score_nonneg (s : Simplex) : 0 ≤ score s := by
  rcases s with ⟨t, i, j⟩
  fin_cases t <;> simp only [score, vertexScore, upScore, downScore]
  all_goals (try split_ifs) <;> positivity

private lemma score_zero (s : Simplex) : score s = 0 ↔ s = root := by
  constructor
  · intro hz
    by_contra hne
    have hp : 0 < score s := by
      rcases s with ⟨t,i,j⟩
      fin_cases t <;> simp only [score]
      all_goals
        try split_ifs
        all_goals
          first
          | (exfalso; apply hne; simp_all [root, Prod.ext_iff]; done)
          | (dsimp only [vertexScore, upScore, downScore]; positivity)
    omega
  · rintro rfl
    norm_num [score, root]

set_option maxHeartbeats 4000000 in
private lemma score_step (s t : Simplex) (h : graph.Adj s t) : score s ≤ score t + 1 := by
  rcases s with ⟨s, i, j⟩
  rcases t with ⟨t, p, q⟩
  generalize hn : score (t, p, q) = n
  have hb : score (t, p, q) ≤ n := hn.le
  clear hn
  fin_cases s <;> fin_cases t
  all_goals
    simp only [graph, support, Finset.insert_subset_iff, Finset.singleton_subset_iff,
      Finset.mem_insert, Finset.mem_singleton, ne_eq, Prod.ext_iff, Fin.reduceEq] at h
    simp only [score] at hb ⊢
    try split_ifs at hb ⊢
    all_goals
      simp only [← le_sub_iff_add_le', min_le_iff, vertexScore, upScore, downScore,
        max_le_iff] at hb ⊢
      omega (config := {splitMinMax := false})


set_option maxHeartbeats 4000000 in
private lemma score_descent (s : Simplex) (hs : 0 < score s) :
    ∃ t : Simplex, graph.Adj s t ∧ score t + 1 = score s := by
  rcases s with ⟨t, i, j⟩
  fin_cases t
  · change 0 < score (0, i, j) at hs
    change ∃ t, graph.Adj (0, i, j) t ∧ score t + 1 = score (0, i, j)
    generalize hn : score (0, i, j) = n at hs ⊢
    have hb : score (0, i, j) ≤ n := hn.le
    have he : (graph.Adj (0, i, j) (1, 0, 0) ∧ score (1, 0, 0) ≤ n - 1) ∨
        (graph.Adj (0, i, j) (4, i, j) ∧ score (4, i, j) ≤ n - 1) ∨
        (graph.Adj (0, i, j) (4, i-1, j) ∧ score (4, i-1, j) ≤ n - 1) ∨
        (graph.Adj (0, i, j) (4, i, j-1) ∧ score (4, i, j-1) ≤ n - 1) ∨
        (graph.Adj (0, i, j) (5, i-1, j-1) ∧ score (5, i-1, j-1) ≤ n - 1) ∨
        (graph.Adj (0, i, j) (5, i-1, j) ∧ score (5, i-1, j) ≤ n - 1) ∨
        (graph.Adj (0, i, j) (5, i, j-1) ∧ score (5, i, j-1) ≤ n - 1) := by
      clear hn
      simp only [score, vertexScore, upScore, downScore, max_le_iff] at hb
      simp only [graph, support, Finset.insert_subset_iff, Finset.singleton_subset_iff,
        Finset.mem_insert, Finset.mem_singleton, ne_eq, Prod.ext_iff, Fin.reduceEq, score,
        vertexScore, upScore, downScore, max_le_iff]
      norm_num
      omega (config := {splitMinMax := false})
    rcases he with h0 | h1 | h2 | h3 | h4 | h5 | h6
    · refine ⟨(1, 0, 0), h0.1, ?_⟩
      have hl := score_step (0, i, j) (1, 0, 0) h0.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · refine ⟨(4, i, j), h1.1, ?_⟩
      have hl := score_step (0, i, j) (4, i, j) h1.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · refine ⟨(4, i-1, j), h2.1, ?_⟩
      have hl := score_step (0, i, j) (4, i-1, j) h2.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · refine ⟨(4, i, j-1), h3.1, ?_⟩
      have hl := score_step (0, i, j) (4, i, j-1) h3.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · refine ⟨(5, i-1, j-1), h4.1, ?_⟩
      have hl := score_step (0, i, j) (5, i-1, j-1) h4.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · refine ⟨(5, i-1, j), h5.1, ?_⟩
      have hl := score_step (0, i, j) (5, i-1, j) h5.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · refine ⟨(5, i, j-1), h6.1, ?_⟩
      have hl := score_step (0, i, j) (5, i, j-1) h6.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
  · change 0 < score (1, i, j) at hs
    change ∃ t, graph.Adj (1, i, j) t ∧ score t + 1 = score (1, i, j)
    generalize hn : score (1, i, j) = n at hs ⊢
    have hb : score (1, i, j) ≤ n := hn.le
    have he : (graph.Adj (1, i, j) (0, i, j) ∧ score (0, i, j) ≤ n - 1) ∨
        (graph.Adj (1, i, j) (0, i+1, j) ∧ score (0, i+1, j) ≤ n - 1) ∨
        (graph.Adj (1, i, j) (4, i, j) ∧ score (4, i, j) ≤ n - 1) ∨
        (graph.Adj (1, i, j) (5, i, j-1) ∧ score (5, i, j-1) ≤ n - 1) := by
      simp only [score] at hb hn
      try split_ifs at hb hn
      all_goals
        simp only [graph, support, Finset.insert_subset_iff, Finset.singleton_subset_iff,
          Finset.mem_insert, Finset.mem_singleton, ne_eq, Prod.ext_iff, Fin.reduceEq, score]
        simp only [← le_sub_iff_add_le', min_le_iff] at hb
        omega (config := {splitMinMax := false})
    rcases he with h0 | h1 | h2 | h3
    · refine ⟨(0, i, j), h0.1, ?_⟩
      have hl := score_step (1, i, j) (0, i, j) h0.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · refine ⟨(0, i+1, j), h1.1, ?_⟩
      have hl := score_step (1, i, j) (0, i+1, j) h1.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · refine ⟨(4, i, j), h2.1, ?_⟩
      have hl := score_step (1, i, j) (4, i, j) h2.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · refine ⟨(5, i, j-1), h3.1, ?_⟩
      have hl := score_step (1, i, j) (5, i, j-1) h3.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
  · change 0 < score (2, i, j) at hs
    change ∃ t, graph.Adj (2, i, j) t ∧ score t + 1 = score (2, i, j)
    generalize hn : score (2, i, j) = n at hs ⊢
    have hb : score (2, i, j) ≤ n := hn.le
    have he : (graph.Adj (2, i, j) (0, i, j) ∧ score (0, i, j) ≤ n - 1) ∨
        (graph.Adj (2, i, j) (0, i, j+1) ∧ score (0, i, j+1) ≤ n - 1) ∨
        (graph.Adj (2, i, j) (4, i, j) ∧ score (4, i, j) ≤ n - 1) ∨
        (graph.Adj (2, i, j) (5, i-1, j) ∧ score (5, i-1, j) ≤ n - 1) := by
      simp only [score] at hb hn
      try split_ifs at hb hn
      all_goals
        simp only [graph, support, Finset.insert_subset_iff, Finset.singleton_subset_iff,
          Finset.mem_insert, Finset.mem_singleton, ne_eq, Prod.ext_iff, Fin.reduceEq, score]
        simp only [← le_sub_iff_add_le', min_le_iff] at hb
        omega (config := {splitMinMax := false})
    rcases he with h0 | h1 | h2 | h3
    · refine ⟨(0, i, j), h0.1, ?_⟩
      have hl := score_step (2, i, j) (0, i, j) h0.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · refine ⟨(0, i, j+1), h1.1, ?_⟩
      have hl := score_step (2, i, j) (0, i, j+1) h1.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · refine ⟨(4, i, j), h2.1, ?_⟩
      have hl := score_step (2, i, j) (4, i, j) h2.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · refine ⟨(5, i-1, j), h3.1, ?_⟩
      have hl := score_step (2, i, j) (5, i-1, j) h3.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
  · change 0 < score (3, i, j) at hs
    change ∃ t, graph.Adj (3, i, j) t ∧ score t + 1 = score (3, i, j)
    generalize hn : score (3, i, j) = n at hs ⊢
    have hb : score (3, i, j) ≤ n := hn.le
    have he : (graph.Adj (3, i, j) (0, i+1, j) ∧ score (0, i+1, j) ≤ n - 1) ∨
        (graph.Adj (3, i, j) (0, i, j+1) ∧ score (0, i, j+1) ≤ n - 1) ∨
        (graph.Adj (3, i, j) (4, i, j) ∧ score (4, i, j) ≤ n - 1) ∨
        (graph.Adj (3, i, j) (5, i, j) ∧ score (5, i, j) ≤ n - 1) := by
      simp only [score] at hb hn
      try split_ifs at hb hn
      all_goals
        simp only [graph, support, Finset.insert_subset_iff, Finset.singleton_subset_iff,
          Finset.mem_insert, Finset.mem_singleton, ne_eq, Prod.ext_iff, Fin.reduceEq, score]
        simp only [← le_sub_iff_add_le', min_le_iff] at hb
        omega (config := {splitMinMax := false})
    rcases he with h0 | h1 | h2 | h3
    · refine ⟨(0, i+1, j), h0.1, ?_⟩
      have hl := score_step (3, i, j) (0, i+1, j) h0.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · refine ⟨(0, i, j+1), h1.1, ?_⟩
      have hl := score_step (3, i, j) (0, i, j+1) h1.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · refine ⟨(4, i, j), h2.1, ?_⟩
      have hl := score_step (3, i, j) (4, i, j) h2.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · refine ⟨(5, i, j), h3.1, ?_⟩
      have hl := score_step (3, i, j) (5, i, j) h3.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
  · change 0 < score (4, i, j) at hs
    change ∃ t, graph.Adj (4, i, j) t ∧ score t + 1 = score (4, i, j)
    generalize hn : score (4, i, j) = n at hs ⊢
    have hb : score (4, i, j) ≤ n := hn.le
    have he : (graph.Adj (4, i, j) (1, 0, 0) ∧ score (1, 0, 0) ≤ n - 1) ∨
        (graph.Adj (4, i, j) (0, i, j) ∧ score (0, i, j) ≤ n - 1) ∨
        (graph.Adj (4, i, j) (0, i+1, j) ∧ score (0, i+1, j) ≤ n - 1) ∨
        (graph.Adj (4, i, j) (0, i, j+1) ∧ score (0, i, j+1) ≤ n - 1) := by
      clear hn
      simp only [score, vertexScore, upScore, downScore, max_le_iff] at hb
      simp only [graph, support, Finset.insert_subset_iff, Finset.singleton_subset_iff,
        Finset.mem_insert, Finset.mem_singleton, ne_eq, Prod.ext_iff, Fin.reduceEq, score,
        vertexScore, upScore, downScore, max_le_iff]
      norm_num
      omega (config := {splitMinMax := false})
    rcases he with h0 | h1 | h2 | h3
    · refine ⟨(1, 0, 0), h0.1, ?_⟩
      have hl := score_step (4, i, j) (1, 0, 0) h0.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · refine ⟨(0, i, j), h1.1, ?_⟩
      have hl := score_step (4, i, j) (0, i, j) h1.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · refine ⟨(0, i+1, j), h2.1, ?_⟩
      have hl := score_step (4, i, j) (0, i+1, j) h2.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · refine ⟨(0, i, j+1), h3.1, ?_⟩
      have hl := score_step (4, i, j) (0, i, j+1) h3.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
  · change 0 < score (5, i, j) at hs
    change ∃ t, graph.Adj (5, i, j) t ∧ score t + 1 = score (5, i, j)
    generalize hn : score (5, i, j) = n at hs ⊢
    have hb : score (5, i, j) ≤ n := hn.le
    have he : (graph.Adj (5, i, j) (1, 0, 0) ∧ score (1, 0, 0) ≤ n - 1) ∨
        (graph.Adj (5, i, j) (0, i+1, j) ∧ score (0, i+1, j) ≤ n - 1) ∨
        (graph.Adj (5, i, j) (0, i, j+1) ∧ score (0, i, j+1) ≤ n - 1) ∨
        (graph.Adj (5, i, j) (0, i+1, j+1) ∧ score (0, i+1, j+1) ≤ n - 1) := by
      clear hn
      simp only [score, vertexScore, upScore, downScore, max_le_iff] at hb
      simp only [graph, support, Finset.insert_subset_iff, Finset.singleton_subset_iff,
        Finset.mem_insert, Finset.mem_singleton, ne_eq, Prod.ext_iff, Fin.reduceEq, score,
        vertexScore, upScore, downScore, max_le_iff]
      norm_num
      omega (config := {splitMinMax := false})
    rcases he with h0 | h1 | h2 | h3
    · refine ⟨(1, 0, 0), h0.1, ?_⟩
      have hl := score_step (5, i, j) (1, 0, 0) h0.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · refine ⟨(0, i+1, j), h1.1, ?_⟩
      have hl := score_step (5, i, j) (0, i+1, j) h1.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · refine ⟨(0, i, j+1), h2.1, ?_⟩
      have hl := score_step (5, i, j) (0, i, j+1) h2.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · refine ⟨(0, i+1, j+1), h3.1, ?_⟩
      have hl := score_step (5, i, j) (0, i+1, j+1) h3.1
      rw [hn] at hl
      omega (config := {splitMinMax := false})

private lemma geodesic (s : Simplex) : ∃ w : graph.Walk root s,
    w.length = (score s).toNat := by
  have h : ∀ n : ℕ, ∀ s : Simplex, (score s).toNat = n →
      ∃ w : graph.Walk root s, w.length = n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hs
      by_cases hn : n = 0
      · have hz : score s = 0 := by have := score_nonneg s; omega
        have he := (score_zero s).mp hz
        subst s
        exact ⟨.nil, hn.symm⟩
      · have hp : 0 < score s := by have := score_nonneg s; omega
        obtain ⟨t, ht, hd⟩ := score_descent s hp
        have ht0 := score_nonneg t
        have hlt : (score t).toNat < n := by omega
        obtain ⟨w, hw⟩ := ih _ hlt t rfl
        exact ⟨w.append ht.symm.toWalk, by simp [hw]; omega⟩
  exact h _ s rfl

private lemma distance_formula (s : Simplex) : distance s = (score s).toNat := by
  obtain ⟨w, hw⟩ := geodesic s
  refine le_antisymm (hw ▸ graph.dist_le w) ?_
  have hl := D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation.potential_dist
    graph (fun s => (score s).toNat) (by
      intro s t h
      have hst := score_step s t h
      have hs := score_nonneg s
      have ht := score_nonneg t
      omega) w.reachable.symm
  have hz : (score root).toNat = 0 := by norm_num [score, root]
  simpa only [hz, zero_add, SimpleGraph.dist_comm, distance] using hl

private lemma shell_finite (n : ℕ) : {s : Simplex | distance s = n}.Finite := by
  have hf := Set.finite_iUnion (fun r : Fin (n + 2) =>
    KisrhombilleFaceCoordination.shell_finite r.val)
  apply hf.subset
  intro s hs
  obtain ⟨w, _⟩ := geodesic s
  have ha : graph.Adj KisrhombilleFaceCoordination.root root := by
    simp [graph, support, KisrhombilleFaceCoordination.root, root, Prod.ext_iff]
  have ht := ha.reachable.dist_triangle_left s
  have hd : graph.dist KisrhombilleFaceCoordination.root root = 1 :=
    graph.dist_eq_one_iff_adj.mpr ha
  have hb : KisrhombilleFaceCoordination.distance s < n + 2 := by
    dsimp [KisrhombilleFaceCoordination.distance]
    rw [hd] at ht
    change distance s = n at hs
    change graph.dist KisrhombilleFaceCoordination.root s ≤ 1 + distance s at ht
    omega
  exact Set.mem_iUnion.mpr ⟨⟨_, hb⟩, rfl⟩

private def slice (t : Fin 6) (n : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.Icc (-(n : ℤ)) n) ×ˢ (Finset.Icc (-(n : ℤ)) n)).filter
    (fun p => score (t, p) ≤ n)

private lemma slice_mem (t : Fin 6) (n : ℕ) (p : ℤ × ℤ) :
    p ∈ slice t n ↔ score (t, p) ≤ n := by
  simp only [slice, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    rcases p with ⟨i, j⟩
    fin_cases t <;> simp only [score] at h
    all_goals
      try split_ifs at h
      all_goals
        simp only [← le_sub_iff_add_le', min_le_iff, vertexScore, upScore, downScore,
          max_le_iff] at h
        dsimp
        omega (config := {splitMinMax := false})

private lemma adjoin_rows_card (S : Finset (ℤ × ℤ)) (k : ℕ) (lo hi c d : ℤ)
    (hl : ∀ p ∈ S, lo < p.2) (hh : ∀ p ∈ S, p.2 < hi) (hlt : lo < hi) :
    ((S ∪ (Finset.Icc c (c + k - 1) ×ˢ {lo})) ∪
      (Finset.Icc d (d + k - 1) ×ˢ {hi})).card = S.card + 2*k := by
  have h1 : Disjoint S (Finset.Icc c (c + k - 1) ×ˢ {lo}) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hj : p.2 = lo := by simpa using (Finset.mem_product.mp hq).2
    have := hl p hp
    omega
  have h2 : Disjoint (S ∪ (Finset.Icc c (c + k - 1) ×ˢ {lo}))
      (Finset.Icc d (d + k - 1) ×ˢ {hi}) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hj : p.2 = hi := by simpa using (Finset.mem_product.mp hq).2
    rcases Finset.mem_union.mp hp with hp | hp
    · have := hh p hp; omega
    · have : p.2 = lo := by simpa using (Finset.mem_product.mp hp).2
      omega
  rw [Finset.card_union_of_disjoint h2, Finset.card_union_of_disjoint h1]
  simp only [Finset.card_product, Finset.card_singleton, mul_one, Int.card_Icc]
  omega


private lemma slice_even_0 (k : ℕ) :
    ((slice 0 (2*(k+1))).card : ℤ) = 3*(k:ℤ)^2+7*k+4 := by
  have he : slice 0 (2*(k+1)) = polygon (2*k+1) (2*k+2) (k+1) (k+1) (-(k:ℤ)) (-(k:ℤ)-1) := by
    ext ⟨i,j⟩
    rw [slice_mem, polygon_mem (2*k+1) (2*k+2) (k+1) (k+1) (-(k:ℤ)) (-(k:ℤ)-1) (by omega) (by omega) (by omega) (by omega)]
    simp only [score, ← le_sub_iff_add_le', min_le_iff, vertexScore, upScore, downScore,
      max_le_iff]
    push_cast
    omega (config := {splitMinMax := false})
  rw [he]
  have hc := polygon_card (2*k+1) (2*k+2) (k+1) (k+1) (-(k:ℤ)) (-(k:ℤ)-1) (by omega) (by omega) (by omega) (by omega) (by omega)
  push_cast at hc
  nlinarith

private lemma slice_even_2 (k : ℕ) :
    ((slice 2 (2*(k+1))).card : ℤ) = 3*(k:ℤ)^2+7*k+4 := by
  have he : slice 2 (2*(k+1)) = polygon (2*k+1) (2*k+1) (k) (k) (-(k:ℤ)) (-(k:ℤ)-1) := by
    ext ⟨i,j⟩
    rw [slice_mem, polygon_mem (2*k+1) (2*k+1) (k) (k) (-(k:ℤ)) (-(k:ℤ)-1) (by omega) (by omega) (by omega) (by omega)]
    simp only [score, ← le_sub_iff_add_le', min_le_iff, vertexScore, upScore, downScore,
      max_le_iff]
    push_cast
    omega (config := {splitMinMax := false})
  rw [he]
  have hc := polygon_card (2*k+1) (2*k+1) (k) (k) (-(k:ℤ)) (-(k:ℤ)-1) (by omega) (by omega) (by omega) (by omega) (by omega)
  push_cast at hc
  nlinarith

private lemma slice_even_4 (k : ℕ) :
    ((slice 4 (2*(k+1))).card : ℤ) = 3*(k:ℤ)^2+8*k+5 := by
  have he : slice 4 (2*(k+1)) = polygon (2*k+2) (2*k+1) (k+1) (k) (-(k:ℤ)-1) (-(k:ℤ)-1) := by
    ext ⟨i,j⟩
    rw [slice_mem, polygon_mem (2*k+2) (2*k+1) (k+1) (k) (-(k:ℤ)-1) (-(k:ℤ)-1) (by omega) (by omega) (by omega) (by omega)]
    simp only [score, ← le_sub_iff_add_le', min_le_iff, vertexScore, upScore, downScore,
      max_le_iff]
    push_cast
    omega (config := {splitMinMax := false})
  rw [he]
  have hc := polygon_card (2*k+2) (2*k+1) (k+1) (k) (-(k:ℤ)-1) (-(k:ℤ)-1) (by omega) (by omega) (by omega) (by omega) (by omega)
  push_cast at hc
  nlinarith

private lemma slice_odd_0 (k : ℕ) :
    ((slice 0 (2*k+1)).card : ℤ) = 3*(k:ℤ)^2+5*k+2 := by
  have he : slice 0 (2*k+1) = polygon (2*k+1) (2*k) (k) (k) (-(k:ℤ)) (-(k:ℤ)) := by
    ext ⟨i,j⟩
    rw [slice_mem, polygon_mem (2*k+1) (2*k) (k) (k) (-(k:ℤ)) (-(k:ℤ)) (by omega) (by omega) (by omega) (by omega)]
    simp only [score, ← le_sub_iff_add_le', min_le_iff, vertexScore, upScore, downScore,
      max_le_iff]
    push_cast
    omega (config := {splitMinMax := false})
  rw [he]
  have hc := polygon_card (2*k+1) (2*k) (k) (k) (-(k:ℤ)) (-(k:ℤ)) (by omega) (by omega) (by omega) (by omega) (by omega)
  push_cast at hc
  nlinarith

private lemma slice_odd_4 (k : ℕ) :
    ((slice 4 (2*k+1)).card : ℤ) = 3*(k:ℤ)^2+4*k+1 := by
  have he : slice 4 (2*k+1) = polygon (2*k) (2*k+1) (k+1) (k) (-(k:ℤ)) (-(k:ℤ)-1) := by
    ext ⟨i,j⟩
    rw [slice_mem, polygon_mem (2*k) (2*k+1) (k+1) (k) (-(k:ℤ)) (-(k:ℤ)-1) (by omega) (by omega) (by omega) (by omega)]
    simp only [score, ← le_sub_iff_add_le', min_le_iff, vertexScore, upScore, downScore,
      max_le_iff]
    push_cast
    omega (config := {splitMinMax := false})
  rw [he]
  have hc := polygon_card (2*k) (2*k+1) (k+1) (k) (-(k:ℤ)) (-(k:ℤ)-1) (by omega) (by omega) (by omega) (by omega) (by omega)
  push_cast at hc
  nlinarith

private lemma slice_odd_1 (k : ℕ) :
    ((slice 1 (2*k+1)).card : ℤ) = 3*(k:ℤ)^2+3*k+1 := by
  have he : slice 1 (2*k+1) = TeaCoordinationSequence.hexagon k k := by
    ext ⟨i,j⟩
    rw [slice_mem, TeaCoordinationSequence.hexagon_mem]
    simp only [score]
    split_ifs
    all_goals
      simp only [← le_sub_iff_add_le', min_le_iff, vertexScore, upScore, downScore,
        max_le_iff]
      omega (config := {splitMinMax := false})
  rw [he]
  have hc := TeaCoordinationSequence.hexagon_card k k (by omega) (by omega)
  push_cast at hc
  nlinarith

private lemma slice_even_1 (k : ℕ) :
    ((slice 1 (2*(k+1))).card : ℤ) = 3*(k:ℤ)^2+9*k+3 := by
  let S := polygon (2*k+2) (2*k) (k) (k) (-(k:ℤ)-1) (-(k:ℤ))
  have hS (i j : ℤ) : (i,j) ∈ S ↔
      (-(k:ℤ)-1) ≤ i ∧ i ≤ (-(k:ℤ)-1) + (2*k+2) ∧
      (-(k:ℤ)) ≤ j ∧ j ≤ (-(k:ℤ)) + (2*k) ∧
      (k : ℤ) ≤ i+j-(-(k:ℤ)-1)-(-(k:ℤ)) ∧
      i+j-(-(k:ℤ)-1)-(-(k:ℤ))+(k) ≤ (2*k+2)+(2*k) :=
    polygon_mem (2*k+2) (2*k) (k) (k) (-(k:ℤ)-1) (-(k:ℤ)) (by omega) (by omega) (by omega) (by omega) (i,j)
  have he : slice 1 (2*(k+1)) = (S ∪
      (Finset.Icc ((1:ℤ)) (((1:ℤ))+k-1) ×ˢ {-(k:ℤ)-1})) ∪
      (Finset.Icc (-(k:ℤ)) ((-(k:ℤ))+k-1) ×ˢ {(k:ℤ)+1}) := by
    ext ⟨i,j⟩
    simp only [slice_mem, Finset.mem_union, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_singleton, hS, score]
    try split_ifs
    all_goals
      simp only [← le_sub_iff_add_le', min_le_iff, vertexScore, upScore, downScore,
        max_le_iff]
      push_cast
      omega (config := {splitMinMax := false})
  have hc := adjoin_rows_card S k (-(k:ℤ)-1) ((k:ℤ)+1) ((1:ℤ)) (-(k:ℤ))
    (by intro ⟨i,j⟩ h; have := (hS i j).mp h; dsimp; push_cast at this ⊢; omega)
    (by intro ⟨i,j⟩ h; have := (hS i j).mp h; dsimp; push_cast at this ⊢; omega)
    (by omega)
  rw [he, hc]
  have hp := polygon_card (2*k+2) (2*k) (k) (k) (-(k:ℤ)-1) (-(k:ℤ)) (by omega) (by omega) (by omega) (by omega) (by omega)
  change 2 * (S.card : ℤ) = _ at hp
  push_cast at hp ⊢
  nlinarith

private lemma slice_odd_2_pos (k : ℕ) :
    ((slice 2 (2*(k+1)+1)).card : ℤ) = 3*(k:ℤ)^2+11*k+8 := by
  let S := polygon (2*k+3) (2*k+1) (k+1) (k+1) (-(k:ℤ)-1) (-(k:ℤ)-1)
  have hS (i j : ℤ) : (i,j) ∈ S ↔
      (-(k:ℤ)-1) ≤ i ∧ i ≤ (-(k:ℤ)-1) + (2*k+3) ∧
      (-(k:ℤ)-1) ≤ j ∧ j ≤ (-(k:ℤ)-1) + (2*k+1) ∧
      (k+1 : ℤ) ≤ i+j-(-(k:ℤ)-1)-(-(k:ℤ)-1) ∧
      i+j-(-(k:ℤ)-1)-(-(k:ℤ)-1)+(k+1) ≤ (2*k+3)+(2*k+1) :=
    polygon_mem (2*k+3) (2*k+1) (k+1) (k+1) (-(k:ℤ)-1) (-(k:ℤ)-1) (by omega) (by omega) (by omega) (by omega) (i,j)
  have he : slice 2 (2*(k+1)+1) = (S ∪
      (Finset.Icc ((1:ℤ)) (((1:ℤ))+(k+1)-1) ×ˢ {-(k:ℤ)-2})) ∪
      (Finset.Icc (-(k:ℤ)) ((-(k:ℤ))+(k+1)-1) ×ˢ {(k:ℤ)+1}) := by
    ext ⟨i,j⟩
    simp only [slice_mem, Finset.mem_union, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_singleton, hS, score]
    try split_ifs
    all_goals
      simp only [← le_sub_iff_add_le', min_le_iff, vertexScore, upScore, downScore,
        max_le_iff]
      push_cast
      omega (config := {splitMinMax := false})
  have hc := adjoin_rows_card S (k+1) (-(k:ℤ)-2) ((k:ℤ)+1) ((1:ℤ)) (-(k:ℤ))
    (by intro ⟨i,j⟩ h; have := (hS i j).mp h; dsimp; push_cast at this ⊢; omega)
    (by intro ⟨i,j⟩ h; have := (hS i j).mp h; dsimp; push_cast at this ⊢; omega)
    (by omega)
  rw [he, hc]
  have hp := polygon_card (2*k+3) (2*k+1) (k+1) (k+1) (-(k:ℤ)-1) (-(k:ℤ)-1) (by omega) (by omega) (by omega) (by omega) (by omega)
  change 2 * (S.card : ℤ) = _ at hp
  push_cast at hp ⊢
  nlinarith

private lemma slice_faces (n : ℕ) : (slice 5 n).card = (slice 4 n).card := by
  apply Finset.card_bij (fun p _ => (-p.1,-p.2-1))
  · rintro ⟨i,j⟩ h
    rw [slice_mem] at h ⊢
    simp only [score, upScore, downScore, max_le_iff] at h ⊢
    dsimp
    omega
  · rintro ⟨i,j⟩ h ⟨p,q⟩ h' he
    simp only [Prod.mk.injEq] at he ⊢
    omega
  · rintro ⟨i,j⟩ h
    refine ⟨(-i,-j-1), ?_, ?_⟩
    · rw [slice_mem] at h ⊢
      simp only [score, upScore, downScore, max_le_iff] at h ⊢
      dsimp
      omega
    · simp

private lemma slice_edges (n : ℕ) : (slice 3 n).card = (slice 2 n).card := by
  apply Finset.card_bij (fun p _ => (p.1+p.2+1,-p.2-1))
  · rintro ⟨i,j⟩ h
    rw [slice_mem] at h ⊢
    simp only [score, ← le_sub_iff_add_le', min_le_iff, vertexScore, upScore, downScore,
      max_le_iff] at h ⊢
    dsimp
    omega (config := {splitMinMax := false})
  · rintro ⟨i,j⟩ h ⟨p,q⟩ h' he
    simp only [Prod.mk.injEq] at he ⊢
    omega
  · rintro ⟨i,j⟩ h
    refine ⟨(i+j,-j-1), ?_, ?_⟩
    · rw [slice_mem] at h ⊢
      simp only [score, ← le_sub_iff_add_le', min_le_iff, vertexScore, upScore, downScore,
        max_le_iff] at h ⊢
      dsimp
      omega (config := {splitMinMax := false})
    · apply Prod.ext <;> dsimp <;> omega

private lemma slice_odd_2 (k : ℕ) :
    ((slice 2 (2*k+1)).card : ℤ) = 3*(k:ℤ)^2+5*k := by
  cases k with
  | zero =>
    have he : slice 2 1 = ∅ := by
      ext ⟨i,j⟩
      simp only [slice_mem, score, ← le_sub_iff_add_le', min_le_iff,
        vertexScore, upScore, downScore, max_le_iff, Finset.notMem_empty, iff_false]
      omega (config := {splitMinMax := false})
    norm_num [he]
  | succ k =>
    rw [slice_odd_2_pos]
    push_cast
    ring

private def ball (n : ℕ) : Finset Simplex :=
  Finset.univ.biUnion (fun t => (slice t n).image (fun p => (t,p)))

private lemma ball_mem (n : ℕ) (s : Simplex) :
    s ∈ ball n ↔ distance s ≤ n := by
  rcases s with ⟨t,p⟩
  rw [distance_formula]
  have hn := score_nonneg (t,p)
  have he : (score (t,p)).toNat ≤ n ↔ score (t,p) ≤ n := by omega
  rw [he]
  simp [ball, slice_mem]

private lemma ball_card_sum (n : ℕ) :
    (ball n).card = ∑ t : Fin 6, (slice t n).card := by
  have hd : (↑(Finset.univ : Finset (Fin 6)) : Set (Fin 6)).PairwiseDisjoint
      (fun t => (slice t n).image (fun p => (t,p))) := by
    rw [← Finset.pairwiseDisjoint_coe]
    apply (Set.pairwiseDisjoint_fiber (fun s : Simplex => s.1) _).mono
    intro t s hs
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hs
    rfl
  rw [ball, Finset.card_biUnion hd]
  apply Finset.sum_congr rfl
  intro t ht
  exact Finset.card_image_of_injective _ (Prod.mk_right_injective t)

private lemma ball_zero : ball 0 = {root} := by
  ext s
  rw [ball_mem]
  simp only [Finset.mem_singleton, distance_formula, Nat.le_zero]
  have hs := score_nonneg s
  rw [show (score s).toNat = 0 ↔ score s = 0 by omega, score_zero]

private lemma ball_even (k : ℕ) :
    ((ball (2*(k+1))).card : ℤ) = 18*(k:ℤ)^2+46*k+25 := by
  rw [ball_card_sum]
  push_cast
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (((slice 0 (2*(k+1))).card : ℤ) + (((slice 1 (2*(k+1))).card : ℤ) +
    (((slice 2 (2*(k+1))).card : ℤ) + (((slice 3 (2*(k+1))).card : ℤ) +
    (((slice 4 (2*(k+1))).card : ℤ) + (((slice 5 (2*(k+1))).card : ℤ) + 0)))))) = _
  rw [slice_faces, slice_edges, slice_even_0, slice_even_1, slice_even_2, slice_even_4]
  ring

private lemma ball_odd (k : ℕ) :
    ((ball (2*k+1)).card : ℤ) = 18*(k:ℤ)^2+26*k+5 := by
  rw [ball_card_sum]
  push_cast
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (((slice 0 (2*k+1)).card : ℤ) + (((slice 1 (2*k+1)).card : ℤ) +
    (((slice 2 (2*k+1)).card : ℤ) + (((slice 3 (2*k+1)).card : ℤ) +
    (((slice 4 (2*k+1)).card : ℤ) + (((slice 5 (2*k+1)).card : ℤ) + 0)))))) = _
  rw [slice_faces, slice_edges, slice_odd_0, slice_odd_1, slice_odd_2, slice_odd_4]
  ring

private lemma shell_succ (n : ℕ) : a (n+1) + (ball n).card = (ball (n+1)).card := by
  have he : (shell_finite (n+1)).toFinset = ball (n+1) \ ball n := by
    ext s
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_sdiff, ball_mem]
    omega
  rw [a, Set.ncard_eq_toFinset_card _ (shell_finite (n+1)), he]
  apply Finset.card_sdiff_add_card_eq_card
  intro s hs
  exact (ball_mem (n+1) s).mpr (by have := (ball_mem n s).mp hs; omega)

private lemma shell_zero : a 0 = 1 := by
  have he : {s : Simplex | distance s = 0} = (ball 0 : Set Simplex) := by
    ext s
    simp [ball_mem]
  rw [a, he, Set.ncard_coe_finset, ball_zero, Finset.card_singleton]

private lemma shell_one : a 1 = 4 := by
  have h := shell_succ 0
  rw [ball_zero, Finset.card_singleton] at h
  have hb := ball_odd 0
  norm_num at hb
  omega

private lemma shell_even (k : ℕ) : (a (2*(k+1)) : ℤ) = 20*(k+1) := by
  have h := congrArg (fun n : ℕ => (n : ℤ)) (shell_succ (2*k+1))
  push_cast at h
  have hn : 2*k+1+1 = 2*(k+1) := by omega
  rw [hn, ball_even, ball_odd] at h
  push_cast
  nlinarith

private lemma shell_odd (k : ℕ) : (a (2*(k+1)+1) : ℤ) = 16*k+24 := by
  have h := congrArg (fun n : ℕ => (n : ℤ)) (shell_succ (2*(k+1)))
  push_cast at h
  rw [ball_even, ball_odd] at h
  push_cast at h ⊢
  nlinarith

private lemma shell_formula (n : ℕ) : (a n : ℤ) =
    if n = 0 then 1 else if n = 1 then 4 else if n % 2 = 0 then 10*n else 8*n := by
  by_cases h0 : n = 0
  · subst n; simp [shell_zero]
  by_cases h1 : n = 1
  · subst n; simp [shell_one]
  simp only [if_neg h0, if_neg h1]
  by_cases he : n % 2 = 0
  · have hx : n = 2*(n/2-1+1) := by omega
    rw [if_pos he, hx, shell_even]
    push_cast
    ring
  · have hx : n = 2*(n/2-1+1)+1 := by omega
    rw [if_neg he, hx, shell_odd]
    push_cast
    ring

/-- Barker's identity for the literal edge-rooted simplex-inclusion graph. -/
theorem result :
    (1 - (PowerSeries.X : PowerSeries ℤ)^2)^2 *
        (PowerSeries.mk fun n => (a n : ℤ)) =
      1 + 4*PowerSeries.X + 18*PowerSeries.X^2 + 16*PowerSeries.X^3 +
        PowerSeries.X^4 - 4*PowerSeries.X^5 := by
  let S : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)
  change (1 - PowerSeries.X^2)^2 * S = _
  have he : (1 - PowerSeries.X^2)^2 * S =
      S - 2*(PowerSeries.X^2*S) + PowerSeries.X^4*S := by ring
  rw [he]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X, PowerSeries.coeff_one,
    PowerSeries.coeff_mk, S, shell_formula]
  by_cases hn : n < 6
  · interval_cases n <;> norm_num
  · have hn2 : 2 ≤ n := by omega
    have hn4 : 4 ≤ n := by omega
    have hm2 : (n-2)%2 = n%2 := by omega
    have hm4 : (n-4)%2 = n%2 := by omega
    simp only [if_pos hn2, if_pos hn4, hm2, hm4,
      if_neg (show n ≠ 0 by omega), if_neg (show n ≠ 1 by omega),
      if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega),
      if_neg (show n ≠ 4 by omega), if_neg (show n ≠ 5 by omega),
      if_neg (show n-2 ≠ 0 by omega), if_neg (show n-2 ≠ 1 by omega),
      if_neg (show n-4 ≠ 0 by omega), if_neg (show n-4 ≠ 1 by omega)]
    split_ifs <;> omega

end D5.S3.StatisticalMechanics.KisrhombilleEdgeCoordination
