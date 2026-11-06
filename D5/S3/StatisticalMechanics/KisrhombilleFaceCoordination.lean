/- GID: D5/S3/StatisticalMechanics/KisrhombilleFaceCoordination
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/KisrhombilleFaceCoordination
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Simplex inclusion distances from a face of the triangular lattice. -/

/-
admission_basis: open-problem-resolution (#27077; Proved)
escape_witness: geodesic (descent paths attaining the explicit potential).
Direct frozen dependency:
D5/S3/Combinatorics/PositionSets/VertexPositionRatioRefutation.potential_dist
statement_id: sha256:2360c26ddcdab5109d1906cf2b6884cebb254549f8cf9a5078002397a1098f09
frozen_module_statement_id: sha256:f8b677ea402e38581fbfa04887d18040684e7baa21f05cad6421d45525c0cd21
Simplex: proof_shape=definition; consumers=graph
support: proof_shape=definition; consumers=graph
graph: proof_shape=definition; consumers=distance
root: proof_shape=definition; consumers=distance
distance: proof_shape=definition; consumers=a
a: proof_shape=definition; consumers=result
hex: proof_shape=definition; consumers=score
score: proof_shape=definition; consumers=geodesic
hex_le: proof_shape=bind-only; consumers=score_step
score_nonneg: proof_shape=bind-only; consumers=geodesic
support_injective: proof_shape=bind-only; consumers=score_zero
score_zero: proof_shape=bind-only; consumers=geodesic
score_step: proof_shape=bind-only; consumers=distance_formula
score_descent: proof_shape=bind-only; consumers=geodesic
geodesic: proof_shape=content; consumers=distance_formula
distance_formula: proof_shape=content; consumers=ball_mem
triangle: proof_shape=definition; consumers=triangle_card
triangle_mem: proof_shape=bind-only; consumers=corner_mem
triangle_card: proof_shape=bind-only; consumers=cut_card
rectangle: proof_shape=definition; consumers=cut_card
corner: proof_shape=definition; consumers=cut_card
corner_mem: proof_shape=bind-only; consumers=cut_mem
corner_card: proof_shape=bind-only; consumers=cut_card
cutRectangle: proof_shape=definition; consumers=polygon
cut_mem: proof_shape=bind-only; consumers=polygon_mem
cut_card: proof_shape=bind-only; consumers=polygon_card
polygon: proof_shape=definition; consumers=polygon_card
polygon_mem: proof_shape=bind-only; consumers=slice_card_from_polygon
polygon_card: proof_shape=bind-only; consumers=slice_card_from_polygon
slice: proof_shape=definition; consumers=ball
slice_mem: proof_shape=bind-only; consumers=ball_mem
slice_card_from_polygon: proof_shape=bind-only; consumers=slice_even_0
slice_even_0: proof_shape=bind-only; consumers=ball_even
slice_even_1: proof_shape=bind-only; consumers=ball_even
slice_even_2: proof_shape=bind-only; consumers=ball_even
slice_even_3: proof_shape=bind-only; consumers=ball_even
slice_even_4: proof_shape=bind-only; consumers=ball_even
slice_even_5: proof_shape=bind-only; consumers=ball_even
slice_odd_0: proof_shape=bind-only; consumers=ball_odd
slice_odd_1: proof_shape=bind-only; consumers=ball_odd
slice_odd_2: proof_shape=bind-only; consumers=ball_odd
slice_odd_3: proof_shape=bind-only; consumers=ball_odd
slice_odd_4: proof_shape=bind-only; consumers=ball_odd
slice_odd_5: proof_shape=bind-only; consumers=ball_odd
ball: proof_shape=definition; consumers=ball_mem
ball_mem: proof_shape=content; consumers=shell_finite
shell_finite: proof_shape=content; consumers=shell_succ
ball_card_sum: proof_shape=bind-only; consumers=ball_even
ball_zero: proof_shape=content; consumers=ball_even
ball_one: proof_shape=bind-only; consumers=ball_odd
ball_even: proof_shape=content; consumers=shell_even
ball_odd: proof_shape=bind-only; consumers=shell_odd
shell_succ: proof_shape=content; consumers=shell_even
shell_zero: proof_shape=content; consumers=shell_formula
shell_odd: proof_shape=content; consumers=shell_formula
shell_even: proof_shape=content; consumers=shell_formula
shell_formula: proof_shape=content; consumers=result
result: proof_shape=content; consumers=Reg.family
-/

import D5.S3.Combinatorics.PositionSets.VertexPositionRatioRefutation
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.IntervalCases

/-! The simplex-inclusion graph of the triangular lattice. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination

/-- Types 0,1,2,3,4,5 are respectively V,H,B,D,U,W at integer coordinates (i,j). -/
abbrev Simplex := Fin 6 × ℤ × ℤ

/-- The underlying nonempty finite set of triangular-lattice vertices. -/
def support (s : Simplex) : Finset (ℤ × ℤ) :=
  let i := s.2.1
  let j := s.2.2
  match s.1 with
  | 0 => {(i, j)}
  | 1 => {(i, j), (i + 1, j)}
  | 2 => {(i, j), (i, j + 1)}
  | 3 => {(i + 1, j), (i, j + 1)}
  | 4 => {(i, j), (i + 1, j), (i, j + 1)}
  | 5 => {(i + 1, j), (i, j + 1), (i + 1, j + 1)}

/-- Distinct simplices are joined exactly when their underlying vertex sets are comparable. -/
def graph : SimpleGraph Simplex where
  Adj s t := s ≠ t ∧ (support s ⊆ support t ∨ support t ⊆ support s)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The upward face with vertices (0,0),(1,0),(0,1). -/
def root : Simplex := (4, 0, 0)

/-- The genuine shortest-walk distance from the specified face. -/
def distance (s : Simplex) : ℕ := graph.dist root s

/-- The coordination sequence, with natural finite cardinality. -/
def a (n : ℕ) : ℕ := Set.ncard {s : Simplex | distance s = n}

private def hex (z a b c d e f : ℤ) : ℤ :=
  max z (max a (max b (max c (max d (max e f)))))

private def score (s : Simplex) : ℤ :=
  let i := s.2.1
  let j := s.2.2
  match s.1 with
  | 0 => hex 1 (1 - 2 * i) (2 * i - 1) (1 - 2 * j) (2 * j - 1) (1 - 2 * (i + j)) (2 * (i + j) - 1)
  | 1 => hex 1 (-2 * i) (2 * i) (1 - 2 * j) (2 * j - 1) (-2 * (i + j)) (2 * (i + j))
  | 2 => hex 1 (1 - 2 * i) (2 * i - 1) (-2 * j) (2 * j) (-2 * (i + j)) (2 * (i + j))
  | 3 => hex 1 (-2 * i) (2 * i) (-2 * j) (2 * j) (-2 * (i + j) - 1) (2 * (i + j) + 1)
  | 4 => hex 0 (-2 * i) (2 * i) (-2 * j) (2 * j) (-2 * (i + j)) (2 * (i + j))
  | 5 => hex 0 (-2 * i) (2 * i) (-2 * j) (2 * j) (-2 * (i + j) - 2) (2 * (i + j) + 2)

private lemma hex_le (z a b c d e f n : ℤ) :
    hex z a b c d e f ≤ n ↔
      z ≤ n ∧ a ≤ n ∧ b ≤ n ∧ c ≤ n ∧ d ≤ n ∧ e ≤ n ∧ f ≤ n := by
  simp only [hex, max_le_iff]

private lemma score_nonneg (s : Simplex) : 0 ≤ score s := by
  rcases s with ⟨t, i, j⟩
  fin_cases t <;> dsimp [score, hex] <;> omega

private lemma support_injective : Function.Injective support := by
  rintro ⟨s, i, j⟩ ⟨t, p, q⟩ he
  have h1 : support (s, i, j) ⊆ support (t, p, q) := he.le
  have h2 : support (t, p, q) ⊆ support (s, i, j) := he.ge
  fin_cases s <;> fin_cases t <;>
    simp only [support, Finset.insert_subset_iff, Finset.singleton_subset_iff,
      Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at h1 h2 <;>
    simp [Prod.ext_iff] <;> omega

private lemma score_zero (s : Simplex) : score s = 0 ↔ s = root := by
  constructor
  · intro hs
    apply support_injective
    rcases s with ⟨t, i, j⟩
    have hl := hs.le
    fin_cases t <;> dsimp only [score] at hl <;> rw [hex_le] at hl
    all_goals
      have hi : i = 0 := by omega
      have hj : j = 0 := by omega
      norm_num [hi, hj, score, hex] at hs <;> simp [hi, hj, support, root]
  · rintro rfl
    norm_num [score, hex, root]

set_option maxHeartbeats 2000000 in
-- The 36 pairs of simplex types have finite inclusion constraints.
private lemma score_step (s t : Simplex) (h : graph.Adj s t) : score s ≤ score t + 1 := by
  rcases s with ⟨s, i, j⟩
  rcases t with ⟨t, p, q⟩
  have hb := le_refl (score (t, p, q))
  fin_cases s <;> fin_cases t
  all_goals
    simp only [graph, support, Finset.insert_subset_iff, Finset.singleton_subset_iff,
      Finset.mem_insert, Finset.mem_singleton, ne_eq, Prod.ext_iff] at h
    dsimp only [score] at hb ⊢
    rw [hex_le] at hb
    rw [hex_le]
    repeat' constructor
    all_goals omega (config := {splitMinMax := false})

set_option maxHeartbeats 4000000 in
-- Descent checks all incident simplex choices for each of the six types.
private lemma score_descent (s : Simplex) (hs : 0 < score s) :
    ∃ t : Simplex, graph.Adj s t ∧ score t + 1 = score s := by
  rcases s with ⟨t, i, j⟩
  fin_cases t
  · change 0 < score (0, i, j) at hs
    change ∃ t, graph.Adj (0, i, j) t ∧ score t + 1 = score (0, i, j)
    generalize hn : score (0, i, j) = n at hs ⊢
    have hb : score (0, i, j) ≤ n := hn.le
    dsimp only [score] at hb
    rw [hex_le] at hb
    have he : score (4, i, j) ≤ n - 1 ∨
        score (4, i - 1, j) ≤ n - 1 ∨
        score (4, i, j - 1) ≤ n - 1 ∨
        score (5, i - 1, j - 1) ≤ n - 1 ∨
        score (5, i - 1, j) ≤ n - 1 ∨
        score (5, i, j - 1) ≤ n - 1 := by
      clear hn
      simp only [score, hex_le]
      omega (config := {splitMinMax := false})
    rcases he with h0 | h1 | h2 | h3 | h4 | h5
    · have ha : graph.Adj (0, i, j) (4, i, j) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(4, i, j), ha, ?_⟩
      have hl := score_step (0, i, j) (4, i, j) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · have ha : graph.Adj (0, i, j) (4, i - 1, j) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(4, i - 1, j), ha, ?_⟩
      have hl := score_step (0, i, j) (4, i - 1, j) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · have ha : graph.Adj (0, i, j) (4, i, j - 1) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(4, i, j - 1), ha, ?_⟩
      have hl := score_step (0, i, j) (4, i, j - 1) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · have ha : graph.Adj (0, i, j) (5, i - 1, j - 1) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(5, i - 1, j - 1), ha, ?_⟩
      have hl := score_step (0, i, j) (5, i - 1, j - 1) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · have ha : graph.Adj (0, i, j) (5, i - 1, j) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(5, i - 1, j), ha, ?_⟩
      have hl := score_step (0, i, j) (5, i - 1, j) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · have ha : graph.Adj (0, i, j) (5, i, j - 1) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(5, i, j - 1), ha, ?_⟩
      have hl := score_step (0, i, j) (5, i, j - 1) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
  · change 0 < score (1, i, j) at hs
    change ∃ t, graph.Adj (1, i, j) t ∧ score t + 1 = score (1, i, j)
    generalize hn : score (1, i, j) = n at hs ⊢
    have hb : score (1, i, j) ≤ n := hn.le
    dsimp only [score] at hb
    rw [hex_le] at hb
    have he : score (0, i, j) ≤ n - 1 ∨
        score (0, i + 1, j) ≤ n - 1 ∨
        score (4, i, j) ≤ n - 1 ∨
        score (5, i, j - 1) ≤ n - 1 := by
      clear hn
      simp only [score, hex_le]
      omega (config := {splitMinMax := false})
    rcases he with h0 | h1 | h2 | h3
    · have ha : graph.Adj (1, i, j) (0, i, j) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(0, i, j), ha, ?_⟩
      have hl := score_step (1, i, j) (0, i, j) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · have ha : graph.Adj (1, i, j) (0, i + 1, j) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(0, i + 1, j), ha, ?_⟩
      have hl := score_step (1, i, j) (0, i + 1, j) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · have ha : graph.Adj (1, i, j) (4, i, j) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(4, i, j), ha, ?_⟩
      have hl := score_step (1, i, j) (4, i, j) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · have ha : graph.Adj (1, i, j) (5, i, j - 1) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(5, i, j - 1), ha, ?_⟩
      have hl := score_step (1, i, j) (5, i, j - 1) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
  · change 0 < score (2, i, j) at hs
    change ∃ t, graph.Adj (2, i, j) t ∧ score t + 1 = score (2, i, j)
    generalize hn : score (2, i, j) = n at hs ⊢
    have hb : score (2, i, j) ≤ n := hn.le
    dsimp only [score] at hb
    rw [hex_le] at hb
    have he : score (0, i, j) ≤ n - 1 ∨
        score (0, i, j + 1) ≤ n - 1 ∨
        score (4, i, j) ≤ n - 1 ∨
        score (5, i - 1, j) ≤ n - 1 := by
      clear hn
      simp only [score, hex_le]
      omega (config := {splitMinMax := false})
    rcases he with h0 | h1 | h2 | h3
    · have ha : graph.Adj (2, i, j) (0, i, j) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(0, i, j), ha, ?_⟩
      have hl := score_step (2, i, j) (0, i, j) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · have ha : graph.Adj (2, i, j) (0, i, j + 1) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(0, i, j + 1), ha, ?_⟩
      have hl := score_step (2, i, j) (0, i, j + 1) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · have ha : graph.Adj (2, i, j) (4, i, j) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(4, i, j), ha, ?_⟩
      have hl := score_step (2, i, j) (4, i, j) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · have ha : graph.Adj (2, i, j) (5, i - 1, j) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(5, i - 1, j), ha, ?_⟩
      have hl := score_step (2, i, j) (5, i - 1, j) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
  · change 0 < score (3, i, j) at hs
    change ∃ t, graph.Adj (3, i, j) t ∧ score t + 1 = score (3, i, j)
    generalize hn : score (3, i, j) = n at hs ⊢
    have hb : score (3, i, j) ≤ n := hn.le
    dsimp only [score] at hb
    rw [hex_le] at hb
    have he : score (0, i + 1, j) ≤ n - 1 ∨
        score (0, i, j + 1) ≤ n - 1 ∨
        score (4, i, j) ≤ n - 1 ∨
        score (5, i, j) ≤ n - 1 := by
      clear hn
      simp only [score, hex_le]
      omega (config := {splitMinMax := false})
    rcases he with h0 | h1 | h2 | h3
    · have ha : graph.Adj (3, i, j) (0, i + 1, j) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(0, i + 1, j), ha, ?_⟩
      have hl := score_step (3, i, j) (0, i + 1, j) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · have ha : graph.Adj (3, i, j) (0, i, j + 1) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(0, i, j + 1), ha, ?_⟩
      have hl := score_step (3, i, j) (0, i, j + 1) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · have ha : graph.Adj (3, i, j) (4, i, j) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(4, i, j), ha, ?_⟩
      have hl := score_step (3, i, j) (4, i, j) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · have ha : graph.Adj (3, i, j) (5, i, j) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(5, i, j), ha, ?_⟩
      have hl := score_step (3, i, j) (5, i, j) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
  · change 0 < score (4, i, j) at hs
    change ∃ t, graph.Adj (4, i, j) t ∧ score t + 1 = score (4, i, j)
    generalize hn : score (4, i, j) = n at hs ⊢
    have hb : score (4, i, j) ≤ n := hn.le
    dsimp only [score] at hb
    rw [hex_le] at hb
    have hn2 : 2 ≤ n := by
      by_contra h
      have hi : i = 0 := by omega
      have hj : j = 0 := by omega
      subst i
      subst j
      norm_num [score, hex] at hn
      omega
    have he : score (0, i, j) ≤ n - 1 ∨
        score (0, i + 1, j) ≤ n - 1 ∨
        score (0, i, j + 1) ≤ n - 1 := by
      clear hn
      simp only [score, hex_le]
      omega (config := {splitMinMax := false})
    rcases he with h0 | h1 | h2
    · have ha : graph.Adj (4, i, j) (0, i, j) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(0, i, j), ha, ?_⟩
      have hl := score_step (4, i, j) (0, i, j) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · have ha : graph.Adj (4, i, j) (0, i + 1, j) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(0, i + 1, j), ha, ?_⟩
      have hl := score_step (4, i, j) (0, i + 1, j) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · have ha : graph.Adj (4, i, j) (0, i, j + 1) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(0, i, j + 1), ha, ?_⟩
      have hl := score_step (4, i, j) (0, i, j + 1) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
  · change 0 < score (5, i, j) at hs
    change ∃ t, graph.Adj (5, i, j) t ∧ score t + 1 = score (5, i, j)
    generalize hn : score (5, i, j) = n at hs ⊢
    have hb : score (5, i, j) ≤ n := hn.le
    dsimp only [score] at hb
    rw [hex_le] at hb
    have he : score (0, i + 1, j) ≤ n - 1 ∨
        score (0, i, j + 1) ≤ n - 1 ∨
        score (0, i + 1, j + 1) ≤ n - 1 := by
      clear hn
      simp only [score, hex_le]
      omega (config := {splitMinMax := false})
    rcases he with h0 | h1 | h2
    · have ha : graph.Adj (5, i, j) (0, i + 1, j) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(0, i + 1, j), ha, ?_⟩
      have hl := score_step (5, i, j) (0, i + 1, j) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · have ha : graph.Adj (5, i, j) (0, i, j + 1) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(0, i, j + 1), ha, ?_⟩
      have hl := score_step (5, i, j) (0, i, j + 1) ha
      rw [hn] at hl
      omega (config := {splitMinMax := false})
    · have ha : graph.Adj (5, i, j) (0, i + 1, j + 1) := by
        simp [graph, support, Prod.ext_iff]
      refine ⟨(0, i + 1, j + 1), ha, ?_⟩
      have hl := score_step (5, i, j) (0, i + 1, j + 1) ha
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
  have hz : (score root).toNat = 0 := by norm_num [score, root, hex]
  simpa only [hz, zero_add, SimpleGraph.dist_comm, distance] using hl

private def triangle (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range n).biUnion Finset.antidiagonal

private lemma triangle_mem (n : ℕ) (p : ℕ × ℕ) :
    p ∈ triangle n ↔ p.1 + p.2 < n := by
  simp [triangle, Finset.mem_antidiagonal]

private lemma triangle_card (n : ℕ) : 2 * (triangle n).card = n * (n + 1) := by
  have hd : (↑(Finset.range n) : Set ℕ).PairwiseDisjoint Finset.antidiagonal := by
    rw [← Finset.pairwiseDisjoint_coe]
    exact (Set.pairwiseDisjoint_fiber (fun p : ℕ × ℕ => p.1 + p.2) _).mono
      (fun i p hp => Finset.mem_antidiagonal.mp hp)
  change 2 * ((Finset.range n).biUnion Finset.antidiagonal).card = _
  rw [Finset.card_biUnion hd]
  simp only [Finset.Nat.card_antidiagonal]
  have hs : (∑ i ∈ Finset.range n, (i + 1)) = ∑ i ∈ Finset.range (n + 1), i := by
    rw [Finset.sum_range_succ']
    simp
  rw [hs, mul_comm]
  simpa [mul_comm] using Finset.sum_range_id_mul_two (n + 1)

private def rectangle (A B : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range (A + 1) ×ˢ Finset.range (B + 1)

private def corner (A B r : ℕ) : Finset (ℕ × ℕ) :=
  (triangle r).image (fun p => (A - p.1, B - p.2))

private lemma corner_mem (A B r : ℕ) (hrA : r ≤ A + 1) (hrB : r ≤ B + 1)
    (p : ℕ × ℕ) : p ∈ corner A B r ↔
      p.1 ≤ A ∧ p.2 ≤ B ∧ (A - p.1) + (B - p.2) < r := by
  simp only [corner, Finset.mem_image, triangle_mem]
  constructor
  · rintro ⟨⟨i, j⟩, hij, rfl⟩
    dsimp at hij ⊢
    omega
  · rintro ⟨hi, hj, h⟩
    exact ⟨(A - p.1, B - p.2), h, by apply Prod.ext <;> dsimp <;> omega⟩

private lemma corner_card (A B r : ℕ) (hrA : r ≤ A + 1) (hrB : r ≤ B + 1) :
    (corner A B r).card = (triangle r).card := by
  apply Finset.card_image_iff.mpr
  intro p hp q hq h
  have hp' := (triangle_mem _ _).mp hp
  have hq' := (triangle_mem _ _).mp hq
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  apply Prod.ext <;> omega

private def cutRectangle (A B l r : ℕ) : Finset (ℕ × ℕ) :=
  rectangle A B \ (triangle l ∪ corner A B r)

private lemma cut_mem (A B l r : ℕ) (hlA : l ≤ A + 1) (hlB : l ≤ B + 1)
    (hrA : r ≤ A + 1) (hrB : r ≤ B + 1) (p : ℕ × ℕ) :
    p ∈ cutRectangle A B l r ↔
      p.1 ≤ A ∧ p.2 ≤ B ∧ l ≤ p.1 + p.2 ∧ p.1 + p.2 + r ≤ A + B := by
  simp only [cutRectangle, Finset.mem_sdiff, Finset.mem_union, triangle_mem,
    corner_mem A B r hrA hrB, rectangle, Finset.mem_product, Finset.mem_range]
  omega

private lemma cut_card (A B l r : ℕ) (hlA : l ≤ A + 1) (hlB : l ≤ B + 1)
    (hrA : r ≤ A + 1) (hrB : r ≤ B + 1) (hdis : l + r ≤ A + B + 1) :
    2 * ((cutRectangle A B l r).card : ℤ) =
      2 * (A + 1) * (B + 1) - (l : ℤ) * (l + 1) - (r : ℤ) * (r + 1) := by
  have hsub : triangle l ∪ corner A B r ⊆ rectangle A B := by
    intro p hp
    simp only [rectangle, Finset.mem_product, Finset.mem_range]
    rcases Finset.mem_union.mp hp with h | h
    · have := (triangle_mem _ _).mp h
      omega
    · have := (corner_mem A B r hrA hrB p).mp h
      omega
  have hd : Disjoint (triangle l) (corner A B r) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have hp' := (triangle_mem _ _).mp hp
    have hq' := (corner_mem A B r hrA hrB p).mp hq
    omega
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  rw [Finset.card_union_of_disjoint hd] at hc
  have hl := triangle_card l
  have hr := triangle_card r
  rw [← corner_card A B r hrA hrB] at hr
  have hrect : (rectangle A B).card = (A + 1) * (B + 1) := by
    simp [rectangle]
  rw [hrect] at hc
  change (cutRectangle A B l r).card + _ = _ at hc
  have hc' := congrArg (fun n : ℕ => (n : ℤ)) hc
  have hl' := congrArg (fun n : ℕ => (n : ℤ)) hl
  have hr' := congrArg (fun n : ℕ => (n : ℤ)) hr
  push_cast at hc' hl' hr'
  nlinarith

private def polygon (A B l r : ℕ) (i0 j0 : ℤ) : Finset (ℤ × ℤ) :=
  (cutRectangle A B l r).image (fun p => (i0 + p.1, j0 + p.2))

private lemma polygon_mem (A B l r : ℕ) (i0 j0 : ℤ)
    (hlA : l ≤ A + 1) (hlB : l ≤ B + 1) (hrA : r ≤ A + 1) (hrB : r ≤ B + 1)
    (p : ℤ × ℤ) : p ∈ polygon A B l r i0 j0 ↔
      i0 ≤ p.1 ∧ p.1 ≤ i0 + A ∧ j0 ≤ p.2 ∧ p.2 ≤ j0 + B ∧
      (l : ℤ) ≤ p.1 + p.2 - i0 - j0 ∧ p.1 + p.2 - i0 - j0 + r ≤ (A : ℤ) + B := by
  simp only [polygon, Finset.mem_image, cut_mem A B l r hlA hlB hrA hrB]
  constructor
  · rintro ⟨⟨i, j⟩, h, rfl⟩
    dsimp at h ⊢
    omega
  · intro h
    refine ⟨((p.1 - i0).toNat, (p.2 - j0).toNat), ?_, ?_⟩
    · dsimp
      omega
    · apply Prod.ext <;> dsimp <;> omega

private lemma polygon_card (A B l r : ℕ) (i0 j0 : ℤ)
    (hlA : l ≤ A + 1) (hlB : l ≤ B + 1) (hrA : r ≤ A + 1) (hrB : r ≤ B + 1)
    (hdis : l + r ≤ A + B + 1) :
    2 * ((polygon A B l r i0 j0).card : ℤ) =
      2 * (A + 1) * (B + 1) - (l : ℤ) * (l + 1) - (r : ℤ) * (r + 1) := by
  have hi : Function.Injective (fun p : ℕ × ℕ => (i0 + p.1, j0 + p.2)) := by
    intro p q h
    obtain ⟨h1, h2⟩ := Prod.mk.inj h
    apply Prod.ext <;> omega
  rw [polygon, Finset.card_image_of_injective _ hi]
  exact cut_card A B l r hlA hlB hrA hrB hdis

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
    fin_cases t <;> dsimp only [score] at h <;> rw [hex_le] at h <;> dsimp <;> omega

private lemma slice_card_from_polygon (t : Fin 6) (n A B l r : ℕ) (i0 j0 : ℤ)
    (hlA : l ≤ A + 1) (hlB : l ≤ B + 1) (hrA : r ≤ A + 1) (hrB : r ≤ B + 1)
    (hdis : l + r ≤ A + B + 1)
    (hshape : ∀ p : ℤ × ℤ, score (t, p) ≤ n ↔
      i0 ≤ p.1 ∧ p.1 ≤ i0 + A ∧ j0 ≤ p.2 ∧ p.2 ≤ j0 + B ∧
      (l : ℤ) ≤ p.1 + p.2 - i0 - j0 ∧ p.1 + p.2 - i0 - j0 + r ≤ (A : ℤ) + B) :
    2 * ((slice t n).card : ℤ) =
      2 * (A + 1) * (B + 1) - (l : ℤ) * (l + 1) - (r : ℤ) * (r + 1) := by
  have he : slice t n = polygon A B l r i0 j0 := by
    ext p
    rw [slice_mem, hshape, polygon_mem A B l r i0 j0 hlA hlB hrA hrB]
  rw [he]
  exact polygon_card A B l r i0 j0 hlA hlB hrA hrB hdis

private lemma slice_even_0 (k : ℕ) :
    ((slice 0 (2 * (k + 1))).card : ℤ) = 3 * (k + 1) ^ 2 := by
  have h := slice_card_from_polygon 0 (2 * (k + 1)) (2 * k + 1) (2 * k + 1) (k) (k + 1)
    (-(k : ℤ)) (-(k : ℤ)) (by omega) (by omega) (by omega) (by omega) (by omega) (by
      rintro ⟨i, j⟩
      simp only [score, hex_le]
      push_cast
      omega)
  push_cast at h ⊢
  nlinarith

private lemma slice_even_1 (k : ℕ) :
    ((slice 1 (2 * (k + 1))).card : ℤ) = 3 * (k + 1) ^ 2 + 2 * (k + 1) := by
  have h := slice_card_from_polygon 1 (2 * (k + 1)) (2 * k + 2) (2 * k + 1) (k) (k + 1)
    (-(k : ℤ) - 1) (-(k : ℤ)) (by omega) (by omega) (by omega) (by omega) (by omega) (by
      rintro ⟨i, j⟩
      simp only [score, hex_le]
      push_cast
      omega)
  push_cast at h ⊢
  nlinarith

private lemma slice_even_2 (k : ℕ) :
    ((slice 2 (2 * (k + 1))).card : ℤ) = 3 * (k + 1) ^ 2 + 2 * (k + 1) := by
  have h := slice_card_from_polygon 2 (2 * (k + 1)) (2 * k + 1) (2 * k + 2) (k) (k + 1)
    (-(k : ℤ)) (-(k : ℤ) - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by
      rintro ⟨i, j⟩
      simp only [score, hex_le]
      push_cast
      omega)
  push_cast at h ⊢
  nlinarith

private lemma slice_even_3 (k : ℕ) :
    ((slice 3 (2 * (k + 1))).card : ℤ) = 3 * (k + 1) ^ 2 + 2 * (k + 1) := by
  have h := slice_card_from_polygon 3 (2 * (k + 1)) (2 * k + 2) (2 * k + 2) (k + 1) (k + 2)
    (-(k : ℤ) - 1) (-(k : ℤ) - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by
      rintro ⟨i, j⟩
      simp only [score, hex_le]
      push_cast
      omega)
  push_cast at h ⊢
  nlinarith

private lemma slice_even_4 (k : ℕ) :
    ((slice 4 (2 * (k + 1))).card : ℤ) = 3 * (k + 1) ^ 2 + 3 * (k + 1) + 1 := by
  have h := slice_card_from_polygon 4 (2 * (k + 1)) (2 * k + 2) (2 * k + 2) (k + 1) (k + 1)
    (-(k : ℤ) - 1) (-(k : ℤ) - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by
      rintro ⟨i, j⟩
      simp only [score, hex_le]
      push_cast
      omega)
  push_cast at h ⊢
  nlinarith

private lemma slice_even_5 (k : ℕ) :
    ((slice 5 (2 * (k + 1))).card : ℤ) = 3 * (k + 1) ^ 2 + 3 * (k + 1) := by
  have h := slice_card_from_polygon 5 (2 * (k + 1)) (2 * k + 2) (2 * k + 2) (k) (k + 2)
    (-(k : ℤ) - 1) (-(k : ℤ) - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by
      rintro ⟨i, j⟩
      simp only [score, hex_le]
      push_cast
      omega)
  push_cast at h ⊢
  nlinarith

private lemma slice_odd_0 (k : ℕ) :
    ((slice 0 (2 * (k + 1) + 1)).card : ℤ) = 3 * (k + 2) ^ 2 := by
  have h := slice_card_from_polygon 0 (2 * (k + 1) + 1) (2 * k + 3) (2 * k + 3) (k + 1) (k + 2)
    (-(k : ℤ) - 1) (-(k : ℤ) - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by
      rintro ⟨i, j⟩
      simp only [score, hex_le]
      push_cast
      omega)
  push_cast at h ⊢
  nlinarith

private lemma slice_odd_1 (k : ℕ) :
    ((slice 1 (2 * (k + 1) + 1)).card : ℤ) = 3 * (k + 1) ^ 2 + 4 * (k + 1) + 1 := by
  have h := slice_card_from_polygon 1 (2 * (k + 1) + 1) (2 * k + 2) (2 * k + 3) (k + 1) (k + 2)
    (-(k : ℤ) - 1) (-(k : ℤ) - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by
      rintro ⟨i, j⟩
      simp only [score, hex_le]
      push_cast
      omega)
  push_cast at h ⊢
  nlinarith

private lemma slice_odd_2 (k : ℕ) :
    ((slice 2 (2 * (k + 1) + 1)).card : ℤ) = 3 * (k + 1) ^ 2 + 4 * (k + 1) + 1 := by
  have h := slice_card_from_polygon 2 (2 * (k + 1) + 1) (2 * k + 3) (2 * k + 2) (k + 1) (k + 2)
    (-(k : ℤ) - 1) (-(k : ℤ) - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by
      rintro ⟨i, j⟩
      simp only [score, hex_le]
      push_cast
      omega)
  push_cast at h ⊢
  nlinarith

private lemma slice_odd_3 (k : ℕ) :
    ((slice 3 (2 * (k + 1) + 1)).card : ℤ) = 3 * (k + 1) ^ 2 + 4 * (k + 1) + 1 := by
  have h := slice_card_from_polygon 3 (2 * (k + 1) + 1) (2 * k + 2) (2 * k + 2) (k) (k + 1)
    (-(k : ℤ) - 1) (-(k : ℤ) - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by
      rintro ⟨i, j⟩
      simp only [score, hex_le]
      push_cast
      omega)
  push_cast at h ⊢
  nlinarith

private lemma slice_odd_4 (k : ℕ) :
    ((slice 4 (2 * (k + 1) + 1)).card : ℤ) = 3 * (k + 1) ^ 2 + 3 * (k + 1) + 1 := by
  have h := slice_card_from_polygon 4 (2 * (k + 1) + 1) (2 * k + 2) (2 * k + 2) (k + 1) (k + 1)
    (-(k : ℤ) - 1) (-(k : ℤ) - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by
      rintro ⟨i, j⟩
      simp only [score, hex_le]
      push_cast
      omega)
  push_cast at h ⊢
  nlinarith

private lemma slice_odd_5 (k : ℕ) :
    ((slice 5 (2 * (k + 1) + 1)).card : ℤ) = 3 * (k + 1) ^ 2 + 3 * (k + 1) := by
  have h := slice_card_from_polygon 5 (2 * (k + 1) + 1) (2 * k + 2) (2 * k + 2) (k) (k + 2)
    (-(k : ℤ) - 1) (-(k : ℤ) - 1) (by omega) (by omega) (by omega) (by omega) (by omega) (by
      rintro ⟨i, j⟩
      simp only [score, hex_le]
      push_cast
      omega)
  push_cast at h ⊢
  nlinarith


private def ball (n : ℕ) : Finset Simplex :=
  Finset.univ.biUnion (fun t => (slice t n).image (fun p => (t, p)))

private lemma ball_mem (n : ℕ) (s : Simplex) :
    s ∈ ball n ↔ distance s ≤ n := by
  rcases s with ⟨t, p⟩
  rw [distance_formula]
  have hn := score_nonneg (t, p)
  have he : (score (t, p)).toNat ≤ n ↔ score (t, p) ≤ n := by omega
  rw [he]
  simp [ball, slice_mem]

private lemma shell_finite (n : ℕ) : {s : Simplex | distance s = n}.Finite := by
  apply (ball n).finite_toSet.subset
  intro s hs
  exact (ball_mem n s).mpr (le_of_eq hs)

private lemma ball_card_sum (n : ℕ) :
    (ball n).card = ∑ t : Fin 6, (slice t n).card := by
  have hd : (↑(Finset.univ : Finset (Fin 6)) : Set (Fin 6)).PairwiseDisjoint
      (fun t => (slice t n).image (fun p => (t, p))) := by
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

private lemma ball_one : (ball 1).card = 7 := by
  have h0 : slice 0 1 = {(0, 0), (1, 0), (0, 1)} := by
    ext ⟨i, j⟩
    simp only [slice_mem, score, hex_le, Finset.mem_insert, Finset.mem_singleton,
      Prod.mk.injEq]
    omega
  have h1 : ∀ t : Fin 6, t ≠ 0 → t ≠ 5 → slice t 1 = {(0, 0)} := by
    intro t ht0 ht5
    fin_cases t <;> try contradiction
    all_goals
      ext ⟨i, j⟩
      simp only [slice_mem, score, hex_le, Finset.mem_singleton, Prod.mk.injEq]
      omega
  have h5 : slice 5 1 = ∅ := by
    ext ⟨i, j⟩
    simp only [slice_mem, score, hex_le, Finset.notMem_empty, iff_false]
    omega
  rw [ball_card_sum]
  simp [Fin.sum_univ_succ, h0, h1, h5]

private lemma ball_even (k : ℕ) : ((ball (2 * k)).card : ℤ) = 18 * k ^ 2 + 12 * k + 1 := by
  cases k with
  | zero => simp [ball_zero]
  | succ k =>
    rw [ball_card_sum]
    push_cast
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    change (((slice 0 (2 * (k + 1))).card : ℤ) + (((slice 1 (2 * (k + 1))).card : ℤ) + (((slice 2 (2 * (k + 1))).card : ℤ) + (((slice 3 (2 * (k + 1))).card : ℤ) + (((slice 4 (2 * (k + 1))).card : ℤ) + (((slice 5 (2 * (k + 1))).card : ℤ) + 0)))))) = _
    rw [slice_even_0, slice_even_1, slice_even_2, slice_even_3, slice_even_4, slice_even_5]
    push_cast
    ring

private lemma ball_odd (k : ℕ) : ((ball (2 * k + 1)).card : ℤ) = 18 * k ^ 2 + 24 * k + 7 := by
  cases k with
  | zero => norm_num [ball_one]
  | succ k =>
    rw [ball_card_sum]
    push_cast
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    change (((slice 0 (2 * (k + 1) + 1)).card : ℤ) + (((slice 1 (2 * (k + 1) + 1)).card : ℤ) + (((slice 2 (2 * (k + 1) + 1)).card : ℤ) + (((slice 3 (2 * (k + 1) + 1)).card : ℤ) + (((slice 4 (2 * (k + 1) + 1)).card : ℤ) + (((slice 5 (2 * (k + 1) + 1)).card : ℤ) + 0)))))) = _
    rw [slice_odd_0, slice_odd_1, slice_odd_2, slice_odd_3, slice_odd_4, slice_odd_5]
    push_cast
    ring

private lemma shell_succ (n : ℕ) : a (n + 1) + (ball n).card = (ball (n + 1)).card := by
  have he : (shell_finite (n + 1)).toFinset = ball (n + 1) \ ball n := by
    ext s
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, Finset.mem_sdiff, ball_mem]
    omega
  rw [a, Set.ncard_eq_toFinset_card _ (shell_finite (n + 1)), he]
  apply Finset.card_sdiff_add_card_eq_card
  intro s hs
  exact (ball_mem (n + 1) s).mpr (by have := (ball_mem n s).mp hs; omega)

private lemma shell_zero : a 0 = 1 := by
  have he : {s : Simplex | distance s = 0} = (ball 0 : Set Simplex) := by
    ext s
    simp [ball_mem]
  rw [a, he, Set.ncard_coe_finset, ball_zero, Finset.card_singleton]

private lemma shell_odd (k : ℕ) : (a (2 * k + 1) : ℤ) = 12 * k + 6 := by
  have h := congrArg (fun n : ℕ => (n : ℤ)) (shell_succ (2 * k))
  push_cast at h
  rw [ball_even, ball_odd] at h
  nlinarith

private lemma shell_even (k : ℕ) : (a (2 * (k + 1)) : ℤ) = 24 * (k + 1) := by
  have h := congrArg (fun n : ℕ => (n : ℤ)) (shell_succ (2 * k + 1))
  push_cast at h
  have hn : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
  rw [hn, ball_even, ball_odd] at h
  push_cast at h ⊢
  nlinarith

private lemma shell_formula (n : ℕ) : (a n : ℤ) =
    if n = 0 then 1 else if n % 2 = 0 then 12 * n else 6 * n := by
  by_cases hn : n = 0
  · subst n
    simp [shell_zero]
  · rw [ite_eq_right hn]
    by_cases he : n % 2 = 0
    · have hx : n = 2 * (n/2 - 1 + 1) := by omega
      rw [ite_eq_left he, hx, shell_even]
      push_cast
      ring
    · have hx : n = 2 * (n/2) + 1 := by omega
      rw [ite_eq_right he, hx, shell_odd]
      push_cast
      ring

/-- Barker's formal generating-function identity for the literal face-rooted inclusion graph. -/
theorem result :
    (1 - (PowerSeries.X : PowerSeries ℤ) ^ 2) ^ 2 *
        (PowerSeries.mk fun n => (a n : ℤ)) =
      1 + 6 * PowerSeries.X + 22 * PowerSeries.X ^ 2 + 6 * PowerSeries.X ^ 3 + PowerSeries.X ^ 4 := by
  let S : PowerSeries ℤ := PowerSeries.mk fun n => (a n : ℤ)
  change (1 - PowerSeries.X ^ 2) ^ 2 * S = _
  have he : (1 - PowerSeries.X ^ 2) ^ 2 * S =
      S - 2 * (PowerSeries.X ^ 2 * S) + PowerSeries.X ^ 4 * S := by ring
  rw [he]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_ofNat_mul, PowerSeries.coeff_X_pow_mul',
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X, PowerSeries.coeff_one,
    PowerSeries.coeff_mk, S, shell_formula]
  by_cases hn : n < 5
  · interval_cases n <;> norm_num
  · have hn2 : 2 ≤ n := by omega
    have hn4 : 4 ≤ n := by omega
    have hz : n ≠ 0 := by omega
    have hz2 : n - 2 ≠ 0 := by omega
    have hz4 : n - 4 ≠ 0 := by omega
    have hm2 : (n - 2)%2 = n%2 := by omega
    have hm4 : (n - 4)%2 = n%2 := by omega
    simp only [ite_eq_left hn2, ite_eq_left hn4, ite_eq_right hz, ite_eq_right hz2, ite_eq_right hz4,
      hm2, hm4, ite_eq_right (show n ≠ 1 by omega), ite_eq_right (show n ≠ 2 by omega),
      ite_eq_right (show n ≠ 3 by omega), ite_eq_right (show n ≠ 4 by omega)]
    split_ifs <;> omega

end D5.S3.StatisticalMechanics.KisrhombilleFaceCoordination
