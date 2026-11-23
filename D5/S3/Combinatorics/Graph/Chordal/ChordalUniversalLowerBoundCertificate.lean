/- GID: D5/S3/Combinatorics/Graph/Chordal/ChordalUniversalLowerBoundCertificate
   generality: I
   mirror-B: none(waiver:covered-by-chordal-universal-lower-bound-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Combinatorics/Graph/Chordal/ChordalUniversalLowerBound.pathPower_three_banach_and_integral_lower_bound; premises=D5/S3/Combinatorics/Graph/Chordal/ChordalUniversalLowerBoundCertificate.column_bound,D5/S3/Combinatorics/Graph/Chordal/ChordalUniversalLowerBoundCertificate.objective_value
   digest: Boundary coordinates and dual weights for the width-three path on twelve vertices. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.FinCases

/-! Oriented incidence data and a dual certificate for the triangle-filling norm. -/

namespace SimpleGraph.PathPower.Certificate

/-- The increasing edges, in lexicographic order. -/
private def edgeAt (e : Fin 30) : Fin 12 × Fin 12 :=
  (#[
    (0, 1),
    (0, 2),
    (0, 3),
    (1, 2),
    (1, 3),
    (1, 4),
    (2, 3),
    (2, 4),
    (2, 5),
    (3, 4),
    (3, 5),
    (3, 6),
    (4, 5),
    (4, 6),
    (4, 7),
    (5, 6),
    (5, 7),
    (5, 8),
    (6, 7),
    (6, 8),
    (6, 9),
    (7, 8),
    (7, 9),
    (7, 10),
    (8, 9),
    (8, 10),
    (8, 11),
    (9, 10),
    (9, 11),
    (10, 11)])[e.val]!

/-- The increasing triangles, in lexicographic order. -/
private def triangle (t : Fin 28) : Fin 12 × Fin 12 × Fin 12 :=
  (#[
    (0, 1, 2),
    (0, 1, 3),
    (0, 2, 3),
    (1, 2, 3),
    (1, 2, 4),
    (1, 3, 4),
    (2, 3, 4),
    (2, 3, 5),
    (2, 4, 5),
    (3, 4, 5),
    (3, 4, 6),
    (3, 5, 6),
    (4, 5, 6),
    (4, 5, 7),
    (4, 6, 7),
    (5, 6, 7),
    (5, 6, 8),
    (5, 7, 8),
    (6, 7, 8),
    (6, 7, 9),
    (6, 8, 9),
    (7, 8, 9),
    (7, 8, 10),
    (7, 9, 10),
    (8, 9, 10),
    (8, 9, 11),
    (8, 10, 11),
    (9, 10, 11)])[t.val]!

/-- Indices retained by the lexicographic greedy spanning tree. -/
private def treeEdge (e : Fin 11) : Fin 30 :=
  (#[0, 1, 2, 5, 8, 11, 14, 17, 20, 23, 26])[e.val]!

/-- Non-tree edges in their inherited order. -/
private def offTreeEdge (j : Fin 19) : Fin 30 :=
  (#[3, 4, 6, 7, 9, 10, 12, 13, 15, 16, 18, 19, 21, 22, 24, 25, 27, 28, 29])[j.val]!

private def incidence (v : Fin 12) (e : Fin 30) : ℤ :=
  if (edgeAt e).2 = v then 1 else if (edgeAt e).1 = v then -1 else 0

private def edgeBoundary (t : Fin 28) (e : Fin 30) : ℤ :=
  let (a, b, c) := triangle t
  if edgeAt e = (a, c) then -1 else if edgeAt e = (a, b) ∨ edgeAt e = (b, c) then 1 else 0

private def boundary (t : Fin 28) (j : Fin 19) : ℤ :=
  edgeBoundary t (offTreeEdge j)

/-- Nonnegative weights on the edge radii, with denominator 96. -/
private def edgeWeight (e : Fin 30) : ℕ :=
  (#[8, 7, 7, 0, 0, 8, 0, 0, 7, 0, 0, 7, 0, 0, 8, 0, 0, 7, 0, 0, 7, 0, 0, 8, 0, 0, 7, 0, 7, 8])[e.val]!

/-- The equality row numerators of the dual, including zero entries. -/
private def triangleWeight (t : Fin 28) (j : Fin 19) : ℤ :=
  ((#[
    #[7, 8, 0, 0, -2, 0, 21, 3, 0, -32, -32, 0, 35, 5, 0, -48, -48, 0, 56],
    #[1, 0, 0, -16, -14, 0, 3, 21, 0, 0, 0, 0, 5, 35, 0, 0, 0, 0, 0],
    #[0, 7, 7, 14, 0, -14, 0, 0, 21, -4, -28, -28, 0, 0, 35, -6, -42, -42, 7],
    #[0, 0, 0, 0, -14, 0, 3, -3, 0, 0, 32, 0, 5, -5, 0, 0, 48, 0, 0],
    #[-7, -8, 0, 0, 16, 0, -24, 0, 0, 32, 0, 0, -40, 0, 0, 48, 0, 0, -56],
    #[-1, 0, 0, 16, 0, 0, 0, -24, 0, 0, 32, 0, 0, -40, 0, 0, 48, 0, 0],
    #[0, -8, 0, 0, 14, 14, -24, 0, 0, 32, -4, 0, 0, 0, -35, 48, -6, 0, -56],
    #[0, 1, -7, -14, 0, 0, 21, 3, -21, -28, 0, 28, -5, 5, 0, -42, 0, 42, 49],
    #[7, 0, 0, 0, -2, 14, 0, 0, 0, 0, -4, 0, 40, 0, -35, 0, -6, 0, 0],
    #[0, 1, 0, -16, -14, 0, 0, 24, -21, -28, 0, 0, -5, 5, 35, 0, 0, 42, 49],
    #[1, 7, 0, 0, 0, -14, 24, 0, 21, -4, -28, 0, 5, 35, 0, -48, -42, -42, 7],
    #[0, 0, 7, -2, -14, 0, -21, 21, 0, 0, 0, -28, 0, 0, 35, 42, 0, 0, 0],
    #[1, 7, 0, 16, 16, -14, 0, -24, 0, 28, -28, 0, 5, 35, 0, -48, 6, 0, 7],
    #[-8, -8, 0, 0, 0, 0, 0, 0, 21, 0, 32, 0, -40, -40, 0, 48, 0, -42, -56],
    #[0, 0, 0, 16, 16, 0, -24, -24, -21, 32, 0, 0, 0, 0, 0, 0, 48, 42, 0],
    #[-8, -8, 0, -14, -2, 0, 0, 0, 0, 0, 28, 28, 0, 0, 0, 48, -6, -42, -56],
    #[7, 1, -7, 0, 0, 14, 21, 3, 0, -28, 0, 0, -5, -35, -35, -42, 0, 42, 49],
    #[0, 0, 0, -14, -2, 0, 0, 0, -21, 0, -4, 28, 40, 40, 0, 0, -6, 0, 0],
    #[7, 1, -7, -2, -14, 14, 0, 0, 21, 0, -28, 0, -5, 0, 0, 0, 0, 42, 56],
    #[1, 7, 7, 0, 0, -14, 24, 24, 0, -32, 0, -28, 5, 0, 0, -48, -42, -42, 0],
    #[0, 0, 0, -2, -14, 0, -21, -3, 21, 28, -28, 0, 0, 35, 35, 42, 0, 0, 7],
    #[1, 7, 7, 16, 16, -14, 24, 0, 0, -32, 28, -28, 0, -40, 0, 0, -42, 0, 0],
    #[-8, -8, 0, 0, 0, 0, -24, 0, 0, 32, 4, 0, -35, 0, 0, 0, 48, -42, -56],
    #[0, 0, 0, 16, 16, 0, 0, -24, 0, 0, 28, 0, -5, -40, 0, 48, 0, 42, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -35, 0, 0, 0, 42, 0, 0],
    #[-1, -7, -7, -14, -2, 14, -3, 3, -21, 4, 0, 28, 35, 5, -35, -42, 0, 0, -7],
    #[8, 8, 0, 0, 0, 0, 24, 0, 0, -32, -4, 0, 0, 0, 0, 0, -6, 42, 56],
    #[0, 0, 0, -16, -16, 0, 0, 24, 0, 0, -28, 0, 40, 40, 0, -48, -42, -42, 0]])[t.val]!)[j.val]!

/-- Transpose of signed edge incidence applied to the equality row numerators. -/
private def combinedWeight (e : Fin 30) (j : Fin 19) : ℤ :=
  ((#[
    #[8, 8, 0, -16, -16, 0, 24, 24, 0, -32, -32, 0, 40, 40, 0, -48, -48, 0, 56],
    #[-7, -1, 7, 14, 2, -14, -21, -3, 21, 28, 4, -28, -35, -5, 35, 42, 6, -42, -49],
    #[-1, -7, -7, 2, 14, 14, -3, -21, -21, 4, 28, 28, -5, -35, -35, 6, 42, 42, -7],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[8, 8, 0, -16, -16, 0, 24, 24, 0, -32, -32, 0, 40, 40, 0, -48, -48, 0, 56],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[-7, -1, 7, 14, 2, -14, -21, -3, 21, 28, 4, -28, -35, -5, 35, 42, 6, -42, -49],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[-1, -7, -7, 2, 14, 14, -3, -21, -21, 4, 28, 28, -5, -35, -35, 6, 42, 42, -7],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[8, 8, 0, -16, -16, 0, 24, 24, 0, -32, -32, 0, 40, 40, 0, -48, -48, 0, 56],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[-7, -1, 7, 14, 2, -14, -21, -3, 21, 28, 4, -28, -35, -5, 35, 42, 6, -42, -49],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[-1, -7, -7, 2, 14, 14, -3, -21, -21, 4, 28, 28, -5, -35, -35, 6, 42, 42, -7],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[8, 8, 0, -16, -16, 0, 24, 24, 0, -32, -32, 0, 40, 40, 0, -48, -48, 0, 56],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[-7, -1, 7, 14, 2, -14, -21, -3, 21, 28, 4, -28, -35, -5, 35, 42, 6, -42, -49],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[-1, -7, -7, 2, 14, 14, -3, -21, -21, 4, 28, 28, -5, -35, -35, 6, 42, 42, -7],
    #[8, 8, 0, -16, -16, 0, 24, 24, 0, -32, -32, 0, 40, 40, 0, -48, -48, 0, 56]])[e.val]!)[j.val]!

/-- Coordinates of a triangle filling for each unit cycle. -/
private def basisFilling (j : Fin 19) (t : Fin 28) : ℤ :=
  ((#[
    #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[-1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[-1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, -1, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
    #[0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
    #[-1, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
    #[0, -1, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0],
    #[0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0],
    #[1, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0]])[j.val]!)[t.val]!

/-- The component on the head side of a deleted tree edge. -/
private def cut (d : Fin 11) (v : Fin 12) : ℤ :=
  ((#[
    #[0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0],
    #[0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1],
    #[0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0],
    #[0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0],
    #[0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1],
    #[0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
    #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]])[d.val]!)[v.val]!

private theorem edge_span (e : Fin 30) :
    (edgeAt e).1.val < (edgeAt e).2.val ∧ (edgeAt e).2.val ≤ (edgeAt e).1.val + 3 := by
  fin_cases e <;> decide +kernel

private theorem edgeAt_complete (u v : Fin 12) :
    u.val < v.val ∧ v.val ≤ u.val + 3 → ∃ e, edgeAt e = (u, v) := by
  revert v
  fin_cases u <;> decide +kernel

private theorem edge_injective : Function.Injective edgeAt := by
  intro e
  fin_cases e <;> decide +kernel

private theorem triangle_complete (a b c : Fin 12) :
    a.val < b.val ∧ b.val < c.val ∧ c.val ≤ a.val + 3 →
      ∃ t, triangle t = (a, b, c) := by
  revert b c
  fin_cases a <;> decide +kernel

private theorem edge_partition (e : Fin 30) :
    (∃ d, treeEdge d = e) ∨ ∃ j, offTreeEdge j = e := by
  fin_cases e <;> decide +kernel

set_option maxHeartbeats 900000 in
-- Evaluate the bounded integer certificate one row at a time.
private theorem boundary_closed (t : Fin 28) (v : Fin 12) :
    (∑ e : Fin 30, incidence v e * edgeBoundary t e) = 0 := by
  revert v
  fin_cases t <;> decide +kernel

set_option maxHeartbeats 900000 in
-- Evaluate the bounded integer certificate one row at a time.
private theorem cut_incidence (d e : Fin 11) :
    (∑ v : Fin 12, cut d v * incidence v (treeEdge e)) = if d = e then 1 else 0 := by
  revert e
  fin_cases d <;> decide +kernel

set_option maxHeartbeats 900000 in
-- Evaluate the bounded integer certificate one row at a time.
private theorem basis_filling (j l : Fin 19) :
    (∑ t : Fin 28, basisFilling j t * boundary t l) = if j = l then 1 else 0 := by
  revert l
  fin_cases j <;> decide +kernel

private theorem boundary_unit (t : Fin 28) (j : Fin 19) : (boundary t j).natAbs ≤ 1 := by
  rcases ht : triangle t with ⟨a, b, c⟩
  simp only [boundary, edgeBoundary, ht]
  split
  · decide
  · split <;> decide

private theorem weight_sum : (∑ e : Fin 30, edgeWeight e) = 96 := by
  decide +kernel

set_option maxHeartbeats 900000 in
-- Evaluate the bounded integer certificate one row at a time.
private theorem weight_combination (e : Fin 30) (j : Fin 19) :
    combinedWeight e j = ∑ t : Fin 28, edgeBoundary t e * triangleWeight t j := by
  revert j
  fin_cases e <;> decide +kernel

set_option maxHeartbeats 900000 in
-- Evaluate the bounded integer certificate one row at a time.
private theorem column_bound (e : Fin 30) (t : Fin 28) :
    (∑ j : Fin 19, combinedWeight e j * boundary t j).natAbs ≤ edgeWeight e := by
  revert t
  fin_cases e <;> decide +kernel

private theorem objective_value :
    (∑ t : Fin 28, ∑ j : Fin 19, triangleWeight t j * boundary t j) = 98 := by
  decide +kernel


/-- The projection of an oriented edge onto its non-tree coordinates. -/
private def gainCoordinate (a b : Fin 12) (j : Fin 19) : ℤ :=
  if edgeAt (offTreeEdge j) = (a, b) then 1 else
  if edgeAt (offTreeEdge j) = (b, a) then -1 else 0

private theorem gain_reverse (a b : Fin 12) (j : Fin 19) :
    gainCoordinate b a j = -gainCoordinate a b j := by
  by_cases h : a = b
  · subst b
    have hn : edgeAt (offTreeEdge j) ≠ (a, a) := by
      intro he
      have hlt := (edge_span (offTreeEdge j)).1
      simp [he] at hlt
    simp [gainCoordinate, hn]
  · by_cases hf : edgeAt (offTreeEdge j) = (a, b)
    · have hb : edgeAt (offTreeEdge j) ≠ (b, a) := by
        intro he
        exact h (congrArg Prod.fst (hf.symm.trans he))
      simp only [gainCoordinate, ite_eq_left hf, ite_eq_right hb]
    · by_cases hb : edgeAt (offTreeEdge j) = (b, a)
      · simp only [gainCoordinate, ite_eq_left hb, ite_eq_right hf, neg_neg]
      · simp only [gainCoordinate, ite_eq_right hf, ite_eq_right hb, neg_zero]

private theorem gain_diagonal (a : Fin 12) (j : Fin 19) : gainCoordinate a a j = 0 := by
  have h := gain_reverse a a j
  omega

set_option maxHeartbeats 1400000 in
-- Evaluate the bounded integer certificate one row at a time.
private theorem triangle_gain (a b c : Fin 12) :
    a ≠ b → b ≠ c → a ≠ c →
    Int.natAbs ((a : ℤ) - (b : ℤ)) ≤ 3 → Int.natAbs ((b : ℤ) - (c : ℤ)) ≤ 3 →
    Int.natAbs ((a : ℤ) - (c : ℤ)) ≤ 3 →
    ∃ (t : Fin 28) (positive : Bool), ∀ j : Fin 19,
      gainCoordinate a b j + gainCoordinate b c j - gainCoordinate a c j =
        if positive then boundary t j else -boundary t j := by
  revert b c
  fin_cases a <;> decide +kernel

set_option maxHeartbeats 1600000 in
-- Evaluate the bounded integer certificate one row at a time.
private theorem boundary_reads_gain (t : Fin 28) (j : Fin 19) :
    (∑ e : Fin 30, edgeBoundary t e * gainCoordinate (edgeAt e).1 (edgeAt e).2 j) =
      boundary t j := by
  revert j
  fin_cases t <;> decide +kernel

end SimpleGraph.PathPower.Certificate
