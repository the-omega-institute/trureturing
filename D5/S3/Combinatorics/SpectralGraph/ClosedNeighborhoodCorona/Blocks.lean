/- GID: D5/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/Blocks
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ClosedNeighborhoodCorona/Blocks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The adjacency and degree blocks of the closed-neighborhood corona. -/

module

public import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
public import Mathlib.LinearAlgebra.Matrix.Kronecker

import OmegaBuild.Commands

/-! # Closed-neighborhood corona blocks

For normalized Laplacian applications, Sason et al. use
`D⁻¹ᐟ² (D - A) D⁻¹ᐟ²`, with inverse square root zero at degree zero.
This gives an isolated vertex a zero row and column.
See [equations (2.16)–(2.18)](https://arxiv.org/html/2412.20775v6#S2.E16).
-/

compile_only_with_mathlib

set_option autoImplicit false

open Matrix
open scoped Kronecker

namespace ClosedNeighborhoodCorona

public section

variable {V W : Type*}

/-- Attach one copy of `H` at each vertex of `G`. Every vertex in that copy is
adjacent to the vertices in the corresponding closed neighborhood in `G`. -/
@[expose] def corona (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ (V × W)) where
  Adj
    | .inl v, .inl u => G.Adj v u
    | .inl v, .inr (u, _) => v = u ∨ G.Adj v u
    | .inr (v, _), .inl u => u = v ∨ G.Adj u v
    | .inr (v, w), .inr (u, z) => v = u ∧ H.Adj w z
  symm := by
    constructor
    intro x y h
    cases x with
    | inl v =>
      cases y with
      | inl u => exact G.adj_symm h
      | inr u => exact h
    | inr v =>
      cases y with
      | inl u => exact h
      | inr u => exact ⟨h.1.symm, H.adj_symm h.2⟩
  loopless := by
    constructor
    intro x h
    cases x with
    | inl v => exact G.irrefl h
    | inr v => exact H.irrefl h.2

instance (G : SimpleGraph V) (H : SimpleGraph W) [DecidableEq V]
    [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (corona G H).Adj :=
  fun
    | .inl v, .inl u => inferInstanceAs (Decidable (G.Adj v u))
    | .inl v, .inr (u, _) => inferInstanceAs (Decidable (v = u ∨ G.Adj v u))
    | .inr (v, _), .inl u => inferInstanceAs (Decidable (u = v ∨ G.Adj u v))
    | .inr (v, w), .inr (u, z) => inferInstanceAs (Decidable (v = u ∧ H.Adj w z))

/-- The cross block repeats each column of the closed-neighborhood matrix
once per vertex of the attached graph. In [Sonar and Srivastava, §3.1]
(https://arxiv.org/html/2407.05653v2#S3.Ex4), the copy coordinates are ordered
as (attached vertex, base vertex). Swapping them to (base vertex, attached
vertex) gives the block identity proved here directly over a semiring. -/
theorem adjMatrix_corona (R : Type*) [Semiring R] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    let B : Matrix V (V × W) R := of fun v p => (G.adjMatrix R + 1) v p.1
    (corona G H).adjMatrix R =
      fromBlocks (G.adjMatrix R) B Bᵀ ((1 : Matrix V V R) ⊗ₖ H.adjMatrix R) := by
  ext (v | ⟨v, w⟩) (u | ⟨u, z⟩)
  · rfl
  · rw [SimpleGraph.adjMatrix_apply]
    by_cases h : v = u
    · subst u
      simp [corona]
    · simp [corona, h]
  · rw [SimpleGraph.adjMatrix_apply]
    by_cases h : u = v
    · subst u
      simp [corona]
    · simp [corona, h]
  · rw [SimpleGraph.adjMatrix_apply]
    by_cases h : v = u
    · subst u
      simp [corona]
    · simp [corona, h]

section Finite

variable [Fintype V] [Fintype W] [DecidableEq V]
variable (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj]

private theorem sum_adjMatrix_row {X : Type*} [Fintype X]
    (K : SimpleGraph X) [DecidableRel K.Adj] (x : X) :
    ∑ y, K.adjMatrix ℕ x y = K.degree x := by
  simpa [Matrix.mulVec, dotProduct] using
    (SimpleGraph.adjMatrix_mulVec_const_apply (G := K) (a := (1 : ℕ)) (v := x))

private theorem sum_closedNeighborhood_row (v : V) :
    ∑ u, (G.adjMatrix ℕ + 1) v u = G.degree v + 1 := by
  simp only [Matrix.add_apply, Finset.sum_add_distrib, sum_adjMatrix_row]
  simp [Matrix.one_apply]

/-- A base vertex keeps its original neighbors and meets every vertex in
each copy indexed by its closed neighborhood. -/
theorem degree_corona_inl (v : V) :
    (corona G H).degree (.inl v) = G.degree v + (G.degree v + 1) * Fintype.card W := by
  rw [← sum_adjMatrix_row, adjMatrix_corona, Fintype.sum_sum_type]
  simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, of_apply, Fintype.sum_prod_type,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum,
    sum_adjMatrix_row, sum_closedNeighborhood_row]
  rw [Nat.cast_id, Nat.mul_comm (Fintype.card W)]

/-- A copy vertex keeps its neighbors inside that copy and meets the closed
neighborhood of the copy's base vertex. -/
theorem degree_corona_inr (v : V) (w : W) :
    (corona G H).degree (.inr (v, w)) = G.degree v + 1 + H.degree w := by
  rw [← sum_adjMatrix_row, adjMatrix_corona, Fintype.sum_sum_type]
  have hAdj (u : V) : (G.adjMatrix ℕ + 1) u v = (G.adjMatrix ℕ + 1) v u := by
    simp [Matrix.one_apply, eq_comm, SimpleGraph.adj_comm]
  simp only [fromBlocks_apply₂₁, fromBlocks_apply₂₂, transpose_apply, of_apply,
    Fintype.sum_prod_type, hAdj, sum_closedNeighborhood_row, kronecker_apply,
    ← Finset.mul_sum, sum_adjMatrix_row, ← Finset.sum_mul]
  simp [Matrix.one_apply]

end Finite

end

end ClosedNeighborhoodCorona
