/- GID: D5/S3/Combinatorics/Graph/SubgroupGenerating/StarSpectra
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/SubgroupGenerating/StarSpectra
   mirror-E: none(waiver:noncomputable-spectral-identities)
   anchors: []
   utility: none
   digest: Characteristic polynomials and full spectra of the star components of subgroup-generating graphs. -/

import D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Combinatorics.SimpleGraph.Star

set_option autoImplicit false

open Matrix Finset Polynomial
open D5.S3.Combinatorics.Graph.SubgroupGenerating.CyclicExtensionRefutation

namespace D5.S3.Combinatorics.Graph.SubgroupGenerating.StarSpectra

noncomputable section

variable {α : Type} [Fintype α] [DecidableEq α]

/-- A constant symmetric arrow matrix, with one distinguished central coordinate. -/
def arrowMatrix (a b c : ℝ) : Matrix (Unit ⊕ α) (Unit ⊕ α) ℝ :=
  Matrix.fromBlocks (Matrix.of (fun _ _ => a)) (Matrix.of (fun _ _ => c)) (Matrix.of (fun _ _ => c))
    (Matrix.diagonal (fun _ => b))

private theorem arrow_charpoly_mul (a b c : ℝ) :
    (X - C b) * (arrowMatrix (α := α) a b c).charpoly =
    (X - C b) ^ Fintype.card α *
      ((X - C a) * (X - C b) - C ((Fintype.card α : ℝ) * c ^ 2)) := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply ((Set.infinite_univ : Set.Infinite (Set.univ : Set ℝ)).sdiff
    (Set.finite_singleton b)).mono
  intro x hx
  have hxb : x - b ≠ 0 := sub_ne_zero.mpr (by simpa using hx.2)
  let D : Matrix α α ℝ := Matrix.diagonal (fun _ => x - b)
  let : Invertible D := Matrix.invertibleOfIsUnitDet D (by
    simp only [D, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ hxb))
  have hmatrix : Matrix.scalar (Unit ⊕ α) x - arrowMatrix a b c =
      Matrix.fromBlocks (Matrix.of (fun _ _ : Unit => x - a)) (Matrix.of (fun (_ : Unit) (_ : α) => -c))
        (Matrix.of (fun (_ : α) (_ : Unit) => -c)) D := by
    ext i j
    cases i <;> cases j <;>
      simp [arrowMatrix, Matrix.scalar, Matrix.diagonal, Matrix.fromBlocks, D, sub_eq_add_neg] <;> split_ifs <;> simp_all
  have hinv : ⅟D = Matrix.diagonal (fun _ => (x - b)⁻¹) := by
    apply invOf_eq_right_inv
    simp [D, Matrix.diagonal_mul_diagonal, hxb]
  simp only [Set.mem_ofPred_eq, Polynomial.eval_mul, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_pow, Matrix.eval_charpoly]
  rw [hmatrix, Matrix.det_fromBlocks₂₂, hinv]
  rw [show D.det = (x - b) ^ Fintype.card α by simp [D]]
  simp [Matrix.det_unique, Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_irrel]
  field_simp
  <;> ring

private theorem arrow_charpoly (a b c : ℝ) (h : 0 < Fintype.card α) :
    (arrowMatrix (α := α) a b c).charpoly =
      (X - C b) ^ (Fintype.card α - 1) *
        ((X - C a) * (X - C b) - C ((Fintype.card α : ℝ) * c ^ 2)) := by
  apply mul_left_cancel₀ (X_sub_C_ne_zero b)
  rw [arrow_charpoly_mul]
  rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel h]

/-- The complete eigenvalue list of one star, including the isolated-center case. -/
def starValues (r : ℕ) (kind : MatrixKind) : Multiset ℝ :=
  if r = 0 then {0} else
    match kind with
    | .adjacency => {Real.sqrt r, -Real.sqrt r} + Multiset.replicate (r - 1) 0
    | .laplacian | .signless => {0, (r : ℝ) + 1} + Multiset.replicate (r - 1) 1
    | .commonNeighbour => {0, (r : ℝ) - 1} + Multiset.replicate (r - 1) (-1)

private theorem star_adjacency :
    sourceMatrix (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ α)) .adjacency =
      arrowMatrix 0 0 1 := by
  ext i j
  cases i <;> cases j <;>
    simp [sourceMatrix, SimpleGraph.adjMatrix, SimpleGraph.starGraph_adj, arrowMatrix]

private theorem star_laplacian :
    sourceMatrix (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ α)) .laplacian =
      arrowMatrix (Fintype.card α) 1 (-1) := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => simp [sourceMatrix, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        SimpleGraph.degree_starGraph_center, SimpleGraph.adjMatrix, SimpleGraph.starGraph_adj,
        arrowMatrix, Subsingleton.elim i (), Subsingleton.elim j ()]
    | inr j => simp [sourceMatrix, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        SimpleGraph.adjMatrix, SimpleGraph.starGraph_adj, arrowMatrix]
  | inr i =>
    cases j with
    | inl j => simp [sourceMatrix, SimpleGraph.lapMatrix, SimpleGraph.degMatrix,
        SimpleGraph.adjMatrix, SimpleGraph.starGraph_adj, arrowMatrix]
    | inr j =>
      have hi := SimpleGraph.degree_starGraph_of_ne_center (r := (Sum.inl () : Unit ⊕ α))
        (v := Sum.inr i) (by simp)
      simp [sourceMatrix, SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
        SimpleGraph.starGraph_adj, arrowMatrix, hi]

private theorem star_signless :
    sourceMatrix (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ α)) .signless =
      arrowMatrix (Fintype.card α) 1 1 := by
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j => simp [sourceMatrix, SimpleGraph.degMatrix,
        SimpleGraph.degree_starGraph_center, SimpleGraph.adjMatrix, SimpleGraph.starGraph_adj,
        arrowMatrix, Subsingleton.elim i (), Subsingleton.elim j ()]
    | inr j => simp [sourceMatrix, SimpleGraph.degMatrix,
        SimpleGraph.adjMatrix, SimpleGraph.starGraph_adj, arrowMatrix]
  | inr i =>
    cases j with
    | inl j => simp [sourceMatrix, SimpleGraph.degMatrix,
        SimpleGraph.adjMatrix, SimpleGraph.starGraph_adj, arrowMatrix]
    | inr j =>
      have hi := SimpleGraph.degree_starGraph_of_ne_center (r := (Sum.inl () : Unit ⊕ α))
        (v := Sum.inr i) (by simp)
      simp [sourceMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
        SimpleGraph.starGraph_adj, arrowMatrix, hi]

private theorem star_commonNeighbour :
    sourceMatrix (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ α)) .commonNeighbour =
      Matrix.fromBlocks (0 : Matrix Unit Unit ℝ) 0 0
        (Matrix.vecMulVec (fun _ : α => (1 : ℝ)) (fun _ => 1) - Matrix.scalar α 1) := by
  ext i j
  cases i with
  | inl i =>
    cases j <;>
      simp [sourceMatrix, commonNeighbourMatrix, SimpleGraph.starGraph_adj, Finset.filter_false,
        Matrix.vecMulVec, Subsingleton.elim i ()]
  | inr i =>
    cases j with
    | inl j =>
      simp [sourceMatrix, commonNeighbourMatrix, SimpleGraph.starGraph_adj,
        Finset.filter_false, Subsingleton.elim j ()]
    | inr j =>
      by_cases hij : i = j
      · subst j
        simp [sourceMatrix, commonNeighbourMatrix, Matrix.vecMulVec]
      · have hf : Finset.univ.filter (fun k : Unit ⊕ α =>
            k ≠ Sum.inr i ∧ k ≠ Sum.inr j ∧
            (SimpleGraph.starGraph (Sum.inl ())).Adj (Sum.inr i) k ∧
            (SimpleGraph.starGraph (Sum.inl ())).Adj (Sum.inr j) k) = {Sum.inl ()} := by
          ext k
          cases k <;> simp [SimpleGraph.starGraph_adj]
        simp [sourceMatrix, commonNeighbourMatrix, hij, hf, Matrix.vecMulVec,
          Matrix.scalar, Matrix.diagonal_apply_ne _ hij]


end
end D5.S3.Combinatorics.Graph.SubgroupGenerating.StarSpectra
