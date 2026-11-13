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

/-! The four literal star matrices and their characteristic-root multisets. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

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
  simp [Matrix.det_unique, Matrix.mul_apply, Matrix.diagonal_apply]
  field_simp

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
  classical
  ext i j
  cases i <;> cases j <;>
    simp [sourceMatrix, SimpleGraph.adjMatrix, SimpleGraph.starGraph_adj, arrowMatrix]

private theorem star_laplacian :
    sourceMatrix (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ α)) .laplacian =
      arrowMatrix (Fintype.card α) 1 (-1) := by
  classical
  have hc : (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ α)).degree (Sum.inl ()) =
      Fintype.card α := by
    rw [SimpleGraph.degree_starGraph_center]
    simp
  have hl (i : α) : (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ α)).degree (Sum.inr i) = 1 :=
    SimpleGraph.degree_starGraph_of_ne_center (by simp)
  ext (i | i) (j | j) <;>
    simp [sourceMatrix, SimpleGraph.lapMatrix, SimpleGraph.degMatrix, Matrix.diagonal_apply,
      Matrix.one_apply, SimpleGraph.adjMatrix, SimpleGraph.starGraph_adj, arrowMatrix]
  · cases i
    simpa only [← SimpleGraph.ncard_neighborSet] using hc
  · split_ifs with hij
    · simpa only [← SimpleGraph.ncard_neighborSet, Nat.cast_one] using congrArg (fun n : ℕ => (n : ℝ)) (hl i)
    · rfl

private theorem star_signless :
    sourceMatrix (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ α)) .signless =
      arrowMatrix (Fintype.card α) 1 1 := by
  classical
  have hc : (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ α)).degree (Sum.inl ()) =
      Fintype.card α := by
    rw [SimpleGraph.degree_starGraph_center]
    simp
  have hl (i : α) : (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ α)).degree (Sum.inr i) = 1 :=
    SimpleGraph.degree_starGraph_of_ne_center (by simp)
  ext (i | i) (j | j) <;>
    simp [sourceMatrix, SimpleGraph.degMatrix, Matrix.diagonal_apply,
      Matrix.one_apply, SimpleGraph.adjMatrix, SimpleGraph.starGraph_adj, arrowMatrix]
  · cases i
    simpa only [← SimpleGraph.ncard_neighborSet] using hc
  · split_ifs with hij
    · simpa only [← SimpleGraph.ncard_neighborSet, Nat.cast_one] using congrArg (fun n : ℕ => (n : ℝ)) (hl i)
    · rfl

private theorem star_commonNeighbour :
    sourceMatrix (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ α)) .commonNeighbour =
      Matrix.fromBlocks (0 : Matrix Unit Unit ℝ) 0 0
        (Matrix.vecMulVec (fun _ : α => (1 : ℝ)) (fun _ => 1) - Matrix.scalar α 1) := by
  classical
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
      · simp only [sourceMatrix, commonNeighbourMatrix, Sum.inr.injEq, hij, ↓reduceIte,
          Matrix.fromBlocks_apply₂₂, Matrix.sub_apply, Matrix.vecMulVec_apply,
          Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, mul_one, sub_zero]
        norm_cast
        apply Finset.card_eq_one.mpr
        refine ⟨Sum.inl (),?_⟩
        ext k
        cases k <;> simp [SimpleGraph.starGraph_adj]

/-- The four literal star matrices, before taking characteristic roots. -/
theorem star_matrix (kind : MatrixKind) :
    sourceMatrix (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ α)) kind =
      match kind with
      | .adjacency => arrowMatrix 0 0 1
      | .laplacian => arrowMatrix (Fintype.card α) 1 (-1)
      | .signless => arrowMatrix (Fintype.card α) 1 1
      | .commonNeighbour => Matrix.fromBlocks (0 : Matrix Unit Unit ℝ) 0 0
          (Matrix.vecMulVec (fun _ : α => (1 : ℝ)) (fun _ => 1) - Matrix.scalar α 1) := by
  cases kind
  · exact star_adjacency
  · exact star_laplacian
  · exact star_signless
  · exact star_commonNeighbour

private theorem star_charpoly (kind : MatrixKind) :
    (sourceMatrix (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ α)) kind).charpoly =
      ((starValues (Fintype.card α) kind).map (fun x => X - C x)).prod := by
  classical
  by_cases hr : Fintype.card α = 0
  · have : IsEmpty α := Fintype.card_eq_zero_iff.mp hr
    have hzero : sourceMatrix (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ α)) kind = 0 := by
      ext (i | i) (j | j)
      · cases i; cases j; cases kind <;>
          simp [sourceMatrix, commonNeighbourMatrix, SimpleGraph.lapMatrix,
            SimpleGraph.degMatrix, SimpleGraph.degree, SimpleGraph.neighborFinset,
            SimpleGraph.neighborSet, SimpleGraph.adjMatrix, SimpleGraph.starGraph_adj]
      · exact isEmptyElim j
      · exact isEmptyElim i
      · exact isEmptyElim i
    simp [hzero, starValues, Matrix.charpoly_zero]
  · have hp : 0 < Fintype.card α := Nat.pos_of_ne_zero hr
    cases kind with
    | adjacency =>
      rw [star_adjacency, arrow_charpoly _ _ _ hp]
      have hs : (C (Real.sqrt (Fintype.card α)) : ℝ[X]) ^ 2 = C (Fintype.card α : ℝ) := by
        rw [← map_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      simp [starValues, hr, Polynomial.C_neg, ← hs]
      ring
    | laplacian =>
      rw [star_laplacian, arrow_charpoly _ _ _ hp]
      simp [starValues, hr, Polynomial.C_add]
      ring
    | signless =>
      rw [star_signless, arrow_charpoly _ _ _ hp]
      simp [starValues, hr, Polynomial.C_add]
      ring
    | commonNeighbour =>
      rw [star_commonNeighbour, Matrix.charpoly_fromBlocks_zero₁₂,
        Matrix.charpoly_sub_scalar, Matrix.charpoly_vecMulVec]
      simp [starValues, hr, Matrix.charpoly_zero, dotProduct, Polynomial.sub_comp,
        Polynomial.pow_comp, Polynomial.C_comp, Polynomial.X_comp, smul_eq_C_mul,
        Polynomial.mul_comp, Polynomial.C_sub]
      nth_rw 1 [show Fintype.card α = (Fintype.card α - 1) + 1 by omega]
      rw [pow_succ]
      ring

/-- The real eigenvalue multiset of the literal star, with every algebraic multiplicity. -/
theorem star_spectrum (kind : MatrixKind) :
    graphSpectrum (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ α)) kind =
      starValues (Fintype.card α) kind := by
  classical
  have hr : (sourceMatrix (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ α)) kind).charpoly.roots =
      graphSpectrum (SimpleGraph.starGraph (Sum.inl () : Unit ⊕ α)) kind :=
    (source_matrix_isHermitian _ kind).roots_charpoly_eq_eigenvalues
  rw [← hr, star_charpoly, Polynomial.roots_multiset_prod_X_sub_C]



end
end D5.S3.Combinatorics.Graph.SubgroupGenerating.StarSpectra
