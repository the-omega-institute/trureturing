/- GID: D5/S3/Quantum/Reduction/WeightedWordDefect
   generality: G
   mirror-B: D5/B/S3/Quantum/Reduction/WeightedWordDefect
   mirror-E: none(waiver:analytic-word-estimate)
   anchors: []
   utility: none
   digest: Weighted pair defects bound every finite Hermitian word of a unital completely positive map. -/

import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import D5.S3.Quantum.Reduction.IsometricCompression
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Reduction.WeightedWordDefect

open Matrix D5.S3.Quantum.Reduction.IsometricCompression

variable {d k n s : Type*} [Fintype d] [DecidableEq d]
  [Fintype k] [DecidableEq k] [Fintype n] [DecidableEq n]
  [Fintype s] [DecidableEq s]

/-- The total weight of all single deletions, with no division by a letter's norm. -/
def singleWeight {α : Type*} (M ε : α → ℝ) : List α → ℝ
  | [] => 0
  | a :: w => ε a * (w.map M).prod + M a * singleWeight M ε w

/-- The total weight of all ordered-position pairs, each with its two norms deleted. -/
def pairWeight {α : Type*} (M ε : α → ℝ) : List α → ℝ
  | [] => 0
  | a :: w => ε a * singleWeight M ε w + M a * pairWeight M ε w

private lemma complement_star (V : Matrix n k ℂ) :
    (1 - support V)ᴴ = 1 - support V := by
  simp [support]

private lemma complement_sq (V : Matrix n k ℂ) (hV : Vᴴ * V = 1) :
    (1 - support V) * (1 - support V) = 1 - support V := by
  have hP : support V * support V = support V := by
    simp [support, Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V, hV]
  calc
    (1 - support V) * (1 - support V) =
        1 - support V - support V + support V * support V := by noncomm_ring
    _ = 1 - support V := by rw [hP]; abel

private lemma complement_norm (V : Matrix n k ℂ) (hV : Vᴴ * V = 1) :
    ‖1 - support V‖ ≤ 1 := by
  apply IsStarProjection.norm_le
  exact ⟨complement_star V, complement_sq V hV⟩

private lemma frame_norm (V : Matrix n k ℂ) (hV : Vᴴ * V = 1) : ‖V‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self V
  rw [hV] at h
  have h1 : ‖(1 : Matrix k k ℂ)‖ ≤ 1 :=
    IsStarProjection.norm_le _ ⟨by simp, by simp⟩
  nlinarith [norm_nonneg V]

private lemma compression_norm (V : Matrix n k ℂ) (hV : Vᴴ * V = 1)
    (A : Matrix n n ℂ) : ‖compress V A‖ ≤ ‖A‖ := by
  calc
    ‖compress V A‖ ≤ (‖Vᴴ‖ * ‖A‖) * ‖V‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ ‖A‖ := by
      rw [Matrix.l2_opNorm_conjTranspose]
      have hv := frame_norm V hV
      nlinarith [norm_nonneg V, norm_nonneg A, mul_nonneg (norm_nonneg V) (norm_nonneg A)]

private lemma gram (V : Matrix n k ℂ) (hV : Vᴴ * V = 1)
    (X Y : Matrix n n ℂ) :
    compress V (Xᴴ * Y) - (compress V X)ᴴ * compress V Y =
      (normal V (X * V))ᴴ * normal V (Y * V) := by
  have hQ := complement_sq V hV
  simp only [normal, compress, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    complement_star, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (1 - support V) (1 - support V), hQ]
  simp [support, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

private lemma normal_residual (V : Matrix n k ℂ) (A : Matrix n n ℂ) :
    normal V (A * V) = A * V - V * compress V A := by
  simp [normal, support, compress, Matrix.sub_mul, Matrix.mul_assoc]

/-- Finite amplification of a matrix on a labelled environment. -/
def amplify : Matrix d d ℂ →⋆ₐ[ℂ] Matrix (d × s) (d × s) ℂ where
  toFun A := blockDiagonal (fun _ : s => A)
  map_one' := blockDiagonal_one
  map_mul' A B := blockDiagonal_mul _ _
  map_zero' := blockDiagonal_zero
  map_add' A B := blockDiagonal_add _ _
  commutes' z := by
    ext ⟨i,r⟩ ⟨j,t⟩
    simp [blockDiagonal_apply, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply,
      Matrix.one_apply, Prod.ext_iff, ite_and]
    split_ifs <;> simp_all
  map_star' A := by exact (blockDiagonal_conjTranspose _).symm


private lemma norm_one_le_matrix : ‖(1 : Matrix d d ℂ)‖ ≤ 1 :=
  IsStarProjection.norm_le _ ⟨by simp, by simp⟩

private lemma norm_prod_le (w : List (Matrix d d ℂ)) :
    ‖w.prod‖ ≤ (w.map norm).prod := by
  induction w with
  | nil => simpa using (norm_one_le_matrix (d := d))
  | cons a w ih =>
      simpa only [List.prod_cons, List.map_cons] using
        (norm_mul_le a w.prod).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg _))

private lemma mapped_norm_prod_le
    (π : Matrix d d ℂ →⋆ₐ[ℂ] Matrix n n ℂ)
    (V : Matrix n k ℂ) (hV : Vᴴ * V = 1) (w : List (Matrix d d ℂ)) :
    ‖(w.map (fun a => compress V (π a))).prod‖ ≤ (w.map norm).prod := by
  induction w with
  | nil => simpa using (norm_one_le_matrix (d := k))
  | cons a w ih =>
      simp only [List.map_cons, List.prod_cons]
      exact (norm_mul_le _ _).trans (mul_le_mul
        ((compression_norm V hV _).trans (NonUnitalStarAlgHom.norm_apply_le π a))
        ih (norm_nonneg _) (norm_nonneg _))

private lemma normal_product (V : Matrix n k ℂ) (A B : Matrix n n ℂ) :
    normal V (A * B * V) =
      normal V (A * V) * compress V B + (1 - support V) * A * normal V (B * V) := by
  simp only [normal, support, compress, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_assoc]
  abel

private lemma residual_product (π : Matrix d d ℂ →⋆ₐ[ℂ] Matrix n n ℂ)
    (V : Matrix n k ℂ) (a : Matrix d d ℂ) (w : List (Matrix d d ℂ)) :
    π ((a :: w).prod) * V - V * ((a :: w).map (fun a => compress V (π a))).prod =
      π a * (π w.prod * V - V * (w.map (fun a => compress V (π a))).prod) +
        normal V (π a * V) * (w.map (fun a => compress V (π a))).prod := by
  simp only [List.prod_cons, List.map_cons, map_mul, normal_residual,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

private lemma residual_bound (π : Matrix d d ℂ →⋆ₐ[ℂ] Matrix n n ℂ)
    (V : Matrix n k ℂ) (hV : Vᴴ * V = 1) (w : List (Matrix d d ℂ)) :
    ‖π w.prod * V - V * (w.map (fun a => compress V (π a))).prod‖ ≤
      singleWeight norm (fun a => ‖normal V (π a * V)‖) w := by
  induction w with
  | nil => simp [singleWeight]
  | cons a w ih =>
      rw [residual_product]
      calc
        _ ≤ ‖π a‖ * ‖π w.prod * V - V * (w.map (fun a => compress V (π a))).prod‖ +
            ‖normal V (π a * V)‖ * ‖(w.map (fun a => compress V (π a))).prod‖ :=
          (norm_add_le _ _).trans (add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _))
        _ ≤ ‖a‖ * singleWeight norm (fun a => ‖normal V (π a * V)‖) w +
            ‖normal V (π a * V)‖ * (w.map norm).prod :=
          add_le_add (mul_le_mul (NonUnitalStarAlgHom.norm_apply_le π a) ih
            (norm_nonneg _) (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (mapped_norm_prod_le π V hV w) (norm_nonneg _))
        _ = _ := by simp [singleWeight, add_comm]

private lemma leakage_bound (π : Matrix d d ℂ →⋆ₐ[ℂ] Matrix n n ℂ)
    (V : Matrix n k ℂ) (hV : Vᴴ * V = 1) (w : List (Matrix d d ℂ)) :
    ‖normal V (π w.prod * V)‖ ≤
      singleWeight norm (fun a => ‖normal V (π a * V)‖) w := by
  have hQV : (1 - support V) * V = 0 := by
    simp [support, Matrix.sub_mul, Matrix.mul_assoc, hV]
  have heq : normal V (π w.prod * V) =
      (1 - support V) * (π w.prod * V - V * (w.map (fun a => compress V (π a))).prod) := by
    simp [normal, Matrix.mul_sub, ← Matrix.mul_assoc (1 - support V) V, hQV]
  rw [heq]
  exact (Matrix.l2_opNorm_mul _ _).trans
    ((mul_le_mul_of_nonneg_right (complement_norm V hV) (norm_nonneg _)).trans
      (by simpa using residual_bound π V hV w))

private lemma compression_word_bound (π : Matrix d d ℂ →⋆ₐ[ℂ] Matrix n n ℂ)
    (V : Matrix n k ℂ) (hV : Vᴴ * V = 1) (w : List (Matrix d d ℂ))
    (hw : ∀ a ∈ w, aᴴ = a) :
    ‖compress V (π w.prod) - (w.map (fun a => compress V (π a))).prod‖ ≤
      pairWeight norm (fun a => ‖normal V (π a * V)‖) w := by
  induction w with
  | nil => simp [compress, hV, pairWeight]
  | cons a w ih =>
      have ha : (π a)ᴴ = π a := by
        change star (π a) = π a
        rw [← map_star]
        exact congrArg π (hw a (by simp))
      have hg := gram V hV (π a) (π w.prod)
      rw [ha] at hg
      have heq : compress V (π ((a :: w).prod)) -
          ((a :: w).map (fun a => compress V (π a))).prod =
          (normal V (π a * V))ᴴ * normal V (π w.prod * V) +
          compress V (π a) * (compress V (π w.prod) -
            (w.map (fun a => compress V (π a))).prod) := by
        rw [← hg]
        simp only [List.prod_cons, List.map_cons, map_mul, Matrix.mul_sub]
        abel
      rw [heq]
      calc
        _ ≤ ‖normal V (π a * V)‖ * ‖normal V (π w.prod * V)‖ +
            ‖compress V (π a)‖ * ‖compress V (π w.prod) -
              (w.map (fun a => compress V (π a))).prod‖ := by
          simpa only [Matrix.l2_opNorm_conjTranspose] using
            (norm_add_le _ _).trans (add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _))
        _ ≤ ‖normal V (π a * V)‖ * singleWeight norm (fun a => ‖normal V (π a * V)‖) w +
            ‖a‖ * pairWeight norm (fun a => ‖normal V (π a * V)‖) w :=
          add_le_add (mul_le_mul_of_nonneg_left (leakage_bound π V hV w) (norm_nonneg _))
            (mul_le_mul ((compression_norm V hV _).trans
              (NonUnitalStarAlgHom.norm_apply_le π a))
              (ih (fun b hb => hw b (by simp [hb]))) (norm_nonneg _) (norm_nonneg _))
        _ = _ := rfl

end D5.S3.Quantum.Reduction.WeightedWordDefect
