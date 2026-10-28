/- GID: D5/S3/VertexAlgebra/TwistedGround/BinarySchur
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/BinarySchur
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.SchurComplement]
   utility: none
   digest: An odd binary pivot splits an even quadratic matrix over the integers modulo eight. -/

import D5.S3.VertexAlgebra.TwistedGround.BinaryGauss
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! The binary elimination step keeps the quadratic half-norm as well as its polarization. -/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.TwistedGround.BinarySchur

open BinaryGauss Matrix

noncomputable section

/-- A coefficient matrix for the binary half-norm. -/
def halfGram (a b c : ZMod 8) : Matrix (Fin 2) (Fin 2) (ZMod 8) :=
  !![a, b; 0, c]

private theorem symmetrize_halfGram (a b c : ZMod 8) :
    halfGram a b c + (halfGram a b c)ᵀ = gram a b c := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [halfGram, gram] <;> ring

private theorem gram_unit (a b c : ZMod 8) (hb : residue b = 1) :
    IsUnit (gram a b c).det := by
  have odd : residue (gram a b c).det = 1 := by
    have two : residue (2 : ZMod 8) = 0 := rfl
    simp only [gram, det_fin_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, map_sub, map_mul, two, hb]
    norm_num
    decide
  have table : ∀ u : ZMod 8, residue u = 1 → u * u = 1 := by decide
  exact IsUnit.of_mul_eq_one _ (table _ odd)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coordinates of the off-plane coupling in the nondegenerate binary plane. -/
def correction (a b c : ZMod 8) (B : Matrix (Fin 2) ι (ZMod 8)) :=
  (gram a b c)⁻¹ * B

/-- The residual coefficient matrix; its polarization is the Schur complement. -/
def residual (a b c : ZMod 8) (B : Matrix (Fin 2) ι (ZMod 8))
    (L : Matrix ι ι (ZMod 8)) : Matrix ι ι (ZMod 8) :=
  L - (correction a b c B)ᵀ * (halfGram a b c)ᵀ * correction a b c B

/-- The determinant-one substitution eliminating the binary cross terms. -/
def shear (a b c : ZMod 8) (B : Matrix (Fin 2) ι (ZMod 8)) :
    Matrix (Fin 2 ⊕ ι) (Fin 2 ⊕ ι) (ZMod 8) :=
  fromBlocks 1 (-correction a b c B) 0 1

omit [Fintype ι] [DecidableEq ι] in
private theorem correction_identity (a b c : ZMod 8) (hb : residue b = 1)
    (B : Matrix (Fin 2) ι (ZMod 8)) :
    gram a b c * correction a b c B = B := by
  rw [correction, ← Matrix.mul_assoc, mul_nonsing_inv _ (gram_unit a b c hb), Matrix.one_mul]

private theorem transformed_half (a b c : ZMod 8) (hb : residue b = 1)
    (B : Matrix (Fin 2) ι (ZMod 8)) (L : Matrix ι ι (ZMod 8)) :
    (shear a b c B)ᵀ * fromBlocks (halfGram a b c) B 0 L * shear a b c B =
      fromBlocks (halfGram a b c)
        ((halfGram a b c)ᵀ * correction a b c B)
        (-((halfGram a b c)ᵀ * correction a b c B)ᵀ)
        (residual a b c B L) := by
  let T := correction a b c B
  have hB : B = halfGram a b c * T + (halfGram a b c)ᵀ * T := by
    rw [← Matrix.add_mul, symmetrize_halfGram, correction_identity a b c hb]
  change (fromBlocks 1 (-T) 0 1)ᵀ * fromBlocks (halfGram a b c) B 0 L *
      fromBlocks 1 (-T) 0 1 =
    fromBlocks (halfGram a b c) ((halfGram a b c)ᵀ * T)
      (-((halfGram a b c)ᵀ * T)ᵀ) (L - Tᵀ * (halfGram a b c)ᵀ * T)
  simp only [fromBlocks_transpose, transpose_one, transpose_neg, transpose_zero,
    fromBlocks_multiply, Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, Matrix.mul_one,
    add_zero, Matrix.mul_neg, Matrix.neg_mul, transpose_mul, transpose_transpose]
  congr 1
  · rw [hB]
    abel
  · rw [hB]
    simp only [Matrix.mul_add, Matrix.mul_assoc]
    abel

private theorem skew_cross_self {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ (ZMod 8)) (B : Matrix κ ι (ZMod 8))
    (R : Matrix ι ι (ZMod 8)) (w : κ ⊕ ι → ZMod 8) :
    (fromBlocks A B (-Bᵀ) R).toBilin' w w =
      A.toBilin' (w ∘ Sum.inl) (w ∘ Sum.inl) +
        R.toBilin' (w ∘ Sum.inr) (w ∘ Sum.inr) := by
  have cross : (∑ i : ι, ∑ j : κ, w (Sum.inr i) * (-Bᵀ) i j * w (Sum.inl j)) =
      -(∑ j : κ, ∑ i : ι, w (Sum.inl j) * B j i * w (Sum.inr i)) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Matrix.neg_apply, Matrix.transpose_apply]
    ring
  simp only [Matrix.toBilin'_apply, Fintype.sum_sum_type,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
    Finset.sum_add_distrib, Function.comp_apply]
  rw [cross]
  abel

/-- Eliminate an odd binary pivot without losing the quadratic half-norm.
The complement remains an even symmetric unit-determinant Gram matrix whenever
the whole matrix has unit determinant. The substitution has determinant one. -/
theorem even_binary_elimination (a b c : ZMod 8) (hb : residue b = 1)
    (B : Matrix (Fin 2) ι (ZMod 8)) (L : Matrix ι ι (ZMod 8))
    (hu : IsUnit (fromBlocks (gram a b c) B Bᵀ (L + Lᵀ)).det) :
    let P := shear a b c B
    let R := residual a b c B L
    P.det = 1 ∧
      Pᵀ * fromBlocks (gram a b c) B Bᵀ (L + Lᵀ) * P =
        fromBlocks (gram a b c) 0 0 (R + Rᵀ) ∧
      IsUnit (R + Rᵀ).det ∧
      ∀ w : Fin 2 ⊕ ι → ZMod 8,
        (fromBlocks (halfGram a b c) B 0 L).toBilin' (P *ᵥ w) (P *ᵥ w) =
          (halfGram a b c).toBilin' (w ∘ Sum.inl) (w ∘ Sum.inl) +
            R.toBilin' (w ∘ Sum.inr) (w ∘ Sum.inr) := by
  let P := shear a b c B
  let R := residual a b c B L
  have hP : P.det = 1 := by simp [P, shear]
  have hhalf := transformed_half a b c hb B L
  have hsym : Pᵀ * fromBlocks (gram a b c) B Bᵀ (L + Lᵀ) * P =
      fromBlocks (gram a b c) 0 0 (R + Rᵀ) := by
    have full : fromBlocks (halfGram a b c) B 0 L +
        (fromBlocks (halfGram a b c) B 0 L)ᵀ =
        fromBlocks (gram a b c) B Bᵀ (L + Lᵀ) := by
      rw [fromBlocks_transpose, fromBlocks_add, symmetrize_halfGram]
      simp
    have split :
        fromBlocks (halfGram a b c) ((halfGram a b c)ᵀ * correction a b c B)
          (-((halfGram a b c)ᵀ * correction a b c B)ᵀ) R +
        (fromBlocks (halfGram a b c) ((halfGram a b c)ᵀ * correction a b c B)
          (-((halfGram a b c)ᵀ * correction a b c B)ᵀ) R)ᵀ =
        fromBlocks (gram a b c) 0 0 (R + Rᵀ) := by
      rw [fromBlocks_transpose, fromBlocks_add, symmetrize_halfGram]
      simp
    calc
      Pᵀ * fromBlocks (gram a b c) B Bᵀ (L + Lᵀ) * P =
          Pᵀ * fromBlocks (halfGram a b c) B 0 L * P +
            (Pᵀ * fromBlocks (halfGram a b c) B 0 L * P)ᵀ := by
        rw [← full]
        simp only [Matrix.mul_add, Matrix.add_mul, transpose_mul, transpose_transpose,
          Matrix.mul_assoc]
      _ = _ := by rw [hhalf]; exact split
  have determinant : (fromBlocks (gram a b c) B Bᵀ (L + Lᵀ)).det =
      (gram a b c).det * (R + Rᵀ).det := by
    have h := congrArg Matrix.det hsym
    simpa [det_mul, det_transpose, hP, det_fromBlocks_zero₁₂] using h
  refine ⟨hP, hsym, (IsUnit.mul_iff.mp (determinant ▸ hu)).2, ?_⟩
  intro w
  have h := congrArg (fun Q : LinearMap.BilinForm (ZMod 8) (Fin 2 ⊕ ι → ZMod 8) => Q w w)
    (Matrix.toBilin'_comp (fromBlocks (halfGram a b c) B 0 L) P P)
  change (fromBlocks (halfGram a b c) B 0 L).toBilin' (P *ᵥ w) (P *ᵥ w) = _ at h
  rw [h, hhalf]
  exact skew_cross_self _ _ _ w

#print axioms even_binary_elimination

end

end D5.S3.VertexAlgebra.TwistedGround.BinarySchur
