module

public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import OmegaBuild.Commands

/-! Omega original.

Strict kernel inclusions and block ranks for one-sided matrix annihilator witnesses. -/

compile_only_with_mathlib

set_option autoImplicit false

public section

namespace OmegaMath.MatrixAnnihilatorRank

open scoped Matrix

variable {F ι : Type*} [Field F] [Fintype ι]

private theorem rank_lt_iff_ker_lt
    {m₁ m₂ : Type*} {P : Matrix m₁ ι F} {Q : Matrix m₂ ι F}
    (hker : LinearMap.ker Q.mulVecLin ≤ LinearMap.ker P.mulVecLin) :
    P.rank < Q.rank ↔ LinearMap.ker Q.mulVecLin < LinearMap.ker P.mulVecLin := by
  have hP : P.rank + Module.finrank F (LinearMap.ker P.mulVecLin) = Fintype.card ι := by
    simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card] using
      P.mulVecLin.finrank_range_add_finrank_ker
  have hQ : Q.rank + Module.finrank F (LinearMap.ker Q.mulVecLin) = Fintype.card ι := by
    simpa only [Matrix.rank, Module.finrank_fintype_fun_eq_card] using
      Q.mulVecLin.finrank_range_add_finrank_ker
  constructor
  · intro hRank
    refine lt_of_le_of_ne hker ?_
    intro hEq
    rw [hEq] at hQ
    omega
  · intro hStrict
    have hDim := Submodule.finrank_lt_finrank_of_lt hStrict
    omega

private theorem ker_fromRows {m₁ m₂ : Type*}
    (C : Matrix m₁ ι F) (A : Matrix m₂ ι F) :
    LinearMap.ker (Matrix.fromRows C A).mulVecLin =
      LinearMap.ker C.mulVecLin ⊓ LinearMap.ker A.mulVecLin := by
  ext v
  simp only [Submodule.mem_inf, LinearMap.mem_ker, Matrix.mulVecLin_apply,
    Matrix.fromRows_mulVec]
  constructor
  · intro h
    exact ⟨funext fun i => congrFun h (Sum.inl i),
      funext fun i => congrFun h (Sum.inr i)⟩
  · rintro ⟨hC, hA⟩
    rw [hC, hA]
    funext i
    cases i <;> rfl

private theorem ker_mul_le (A B : Matrix ι ι F) :
    LinearMap.ker B.mulVecLin ≤ LinearMap.ker (A * B).mulVecLin := by
  rw [Matrix.mulVecLin_mul]
  exact LinearMap.ker_le_ker_comp B.mulVecLin A.mulVecLin

/-- A right matrix witness exists exactly when the product kernel strictly contains
the kernel of the second factor and the kernel of the product stacked above the first factor. -/
theorem rightWitness_iff_strict_kernels (A B : Matrix ι ι F) :
    (∃ T : Matrix ι ι F, (A * B) * T = 0 ∧ A * T ≠ 0 ∧ B * T ≠ 0) ↔
      LinearMap.ker B.mulVecLin < LinearMap.ker (A * B).mulVecLin ∧
        LinearMap.ker (Matrix.fromRows (A * B) A).mulVecLin <
          LinearMap.ker (A * B).mulVecLin := by
  rw [ker_fromRows]
  constructor
  · rintro ⟨T, hProduct, hA, hB⟩
    have col_mem (j : ι) : T.col j ∈ LinearMap.ker (A * B).mulVecLin := by
      apply LinearMap.mem_ker.mpr
      rw [Matrix.mulVecLin_apply, ← Matrix.col_mul_eq_mulVec_col, hProduct]
      rfl
    have product_eq_zero_of_le (M : Matrix ι ι F)
        (h : LinearMap.ker (A * B).mulVecLin ≤ LinearMap.ker M.mulVecLin) :
        M * T = 0 := by
      apply Matrix.ext_col
      intro j
      rw [Matrix.col_mul_eq_mulVec_col]
      exact LinearMap.mem_ker.mp (h (col_mem j))
    refine ⟨lt_iff_le_not_ge.mpr ⟨ker_mul_le A B, ?_⟩,
      lt_iff_le_not_ge.mpr ⟨inf_le_left, ?_⟩⟩
    · exact fun h => hB (product_eq_zero_of_le B h)
    · exact fun h => hA (product_eq_zero_of_le A (h.trans inf_le_right))
  · rintro ⟨hB, hStack⟩
    have hA : ¬ LinearMap.ker (A * B).mulVecLin ≤ LinearMap.ker A.mulVecLin :=
      fun h => (not_le_of_gt hStack) (le_inf le_rfl h)
    have hUnion : ¬ (LinearMap.ker (A * B).mulVecLin : Set (ι → F)) ⊆
        (LinearMap.ker A.mulVecLin : Set (ι → F)) ∪ LinearMap.ker B.mulVecLin :=
      fun h => (AddSubgroupClass.subset_union.mp h).elim hA (not_le_of_gt hB)
    obtain ⟨v, hvProduct, hvOutside⟩ := Set.not_subset.mp hUnion
    have hvA : A *ᵥ v ≠ 0 := fun h => hvOutside (Or.inl (LinearMap.mem_ker.mpr h))
    have hvB : B *ᵥ v ≠ 0 := fun h => hvOutside (Or.inr (LinearMap.mem_ker.mpr h))
    have hv : v ≠ 0 := by
      intro h
      exact hvA (by rw [h, Matrix.mulVec_zero])
    have hvZero : (A * B) *ᵥ v = 0 := LinearMap.mem_ker.mp hvProduct
    refine ⟨Matrix.vecMulVec v v, ?_, ?_, ?_⟩
    · rw [Matrix.mul_vecMulVec, hvZero, Matrix.zero_vecMulVec]
    · rw [Matrix.mul_vecMulVec]
      exact Matrix.vecMulVec_ne_zero hvA hv
    · rw [Matrix.mul_vecMulVec]
      exact Matrix.vecMulVec_ne_zero hvB hv

/-- The right witness is equivalent to two strict rank inequalities. -/
theorem rightWitness_iff_rank (A B : Matrix ι ι F) :
    (∃ T : Matrix ι ι F, (A * B) * T = 0 ∧ A * T ≠ 0 ∧ B * T ≠ 0) ↔
      (A * B).rank < B.rank ∧ (A * B).rank < (Matrix.fromRows (A * B) A).rank := by
  have hStack : LinearMap.ker (Matrix.fromRows (A * B) A).mulVecLin ≤
      LinearMap.ker (A * B).mulVecLin := by
    rw [ker_fromRows]
    exact inf_le_left
  exact (rightWitness_iff_strict_kernels A B).trans
    (and_congr (rank_lt_iff_ker_lt (ker_mul_le A B)).symm
      (rank_lt_iff_ker_lt hStack).symm)

/-- Transposing the left witness swaps the two factors and turns the row stack
in the right criterion into a column block. -/
theorem leftWitness_iff_rank (A B : Matrix ι ι F) :
    (∃ T : Matrix ι ι F, T * (A * B) = 0 ∧ T * A ≠ 0 ∧ T * B ≠ 0) ↔
      (A * B).rank < A.rank ∧ (A * B).rank < (Matrix.fromCols (A * B) B).rank := by
  have hTranspose :
      (∃ T : Matrix ι ι F, T * (A * B) = 0 ∧ T * A ≠ 0 ∧ T * B ≠ 0) ↔
        ∃ T : Matrix ι ι F, (Bᵀ * Aᵀ) * T = 0 ∧ Bᵀ * T ≠ 0 ∧ Aᵀ * T ≠ 0 := by
    constructor
    · rintro ⟨T, hProduct, hA, hB⟩
      refine ⟨Tᵀ, ?_, ?_, ?_⟩
      · simpa only [Matrix.transpose_mul] using Matrix.transpose_eq_zero.mpr hProduct
      · simpa only [Matrix.transpose_mul, Matrix.transpose_eq_zero] using
          (show (T * B)ᵀ ≠ 0 from fun h => hB (Matrix.transpose_eq_zero.mp h))
      · simpa only [Matrix.transpose_mul, Matrix.transpose_eq_zero] using
          (show (T * A)ᵀ ≠ 0 from fun h => hA (Matrix.transpose_eq_zero.mp h))
    · rintro ⟨T, hProduct, hB, hA⟩
      refine ⟨Tᵀ, ?_, ?_, ?_⟩
      · simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
          Matrix.transpose_eq_zero.mpr hProduct
      · intro h
        apply hA
        simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
          Matrix.transpose_eq_zero.mpr h
      · intro h
        apply hB
        simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
          Matrix.transpose_eq_zero.mpr h
  have hRank := rightWitness_iff_rank Bᵀ Aᵀ
  rw [← Matrix.transpose_mul] at hTranspose
  simp only [← Matrix.transpose_mul, ← Matrix.transpose_fromCols,
    Matrix.rank_transpose] at hRank
  exact hTranspose.trans hRank

/-- The expanded nonzero one-sided annihilator predicate for a square matrix
is equivalent to being nonzero and singular. -/
theorem nonzero_annihilator_iff_det_eq_zero [DecidableEq ι] (A : Matrix ι ι F) :
    (A ≠ 0 ∧ ∃ T : Matrix ι ι F, T ≠ 0 ∧ (A * T = 0 ∨ T * A = 0)) ↔
      A ≠ 0 ∧ A.det = 0 := by
  have rightRegular :
      (∀ T : Matrix ι ι F, A * T = 0 → T = 0) ↔ A.det ≠ 0 :=
    (isLeftRegular_iff_right_eq_zero_of_mul (r := A)).symm.trans
      ((Matrix.isLeftRegular_iff_nonsingular (A := A)).trans
        (Matrix.nonsingular_iff_det_ne_zero (A := A)))
  have leftRegular :
      (∀ T : Matrix ι ι F, T * A = 0 → T = 0) ↔ A.det ≠ 0 :=
    (isRightRegular_iff_left_eq_zero_of_mul (r := A)).symm.trans
      ((Matrix.isRightRegular_iff_nonsingular (A := A)).trans
        (Matrix.nonsingular_iff_det_ne_zero (A := A)))
  have witness_iff (p : Matrix ι ι F → Prop)
      (regular : (∀ T, p T → T = 0) ↔ A.det ≠ 0) :
      (∃ T, T ≠ 0 ∧ p T) ↔ A.det = 0 := by
    constructor
    · rintro ⟨T, hT, hp⟩
      exact Classical.byContradiction (fun hDet => hT (regular.mpr hDet T hp))
    · intro hDet
      apply Classical.byContradiction
      intro hWitness
      have hZero : ∀ T, p T → T = 0 := by
        intro T hp
        exact Classical.byContradiction (fun hT => hWitness ⟨T, hT, hp⟩)
      exact (regular.mp hZero) hDet
  have right := witness_iff (fun T => A * T = 0) rightRegular
  have left := witness_iff (fun T => T * A = 0) leftRegular
  constructor
  · rintro ⟨hA, T, hT, h⟩
    exact ⟨hA, h.elim (fun hAT => right.mp ⟨T, hT, hAT⟩)
      (fun hTA => left.mp ⟨T, hT, hTA⟩)⟩
  · rintro ⟨hA, hDet⟩
    obtain ⟨T, hT, hAT⟩ := right.mpr hDet
    exact ⟨hA, T, hT, Or.inl hAT⟩

end OmegaMath.MatrixAnnihilatorRank
