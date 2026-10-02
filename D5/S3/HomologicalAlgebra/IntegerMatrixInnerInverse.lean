/- GID: D5/S3/HomologicalAlgebra/IntegerMatrixInnerInverse
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/IntegerMatrixInnerInverse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every finite totally unimodular integer matrix admits an integer inner inverse. -/

import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyUnimodular
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Nat.Find
import Mathlib.Logic.Equiv.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse

open Matrix

set_option backward.isDefEq.respectTransparency false in
theorem exists_integer_inner_inverse
    {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℤ)
    (hA : A.IsTotallyUnimodular) :
    ∃ B : Matrix n m ℤ, A * B * A = A := by
  classical
  let P : ℕ → Prop := fun size =>
    ∃ (rows : Fin size → m) (cols : Fin size → n),
      Function.Injective rows ∧ Function.Injective cols ∧
        (A.submatrix rows cols).det ≠ 0
  have hzero : P 0 := by
    refine ⟨Fin.elim0, Fin.elim0, ?_, ?_, ?_⟩
    · exact Function.injective_of_subsingleton _
    · exact Function.injective_of_subsingleton _
    · simp
  let size := Nat.findGreatest P (Fintype.card m)
  obtain ⟨rows, cols, hrows, hcols, hdet⟩ :=
    Nat.findGreatest_spec (Nat.zero_le (Fintype.card m)) hzero
  let U : Matrix (Fin size) (Fin size) ℤ := A.submatrix rows cols
  have hunit : IsUnit U.det := by
    obtain ⟨sign, hsign⟩ := hA size rows cols hrows hcols
    cases sign with
    | zero => exact (hdet (by simpa using hsign.symm)).elim
    | neg => simp [U, ← hsign]
    | pos => simp [U, ← hsign]
  let : Invertible U := Matrix.invertibleOfIsUnitDet U hunit
  let RowRest := {row : m // row ∉ Set.range rows}
  let ColRest := {col : n // col ∉ Set.range cols}
  let rowEquiv : Fin size ⊕ RowRest ≃ m :=
    (Equiv.sumCongr (Equiv.ofInjective rows hrows) (Equiv.refl RowRest)).trans
      (Equiv.Set.sumCompl (Set.range rows))
  let colEquiv : Fin size ⊕ ColRest ≃ n :=
    (Equiv.sumCongr (Equiv.ofInjective cols hcols) (Equiv.refl ColRest)).trans
      (Equiv.Set.sumCompl (Set.range cols))
  let R : Matrix (Fin size) ColRest ℤ := fun row col => A (rows row) col.val
  let C : Matrix RowRest (Fin size) ℤ := fun row col => A row.val (cols col)
  let D : Matrix RowRest ColRest ℤ := fun row col => A row.val col.val
  have hreconstruct : D = C * ⅟U * R := by
    ext row col
    let borderRows : Fin size ⊕ Fin 1 → m := Sum.elim rows (fun _ => row.val)
    let borderCols : Fin size ⊕ Fin 1 → n := Sum.elim cols (fun _ => col.val)
    have hborderRows : Function.Injective borderRows := by
      apply Sum.elim_injective.mpr
      refine ⟨hrows, Function.injective_of_subsingleton _, ?_⟩
      intro selected extra heq
      exact row.property ⟨selected, heq⟩
    have hborderCols : Function.Injective borderCols := by
      apply Sum.elim_injective.mpr
      refine ⟨hcols, Function.injective_of_subsingleton _, ?_⟩
      intro selected extra heq
      exact col.property ⟨selected, heq⟩
    let indexEquiv : Fin size ⊕ Fin 1 ≃ Fin (size + 1) := finSumFinEquiv
    have hbound : size + 1 ≤ Fintype.card m := by
      simpa using Fintype.card_le_of_injective _ (hborderRows.comp indexEquiv.symm.injective)
    have hborderDet : (A.submatrix borderRows borderCols).det = 0 := by
      by_contra hnonzero
      have hnext : P (size + 1) := by
        refine ⟨borderRows ∘ indexEquiv.symm, borderCols ∘ indexEquiv.symm,
          hborderRows.comp indexEquiv.symm.injective,
          hborderCols.comp indexEquiv.symm.injective, ?_⟩
        change ((A.submatrix borderRows borderCols).submatrix
          indexEquiv.symm indexEquiv.symm).det ≠ 0
        rw [Matrix.det_submatrix_equiv_self]
        exact hnonzero
      have hmax := Nat.le_findGreatest hbound hnext
      exact Nat.not_succ_le_self size hmax
    have hblock : A.submatrix borderRows borderCols =
        Matrix.fromBlocks U (fun selected _ => R selected col)
          (fun _ selected => C row selected) (fun _ _ => D row col) := by
      ext left right
      cases left <;> cases right <;> rfl
    rw [hblock] at hborderDet
    rw [Matrix.det_fromBlocks₁₁, Matrix.det_unique (n := Fin 1)] at hborderDet
    have hresidual : D row col - (C * ⅟U * R) row col = 0 := by
      have hcancel := (mul_eq_zero.mp hborderDet).resolve_left hdet
      simpa [Matrix.sub_apply, Matrix.mul_apply] using hcancel
    exact sub_eq_zero.mp hresidual
  have hblock : A.submatrix rowEquiv colEquiv = Matrix.fromBlocks U R C D := by
    ext row col
    cases row <;> cases col <;> rfl
  let G : Matrix (Fin size ⊕ ColRest) (Fin size ⊕ RowRest) ℤ :=
    Matrix.fromBlocks (⅟U) 0 0 0
  have hinner : Matrix.fromBlocks U R C D * G * Matrix.fromBlocks U R C D =
      Matrix.fromBlocks U R C D := by
    simp only [G, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, mul_invOf_self, Matrix.one_mul,
      Matrix.invOf_mul_cancel_right, ← hreconstruct]
  refine ⟨G.submatrix colEquiv.symm rowEquiv.symm, ?_⟩
  apply (Matrix.reindex rowEquiv.symm colEquiv.symm).injective
  change (A * G.submatrix colEquiv.symm rowEquiv.symm * A).submatrix
    rowEquiv colEquiv = A.submatrix rowEquiv colEquiv
  rw [Matrix.submatrix_mul _ _ rowEquiv rowEquiv colEquiv rowEquiv.bijective,
    Matrix.submatrix_mul _ _ rowEquiv colEquiv rowEquiv colEquiv.bijective]
  have hG : (G.submatrix colEquiv.symm rowEquiv.symm).submatrix colEquiv rowEquiv = G := by
    ext row col
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rw [hG, hblock]
  exact hinner

end D5.S3.HomologicalAlgebra.IntegerMatrixInnerInverse
