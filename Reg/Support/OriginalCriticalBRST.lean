import D5.S3.VertexAlgebra.Lattice.LatticeBRSTCohomologyNonvacuity

/-! Full critical parameter domain for quotient audit attempts. The diagonal
lattice is only an inhabited infinite-carrier sensitivity witness; no original
state or quotient theorem is specialized or replaced by it. -/
set_option autoImplicit false
open _root_.D5.S3.VertexAlgebra
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
namespace Reg.Support.OriginalCriticalBRST
noncomputable section
structure Input where
  D : LatticeData
  H : Matrix (Fin D.rank) (Fin D.rank) ℂ
  h26 : D.rank = 26
  hHG : H * LatticeSugawaraCurrents.gramComplex D = 1
  hGH : LatticeSugawaraCurrents.gramComplex D * H = 1

abbrev Space (x : Input) :=
  LatticeBRSTCohomologyField.Cohomology x.D x.H x.h26 x.hHG x.hGH

abbrev diagonal : LatticeData where
  rank := 26
  G := (2 : ℤ) • (1 : Matrix (Fin 26) (Fin 26) ℤ)
  symmetric := by intro i j; simp [Matrix.one_apply, eq_comm]
  even_diagonal := by intro i; norm_num

private theorem diagonal_gram : LatticeSugawaraCurrents.gramComplex diagonal =
    (2 : ℂ) • (1 : Matrix (Fin 26) (Fin 26) ℂ) := by
  ext i j
  change ((((2 : ℤ) • (1 : Matrix (Fin 26) (Fin 26) ℤ)) i j : ℤ) : ℂ) =
    ((2 : ℂ) • (1 : Matrix (Fin 26) (Fin 26) ℂ)) i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

private theorem diagonal_inverse_left :
    ((2 : ℂ)⁻¹ • (1 : Matrix (Fin 26) (Fin 26) ℂ)) *
      LatticeSugawaraCurrents.gramComplex diagonal = 1 := by
  rw [diagonal_gram]
  simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

private theorem diagonal_inverse_right :
    LatticeSugawaraCurrents.gramComplex diagonal *
      ((2 : ℂ)⁻¹ • (1 : Matrix (Fin 26) (Fin 26) ℂ)) = 1 := by
  rw [diagonal_gram]
  simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul]

def witness : Input := ⟨diagonal, (2 : ℂ)⁻¹ • 1, rfl,
  diagonal_inverse_left, diagonal_inverse_right⟩

instance space_nontrivial (x : Input) : Nontrivial (Space x) :=
  LatticeBRSTCohomologyField.cohomology_nontrivial x.D x.H x.h26 x.hHG x.hGH
end
end Reg.Support.OriginalCriticalBRST
