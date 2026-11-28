import OmegaBuild.Commands
import Mathlib.Basic.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.UnitaryGroup

/-! Omega original.

Real block matrices for complex linear maps and their determinant. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped Matrix ComplexConjugate

namespace OmegaMath.ComplexRealification

variable {n : Type*}

/-- Real and imaginary coordinates of a complex matrix action. -/
def realification (A : Matrix n n ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℝ :=
  fromBlocks (A.map Complex.re) (-(A.map Complex.im)) (A.map Complex.im) (A.map Complex.re)

theorem realification_injective : Function.Injective (realification (n := n)) := by
  intro A B h
  obtain ⟨hr, _, hi, _⟩ := fromBlocks_inj.mp h
  ext i j
  exact Complex.ext (congrFun (congrFun hr i) j) (congrFun (congrFun hi i) j)

variable [DecidableEq n]

private theorem im_one : (1 : Matrix n n ℂ).map Complex.im = 0 := by
  ext i j
  by_cases hij : i = j <;> simp [hij]

theorem realification_one : realification (1 : Matrix n n ℂ) = 1 := by
  simp [realification, im_one, fromBlocks_one]

omit [DecidableEq n] in
theorem realification_mul [Fintype n] (A B : Matrix n n ℂ) :
    realification (A * B) = realification A * realification B := by
  have hr : (A * B).map Complex.re =
      A.map Complex.re * B.map Complex.re - A.map Complex.im * B.map Complex.im := by
    ext i j
    simp [Matrix.mul_apply, Complex.re_sum, Complex.mul_re, Finset.sum_sub_distrib]
  have hi : (A * B).map Complex.im =
      A.map Complex.re * B.map Complex.im + A.map Complex.im * B.map Complex.re := by
    ext i j
    simp [Matrix.mul_apply, Complex.im_sum, Complex.mul_im, Finset.sum_add_distrib, add_comm]
  simp [realification, hr, hi, fromBlocks_multiply, sub_eq_add_neg, add_comm]

omit [DecidableEq n] in
theorem realification_conjTranspose (A : Matrix n n ℂ) :
    realification Aᴴ = (realification A)ᵀ := by
  rw [realification, realification, fromBlocks_transpose]
  apply fromBlocks_inj.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    simp [Matrix.conjTranspose_apply, Complex.star_def]

variable [Fintype n]

private def changeCoordinates : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  fromBlocks 1 (Complex.I • 1) 1 (-Complex.I • 1)

private theorem changeCoordinates_det_ne_zero :
    (changeCoordinates (n := n)).det ≠ 0 := by
  rw [changeCoordinates, det_fromBlocks_one₁₁, Matrix.one_mul, ← sub_smul, det_smul, det_one,
    mul_one]
  apply pow_ne_zero
  intro h
  have him := congrArg Complex.im h
  norm_num [Complex.sub_im, Complex.neg_im] at him

private theorem realification_diagonalize (A : Matrix n n ℂ) :
    changeCoordinates * (realification A).map Complex.ofReal =
    fromBlocks A 0 0 (A.map conj) * changeCoordinates := by
  simp only [changeCoordinates, realification, fromBlocks_map, fromBlocks_multiply,
    Matrix.one_mul, Matrix.mul_one, add_zero, zero_add,
    Matrix.smul_mul, Matrix.mul_smul, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;>
    apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.neg_re, Complex.neg_im]

/-- The complexification of a realified map has determinant equal to the
product of the complex determinant and its conjugate. -/
theorem realification_det (A : Matrix n n ℂ) :
    ((realification A).det : ℂ) = A.det * conj A.det := by
  have h := congrArg Matrix.det (realification_diagonalize A)
  rw [det_mul, det_mul, mul_comm _ (changeCoordinates (n := n)).det] at h
  have hd := mul_left_cancel₀ changeCoordinates_det_ne_zero h
  rw [det_fromBlocks_zero₂₁] at hd
  change Complex.ofRealHom (realification A).det = A.det * (starRingEnd ℂ) A.det
  rw [Complex.ofRealHom.map_det, (starRingEnd ℂ).map_det]
  exact hd

/-- Realification sends special unitary matrices to special orthogonal matrices. -/
def specialUnitaryToSpecialOrthogonal :
    Matrix.specialUnitaryGroup n ℂ →* Matrix.specialOrthogonalGroup (n ⊕ n) ℝ where
  toFun A := ⟨realification A.1, by
    obtain ⟨hu, hd⟩ := Matrix.mem_specialUnitaryGroup_iff.mp A.2
    apply Matrix.mem_specialOrthogonalGroup_iff.mpr
    constructor
    · apply (Matrix.mem_orthogonalGroup_iff (n ⊕ n) ℝ).mpr
      rw [← realification_conjTranspose, ← realification_mul,
        ← Matrix.star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff.mp hu,
        realification_one]
    · apply Complex.ofReal_injective
      rw [realification_det, hd]
      simp⟩
  map_one' := Subtype.ext realification_one
  map_mul' A B := Subtype.ext (realification_mul A.1 B.1)

theorem specialUnitaryToSpecialOrthogonal_injective :
    Function.Injective (specialUnitaryToSpecialOrthogonal (n := n)) := by
  intro A B h
  exact Subtype.ext (realification_injective (congrArg Subtype.val h))

/-- In numbered coordinates, the real parts precede the imaginary parts. -/
def specialUnitaryToSpecialOrthogonalFin (m : ℕ) :
    Matrix.specialUnitaryGroup (Fin m) ℂ →*
      Matrix.specialOrthogonalGroup (Fin (m + m)) ℝ where
  toFun A := ⟨Matrix.reindexAlgEquiv ℝ ℝ finSumFinEquiv
      (specialUnitaryToSpecialOrthogonal A).1, by
    obtain ⟨ho, hd⟩ := Matrix.mem_specialOrthogonalGroup_iff.mp
      (specialUnitaryToSpecialOrthogonal A).2
    apply Matrix.mem_specialOrthogonalGroup_iff.mpr
    constructor
    · apply (Matrix.mem_orthogonalGroup_iff (Fin (m + m)) ℝ).mpr
      change (Matrix.reindex _ _ _) * (Matrix.reindex _ _ _)ᵀ = _
      rw [transpose_reindex]
      change Matrix.reindexAlgEquiv ℝ ℝ finSumFinEquiv _ *
        Matrix.reindexAlgEquiv ℝ ℝ finSumFinEquiv _ = _
      rw [← map_mul, (Matrix.mem_orthogonalGroup_iff (Fin m ⊕ Fin m) ℝ).mp ho, map_one]
    · exact (Matrix.det_reindex_self finSumFinEquiv _).trans hd⟩
  map_one' := Subtype.ext <| by
    change Matrix.reindexAlgEquiv ℝ ℝ finSumFinEquiv (realification 1) = 1
    rw [realification_one, map_one]
  map_mul' A B := Subtype.ext <| by
    change Matrix.reindexAlgEquiv ℝ ℝ finSumFinEquiv (realification (A.1 * B.1)) = _
    rw [realification_mul, map_mul]
    rfl

theorem specialUnitaryToSpecialOrthogonalFin_injective (m : ℕ) :
    Function.Injective (specialUnitaryToSpecialOrthogonalFin m) := by
  intro A B h
  exact specialUnitaryToSpecialOrthogonal_injective <| Subtype.ext <|
    (Matrix.reindexAlgEquiv ℝ ℝ finSumFinEquiv).injective (congrArg Subtype.val h)

end OmegaMath.ComplexRealification
