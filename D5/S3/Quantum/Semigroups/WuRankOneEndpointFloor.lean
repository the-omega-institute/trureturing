/- GID: D5/S3/Quantum/Semigroups/WuRankOneEndpointFloor
   generality: I
   mirror-B: D5/B/S3/Quantum/Semigroups/WuRankOneEndpointFloor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The endpoint applies the two local maps on different tensor factors with a diagonal sign conjugation. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Information.Pauli.PauliMatrix
import Mathlib.Analysis.Matrix.Order

noncomputable section

open Matrix Kronecker
open scoped Matrix MatrixOrder ComplexOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

namespace WuRankOneEndpointFloor

abbrev Bit := Fin 2
abbrev Mode := Bit × Bit
abbrev Qubit := Matrix Bit Bit ℂ
abbrev TwoMode := Matrix Mode Mode ℂ

def lambda : ℝ := Real.sqrt (2 / 3)
private theorem lambda_sq : lambda ^ 2 = 2 / 3 :=
  Real.sq_sqrt (by norm_num)

def Λ (X : Qubit) : Qubit := fun i j =>
  if i = j then (5 / 6 : ℂ) * X i j + (1 / 6 : ℂ) * X i.rev j.rev
  else (lambda : ℂ) * X i j

def localMap : MatrixMap Bit Bit ℂ where
  toFun := Λ
  map_add' X Y := by
    ext i j
    by_cases h : i = j <;> simp [Λ, h] <;> ring
  map_smul' c X := by
    ext i j
    by_cases h : i = j <;> simp [Λ, h] <;> ring

private def signW (i : Mode) : ℂ := if i = (1, 0) then -1 else 1

/-- Lexicographic order is 00, 01, 10, 11. -/
def W : TwoMode := diagonal signW

def A₁ : MatrixMap Mode Mode ℂ :=
  (MatrixMap.kron localMap LinearMap.id).comp
    ((MatrixMap.conj W).comp ((MatrixMap.kron LinearMap.id localMap).comp
      (MatrixMap.conj W)))

private theorem conjW_apply (X : TwoMode) (i j : Mode) :
    MatrixMap.conj W X i j = signW i * X i j * signW j := by
  have hW : Wᴴ = W := by
    ext x y
    by_cases h : x = y
    · subst y
      by_cases h : x = (1, 0) <;> simp [W, signW, h, Matrix.conjTranspose_apply]
    · simp [W, Matrix.conjTranspose_apply, diagonal_apply, h, Ne.symm h]
  rw [MatrixMap.conj_apply, hW]
  unfold W
  rw [mul_diagonal, diagonal_mul]

private theorem left_apply (X : TwoMode) (i j k l : Bit) :
    MatrixMap.kron localMap LinearMap.id X (i,k) (j,l) =
      if i = j then (5 / 6 : ℂ) * X (i,k) (j,l) + (1 / 6 : ℂ) * X (i.rev,k) (j.rev,l)
      else (lambda : ℂ) * X (i,k) (j,l) := by
  rw [MatrixMap.kron_def]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Fin.sum_univ_two, localMap, Λ, Matrix.single_apply, Fin.rev,
      Fin.isValue, -one_div] <;> ring

private theorem right_apply (X : TwoMode) (i j k l : Bit) :
    MatrixMap.kron LinearMap.id localMap X (i,k) (j,l) =
      if k = l then (5 / 6 : ℂ) * X (i,k) (j,l) + (1 / 6 : ℂ) * X (i,k.rev) (j,l.rev)
      else (lambda : ℂ) * X (i,k) (j,l) := by
  rw [MatrixMap.kron_def]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [Fin.sum_univ_two, localMap, Λ, Matrix.single_apply, Fin.rev,
      Fin.isValue, -one_div] <;> ring

private theorem lambda_complex_sq : (lambda : ℂ) * (lambda : ℂ) = 2 / 3 := by
  rw [← Complex.ofReal_mul, show lambda * lambda = 2 / 3 by simpa [pow_two] using lambda_sq]
  push_cast
  rfl

theorem A1_apply (X : TwoMode) (i j k l : Bit) :
    A₁ X (i,k) (j,l) =
      if i = j then
        if k = l then
          (25 / 36 : ℂ) * X (i,k) (j,l) +
          (5 / 36 : ℂ) * X (i,k.rev) (j,l.rev) +
          (5 / 36 : ℂ) * X (i.rev,k) (j.rev,l) +
          (1 / 36 : ℂ) * X (i.rev,k.rev) (j.rev,l.rev)
        else (lambda : ℂ) * ((5 / 6 : ℂ) * X (i,k) (j,l) +
          (1 / 6 : ℂ) * X (i.rev,k) (j.rev,l))
      else if k = l then (lambda : ℂ) * ((5 / 6 : ℂ) * X (i,k) (j,l) -
          (1 / 6 : ℂ) * X (i,k.rev) (j,l.rev))
        else (2 / 3 : ℂ) * X (i,k) (j,l) := by
  simp only [A₁, LinearMap.comp_apply, left_apply, right_apply, conjW_apply]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [signW, Fin.rev, ← mul_assoc, lambda_complex_sq, -mul_eq_mul_left_iff, -mul_eq_mul_right_iff] <;> ring

#print axioms A1_apply

end WuRankOneEndpointFloor
