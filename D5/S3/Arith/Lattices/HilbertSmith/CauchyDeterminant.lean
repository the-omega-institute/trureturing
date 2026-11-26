/- GID: D5/S3/Arith/Lattices/HilbertSmith/CauchyDeterminant
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/HilbertSmith/CauchyDeterminant
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Schur elimination gives the general Cauchy determinant product. -/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Option
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The Cauchy determinant -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Lattices.HilbertSmith.CauchyDeterminant

open Finset
open scoped BigOperators

section Cauchy

variable {K : Type*} [Field K]

/-- The Cauchy matrix associated to two ordered arrays. -/
def cauchyMatrix {k : ℕ} (x y : Fin k → K) : Matrix (Fin k) (Fin k) K :=
  fun i j => (x i + y j)⁻¹

/-- One factor for every pair of indices in increasing order. -/
def orderedDifferences {k : ℕ} (x : Fin k → K) : K :=
  ∏ i, ∏ j ∈ Ioi i, (x j - x i)

def cauchyDenominator {k : ℕ} (x y : Fin k → K) : K :=
  ∏ i, ∏ j, (x i + y j)

private theorem orderedDifferences_succ {k : ℕ} (x : Fin (k + 1) → K) :
    orderedDifferences x =
      (∏ i : Fin k, (x i.succ - x 0)) * orderedDifferences (fun i => x i.succ) := by
  unfold orderedDifferences
  rw [Fin.prod_univ_succ, Fin.prod_Ioi_zero]
  simp only [Fin.prod_Ioi_succ]

private theorem cauchyDenominator_succ {k : ℕ} (x y : Fin (k + 1) → K) :
    cauchyDenominator x y =
      (x 0 + y 0) * (∏ i : Fin k, (x i.succ + y 0)) *
        (∏ j : Fin k, (x 0 + y j.succ)) *
        cauchyDenominator (fun i => x i.succ) (fun j => y j.succ) := by
  unfold cauchyDenominator
  have splitRow (i : Fin (k + 1)) :
      (∏ j, (x i + y j)) = (x i + y 0) * ∏ j : Fin k, (x i + y j.succ) :=
    Fin.prod_univ_succ (fun j => x i + y j)
  rw [Fin.prod_univ_succ (fun i => ∏ j, (x i + y j))]
  simp_rw [splitRow]
  rw [Finset.prod_mul_distrib]
  ac_rfl

private def headTail (k : ℕ) : PUnit.{1} ⊕ Fin k ≃ Fin (k + 1) :=
  (Equiv.sumComm PUnit.{1} (Fin k)).trans
    ((Equiv.optionEquivSumPUnit (Fin k)).symm.trans (finSuccEquiv k).symm)

private theorem headTail_left {k : ℕ} (u : PUnit.{1}) :
    headTail k (Sum.inl u) = 0 := by
  change (finSuccEquiv k).symm none = 0
  exact finSuccEquiv_symm_none

private theorem headTail_right {k : ℕ} (i : Fin k) :
    headTail k (Sum.inr i) = i.succ := by
  change (finSuccEquiv k).symm (some i) = i.succ
  exact finSuccEquiv_symm_some i

private theorem cauchy_schur_factor (x x₀ y y₀ : K)
    (h : x + y ≠ 0) (hr : x + y₀ ≠ 0) (hc : x₀ + y ≠ 0) :
    (x + y)⁻¹ - (x + y₀)⁻¹ * (x₀ + y₀) * (x₀ + y)⁻¹ =
      ((x - x₀) / (x + y₀)) * (x + y)⁻¹ * ((y - y₀) / (x₀ + y)) := by
  field_simp [h, hr, hc] <;> ring

/-- The Cauchy determinant, by eliminating the first column with a
one-by-one Schur complement and scaling its rows and columns.
Nonvanishing of all sums suffices, including when coordinates coincide. -/
theorem det_cauchyMatrix {k : ℕ} (x y : Fin k → K)
    (hs : ∀ i j, x i + y j ≠ 0) :
    (cauchyMatrix x y).det =
      orderedDifferences x * orderedDifferences y / cauchyDenominator x y := by
  classical
  induction k with
  | zero =>
    simp [orderedDifferences, cauchyDenominator]
  | succ k ih =>
    let pivot : K := x 0 + y 0
    let A : Matrix PUnit.{1} PUnit.{1} K := fun _ _ => pivot⁻¹
    let Ainv : Matrix PUnit.{1} PUnit.{1} K := fun _ _ => pivot
    let B : Matrix PUnit.{1} (Fin k) K := fun _ j => (x 0 + y j.succ)⁻¹
    let C : Matrix (Fin k) PUnit.{1} K := fun i _ => (x i.succ + y 0)⁻¹
    let D : Matrix (Fin k) (Fin k) K := cauchyMatrix (fun i => x i.succ) (fun j => y j.succ)
    let r : Fin k → K := fun i => (x i.succ - x 0) / (x i.succ + y 0)
    let c : Fin k → K := fun j => (y j.succ - y 0) / (x 0 + y j.succ)
    have hpivot : pivot ≠ 0 := hs 0 0
    let : Invertible A :=
      { invOf := Ainv
        invOf_mul_self := by
          apply Matrix.ext
          intro i j
          cases i
          cases j
          rw [Matrix.mul_apply, Fintype.sum_unique, Matrix.one_apply_eq]
          exact mul_inv_cancel₀ hpivot
        mul_invOf_self := by
          apply Matrix.ext
          intro i j
          cases i
          cases j
          rw [Matrix.mul_apply, Fintype.sum_unique, Matrix.one_apply_eq]
          exact inv_mul_cancel₀ hpivot }
    have hinv : ⅟A = Ainv := rfl
    have hblocks : (cauchyMatrix x y).submatrix (headTail k) (headTail k) =
        Matrix.fromBlocks A B C D := by
      apply Matrix.ext
      intro i j
      cases i <;> cases j <;>
        simp [Matrix.submatrix_apply, headTail_left, headTail_right, Matrix.fromBlocks,
          A, B, C, D, pivot, cauchyMatrix]
    have hschur : D - C * ⅟A * B = Matrix.diagonal r * D * Matrix.diagonal c := by
      apply Matrix.ext
      intro i j
      rw [hinv, Matrix.mul_diagonal, Matrix.diagonal_mul]
      change D i j - (C * Ainv * B) i j = r i * D i j * c j
      rw [Matrix.mul_apply, Fintype.sum_unique, Matrix.mul_apply, Fintype.sum_unique]
      simpa [D, C, Ainv, B, pivot, r, c, cauchyMatrix] using
        cauchy_schur_factor (x i.succ) (x 0) (y j.succ) (y 0)
          (hs i.succ j.succ) (hs i.succ 0) (hs 0 j.succ)
    have hdetA : A.det = pivot⁻¹ := Matrix.det_unique A
    have htail : cauchyDenominator (fun i : Fin k => x i.succ) (fun j => y j.succ) ≠ 0 := by
      unfold cauchyDenominator
      exact prod_ne_zero_iff.mpr fun i _ => prod_ne_zero_iff.mpr fun j _ => hs i.succ j.succ
    have hrow : (∏ i : Fin k, (x i.succ + y 0)) ≠ 0 :=
      prod_ne_zero_iff.mpr fun i _ => hs i.succ 0
    have hcol : (∏ j : Fin k, (x 0 + y j.succ)) ≠ 0 :=
      prod_ne_zero_iff.mpr fun j _ => hs 0 j.succ
    calc
      (cauchyMatrix x y).det = (Matrix.fromBlocks A B C D).det := by
        rw [← hblocks, Matrix.det_submatrix_equiv_self]
      _ = pivot⁻¹ * ((∏ i, r i) * D.det * (∏ j, c j)) := by
        rw [Matrix.det_fromBlocks₁₁, hdetA, hschur, Matrix.det_mul, Matrix.det_mul,
          Matrix.det_diagonal, Matrix.det_diagonal]
      _ = _ := by
        rw [show D.det = orderedDifferences (fun i : Fin k => x i.succ) *
            orderedDifferences (fun j : Fin k => y j.succ) /
            cauchyDenominator (fun i : Fin k => x i.succ) (fun j => y j.succ) from
          ih _ _ (fun i j => hs i.succ j.succ)]
        rw [orderedDifferences_succ x, orderedDifferences_succ y, cauchyDenominator_succ x y]
        dsimp only [r, c]
        simp only [Finset.prod_div_distrib]
        change _ = _ / (pivot * (∏ i : Fin k, (x i.succ + y 0)) *
          (∏ j : Fin k, (x 0 + y j.succ)) *
          cauchyDenominator (fun i : Fin k => x i.succ) (fun j => y j.succ))
        field_simp [hpivot, hrow, hcol, htail] <;> ring

end Cauchy

end D5.S3.Arith.Lattices.HilbertSmith.CauchyDeterminant
