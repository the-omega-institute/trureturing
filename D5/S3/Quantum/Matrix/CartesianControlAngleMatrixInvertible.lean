/- GID: D5/S3/Quantum/Matrix/CartesianControlAngleMatrixInvertible
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/CartesianControlAngleMatrixInvertible
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Cartesian-control angle matrices are invertible for all finite products. -/

import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Basic.Real.Basic

/-! Invertibility of the Cartesian-control angle matrix. -/
noncomputable section
open scoped BigOperators
set_option autoImplicit false

namespace D5.S3.Quantum.Matrix.CartesianControlAngleMatrixInvertible

private def A (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := fun r s =>
  if 0 < (r : ℕ) ∧ (r : ℕ) ≤ (s : ℕ) then (-1 : ℝ) else 1

private def E (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := fun r t =>
  if (r : ℕ) = 0 then (if (t : ℕ) = 0 then 1 else 0)
  else (if (t : ℕ) = 0 then 1 / 2 else 0) - (if t = r then 1 / 2 else 0)

private theorem E_mul_A (m : ℕ) :
    E m * A m = (⇑(IncidenceAlgebra.zeta ℝ (α := Fin m)) : Matrix (Fin m) (Fin m) ℝ) := by
  ext r s
  let z : Fin m := ⟨0, Nat.zero_lt_of_lt r.isLt⟩
  have hz (t : Fin m) : (t : ℕ) = 0 ↔ t = z := by
    change ((t : ℕ) = (z : ℕ) ↔ t = z)
    exact Fin.ext_iff.symm
  change (∑ t : Fin m,
    (if (r : ℕ) = 0 then (if (t : ℕ) = 0 then (1 : ℝ) else 0)
      else (if (t : ℕ) = 0 then 1 / 2 else 0) - (if t = r then 1 / 2 else 0)) *
    (if 0 < (t : ℕ) ∧ (t : ℕ) ≤ (s : ℕ) then (-1 : ℝ) else 1)) =
    if (r : ℕ) ≤ (s : ℕ) then 1 else 0
  by_cases hr : (r : ℕ) = 0
  · simp only [hr, ↓reduceIte, hz, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    simp only [z, lt_self_iff_false, false_and,
      ↓reduceIte, Nat.zero_le]
  · simp only [hr, ↓reduceIte, sub_mul, ite_mul, zero_mul, Finset.sum_sub_distrib,
      hz, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    have hrpos : 0 < (r : ℕ) := Nat.pos_of_ne_zero hr
    simp only [z, lt_self_iff_false, false_and,
      ↓reduceIte, hrpos, true_and]
    split_ifs <;> norm_num

private theorem det_zeta (m : ℕ) :
    Matrix.det (⇑(IncidenceAlgebra.zeta ℝ (α := Fin m))) = 1 := by
  have ht :
      Matrix.IsUpperTriangular (⇑(IncidenceAlgebra.zeta ℝ (α := Fin m))) := by
    intro i j hji
    exact IncidenceAlgebra.apply_eq_zero_of_not_le (not_le_of_gt hji) _
  rw [Matrix.det_of_isUpperTriangular ht]
  simp only [IncidenceAlgebra.zeta_apply, le_refl, ↓reduceIte, Finset.prod_const_one]

private theorem det_A_isUnit (m : ℕ) : IsUnit (A m).det := by
  have h : (E m).det * (A m).det = 1 := by
    rw [← Matrix.det_mul, E_mul_A, det_zeta]
  exact IsUnit.of_mul_eq_one_right (E m).det h

private def K {k : ℕ} (d : Fin k → ℕ) :
    Matrix ((l : Fin k) → Fin (d l)) ((l : Fin k) → Fin (d l)) ℝ := fun r s =>
  ∏ l, A (d l) (r l) (s l)

private def LinvPrime {k : ℕ} (d : Fin k → ℕ) :
    Matrix ((l : Fin k) → Fin (d l)) ((l : Fin k) → Fin (d l)) ℝ := fun r s =>
  ∏ l, (A (d l))⁻¹ (r l) (s l)

private theorem LinvPrime_mul_K {k : ℕ} (d : Fin k → ℕ) :
    LinvPrime d * K d = (1 : Matrix ((l : Fin k) → Fin (d l)) ((l : Fin k) → Fin (d l)) ℝ) := by
  classical
  ext s t
  change (∑ r : (l : Fin k) → Fin (d l),
    (∏ l, (A (d l))⁻¹ (s l) (r l)) * (∏ l, A (d l) (r l) (t l))) = _
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun l (r : Fin (d l)) =>
    (A (d l))⁻¹ (s l) r * A (d l) r (t l))]
  have h (l : Fin k) : (∑ r, (A (d l))⁻¹ (s l) r * A (d l) r (t l)) =
      if s l = t l then 1 else 0 := by
    change ((A (d l))⁻¹ * A (d l)) (s l) (t l) = _
    rw [Matrix.nonsing_inv_mul _ (det_A_isUnit _), Matrix.one_apply]
  simp only [h, Fintype.prod_boole, ← funext_iff, Matrix.one_apply]

def angleMatrix {k : ℕ} (d : Fin k → ℕ)
    (b g : Fin (∏ l, d l) ≃ ((l : Fin k) → Fin (d l))) :
    Matrix (Fin (∏ l, d l)) (Fin (∏ l, d l)) ℝ := fun i j =>
  ∏ l, (if 0 < (b i l : ℕ) ∧ (b i l : ℕ) ≤ (g j l : ℕ) then (-1 : ℝ) else 1)

def claim : Prop := ∀ (k : ℕ) (d : Fin k → ℕ)
    (b g : Fin (∏ l, d l) ≃ ((l : Fin k) → Fin (d l))),
    IsUnit (angleMatrix d b g)

theorem result : claim := by
  intro k d b g
  change IsUnit ((K d).submatrix b g)
  exact (Matrix.isUnit_submatrix_equiv b g).mpr
    ((Matrix.isUnit_iff_isUnit_det (K d)).mpr
      (Matrix.isUnit_det_of_left_inverse (LinvPrime_mul_K d)))

end D5.S3.Quantum.Matrix.CartesianControlAngleMatrixInvertible
