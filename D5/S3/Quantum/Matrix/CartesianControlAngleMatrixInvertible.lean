/- GID: D5/S3/Quantum/Matrix/CartesianControlAngleMatrixInvertible
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/CartesianControlAngleMatrixInvertible
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The Cartesian-control angle matrix has an explicit inverse for every finite product of qudit dimensions. -/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! Invertibility of the Cartesian-control angle matrix. -/
noncomputable section
open scoped BigOperators
set_option autoImplicit false

namespace D5.S3.Quantum.Matrix.CartesianControlAngleMatrixInvertible

private def A (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := fun r s =>
  if 0 < (r : ℕ) ∧ (r : ℕ) ≤ (s : ℕ) then (-1 : ℝ) else 1

private def Linv (m : ℕ) : Matrix (Fin m) (Fin m) ℝ := fun r s =>
  if m = 1 then 1 else
    if (r : ℕ) = 0 then
      if (s : ℕ) = 0 ∨ (s : ℕ) = 1 then (1 / 2 : ℝ) else 0
    else if (r : ℕ) + 1 = m then
      if (s : ℕ) = 0 then (1 / 2 : ℝ) else if (s : ℕ) + 1 = m then (-1 / 2 : ℝ) else 0
    else if s = r then (-1 / 2 : ℝ) else if (s : ℕ) = (r : ℕ) + 1 then (1 / 2 : ℝ) else 0

private theorem Linv_mul_A (m : ℕ) : Linv m * A m = (1 : Matrix (Fin m) (Fin m) ℝ) := by sorry

private theorem A_mul_Linv (m : ℕ) : A m * Linv m = (1 : Matrix (Fin m) (Fin m) ℝ) := by
  rw [mul_eq_one_comm]
  exact Linv_mul_A m

private def K {k : ℕ} (d : Fin k → ℕ) :
    Matrix ((l : Fin k) → Fin (d l)) ((l : Fin k) → Fin (d l)) ℝ := fun r s =>
  ∏ l, A (d l) (r l) (s l)

private def LinvPrime {k : ℕ} (d : Fin k → ℕ) :
    Matrix ((l : Fin k) → Fin (d l)) ((l : Fin k) → Fin (d l)) ℝ := fun r s =>
  ∏ l, Linv (d l) (r l) (s l)

private theorem LinvPrime_mul_K {k : ℕ} (d : Fin k → ℕ) :
    LinvPrime d * K d = (1 : Matrix ((l : Fin k) → Fin (d l)) ((l : Fin k) → Fin (d l)) ℝ) := by sorry

private theorem K_mul_LinvPrime {k : ℕ} (d : Fin k → ℕ) :
    K d * LinvPrime d = (1 : Matrix ((l : Fin k) → Fin (d l)) ((l : Fin k) → Fin (d l)) ℝ) := by
  rw [mul_eq_one_comm]
  exact LinvPrime_mul_K d

def angleMatrix {k : ℕ} (d : Fin k → ℕ)
    (b g : Fin (∏ l, d l) ≃ ((l : Fin k) → Fin (d l))) :
    Matrix (Fin (∏ l, d l)) (Fin (∏ l, d l)) ℝ := fun i j =>
  ∏ l, (if 0 < (b i l : ℕ) ∧ (b i l : ℕ) ≤ (g j l : ℕ) then (-1 : ℝ) else 1)

private theorem angleMatrix_eq_submatrix {k : ℕ} (d : Fin k → ℕ)
    (b g : Fin (∏ l, d l) ≃ ((l : Fin k) → Fin (d l))) :
    angleMatrix d b g = (K d).submatrix b g := by sorry

def claim : Prop := ∀ (k : ℕ) (d : Fin k → ℕ)
    (b g : Fin (∏ l, d l) ≃ ((l : Fin k) → Fin (d l))),
    IsUnit (angleMatrix d b g)

theorem result : claim := by sorry

end D5.S3.Quantum.Matrix.CartesianControlAngleMatrixInvertible
