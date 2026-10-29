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
      (if (s : ℕ) = 0 then (1 / 2 : ℝ) else 0) +
        (if (s : ℕ) = 1 then (1 / 2 : ℝ) else 0)
    else if (r : ℕ) + 1 = m then
      (if (s : ℕ) = 0 then (1 / 2 : ℝ) else 0) +
        (if (s : ℕ) + 1 = m then (-1 / 2 : ℝ) else 0)
    else
      (if s = r then (-1 / 2 : ℝ) else 0) +
        (if (s : ℕ) = (r : ℕ) + 1 then (1 / 2 : ℝ) else 0)

private theorem sum_val_indicator (m n : ℕ) (hn : n < m) (f : Fin m → ℝ) :
    ∑ s : Fin m, (if (s : ℕ) = n then f s else 0) = f ⟨n, hn⟩ := by
  classical
  rw [Finset.sum_eq_single ⟨n, hn⟩]
  · simp
  · intro b hb hbn
    by_cases h : (b : ℕ) = n
    · exact (hbn (Fin.ext (by omega))).elim
    · simp [h]
  · intro h
    exact (h (Finset.mem_univ _)).elim

private theorem Linv_mul_A (m : ℕ) : Linv m * A m = (1 : Matrix (Fin m) (Fin m) ℝ) := by
  classical
  cases m with
  | zero => exact Subsingleton.elim _ _
  | succ m =>
    cases m with
    | zero =>
        ext r s
        fin_cases r
        fin_cases s
        norm_num [Matrix.mul_apply, Linv, A]
    | succ n =>
        ext r t
        by_cases hr0 : (r : ℕ) = 0
        · have hr : r = ⟨0, by omega⟩ := Fin.ext (by omega)
          rw [hr]
          rw [Matrix.mul_apply]
          simp [Linv, hr0]
          simp_rw [add_mul]
          rw [Finset.sum_add_distrib]
          simp only [ite_mul, zero_mul]
          simp [Finset.sum_ite_eq']
          rw [sum_val_indicator (n + 1 + 1) 1 (by omega)]
          by_cases ht0 : (t : ℕ) = 0
          · have ht : t = ⟨0, by omega⟩ := Fin.ext (by omega)
            rw [ht]
            norm_num [A, Matrix.one_apply]
          · have ht1 : 1 ≤ (t : ℕ) := by omega
            simp [A, Matrix.one_apply, ht0]
            omega
        · by_cases hrlast : (r : ℕ) + 1 = n + 1 + 1
          · have hr : r = ⟨n + 1, by omega⟩ := by
              apply Fin.ext
              simp
              omega
            rw [hr]
            rw [Matrix.mul_apply]
            simp [Linv, hrlast]
            simp_rw [add_mul]
            rw [Finset.sum_add_distrib]
            simp only [ite_mul, zero_mul]
            simp [Finset.sum_ite_eq']
            rw [sum_val_indicator (n + 1 + 1) (n + 1) (by omega)]
            have hlast : n + 1 < n + 1 + 1 := by omega
            have hsumlast :
                (∑ s : Fin (n + 1 + 1), (if (s : ℕ) = n + 1 then
                  (-1 / 2 : ℝ) * A (n + 1 + 1) s t else 0)) =
                (-1 / 2 : ℝ) * A (n + 1 + 1) ⟨n + 1, hlast⟩ t := by
              simpa using (sum_val_indicator (n + 1 + 1) (n + 1) hlast
                (fun s => (-1 / 2 : ℝ) * A (n + 1 + 1) s t))
            rw [hsumlast]
            by_cases htlast : (t : ℕ) = n + 1
            · have ht : t = ⟨n + 1, by omega⟩ := Fin.ext (by omega)
              rw [ht]
              norm_num [A, Matrix.one_apply]
            · have hAt : A (n + 1 + 1) ⟨0, by omega⟩ t = 1 := by simp [A]
              have hAlast : A (n + 1 + 1) ⟨n + 1, by omega⟩ t = 1 := by
                simp [A]
                omega
              rw [hAt, hAlast]
              simp [Matrix.one_apply, htlast]
          · have hrpos : 0 < (r : ℕ) := by omega
            have hrsucc : (r : ℕ) + 1 < n + 1 + 1 := by omega
            have hrnotlast : (r : ℕ) ≠ n + 1 := by omega
            rw [Matrix.mul_apply]
            simp [Linv, hr0, hrnotlast]
            simp_rw [add_mul]
            rw [Finset.sum_add_distrib]
            simp only [ite_mul, zero_mul]
            simp [Finset.sum_ite_eq']
            have hsumrs : (∑ s : Fin (n + 1 + 1),
                (if (s : ℕ) = (r : ℕ) + 1 then (1 / 2 : ℝ) * A (n + 1 + 1) s t else 0)) =
                (1 / 2 : ℝ) * A (n + 1 + 1) ⟨(r : ℕ) + 1, hrsucc⟩ t := by
              simpa using (sum_val_indicator (n + 1 + 1) ((r : ℕ) + 1) hrsucc
                (fun s => (1 / 2 : ℝ) * A (n + 1 + 1) s t))
            rw [show (∑ x : Fin (n + 1 + 1),
                if (x : ℕ) = (r : ℕ) + 1 then (2⁻¹ : ℝ) * A (n + 1 + 1) x t else 0) =
                (1 / 2 : ℝ) * A (n + 1 + 1) ⟨(r : ℕ) + 1, hrsucc⟩ t by
              simpa only [one_div] using hsumrs]
            have hreq : (⟨(r : ℕ) + 1, hrsucc⟩ : Fin (n + 1 + 1)) = r := by omega
            by_cases htr : (t : ℕ) < (r : ℕ)
            · have htr' : (t : ℕ) < (r : ℕ) + 1 := by omega
              have har : A (n + 1 + 1) r t = 1 := by
                change (if 0 < (r : ℕ) ∧ (r : ℕ) ≤ (t : ℕ) then (-1 : ℝ) else 1) = 1
                simp [htr]
              have has : A (n + 1 + 1) ⟨(r : ℕ) + 1, hrsucc⟩ t = 1 := by
                change (if 0 < (r : ℕ) + 1 ∧ (r : ℕ) + 1 ≤ (t : ℕ) then (-1 : ℝ) else 1) = 1
                simp [htr']
              rw [har, has]
              simp [Matrix.one_apply, htr, hteq]
            · by_cases hteq : (t : ℕ) = (r : ℕ)
              · have ht : t = r := Fin.ext hteq
                rw [ht]
                have har : A (n + 1 + 1) r r = -1 := by
                  change (if 0 < (r : ℕ) ∧ (r : ℕ) ≤ (r : ℕ) then (-1 : ℝ) else 1) = -1
                  simp [hrpos]
                have has : A (n + 1 + 1) ⟨(r : ℕ) + 1, hrsucc⟩ r = 1 := by
                  change (if 0 < (r : ℕ) + 1 ∧ (r : ℕ) + 1 ≤ (r : ℕ) then (-1 : ℝ) else 1) = 1
                  simp
                rw [har, has]
                simp [Matrix.one_apply]
              · have htr' : (r : ℕ) < (t : ℕ) := by omega
                have har : A (n + 1 + 1) r t = -1 := by
                  change (if 0 < (r : ℕ) ∧ (r : ℕ) ≤ (t : ℕ) then (-1 : ℝ) else 1) = -1
                  simp [hrpos, htr']
                have has : A (n + 1 + 1) ⟨(r : ℕ) + 1, hrsucc⟩ t =
                    if (r : ℕ) + 1 ≤ (t : ℕ) then -1 else 1 := by
                  simp [A]
                rw [har, has]
                by_cases hnext : (r : ℕ) + 1 ≤ (t : ℕ)
                · norm_num [hnext, Matrix.one_apply, hteq]
                · have : (t : ℕ) = (r : ℕ) := by omega
                  exact (hteq this).elim

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
