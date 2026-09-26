/- GID: D5/S3/Estimation/TimeArrow/ParityKernelCharpoly
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/ParityKernelCharpoly
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every balanced hypercube parity kernel has characteristic polynomial (X - 1) X^(2^d - 1). -/

import D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.ParityKernelCharpoly

open Finset Polynomial
open D5.S3.Estimation.TimeArrow.ParityKernelSubcoordinates

/-- The parity character sums to zero over a hypercube of positive dimension; this is the
`a = 1`, `b = 0` instance of two-step uniform mixing. -/
private theorem sum_parity_eq_zero {d : ℕ} (hd : 1 ≤ d) :
    ∑ y : Fin d → ℤˣ, parity y = 0 := by
  have h := parityKernel_mul_eq_uniform hd (fun _ => 1) (fun _ => 0) (by simp) (by simp)
    (fun _ => 1) (fun _ => 1)
  simp only [parityKernel, zero_mul, add_zero, one_mul] at h
  have hn : (2 : ℝ) ^ d ≠ 0 := by positivity
  have hcard : (Fintype.card (Fin d → ℤˣ) : ℝ) = 2 ^ d := by
    simp [Fintype.card_units_int]
  rw [← Finset.sum_mul, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, hcard] at h
  field_simp at h
  linarith

/-- **Characteristic polynomial of a balanced parity kernel.** If `d ≥ 1`, `∑ a = 0` and
`∑ χ a = 0`, the parity kernel `P_a` on the `d`-dimensional sign hypercube has characteristic
polynomial `(X - 1) X^(2^d - 1)`. -/
theorem charpoly_parityKernel {d : ℕ} (hd : 1 ≤ d) (a : (Fin d → ℤˣ) → ℝ)
    (ha : ∑ y, a y = 0) (hχa : ∑ y, parity y * a y = 0) :
    (Matrix.of fun x y => parityKernel a x y).charpoly = (X - 1) * X ^ (2 ^ d - 1) := by
  classical
  -- the kernel is the rank-two product `U V` with `U = [1, a] / 2^d` and `V = [1, χ]ᵀ`
  let U : Matrix (Fin d → ℤˣ) (Fin 2) ℝ :=
    Matrix.of fun x i => if i = 0 then 1 / 2 ^ d else a x / 2 ^ d
  let V : Matrix (Fin 2) (Fin d → ℤˣ) ℝ := Matrix.of fun i y => if i = 0 then 1 else parity y
  have hUV : U * V = Matrix.of fun x y => parityKernel a x y := by
    ext x y
    simp [U, V, Matrix.mul_apply, Fin.sum_univ_two, parityKernel]
    ring
  have hn : (2 : ℝ) ^ d ≠ 0 := by positivity
  have hcard : (Fintype.card (Fin d → ℤˣ) : ℝ) = 2 ^ d := by
    simp [Fintype.card_units_int]
  have hχ := sum_parity_eq_zero hd
  have hVU : V * U = !![1, 0; 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [U, V, Matrix.mul_apply, ← Finset.sum_div, ha, hcard]
    · rw [← Finset.sum_mul, hχ, zero_mul]
    · simp_rw [← mul_div_assoc]
      rw [← Finset.sum_div, hχa, zero_div]
  have hle : Fintype.card (Fin 2) ≤ Fintype.card (Fin d → ℤˣ) := by
    have : (2 : ℕ) ≤ 2 ^ d := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    simpa [Fintype.card_units_int] using this
  rw [← hUV, Matrix.charpoly_mul_comm_of_le U V hle, hVU, Matrix.charpoly_fin_two]
  have hcardn : Fintype.card (Fin d → ℤˣ) = 2 ^ d := by simp [Fintype.card_units_int]
  rw [hcardn, Fintype.card_fin]
  simp only [Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have h2 : 2 ^ d - 1 = (2 ^ d - 2) + 1 := by
    have : 2 ≤ 2 ^ d := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    omega
  rw [h2, pow_succ]
  simp
  ring

#print axioms charpoly_parityKernel

end D5.S3.Estimation.TimeArrow.ParityKernelCharpoly
