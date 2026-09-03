/- GID: D5/S3/Observer/GoldenCoding/PrimitiveIntegralSelection
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenCoding/PrimitiveIntegralSelection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Trace one and determinant minus one select the Fibonacci matrix up to coordinate swap. -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/- Library-search audit trail (2026-09-03):
   * Current-tree statement and body-shape searches found no frozen theorem
     classifying all nonnegative integral binary matrices with these invariants.
   * The nearby Fibonacci matrix modules state spectral and sharp lower-bound
     facts, but do not classify arbitrary matrices.
   * Pinned Mathlib and Loogle supply `Matrix.trace_fin_two`,
     `Matrix.det_fin_two`, and `Nat.mul_eq_one`; no exact classification theorem
     was found. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix

namespace D5.S3.Observer.GoldenCoding.PrimitiveIntegralSelection

/-- A nonnegative integral `2 x 2` matrix with trace one and signed determinant
minus one is the Fibonacci matrix or its simultaneous coordinate swap. -/
theorem primitive_integral_selection
    (M : Matrix (Fin 2) (Fin 2) Nat)
    (htrace : Matrix.trace M = 1)
    (hdet : Matrix.det (M.map Int.ofNat) = -1) :
    M = !![1, 1; 1, 0] \/ M = !![0, 1; 1, 1] := by
  rw [Matrix.trace_fin_two] at htrace
  rw [Matrix.det_fin_two] at hdet
  have hdiag :
      (M 0 0 = 1 /\ M 1 1 = 0) \/ (M 0 0 = 0 /\ M 1 1 = 1) := by
    omega
  rcases hdiag with hdiag | hdiag
  · left
    obtain ⟨ha, hd⟩ := hdiag
    have hbcInt : (M 0 1 : Int) * (M 1 0 : Int) = 1 := by
      simpa [ha, hd] using hdet
    have hbc : M 0 1 * M 1 0 = 1 := by
      exact_mod_cast hbcInt
    obtain ⟨hb, hc⟩ := mul_eq_one.mp hbc
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]
  · right
    obtain ⟨ha, hd⟩ := hdiag
    have hbcInt : (M 0 1 : Int) * (M 1 0 : Int) = 1 := by
      simpa [ha, hd] using hdet
    have hbc : M 0 1 * M 1 0 = 1 := by
      exact_mod_cast hbcInt
    obtain ⟨hb, hc⟩ := mul_eq_one.mp hbc
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

#print axioms primitive_integral_selection

end D5.S3.Observer.GoldenCoding.PrimitiveIntegralSelection
