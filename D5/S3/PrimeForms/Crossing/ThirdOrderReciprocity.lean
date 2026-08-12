/- GID: D5/S3/PrimeForms/Crossing/ThirdOrderReciprocity
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Crossing/ThirdOrderReciprocity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The third-order reciprocity matrix K = [[1,-2],[2,-1]] (det 3, K² = −3·1) satisfies, for every integer 2×2 matrix γ, the linear-constitution biconditional K·γ·adj(K) = 3·adj(γ) ⟺ trace(γ·K) = 0 — conjugation by K sends γ to (det K)·adj(γ) exactly when γ is trace-orthogonal to K. This is the algebraic linear constitution of residual E.72; the geometric axis biconditional, the class-level crossing criterion, and the Sarnak/Fricke reciprocity dictionary are not covered. -/

import Mathlib

open Matrix

namespace D5.S3.PrimeForms.Crossing.ThirdOrderReciprocity

/-- The third-order (√−3) matrix `K = [[1,-2],[2,-1]]`, the π-rotation at the reference point. -/
def K : Matrix (Fin 2) (Fin 2) ℤ := !![1, -2; 2, -1]

/-- `K` has determinant `3`. -/
theorem K_det : K.det = 3 := by
  simp [K, Matrix.det_fin_two]

/-- `K² = -3·I`: the minimal polynomial of `K` is `x² + 3`. -/
theorem K_sq : K * K = (-3 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Third-order reciprocity, linear constitution (E.72, 系理三).** For every integer `2×2` matrix
`γ`, conjugation by the reciprocity matrix `K` reverses `γ` to `(det K)·adjugate γ` exactly when `γ`
is trace-orthogonal to `K`:
`K · γ · adjugate K = 3 • adjugate γ ↔ trace (γ · K) = 0`.
The inverse-free adjugate form holds for all `γ` (singular included). Only this algebraic linear
constitution is recorded; the geometric axis biconditional `axis(γ) ∋ ρ₀`, the class-level crossing
criterion, and the Sarnak/Fricke reciprocity dictionary of E.72 are not covered. -/
theorem k_reversal_iff (γ : Matrix (Fin 2) (Fin 2) ℤ) :
    K * γ * adjugate K = (3 : ℤ) • adjugate γ ↔ trace (γ * K) = 0 := by
  have htr : trace (γ * K) = γ 0 0 + 2 * γ 0 1 - 2 * γ 1 0 - γ 1 1 := by
    simp [Matrix.trace_fin_two, Matrix.mul_apply, K, Fin.sum_univ_two]; ring
  rw [htr, ← Matrix.ext_iff]
  constructor
  · intro h
    have h00 := h 0 0
    rw [Matrix.eta_fin_two γ] at h00
    simp [K, Matrix.mul_apply, Matrix.adjugate_fin_two, Matrix.smul_apply,
      Fin.sum_univ_two] at h00
    linarith
  · intro hV i j
    rw [Matrix.eta_fin_two γ]
    fin_cases i <;> fin_cases j <;>
      · simp [K, Matrix.mul_apply, Matrix.adjugate_fin_two, Matrix.smul_apply,
          Fin.sum_univ_two]
        linarith

end D5.S3.PrimeForms.Crossing.ThirdOrderReciprocity
