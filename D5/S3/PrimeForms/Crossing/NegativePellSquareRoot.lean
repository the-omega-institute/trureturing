/- GID: D5/S3/PrimeForms/Crossing/NegativePellSquareRoot
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Crossing/NegativePellSquareRoot
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A trace-zero negative-Pell square root yields a determinant-negative-one matrix. -/

import Mathlib

open Matrix

namespace D5.S3.PrimeForms.Crossing.NegativePellSquareRoot

/-- Let `V` be a trace-zero integer matrix with `V^2 = (36j^2 + 1)I`. Then
`delta = 6jI + V` has determinant `-1`, and its square is the explicit matrix
`(72j^2 + 1)I + 12jV` from the negative-Pell construction. -/
theorem negative_pell_square_root (j : ℤ) (V : Matrix (Fin 2) (Fin 2) ℤ)
    (htrace : trace V = 0)
    (hsquare : V * V = Matrix.scalar (Fin 2) (36 * j ^ 2 + 1 : ℤ)) :
    let delta := Matrix.scalar (Fin 2) (6 * j : ℤ) + V
    delta.det = -1 ∧
      delta * delta = Matrix.scalar (Fin 2) (72 * j ^ 2 + 1 : ℤ) +
        Matrix.scalar (Fin 2) (12 * j : ℤ) * V := by
  dsimp only
  have hdiag : V 1 1 = -V 0 0 := by
    rw [Matrix.trace_fin_two] at htrace
    linarith
  have hsquare00 : V 0 0 * V 0 0 + V 0 1 * V 1 0 = 36 * j ^ 2 + 1 := by
    have h := congr_fun (congr_fun hsquare 0) 0
    rw [Matrix.mul_apply, Fin.sum_univ_two] at h
    change V 0 0 * V 0 0 + V 0 1 * V 1 0 = 36 * j ^ 2 + 1 at h
    exact h
  constructor
  · rw [Matrix.det_fin_two]
    have h01 : (0 : Fin 2) ≠ 1 := by decide
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    simp only [Matrix.add_apply, Matrix.scalar_apply, diagonal_apply, h01, h10,
      ↓reduceIte, zero_add]
    rw [hdiag]
    nlinarith [hsquare00]
  · calc
      (Matrix.scalar (Fin 2) (6 * j : ℤ) + V) *
          (Matrix.scalar (Fin 2) (6 * j : ℤ) + V) =
          Matrix.scalar (Fin 2) (6 * j : ℤ) * Matrix.scalar (Fin 2) (6 * j : ℤ) +
            Matrix.scalar (Fin 2) (6 * j : ℤ) * V +
            V * Matrix.scalar (Fin 2) (6 * j : ℤ) + V * V := by
              noncomm_ring
      _ = Matrix.scalar (Fin 2) (6 * j : ℤ) * Matrix.scalar (Fin 2) (6 * j : ℤ) +
            Matrix.scalar (Fin 2) (6 * j : ℤ) * V +
            Matrix.scalar (Fin 2) (6 * j : ℤ) * V +
            Matrix.scalar (Fin 2) (36 * j ^ 2 + 1 : ℤ) := by
              rw [← Matrix.scalar_comm (6 * j) (fun r => Commute.all _ r) V, hsquare]
      _ = Matrix.scalar (Fin 2) ((6 * j) * (6 * j) + (36 * j ^ 2 + 1) : ℤ) +
            Matrix.scalar (Fin 2) ((6 * j) + (6 * j) : ℤ) * V := by
              simp only [map_add, map_mul, add_mul]
              noncomm_ring
      _ = Matrix.scalar (Fin 2) (72 * j ^ 2 + 1 : ℤ) +
            Matrix.scalar (Fin 2) (12 * j : ℤ) * V := by
              have h72 : (6 * j) * (6 * j) + (36 * j ^ 2 + 1) = 72 * j ^ 2 + 1 := by
                ring
              have h12 : (6 * j) + (6 * j) = 12 * j := by ring
              rw [h72, h12]

end D5.S3.PrimeForms.Crossing.NegativePellSquareRoot
