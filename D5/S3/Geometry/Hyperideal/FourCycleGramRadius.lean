/- GID: D5/S3/Geometry/Hyperideal/FourCycleGramRadius
   generality: G
   mirror-B: none(waiver:initial-companion)
   mirror-E: none(waiver:unbounded-real-radius)
   anchors: []
   utility: none
   digest: Six-variable signed Gram negativity from a quantitative paired-symmetry radius. -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Geometry.Hyperideal.FourCycleGramRadius

def gram (r a b o c d : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, -r, -a, -b; -r, 1, -d, -c; -a, -d, 1, -o; -b, -c, -o, 1]

set_option maxHeartbeats 2000000 in
-- The concrete 4x4 determinant normalization expands a large polynomial.
theorem gram_det_radius
    (r a b o c d : ℝ)
    (_hr : 1 < r) (_ha : 1 < a) (_hb : 1 < b)
    (_ho : 1 < o) (_hc : 1 < c) (_hd : 1 < d)
    (_hL : 0 < ((a + c) / 2 + (b + d) / 2) ^ 2 - (r - 1) * (o - 1))
    (_hM : 0 < (r + 1) * (o + 1) - ((a + c) / 2 - (b + d) / 2) ^ 2)
    (hbound : (((a - c) / 2) ^ 2 + ((b - d) / 2) ^ 2) ^ 2 +
        2 * (r * o - 1 + Real.sqrt ((((a + c) / 2) ^ 2 - ((b + d) / 2) ^ 2) ^ 2 +
          (r - o) ^ 2)) * (((a - c) / 2) ^ 2 + ((b - d) / 2) ^ 2) <
        (((a + c) / 2 + (b + d) / 2) ^ 2 - (r - 1) * (o - 1)) *
          ((r + 1) * (o + 1) - ((a + c) / 2 - (b + d) / 2) ^ 2)) :
    Matrix.det (gram r a b o c d) < 0 := by
  let A : ℝ := (a + c) / 2
  let B : ℝ := (b + d) / 2
  let xi : ℝ := (a - c) / 2
  let zeta : ℝ := (b - d) / 2
  let L : ℝ := (A + B)^2 - (r - 1) * (o - 1)
  let M : ℝ := (r + 1) * (o + 1) - (A - B)^2
  let t : ℝ := xi^2 + zeta^2
  let P : ℝ := A^2 - B^2
  let Q : ℝ := r - o
  let S : ℝ := Real.sqrt (P^2 + Q^2)
  let C : ℝ := r * o - 1 + S
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSsq : S^2 = P^2 + Q^2 := by
    dsimp [S]
    rw [Real.sq_sqrt]
    positivity
  have hdet : Matrix.det (gram r a b o c d) = -L * M +
      (2 * (r * o - 1 - A^2 + B^2) * xi^2 +
        2 * (r * o - 1 + A^2 - B^2) * zeta^2 +
        4 * (r - o) * xi * zeta + (xi^2 - zeta^2)^2) := by
    dsimp [gram, L, M, A, B, xi, zeta]
    simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.cons_val_two,
      Matrix.cons_val_one, Matrix.vecHead, Matrix.vecTail]
    simp only [show Fin.succAbove (1 : Fin 4) (2 : Fin 3) = (3 : Fin 4) by decide,
      show Fin.succAbove (2 : Fin 4) (2 : Fin 3) = (3 : Fin 4) by decide,
      show Fin.succAbove (3 : Fin 4) (2 : Fin 3) = (2 : Fin 4) by decide]
    simp [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail]
    ring_nf
  have hcauchy : P * (zeta^2 - xi^2) + 2 * Q * xi * zeta ≤ S * t := by
    have ht0 : 0 ≤ t := by dsimp [t]; positivity
    let E : ℝ := P * (zeta^2 - xi^2) + 2 * Q * xi * zeta
    have hid : S^2 * t^2 - E^2 =
        (P * (2 * xi * zeta) - Q * (zeta^2 - xi^2))^2 := by
      rw [hSsq]
      dsimp [E, t]
      ring
    have hE : E^2 ≤ S^2 * t^2 := by
      nlinarith [hid, sq_nonneg (P * (2 * xi * zeta) - Q * (zeta^2 - xi^2))]
    have hSt0 : 0 ≤ S * t := mul_nonneg hS0 ht0
    have hEle : E ≤ S * t := by
      by_cases h : E ≤ 0
      · exact le_trans h hSt0
      · nlinarith [hE]
    exact hEle
  have hxi : 0 ≤ xi^2 := sq_nonneg _
  have hzeta : 0 ≤ zeta^2 := sq_nonneg _
  have hquartic : (xi^2 - zeta^2)^2 ≤ t^2 := by
    nlinarith [mul_nonneg hxi hzeta]
  have hXi : 2 * (r * o - 1 - A^2 + B^2) * xi^2 +
      2 * (r * o - 1 + A^2 - B^2) * zeta^2 +
      4 * (r - o) * xi * zeta + (xi^2 - zeta^2)^2 ≤ 2 * C * t + t^2 := by
    have hrewrite : 2 * (r * o - 1 - A^2 + B^2) * xi^2 +
        2 * (r * o - 1 + A^2 - B^2) * zeta^2 +
        4 * (r - o) * xi * zeta + (xi^2 - zeta^2)^2 =
        2 * (r * o - 1) * t +
          2 * (P * (zeta^2 - xi^2) + 2 * Q * xi * zeta) +
          (xi^2 - zeta^2)^2 := by
      dsimp [P, Q, t]
      ring
    rw [hrewrite]
    dsimp [C]
    nlinarith [hcauchy, hquartic]
  change t^2 + 2 * C * t < L * M at hbound
  rw [hdet]
  nlinarith [hXi]

end D5.S3.Geometry.Hyperideal.FourCycleGramRadius
