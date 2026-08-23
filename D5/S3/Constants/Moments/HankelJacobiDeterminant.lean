/- GID: D5/S3/Constants/Moments/HankelJacobiDeterminant
   generality: I
   mirror-B: D5/B/S3/Constants/Moments/HankelJacobiDeterminant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The determinant Jacobi coefficient obeys the Hankel ratio. -/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.NormNum

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'hankel_jacobi_coefficient_sq_eq_det_ratio' D5 \
     Golden/Frozen/accepted` returned no matches.
   * Repository searches for `Hankel`, `Jacobi`, `moment`, and `orthogonal.*polynomial`
     found only a Hankel governance deferral and unrelated number-theoretic Jacobi symbols;
     no public or private declaration states the target determinant identity.
   * Pinned-Mathlib searches found `Matrix.det`, `Matrix.det_fin_two`,
     `Matrix.det_fin_three`, and `Real.sq_sqrt`, but no Hankel-matrix or three-term
     orthogonal-polynomial recurrence API. Loogle and LeanSearch were not exposed by the
     configured NyxID service catalog, so no online result is claimed.
   * The proof therefore uses the pinned determinant and real-square-root primitives; the
     coefficient is determinant-defined and is not identified with a recurrence coefficient.
 -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Constants.Moments.HankelJacobiDeterminant

/-- The `(k + 1)`-square Hankel matrix of a real moment sequence. -/
def hankelMatrix (m : Nat -> Real) (k : Nat) : Matrix (Fin (k + 1)) (Fin (k + 1)) Real :=
  fun i j => m (i.1 + j.1)

/-- The leading Hankel determinant of order `k`, using a matrix of size `k + 1`. -/
def hankelDet (m : Nat -> Real) (k : Nat) : Real :=
  Matrix.det (hankelMatrix m k)

/-- Positive indices for off-diagonal Jacobi coefficients. -/
def JacobiIndex := {k : Nat // 0 < k}

/-- The determinant-defined candidate for the positive-index Jacobi coefficient `b_k`.
This definition does not assert that it arises from an orthogonal-polynomial recurrence. -/
noncomputable def hankelJacobiCoefficient (m : Nat -> Real) (k : JacobiIndex) : Real :=
  Real.sqrt (hankelDet m (k.1 - 1) * hankelDet m (k.1 + 1)) / hankelDet m k.1

/-- Squaring the determinant-defined coefficient gives the Hankel determinant ratio. -/
theorem hankel_jacobi_coefficient_sq_eq_det_ratio
    (m : Nat -> Real) (k : JacobiIndex)
    (hprod : 0 <= hankelDet m (k.1 - 1) * hankelDet m (k.1 + 1))
    (hdet : hankelDet m k.1 ≠ 0) :
    hankelJacobiCoefficient m k ^ 2 =
      hankelDet m (k.1 - 1) * hankelDet m (k.1 + 1) / hankelDet m k.1 ^ 2 := by
  have hdetSq : hankelDet m k.1 ^ 2 ≠ 0 := pow_ne_zero 2 hdet
  unfold hankelJacobiCoefficient
  field_simp [hdet, hdetSq]
  rw [Real.sq_sqrt hprod]

/-- Positive neighboring Hankel determinants make the determinant-defined coefficient
strictly positive. -/
theorem hankel_jacobi_coefficient_pos
    (m : Nat -> Real) (k : JacobiIndex)
    (hprev : 0 < hankelDet m (k.1 - 1))
    (hcur : 0 < hankelDet m k.1)
    (hnext : 0 < hankelDet m (k.1 + 1)) :
    0 < hankelJacobiCoefficient m k := by
  exact div_pos (Real.sqrt_pos.2 (mul_pos hprev hnext)) hcur

/-- A small positive-definite truncated moment table used to exercise the definitions. -/
def smokeMoment (n : Nat) : Real :=
  if n = 0 then 1 else if n = 2 then 1 else if n = 4 then 2 else 0

example : hankelJacobiCoefficient smokeMoment ⟨1, by norm_num⟩ = 1 := by
  change Real.sqrt (hankelDet smokeMoment 0 * hankelDet smokeMoment 2) /
      hankelDet smokeMoment 1 = 1
  have hzero : hankelDet smokeMoment 0 = 1 := by
    simp [hankelDet, hankelMatrix, smokeMoment]
  have hone : hankelDet smokeMoment 1 = 1 := by
    rw [hankelDet, Matrix.det_fin_two]
    norm_num [hankelMatrix, smokeMoment]
  have htwo : hankelDet smokeMoment 2 = 1 := by
    rw [hankelDet, Matrix.det_fin_three]
    norm_num [hankelMatrix, smokeMoment]
  rw [hzero, hone, htwo]
  norm_num

#print axioms hankel_jacobi_coefficient_sq_eq_det_ratio

end D5.S3.Constants.Moments.HankelJacobiDeterminant
