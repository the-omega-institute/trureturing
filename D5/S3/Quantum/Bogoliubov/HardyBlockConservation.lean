/- GID: D5/S3/Quantum/Bogoliubov/HardyBlockConservation
   generality: G
   mirror-B: D5/B/S3/Quantum/Bogoliubov/HardyBlockConservation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Isometric compression and leakage blocks conserve the input projection. -/

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

/- Library-search audit trail (2026-09-02):
   * Six repository routes found no theorem equating the two Hardy block Gram matrices with
     their input projection; exact atom, receipt, digest, generalized-body, and in-flight
     branch searches were negative.
   * The nearest repository results concern four-block decompositions, complementary
     projections, or the hyperbolic Bogoliubov norm, but none implies this identity directly.
   * Pinned Mathlib supplies `Matrix.conjTranspose_mul`, `Matrix.conjTranspose_sub`, and
     `Matrix.conjTranspose_one`; they are used directly below.
   * On the ambient space the right side is `P`, not `1`. It becomes the identity only on
     inputs fixed by `P`; a proper `Fin 2` projection witnesses failure of the ambient claim. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Bogoliubov.HardyBlockConservation

/-- The compression of an ambient evolution to the chosen Hardy sector. -/
def compressedBlock {n : Type*} [Fintype n] [DecidableEq n]
    (P U : Matrix n n ℂ) : Matrix n n ℂ :=
  P * U * P

/-- The part of an input in the chosen Hardy sector that leaks to its orthogonal complement. -/
def leakageBlock {n : Type*} [Fintype n] [DecidableEq n]
    (P U : Matrix n n ℂ) : Matrix n n ℂ :=
  (1 - P) * U * P

/-- The Gram matrices of the compression and leakage blocks add to the input projection. -/
theorem hardy_block_conservation {n : Type*} [Fintype n] [DecidableEq n]
    (P U : Matrix n n ℂ)
    (hPstar : Matrix.conjTranspose P = P)
    (hPidem : P * P = P)
    (hUisometry : Matrix.conjTranspose U * U = 1) :
    Matrix.conjTranspose (compressedBlock P U) * compressedBlock P U +
      Matrix.conjTranspose (leakageBlock P U) * leakageBlock P U = P := by
  have hQidem : (1 - P) * (1 - P) = 1 - P := by
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hPidem]; noncomm_ring
  have hPabsorb (A : Matrix n n ℂ) : P * (P * A) = P * A := by
    rw [← mul_assoc, hPidem]
  have hQabsorb (A : Matrix n n ℂ) :
      (1 - P) * ((1 - P) * A) = (1 - P) * A := by
    rw [← mul_assoc, hQidem]
  have hUabsorb (A : Matrix n n ℂ) :
      Matrix.conjTranspose U * (U * A) = A := by
    rw [← mul_assoc, hUisometry, one_mul]
  unfold compressedBlock leakageBlock
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_one, hPstar]
  calc
    P * (Matrix.conjTranspose U * P) * (P * U * P) +
          P * (Matrix.conjTranspose U * (1 - P)) * ((1 - P) * U * P) =
        P * Matrix.conjTranspose U * P * U * P +
          P * Matrix.conjTranspose U * (1 - P) * U * P := by
      simp only [mul_assoc, hPabsorb, hQabsorb]
    _ = P * Matrix.conjTranspose U * U * P := by noncomm_ring
    _ = P * P := by simp only [mul_assoc, hUabsorb]
    _ = P := hPidem

/-- On an input fixed by `P`, the ambient conservation law acts as the identity. -/
theorem hardy_block_conservation_on_projected_input
    {n : Type*} [Fintype n] [DecidableEq n]
    (P U : Matrix n n ℂ)
    (hPstar : Matrix.conjTranspose P = P)
    (hPidem : P * P = P)
    (hUisometry : Matrix.conjTranspose U * U = 1)
    (v : n → ℂ) (hv : Matrix.mulVec P v = v) :
    Matrix.mulVec
      (Matrix.conjTranspose (compressedBlock P U) * compressedBlock P U +
        Matrix.conjTranspose (leakageBlock P U) * leakageBlock P U) v = v := by
  rw [hardy_block_conservation P U hPstar hPidem hUisometry, hv]

/-- The nonzero proper projection onto the first coordinate of `ℂ²`. -/
def firstCoordinateProjection : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun i => if i = 0 then 1 else 0

/-- A proper input projection shows that the ambient right side cannot be replaced by `1`. -/
theorem ambient_identity_rhs_counterexample :
    firstCoordinateProjection ≠ 0 ∧
      firstCoordinateProjection ≠ 1 ∧
      Matrix.conjTranspose firstCoordinateProjection = firstCoordinateProjection ∧
      firstCoordinateProjection * firstCoordinateProjection = firstCoordinateProjection ∧
      Matrix.conjTranspose
          (compressedBlock firstCoordinateProjection (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          compressedBlock firstCoordinateProjection 1 +
        Matrix.conjTranspose
          (leakageBlock firstCoordinateProjection (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          leakageBlock firstCoordinateProjection 1 = firstCoordinateProjection ∧
      Matrix.conjTranspose
          (compressedBlock firstCoordinateProjection (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          compressedBlock firstCoordinateProjection 1 +
        Matrix.conjTranspose
          (leakageBlock firstCoordinateProjection (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
          leakageBlock firstCoordinateProjection 1 ≠ 1 := by
  have hPstar : Matrix.conjTranspose firstCoordinateProjection =
      firstCoordinateProjection := by
    rw [firstCoordinateProjection, Matrix.diagonal_conjTranspose]
    apply congrArg Matrix.diagonal
    funext i
    by_cases hi : i = 0 <;> simp [hi]
  have hPidem : firstCoordinateProjection * firstCoordinateProjection =
      firstCoordinateProjection := by
    rw [firstCoordinateProjection, Matrix.diagonal_mul_diagonal]
    apply congrArg Matrix.diagonal
    funext i
    by_cases hi : i = 0 <;> simp [hi]
  have hPneZero : firstCoordinateProjection ≠ 0 := by
    intro h
    have h00 := congrFun (congrFun h 0) 0
    norm_num [firstCoordinateProjection] at h00
  have hPneOne : firstCoordinateProjection ≠ 1 := by
    intro h
    have h11 := congrFun (congrFun h 1) 1
    norm_num [firstCoordinateProjection] at h11
  have hConservation := hardy_block_conservation firstCoordinateProjection
    (1 : Matrix (Fin 2) (Fin 2) ℂ) hPstar hPidem (by simp)
  exact ⟨hPneZero, hPneOne, hPstar, hPidem, hConservation,
    fun hIdentity => hPneOne (hConservation.symm.trans hIdentity)⟩

#print axioms hardy_block_conservation
#print axioms hardy_block_conservation_on_projected_input
#print axioms ambient_identity_rhs_counterexample

end D5.S3.Quantum.Bogoliubov.HardyBlockConservation
