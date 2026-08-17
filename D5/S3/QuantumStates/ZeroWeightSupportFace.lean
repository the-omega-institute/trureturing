/- GID: D5/S3/QuantumStates/ZeroWeightSupportFace
   generality: G
   mirror-B: D5/B/S3/QuantumStates/ZeroWeightSupportFace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Zero projection weight forces complementary support compression. -/

import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/- Library-search audit trail (2026-08-17):
   * Repository searches found no theorem containing both one-sided
     annihilations and the complementary support identity. A private
     conditioning lemma proves only that a compressed matrix is zero.
   * Pinned Mathlib has no theorem packaging the complete statement.
     `Matrix.PosSemidef.trace_eq_zero_iff`,
     `CStarAlgebra.nonneg_iff_eq_star_mul_self`, and
     `Matrix.trace_conjTranspose_mul_self_eq_zero_iff` are exact component
     hits and are applied directly below. -/

open scoped ComplexOrder MatrixOrder

namespace D5.S3.QuantumStates.ZeroWeightSupportFace

universe u

/-- A positive matrix assigning zero trace weight to an orthogonal projection
is supported on the complementary projection. -/
theorem zero_weight_support_face
    {n : Type u} [Fintype n] [DecidableEq n]
    (rho P : Matrix n n ℂ)
    (hrho : rho.PosSemidef)
    (hPstar : Matrix.conjTranspose P = P)
    (hPidem : P * P = P)
    (htrace : Matrix.trace (rho * P) = 0) :
    (P * rho = 0 ∧ rho * P = 0) ∧
      rho = (1 - P) * rho * (1 - P) := by
  fail_if_success rfl
  have hCompressed : (P * rho * P).PosSemidef := by
    simpa only [hPstar] using hrho.mul_mul_conjTranspose_same P
  have hCompressedTrace : Matrix.trace (P * rho * P) = 0 := by
    calc
      Matrix.trace (P * rho * P) = Matrix.trace (P * P * rho) :=
        Matrix.trace_mul_cycle P rho P
      _ = Matrix.trace (P * rho) := by rw [hPidem]
      _ = Matrix.trace (rho * P) := Matrix.trace_mul_comm P rho
      _ = 0 := htrace
  have hCompressedZero : P * rho * P = 0 :=
    hCompressed.trace_eq_zero_iff.mp hCompressedTrace
  obtain ⟨A, hA⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hrho.nonneg
  have hA' : rho = Matrix.conjTranspose A * A := by
    simpa only [Matrix.star_eq_conjTranspose] using hA
  have hAP : A * P = 0 := by
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    calc
      Matrix.trace (Matrix.conjTranspose (A * P) * (A * P)) =
          Matrix.trace (P * rho * P) := by
            rw [Matrix.conjTranspose_mul, hPstar]
            congr 1
            calc
              P * Matrix.conjTranspose A * (A * P) =
                  P * (Matrix.conjTranspose A * A) * P := by noncomm_ring
              _ = P * rho * P := by rw [← hA']
      _ = 0 := by rw [hCompressedZero, Matrix.trace_zero]
  have hRhoP : rho * P = 0 := by
    rw [hA', mul_assoc, hAP, mul_zero]
  have hPRho : P * rho = 0 := by
    have h := congrArg Matrix.conjTranspose hRhoP
    simpa only [Matrix.conjTranspose_mul, hPstar, hrho.isHermitian.eq,
      Matrix.conjTranspose_zero] using h
  refine ⟨⟨hPRho, hRhoP⟩, ?_⟩
  symm
  calc
    (1 - P) * rho * (1 - P) = (rho - P * rho) * (1 - P) := by
      rw [sub_mul, one_mul]
    _ = rho * (1 - P) := by rw [hPRho, sub_zero]
    _ = rho - rho * P := by rw [mul_sub, mul_one]
    _ = rho := by rw [hRhoP, sub_zero]

example :
    let rho : Matrix Unit Unit ℂ := 1
    let P : Matrix Unit Unit ℂ := 0
    (P * rho = 0 ∧ rho * P = 0) ∧
      rho = (1 - P) * rho * (1 - P) := by
  dsimp only
  apply zero_weight_support_face (rho := (1 : Matrix Unit Unit ℂ))
    (P := (0 : Matrix Unit Unit ℂ))
  · exact Matrix.PosSemidef.one
  · simp
  · simp
  · simp

#print axioms zero_weight_support_face

end D5.S3.QuantumStates.ZeroWeightSupportFace
