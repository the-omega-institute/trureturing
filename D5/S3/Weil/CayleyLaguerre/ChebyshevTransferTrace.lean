/- GID: D5/S3/Weil/CayleyLaguerre/ChebyshevTransferTrace
   generality: G
   mirror-B: D5/B/S3/Weil/CayleyLaguerre/ChebyshevTransferTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Chebyshev transfer traces and slack identities include zero-input audits. -/

/- Library-search audit trail (2026-08-25):
   * Exact object-name searches for `ChebyshevTransferTrace` and
     `chebyshev_transfer_trace` found no declaration in D5 or pinned Mathlib.
   * Mathlib-vocabulary searches found `Polynomial.Chebyshev.T_add_two`,
     `Matrix.aeval_self_charpoly`, `Matrix.charpoly_fin_two`, and
     `Matrix.discr_fin_two`, but no theorem connecting a power trace to Chebyshev T.
   * The source digest and its explicit matrix body had no repository match.
   * The nearest D5 modules prove general power-trace saturation, one fixed transfer
     spectrum, and Chebyshev interval bounds; none defines the source matrix.
   * Loogle's shape `Matrix.trace (?M ^ ?n) = ?x` returned only two finite-field
     Frobenius results; its trace-to-Chebyshev-C shape returned zero results.
   * LeanSearch queries using Cayley-Hamilton, companion-matrix, unimodular, and
     Vieta-Lucas vocabulary returned recurrence components but not this identity. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Disc
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.CayleyLaguerre.ChebyshevTransferTrace

/-- The free determinant-one transfer matrix attached to a real spectral coordinate. -/
def freeTransferMatrix (y : Real) : Matrix (Fin 2) (Fin 2) Real :=
  !![2 * y, -1; 1, 0]

/-- The first-kind Chebyshev slack at degree `N` and coordinate `y`. -/
def chebyshevSlack (N : Nat) (y : Real) : Real :=
  1 - (Polynomial.Chebyshev.T Real (N : Int)).eval y ^ 2

/-- The free transfer matrix has determinant one and half-trace equal to its coordinate. -/
theorem free_transfer_matrix_invariants (y : Real) :
    Matrix.det (freeTransferMatrix y) = 1 /\
      (1 / 2 : Real) * Matrix.trace (freeTransferMatrix y) = y := by
  constructor
  · norm_num [freeTransferMatrix, Matrix.det_fin_two]
  · norm_num [freeTransferMatrix, Matrix.trace_fin_two]
    ring_nf

#print axioms free_transfer_matrix_invariants

private theorem free_transfer_matrix_sq (y : Real) :
    freeTransferMatrix y ^ 2 =
      (2 * y) • freeTransferMatrix y - (1 : Matrix (Fin 2) (Fin 2) Real) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [pow_two, freeTransferMatrix, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem free_transfer_trace_add_two (N : Nat) (y : Real) :
    Matrix.trace (freeTransferMatrix y ^ (N + 2)) =
      2 * y * Matrix.trace (freeTransferMatrix y ^ (N + 1)) -
        Matrix.trace (freeTransferMatrix y ^ N) := by
  have hPower :
      freeTransferMatrix y ^ (N + 2) =
        (2 * y) • freeTransferMatrix y ^ (N + 1) - freeTransferMatrix y ^ N := by
    calc
      freeTransferMatrix y ^ (N + 2) =
          freeTransferMatrix y ^ N * freeTransferMatrix y ^ 2 := by
            rw [pow_add]
      _ = freeTransferMatrix y ^ N *
          ((2 * y) • freeTransferMatrix y - 1) := by
            rw [free_transfer_matrix_sq]
      _ = (2 * y) • freeTransferMatrix y ^ (N + 1) -
          freeTransferMatrix y ^ N := by
            simp [Matrix.mul_sub, pow_succ]
  simpa using congrArg Matrix.trace hPower

private theorem free_transfer_trace_eq_two_mul_chebyshev (N : Nat) (y : Real) :
    Matrix.trace (freeTransferMatrix y ^ N) =
      2 * (Polynomial.Chebyshev.T Real (N : Int)).eval y := by
  induction N using Nat.twoStepInduction with
  | zero =>
      norm_num [freeTransferMatrix, Matrix.trace_fin_two]
  | one =>
      norm_num [freeTransferMatrix, Matrix.trace_fin_two]
  | more n ih0 ih1 =>
      rw [show ((n + 1 : Nat) : Int) = n + 1 by omega] at ih1
      rw [free_transfer_trace_add_two, show ((n + 2 : Nat) : Int) = n + 2 by omega,
        Polynomial.Chebyshev.T_add_two]
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
        Polynomial.eval_X, ih0, ih1]
      ring

/-- Half the trace of the `N`th free transfer power is the first-kind Chebyshev value. -/
theorem chebyshev_transfer_trace (N : Nat) (y : Real) :
    (1 / 2 : Real) * Matrix.trace (freeTransferMatrix y ^ N) =
      (Polynomial.Chebyshev.T Real (N : Int)).eval y := by
  rw [free_transfer_trace_eq_two_mul_chebyshev]
  ring

#print axioms chebyshev_transfer_trace

/-- The bracketed transfer expression is Mathlib's characteristic-polynomial discriminant. -/
theorem free_transfer_power_discriminant (N : Nat) (y : Real) :
    (freeTransferMatrix y ^ N).discr =
      Matrix.trace (freeTransferMatrix y ^ N) ^ 2 - 4 := by
  rw [Matrix.discr_fin_two, Matrix.det_pow, (free_transfer_matrix_invariants y).1]
  ring

#print axioms free_transfer_power_discriminant

/-- Chebyshev slack is minus one quarter of the free transfer discriminant expression. -/
theorem chebyshev_slack_eq_transfer_discriminant (N : Nat) (y : Real) :
    chebyshevSlack N y =
      -(1 / 4 : Real) * (Matrix.trace (freeTransferMatrix y ^ N) ^ 2 - 4) := by
  rw [chebyshevSlack, ← chebyshev_transfer_trace]
  ring

#print axioms chebyshev_slack_eq_transfer_discriminant

/-- At zero degree the power is the identity and the slack vanishes; zero coordinate also works. -/
theorem chebyshev_transfer_trace_degenerate_cases :
    (1 / 2 : Real) * Matrix.trace (freeTransferMatrix 0 ^ 0) =
        (Polynomial.Chebyshev.T Real (0 : Int)).eval 0 /\
      (1 / 2 : Real) * Matrix.trace (freeTransferMatrix 0 ^ 1) =
        (Polynomial.Chebyshev.T Real (1 : Int)).eval 0 /\
      chebyshevSlack 0 0 = 0 := by
  norm_num [freeTransferMatrix, chebyshevSlack, Matrix.trace_fin_two]

#print axioms chebyshev_transfer_trace_degenerate_cases

end D5.S3.Weil.CayleyLaguerre.ChebyshevTransferTrace
