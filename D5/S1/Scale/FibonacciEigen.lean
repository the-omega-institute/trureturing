/- GID: D5/S1/Scale/FibonacciEigen
   generality: I
   mirror-B: D5/B/S1/Scale/FibonacciEigen
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Fibonacci substitution has golden eigenvalues and an exact contracting error term. -/

import D5.S0.Carrier.GoldenRatio
import Mathlib.Data.Matrix.Reflection

namespace D5.S1.Scale

open scoped Matrix

/-- The Fibonacci substitution matrix `[[1, 1], [1, 0]]`. -/
def fibonacciSubstitution : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 1; 1, 0]

/-- An eigenvector for the expanding golden eigenvalue. -/
noncomputable def expandingEigenvector : Fin 2 → ℝ :=
  ![Real.goldenRatio, 1]

/-- The contracting eigenvalue, written in the form used by the source claim. -/
noncomputable def contractingEigenvalue : ℝ :=
  -(1 / Real.goldenRatio)

/-- An eigenvector for the contracting golden eigenvalue. -/
noncomputable def contractingEigenvector : Fin 2 → ℝ :=
  ![contractingEigenvalue, 1]

theorem contracting_eigenvalue_eq_goldenConj :
    contractingEigenvalue = Real.goldenConj := by
  rw [contractingEigenvalue, one_div, Real.inv_goldenRatio]
  simp

/--
The two stated eigenpairs and the exact Fibonacci contracting-error identity.
The eigenvectors are visibly nonzero because their second coordinate is one.
-/
theorem fibonacci_substitution_spec (n : ℕ) :
    expandingEigenvector ≠ 0 ∧
      fibonacciSubstitution *ᵥ expandingEigenvector =
        Real.goldenRatio • expandingEigenvector ∧
      contractingEigenvector ≠ 0 ∧
      fibonacciSubstitution *ᵥ contractingEigenvector =
        contractingEigenvalue • contractingEigenvector ∧
      (Nat.fib n : ℝ) * Real.goldenRatio - Nat.fib (n + 1) =
        -(contractingEigenvalue ^ n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hzero
    have h := congr_fun hzero (1 : Fin 2)
    norm_num [expandingEigenvector] at h
  · ext i
    fin_cases i
    · simp [fibonacciSubstitution, expandingEigenvector]
      nlinarith [Real.goldenRatio_sq]
    · simp [fibonacciSubstitution, expandingEigenvector]
  · intro hzero
    have h := congr_fun hzero (1 : Fin 2)
    norm_num [contractingEigenvector] at h
  · rw [contracting_eigenvalue_eq_goldenConj]
    ext i
    fin_cases i
    · simp [fibonacciSubstitution, contractingEigenvector,
        contracting_eigenvalue_eq_goldenConj]
      nlinarith [Real.goldenConj_sq]
    · simp [fibonacciSubstitution, contractingEigenvector,
        contracting_eigenvalue_eq_goldenConj]
  · calc
      (Nat.fib n : ℝ) * Real.goldenRatio - Nat.fib (n + 1) =
          -(Nat.fib (n + 1) - Real.goldenRatio * Nat.fib n) := by ring
      _ = -(Real.goldenConj ^ n) := by
        rw [Real.fib_succ_sub_goldenRatio_mul_fib]
      _ = -(contractingEigenvalue ^ n) := by
        rw [contracting_eigenvalue_eq_goldenConj]

end D5.S1.Scale
