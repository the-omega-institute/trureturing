/- GID: D5/S3/Quantum/FiniteDimensional
   generality: G
   mirror-B: D5/B/S3/Quantum/FiniteDimensional
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Formalize finite-dimensional complex matrix-algebra and probability skeletons. -/

import Mathlib

namespace D5.S3.Quantum.FiniteDimensional

open scoped ComplexOrder

/-- The matrix algebra of a two-dimensional complex Hilbert space. -/
abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- The Pauli `X` matrix. -/
def qubitX : QubitMatrix := !![0, 1; 1, 0]

/-- The Pauli `Z` matrix. -/
def qubitZ : QubitMatrix := !![1, 0; 0, -1]

/-- The standard qubit Weyl pair anticommutes, is self-adjoint, and squares to one. -/
theorem qubit_weyl_star :
    qubitZ * qubitX = -(qubitX * qubitZ) ∧
      star qubitX = qubitX ∧ star qubitZ = qubitZ ∧
      qubitX ^ 2 = 1 ∧ qubitZ ^ 2 = 1 := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [qubitX, qubitZ, Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [qubitX]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [qubitZ]
  constructor <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
      simp [qubitX, qubitZ, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- The qubit matrix algebra has no unital complex-algebra character. -/
theorem qubit_matrix_algebra_has_no_character :
    IsEmpty (QubitMatrix →ₐ[ℂ] ℂ) := by
  constructor
  intro character
  rcases qubit_weyl_star with ⟨hAnticommute, _, _, hXSquare, hZSquare⟩
  have hAnticommuteImage :
      character qubitZ * character qubitX =
        -(character qubitX * character qubitZ) := by
    simpa using congrArg character hAnticommute
  have hSelfNegating :
      character qubitX * character qubitZ =
        -(character qubitX * character qubitZ) := by
    calc
      character qubitX * character qubitZ =
          character qubitZ * character qubitX := mul_comm _ _
      _ = -(character qubitX * character qubitZ) := hAnticommuteImage
  have hProductZero : character qubitX * character qubitZ = 0 := by
    linear_combination (1 / 2 : ℂ) * hSelfNegating
  have hXSquareImage : character qubitX ^ 2 = 1 := by
    simpa using congrArg character hXSquare
  have hZSquareImage : character qubitZ ^ 2 = 1 := by
    simpa using congrArg character hZSquare
  rcases mul_eq_zero.mp hProductZero with hXZero | hZZero
  · simp [hXZero] at hXSquareImage
  · simp [hZZero] at hZSquareImage

/-- The trace weight assigned by `rho` to a finite-dimensional matrix. -/
noncomputable def bornProbability {n : Type*} [Fintype n]
    (rho P : Matrix n n ℂ) : ℂ :=
  Matrix.trace (rho * P)

/-- A positive trace-one matrix induces a normalized additive nonnegative weight on projections. -/
theorem born_probability_skeleton {n : Type*} [Fintype n] [DecidableEq n]
    (rho : Matrix n n ℂ) (hRho : rho.PosSemidef) (hTrace : Matrix.trace rho = 1) :
    bornProbability rho (1 : Matrix n n ℂ) = 1 ∧
      (∀ P Q : Matrix n n ℂ, bornProbability rho (P + Q) =
        bornProbability rho P + bornProbability rho Q) ∧
      ∀ P : Matrix n n ℂ, star P = P → P * P = P → 0 ≤ bornProbability rho P := by
  constructor
  · simpa [bornProbability] using hTrace
  constructor
  · intro P Q
    simp [bornProbability, Matrix.mul_add]
  · intro P hSelfAdjoint hIdempotent
    have hConjTranspose : Matrix.conjTranspose P = P := by
      simpa only [Matrix.star_eq_conjTranspose] using hSelfAdjoint
    have hCompressed : (P * rho * Matrix.conjTranspose P).PosSemidef :=
      hRho.mul_mul_conjTranspose_same P
    have hTraceCompressed :
        Matrix.trace (P * rho * Matrix.conjTranspose P) = Matrix.trace (rho * P) := by
      calc
        Matrix.trace (P * rho * Matrix.conjTranspose P) =
            Matrix.trace (Matrix.conjTranspose P * P * rho) :=
          Matrix.trace_mul_cycle P rho (Matrix.conjTranspose P)
        _ = Matrix.trace (P * P * rho) := by rw [hConjTranspose]
        _ = Matrix.trace (P * rho) := by rw [hIdempotent]
        _ = Matrix.trace (rho * P) := Matrix.trace_mul_comm P rho
    rw [bornProbability, ← hTraceCompressed]
    exact hCompressed.trace_nonneg

end D5.S3.Quantum.FiniteDimensional
