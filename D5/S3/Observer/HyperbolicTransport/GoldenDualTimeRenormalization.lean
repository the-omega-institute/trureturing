/- GID: D5/S3/Observer/HyperbolicTransport/GoldenDualTimeRenormalization
   generality: I
   mirror-B: D5/B/S3/Observer/HyperbolicTransport/GoldenDualTimeRenormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden reciprocal time scaling preserves the dual product and reflection reverses it. -/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * Current-tree name and body-shape searches for golden dual-time scaling,
     reciprocal diagonal transport, product invariance, and swap conjugation
     found no exact theorem. The nearby golden scale-circle, zeta-reflection,
     Lorentz-update, and hyperbolic-inflation modules prove different claims.
   * Pinned Mathlib supplies `Matrix.inv_diagonal`, `inv_mul_cancel₀`, and
     `mul_inv_cancel₀`, but no packaged theorem combining this golden matrix,
     its product invariant, and the reflection relation.
   * Searches of the installed non-Mathlib Lean packages found no exact result. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped Matrix

noncomputable section

namespace D5.S3.Observer.HyperbolicTransport.GoldenDualTimeRenormalization

/-- The orientation-preserving golden scale used by the two time directions. -/
def goldenDualTimeScale : ℝ :=
  Real.goldenRatio ^ 2

/-- Contract the transverse coordinate and expand the observation length. -/
def goldenDualTimeRenormalization (state : ℝ × ℝ) : ℝ × ℝ :=
  (goldenDualTimeScale⁻¹ * state.1, goldenDualTimeScale * state.2)

/-- The explicit reverse of golden dual-time renormalization. -/
def goldenDualTimeReverse (state : ℝ × ℝ) : ℝ × ℝ :=
  (goldenDualTimeScale * state.1, goldenDualTimeScale⁻¹ * state.2)

/-- Reflection exchanges the stable and unstable time coordinates. -/
def goldenTimeReflection (state : ℝ × ℝ) : ℝ × ℝ :=
  (state.2, state.1)

/-- Matrix of golden dual-time renormalization. -/
def goldenDualTimeMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![goldenDualTimeScale⁻¹, 0; 0, goldenDualTimeScale]

/-- Matrix of the reverse golden dual-time renormalization. -/
def goldenDualTimeReverseMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![goldenDualTimeScale, 0; 0, goldenDualTimeScale⁻¹]

/-- Matrix exchanging the two time coordinates. -/
def goldenTimeReflectionMatrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

private theorem golden_dual_time_scale_ne_zero : goldenDualTimeScale ≠ 0 := by
  exact pow_ne_zero 2 Real.goldenRatio_ne_zero

private theorem golden_dual_time_matrix_reflection :
    goldenTimeReflectionMatrix * goldenDualTimeMatrix * goldenTimeReflectionMatrix =
      goldenDualTimeReverseMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [goldenTimeReflectionMatrix, goldenDualTimeMatrix,
      goldenDualTimeReverseMatrix, Matrix.mul_apply, Fin.sum_univ_two]

private theorem golden_dual_time_matrix_mul_reverse :
    goldenDualTimeMatrix * goldenDualTimeReverseMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [goldenDualTimeMatrix, goldenDualTimeReverseMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, golden_dual_time_scale_ne_zero]

private theorem golden_dual_time_reverse_mul_matrix :
    goldenDualTimeReverseMatrix * goldenDualTimeMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [goldenDualTimeMatrix, goldenDualTimeReverseMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, golden_dual_time_scale_ne_zero]

/-- Golden reciprocal scaling sends `(delta, L)` to
`(phi^(-2) delta, phi^2 L)`. It preserves `delta * L`; coordinate reflection
conjugates the update to its explicit two-sided inverse; and the displayed
matrices realize the same dihedral relation. -/
theorem golden_dual_time_renormalization (delta observationLength : ℝ) :
    let state := (delta, observationLength)
    let updated := goldenDualTimeRenormalization state
    updated.1 * updated.2 = state.1 * state.2 ∧
      goldenTimeReflection
          (goldenDualTimeRenormalization (goldenTimeReflection state)) =
        goldenDualTimeReverse state ∧
      goldenDualTimeReverse (goldenDualTimeRenormalization state) = state ∧
      goldenDualTimeRenormalization (goldenDualTimeReverse state) = state ∧
      goldenTimeReflectionMatrix * goldenDualTimeMatrix * goldenTimeReflectionMatrix =
        goldenDualTimeReverseMatrix ∧
      goldenDualTimeMatrix * goldenDualTimeReverseMatrix = 1 ∧
      goldenDualTimeReverseMatrix * goldenDualTimeMatrix = 1 := by
  dsimp only
  have hScale := golden_dual_time_scale_ne_zero
  refine ⟨?_, rfl, ?_, ?_, golden_dual_time_matrix_reflection,
    golden_dual_time_matrix_mul_reverse, golden_dual_time_reverse_mul_matrix⟩
  · simp only [goldenDualTimeRenormalization]
    field_simp [hScale]
  · simp [goldenDualTimeReverse, goldenDualTimeRenormalization, hScale]
  · simp [goldenDualTimeReverse, goldenDualTimeRenormalization, hScale]

/-- A concrete nonzero state realizes the product invariant. -/
example :
    let updated := goldenDualTimeRenormalization (2, 3)
    updated.1 * updated.2 = 2 * 3 := by
  simpa using (golden_dual_time_renormalization 2 3).1

/-- The abstract reciprocal-scaling product law fails at a zero scale. -/
example :
    ¬(((0 : ℝ)⁻¹ * 1) * (0 * 1) = 1 * 1) := by
  norm_num

#print axioms golden_dual_time_renormalization

end D5.S3.Observer.HyperbolicTransport.GoldenDualTimeRenormalization
