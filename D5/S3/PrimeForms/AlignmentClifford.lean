/- GID: D5/S3/PrimeForms/AlignmentClifford
   generality: G
   mirror-B: D5/B/S3/PrimeForms/AlignmentClifford
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The alignment matrix K = [[1,-2],[2,-1]] squares to -3·I. On the alignment hyperplane V = {X : tr(X K) = 0} the generalized-flow identity β K β = (det β)·K holds for every β in V, and V is closed under the sandwich β,γ ↦ β γ β. The flow identity uses the hyperplane constraint entrywise; closure follows by trace cyclicity. -/

import Mathlib

open Matrix

namespace D5.S3.PrimeForms.AlignmentClifford

/-- The **alignment matrix** `K = [[1, -2], [2, -1]]`, an integer `2 × 2` matrix that squares to
`-3 • I` (see `K_sq`), so it represents a square root of `-3`. -/
def K : Matrix (Fin 2) (Fin 2) ℤ := !![1, -2; 2, -1]

/-- `K` squares to `-3 • I`: the alignment matrix has minimal polynomial `x² + 3`, so it plays the
role of a square root of `-3`. -/
theorem K_sq : K * K = (-3 : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Generalized-flow identity.** Every integer matrix `β` on the *alignment hyperplane*
`V = {X : tr (X K) = 0}` satisfies `β K β = (det β) • K`. The determinant appears as the exact scaling
factor, so `β` sends `K` to a rescaled copy of itself; the identity holds for *all* `β ∈ V`, with the
unimodular case `det β = ±1` (reflection-like action `K ↦ ±K`) as a special case. The proof reads off
the hyperplane constraint `β₀₀ + 2β₀₁ - 2β₁₀ - β₁₁ = 0` and applies it entrywise to the four entries
of `β K β - (det β) • K`.

Only the square identity `K_sq`, this generalized flow, and the closure `alignment_closed` are recorded
here; the `det β = ±1` acts-by-`±1` corollary reading, the flow / self-insertion / even-texture
unification, the paired-and-zero census certificate, and the phase-charge parity interpretation of the
wider result are not covered by these statements. -/
theorem generalized_flow (β : Matrix (Fin 2) (Fin 2) ℤ)
    (hβ : Matrix.trace (β * K) = 0) :
    β * K * β = (β.det) • K := by
  have hV : β 0 0 + 2 * β 0 1 - 2 * β 1 0 - β 1 1 = 0 := by
    have h := hβ
    simp [K, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at h
    linear_combination h
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [K, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two,
      Matrix.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one, Fin.isValue, Fin.mk_zero, Fin.mk_one]
  · linear_combination (β 0 0) * hV
  · linear_combination (β 0 1) * hV
  · linear_combination (β 1 0) * hV
  · linear_combination (β 1 1) * hV

/-- **Closure of the alignment hyperplane under the sandwich.** If `β` and `γ` both lie on
`V = {X : tr (X K) = 0}`, then so does `β γ β`. This is a trace-cyclicity corollary of the
generalized-flow identity: `tr (β γ β K) = tr (β K β γ) = (det β) · tr (K γ) = 0`. -/
theorem alignment_closed (β γ : Matrix (Fin 2) (Fin 2) ℤ)
    (hβ : Matrix.trace (β * K) = 0) (hγ : Matrix.trace (γ * K) = 0) :
    Matrix.trace (β * γ * β * K) = 0 := by
  have e1 : Matrix.trace (β * γ * β * K) = Matrix.trace (β * K * β * γ) := by
    have h := Matrix.trace_mul_comm (β * γ) (β * K)
    simpa [mul_assoc] using h
  rw [e1, generalized_flow β hβ, smul_mul_assoc, Matrix.trace_smul,
    Matrix.trace_mul_comm, hγ, smul_zero]

end D5.S3.PrimeForms.AlignmentClifford
