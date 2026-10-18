/- GID: D5/S3/Zeros/CriticalPoints/SchurStripCenter
   generality: G
   mirror-B: D5/B/S3/Zeros/CriticalPoints/SchurStripCenter
   mirror-E: none(waiver:open-problem-resolution)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Matrix.Trace]
   utility: none
   digest: The Schur interpolation trace at the reciprocal exponent. -/

import D5.S3.Zeros.CriticalPoints.SchurStripFunctions

/-! The interpolation center recovers the prescribed weighted Schur diagonal sum. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.Zeros.CriticalPoints.SchurStripCenter

open Matrix Complex
open scoped ComplexConjugate
open RankOneComplexPowers SchurStripFunctions

/-- The trace at `1 / p` is the weighted diagonal sum in the same matrix basis. -/
theorem center_identity (n : ℕ) (Q : Matrix (Fin n) (Fin n) ℂ)
    (u v b μ : Fin n → ℂ) (t ρ : Fin n → ℝ) (p N : ℝ)
    (hp : 0 < p) (ht : ∀ j, 0 < t j) (hρ : ∀ k, 0 < ρ k)
    (hb : ∀ j, b j = u j * (t j : ℂ))
    (hμ : ∀ k, μ k =
      (Qᴴ * (H n (1 / 2) * diagonal b * H n (1 / 2)) * Q) k k)
    (hsum : (∑ k, (conj (v k) * ((ρ k ^ (p - 1) : ℝ) : ℂ)) * μ k) = (N : ℂ)) :
    f n Q u v t ρ p ((1 / p : ℝ) : ℂ) = (N : ℂ) := by
  have hp0 : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hp)
  have hcenter : (p : ℂ) * ((1 / p : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp [hp0]
  have hexp : (p : ℂ) * (1 - ((1 / p : ℝ) : ℂ)) = ((p - 1 : ℝ) : ℂ) := by
    push_cast
    field_simp [hp0] <;> ring
  let A : Matrix (Fin n) (Fin n) ℂ := H n (1 / 2) * diagonal b * H n (1 / 2)
  let d : Fin n → ℂ := fun k => conj (v k) * ((ρ k ^ (p - 1) : ℝ) : ℂ)
  have hF : F n u t p ((1 / p : ℝ) : ℂ) = A := by
    have hD : diagonal (fun j => u j * positivePower (t j) 1) = diagonal b := by
      congr 1
      funext j
      rw [positivePower_one (ht j), ← hb j]
    unfold F
    rw [hcenter, hD]
  have hK : K n Q v ρ p ((1 / p : ℝ) : ℂ) = Q * diagonal d * Qᴴ := by
    have hD : diagonal (fun k => conj (v k) * positivePower (ρ k) ((p - 1 : ℝ) : ℂ)) =
        diagonal d := by
      congr 1
      funext k
      exact congrArg (fun z : ℂ => conj (v k) * z) (positivePower_ofReal (hρ k) (p - 1))
    simp only [K, hexp, hD]
  unfold f
  rw [hF, hK, Matrix.mul_assoc (Q * diagonal d) Qᴴ A,
    trace_mul_cycle, trace_mul_comm _ (diagonal d)]
  change (∑ k, (diagonal d * (Qᴴ * A * Q)) k k) = (N : ℂ)
  simp only [Matrix.diagonal_mul]
  dsimp only [A, d]
  simpa only [← hμ] using hsum

end D5.S3.Zeros.CriticalPoints.SchurStripCenter
