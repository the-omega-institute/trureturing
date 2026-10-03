/- GID: D5/S3/Quantum/Measurement/SequentialWeakPointerRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/SequentialWeakPointerRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Measurement/SequentialWeakPointerRefutation.claim; result=D5/S3/Quantum/Measurement/SequentialWeakPointerRefutation.result; claim=D5/S3/Quantum/Measurement/SequentialWeakPointerRefutation.claim
   digest: Three projections on C^3 and the state e_3 give pointer mean -1/6 < -1/8 (1805.09364). -/

/-
proof_shape: result: bind-only (evaluation of the definitions at three explicit rational
  projections on `ℂ³` and the state `e₃`: entrywise `simp` and `ring` for `P² = P = P†`, and
  `simp` and `norm_num` for the pointer mean `-1/6`)
escape_witness: null
admission_basis: open-problem-resolution (issue #11377; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Algebra.Star.StarProjection
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Measurement.SequentialWeakPointerRefutation

/-!
A. A. Abbott, R. Silva, J. Wechs, N. Brunner and C. Branciard, *Anomalous weak values without
post-selection*, arXiv:1805.09364 (Quantum 3, 194 (2019)). For `n` sequential weak measurements
of observables `A₁, …, Aₙ` on a pure state `ψ`, without post-selection, the mean product of the
pointer positions is `2^{-(n-1)} ⟨ψ| {A₁, {A₂, …, {A_{n-1}, Aₙ}…}} |ψ⟩` (Appendix). For two
projection observables (eigenvalues 0 and 1) the paper proves that this is at least `-1/8`, and
it conjectures the same bound for every number of projection observables. The conjecture fails
for three observables on `ℂ³`: the projection onto `(1, 1, -1)`, the projection `I - |v⟩⟨v|` with
`v = (0, 1, -1)/√2`, the projection `I - |w⟩⟨w|` with `w = (1, 0, -1)/√2`, and the state `e₃`
give `-1/6`.
-/

open Matrix

/-- The nested anticommutator `{A₀, {A₁, …, {A_{n-1}, A_n}…}}` of `n + 1` observables. -/
def nestedAnti {d : ℕ} :
    (n : ℕ) → (Fin (n + 1) → Matrix (Fin d) (Fin d) ℂ) → Matrix (Fin d) (Fin d) ℂ
  | 0, A => A 0
  | n + 1, A => A 0 * nestedAnti n (fun i => A i.succ) + nestedAnti n (fun i => A i.succ) * A 0

/-- The mean product of the pointer positions of `n + 1` sequential weak measurements of
`A 0, …, A n` on the pure state `ψ`, without post-selection. -/
noncomputable def pointerMean {d n : ℕ} (A : Fin (n + 1) → Matrix (Fin d) (Fin d) ℂ)
    (ψ : Fin d → ℂ) : ℝ :=
  (2 ^ n : ℝ)⁻¹ * (star ψ ⬝ᵥ (nestedAnti n A *ᵥ ψ)).re

/-- The conjecture of arXiv:1805.09364: for every number of sequential weak measurements of
projection observables and every pure state, the mean product of the pointer positions is at
least `-1/8`. -/
def claim : Prop :=
  ∀ (d n : ℕ) (A : Fin (n + 1) → Matrix (Fin d) (Fin d) ℂ), (∀ i, IsStarProjection (A i)) →
    ∀ ψ : Fin d → ℂ, star ψ ⬝ᵥ ψ = 1 → -1 / 8 ≤ pointerMean A ψ

private noncomputable def P1 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1 / 3, 1 / 3, -1 / 3; 1 / 3, 1 / 3, -1 / 3; -1 / 3, -1 / 3, 1 / 3]
private noncomputable def P2 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0; 0, 1 / 2, 1 / 2; 0, 1 / 2, 1 / 2]
private noncomputable def P3 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1 / 2, 0, 1 / 2; 0, 1, 0; 1 / 2, 0, 1 / 2]

/-- The conjecture fails: three projections on `ℂ³` and the state `e₃` give `-1/6`. -/
theorem result : ¬ claim := by
  intro h
  have hA : ∀ i, IsStarProjection (![P1, P2, P3] i) := by
    intro i
    fin_cases i <;> refine ⟨?_, ?_⟩ <;> ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [P1, P2, P3, Matrix.mul_apply, Matrix.star_apply, Fin.sum_univ_three] <;> ring
  have hψ : star (Pi.single 2 1 : Fin 3 → ℂ) ⬝ᵥ Pi.single 2 1 = 1 := by
    simp [dotProduct, Pi.single_apply]
  have hval : pointerMean ![P1, P2, P3] (Pi.single 2 1) = -1 / 6 := by
    simp [pointerMean, nestedAnti, P1, P2, P3, Matrix.mulVec, dotProduct, Pi.single_apply]
    norm_num
  have hle := h 3 2 ![P1, P2, P3] hA (Pi.single 2 1) hψ
  rw [hval] at hle
  norm_num at hle

end D5.S3.Quantum.Measurement.SequentialWeakPointerRefutation
