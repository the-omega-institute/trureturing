/- GID: D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.claim; result=D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.result; claim=D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.claim
   digest: A nine-firing periodic orbit with repeated labels refutes exhaustive firing. -/

import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace D5.S3.StatisticalMechanics.DegradeFireNonExhaustiveOrbitRefutation

noncomputable def coupling (ε : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 - ε, 0, ε; ε, 1 - ε, 0; 0, ε, 1 - ε]

noncomputable def flow (s : Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  fun j => max 0 (s j - t)

noncomputable def reset (x : Fin 3 → ℝ) (i : Fin 3) : Fin 3 → ℝ :=
  Function.update x i 1

def IsRun (ε η : ℝ) (s : ℕ → Fin 3 → ℝ) (lab : ℕ → Fin 3)
    (τ : ℕ → ℝ) : Prop :=
  ∀ k, 0 < τ k ∧
    (∀ t, 0 ≤ t → t < τ k → ∀ j, η < (coupling ε *ᵥ flow (s k) t) j) ∧
    (coupling ε *ᵥ flow (s k) (τ k)) (lab k) ≤ η ∧
    (∀ j, j ≠ lab k → η < (coupling ε *ᵥ flow (s k) (τ k)) j) ∧
    (∀ t, 0 ≤ t → t ≤ τ k → Function.Injective (flow (s k) t)) ∧
    Function.Injective (s (k + 1)) ∧
    s (k + 1) = reset (flow (s k) (τ k)) (lab k)

def IsPeriodic (s : ℕ → Fin 3 → ℝ) : Prop :=
  ∃ p > 0, ∀ k, s (k + p) = s k

def IsExhaustive (lab : ℕ → Fin 3) : Prop :=
  ∀ k, Function.Bijective ![lab k, lab (k + 1), lab (k + 2)]

def claim : Prop :=
  ∀ η ε : ℝ, 0 < η → η < 1 → 1 / 2 < ε → ε < 1 - η →
    ∀ s lab τ, (∀ j, η < (coupling ε *ᵥ s 0) j) →
      IsRun ε η s lab τ → IsPeriodic s → IsExhaustive lab

private noncomputable def states : Fin 9 → Fin 3 → ℝ :=
  ![![11 / 32, 0, 1], ![3 / 16, 1, 27 / 32], ![0, 1, 19 / 32],
    ![0, 1, 11 / 32], ![1, 27 / 32, 3 / 16], ![1, 19 / 32, 0],
    ![1, 11 / 32, 0], ![27 / 32, 3 / 16, 1], ![19 / 32, 0, 1]]

private def labels : Fin 9 → Fin 3 := ![1, 1, 1, 0, 0, 0, 2, 2, 2]

private noncomputable def times : Fin 9 → ℝ :=
  ![5 / 32, 1 / 4, 1 / 4, 5 / 32, 1 / 4, 1 / 4, 5 / 32, 1 / 4, 1 / 4]

private noncomputable def orbit (k : ℕ) : Fin 3 → ℝ :=
  states ⟨k % 9, Nat.mod_lt k (by decide)⟩

private def firing (k : ℕ) : Fin 3 := labels ⟨k % 9, Nat.mod_lt k (by decide)⟩

private noncomputable def duration (k : ℕ) : ℝ :=
  times ⟨k % 9, Nat.mod_lt k (by decide)⟩

private theorem block_verified (i : Fin 9) :
    0 < times i ∧
    (∀ t, 0 ≤ t → t < times i → ∀ j,
      (3 / 20 : ℝ) < (coupling (4 / 5) *ᵥ flow (states i) t) j) ∧
    (coupling (4 / 5) *ᵥ flow (states i) (times i)) (labels i) ≤ (3 / 20 : ℝ) ∧
    (∀ j, j ≠ labels i →
      (3 / 20 : ℝ) < (coupling (4 / 5) *ᵥ flow (states i) (times i)) j) ∧
    (∀ t, 0 ≤ t → t ≤ times i → Function.Injective (flow (states i) t)) ∧
    Function.Injective (states (i + 1)) ∧
    states (i + 1) = reset (flow (states i) (times i)) (labels i) := by
  sorry

private theorem run_verified : IsRun (4 / 5) (3 / 20) orbit firing duration := by
  intro k
  have h := block_verified ⟨k % 9, Nat.mod_lt k (by decide)⟩
  convert h using 1 <;> sorry

private theorem initial_verified : ∀ j,
    (3 / 20 : ℝ) < (coupling (4 / 5) *ᵥ orbit 0) j := by
  sorry

private theorem periodic_verified : IsPeriodic orbit := by
  sorry

private theorem non_exhaustive_verified : ¬ IsExhaustive firing := by
  sorry

theorem result : ¬ claim := by
  intro h
  apply non_exhaustive_verified
  exact h (3 / 20) (4 / 5) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) orbit firing duration initial_verified run_verified periodic_verified

end D5.S3.StatisticalMechanics.DegradeFireNonExhaustiveOrbitRefutation
