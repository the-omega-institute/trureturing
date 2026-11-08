/- GID: D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.claim; result=D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.result; claim=D5/S3/StatisticalMechanics/DegradeFireNonExhaustiveOrbitRefutation.claim
   digest: A nine-firing periodic orbit with repeated labels refutes exhaustive firing. -/


import D5.S3.Geometry.FiniteCoordinateTruncation
import Mathlib.LinearAlgebra.Matrix.Circulant

/-! A saturated degrade-and-fire flow with a non-exhaustive periodic trajectory. -/

set_option autoImplicit false
set_option linter.style.longLine false

namespace D5.S3.StatisticalMechanics.DegradeFireNonExhaustiveOrbitRefutation

open Matrix
open D5.S3.Geometry.FiniteCoordinateTruncation (cut)

noncomputable def coupling (ε : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  circulant ![1 - ε, ε, 0]

noncomputable def reset (x : Fin 3 → ℝ) (i : Fin 3) : Fin 3 → ℝ :=
  Function.update x i 1

def IsRun (ε θ : ℝ) (s : ℕ → Fin 3 → ℝ) (lab : ℕ → Fin 3)
    (τ : ℕ → ℝ) : Prop :=
  ∀ k, 0 < τ k ∧
    (∀ t, 0 ≤ t → t < τ k → ∀ j, θ < (coupling ε *ᵥ cut t (s k)) j) ∧
    (coupling ε *ᵥ cut (τ k) (s k)) (lab k) ≤ θ ∧
    (∀ j, j ≠ lab k → θ < (coupling ε *ᵥ cut (τ k) (s k)) j) ∧
    (∀ t, 0 ≤ t → t ≤ τ k → Function.Injective (cut t (s k))) ∧
    Function.Injective (s (k + 1)) ∧
    s (k + 1) = reset (cut (τ k) (s k)) (lab k)

def IsPeriodic (s : ℕ → Fin 3 → ℝ) : Prop :=
  ∃ p > 0, ∀ k, s (k + p) = s k

def IsExhaustive (lab : ℕ → Fin 3) : Prop :=
  ∀ k, Function.Bijective ![lab k, lab (k + 1), lab (k + 2)]

def claim : Prop :=
  ∀ θ ε : ℝ, 0 < θ → θ < 1 → 1 / 2 < ε → ε < 1 - θ →
    ∀ s lab τ, (∀ j, θ < (coupling ε *ᵥ s 0) j) →
      IsRun ε θ s lab τ → IsPeriodic s → IsExhaustive lab

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

private theorem injective_three (x : Fin 3 → ℝ)
    (hab : x 0 ≠ x 1) (hac : x 0 ≠ x 2) (hbc : x 1 ≠ x 2) :
    Function.Injective x := by
  rw [Function.injective_iff_pairwise_ne]
  simpa only [pairwise_fin_succ_iff, Fin.forall_fin_succ,
    Fin.forall_fin_zero, Function.onFun, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Subsingleton.pairwise, and_true] using And.intro (And.intro hab.symm hac.symm)
      (And.intro (And.intro hab hac) (And.intro hbc.symm hbc))

private theorem duration_positive (i : Fin 9) : 0 < times i := by
  delta times
  fin_cases i <;> norm_num

private theorem before_threshold (i : Fin 9) (t : ℝ) (hτ : t < times i) (j : Fin 3) :
    (3 / 20 : ℝ) < (coupling (4 / 5) *ᵥ cut t (states i)) j := by
  delta times states coupling cut at *
  fin_cases i <;> fin_cases j <;>
    norm_num [circulant_apply, mulVec, vec3_dotProduct, vecHead, vecTail] at hτ ⊢ <;>
    simp only [max_def] <;> split_ifs <;> linarith

private theorem at_threshold (i : Fin 9) :
    (coupling (4 / 5) *ᵥ cut (times i) (states i)) (labels i) ≤ (3 / 20 : ℝ) := by
  delta times states labels coupling cut
  fin_cases i <;> norm_num [circulant_apply, mulVec, vec3_dotProduct, vecHead, vecTail]

private theorem other_above (i : Fin 9) (j : Fin 3) (hj : j ≠ labels i) :
    (3 / 20 : ℝ) < (coupling (4 / 5) *ᵥ cut (times i) (states i)) j := by
  delta times states labels coupling cut at *
  fin_cases i <;> fin_cases j <;>
    norm_num [circulant_apply, mulVec, vec3_dotProduct, vecHead, vecTail] at *

private theorem cut_distinct (i : Fin 9) (t : ℝ) (hτ : t ≤ times i) :
    Function.Injective (cut t (states i)) := by
  apply injective_three
  all_goals
    delta times states cut at *
    fin_cases i <;> norm_num at hτ ⊢ <;>
      simp only [max_def] <;> split_ifs <;> linarith

private theorem state_distinct (i : Fin 9) : Function.Injective (states i) := by
  delta states
  apply injective_three <;> fin_cases i <;> norm_num

private theorem reset_verified (i : Fin 9) :
    states (i + 1) = reset (cut (times i) (states i)) (labels i) := by
  delta states times labels reset cut
  ext j
  fin_cases i <;> fin_cases j <;> norm_num [Function.update]

private theorem block_verified (i : Fin 9) :
    0 < times i ∧
    (∀ t, 0 ≤ t → t < times i → ∀ j,
      (3 / 20 : ℝ) < (coupling (4 / 5) *ᵥ cut t (states i)) j) ∧
    (coupling (4 / 5) *ᵥ cut (times i) (states i)) (labels i) ≤ (3 / 20 : ℝ) ∧
    (∀ j, j ≠ labels i →
      (3 / 20 : ℝ) < (coupling (4 / 5) *ᵥ cut (times i) (states i)) j) ∧
    (∀ t, 0 ≤ t → t ≤ times i → Function.Injective (cut t (states i))) ∧
    Function.Injective (states (i + 1)) ∧
    states (i + 1) = reset (cut (times i) (states i)) (labels i) := by
  exact ⟨duration_positive i, fun t _ hτ j => before_threshold i t hτ j,
    at_threshold i, other_above i, fun t _ hτ => cut_distinct i t hτ,
    state_distinct (i + 1), reset_verified i⟩

private theorem run_verified : IsRun (4 / 5) (3 / 20) orbit firing duration := by
  intro k
  have h := block_verified ⟨k % 9, Nat.mod_lt k (by decide)⟩
  have hi : (⟨(k + 1) % 9, Nat.mod_lt (k + 1) (by decide)⟩ : Fin 9) =
      (⟨k % 9, Nat.mod_lt k (by decide)⟩ : Fin 9) + 1 :=
    Fin.ext (Nat.add_mod k 1 9)
  delta orbit firing duration
  rw [hi]
  exact h

private theorem initial_verified : ∀ j,
    (3 / 20 : ℝ) < (coupling (4 / 5) *ᵥ orbit 0) j := by
  delta coupling orbit states
  intro j
  fin_cases j <;> norm_num [circulant_apply, mulVec, vec3_dotProduct, vecHead, vecTail]

private theorem periodic_verified : IsPeriodic orbit := by
  refine ⟨9, by norm_num, ?_⟩
  intro k
  exact congrArg states (Fin.ext (Nat.add_mod_right k 9))

private theorem non_exhaustive_verified : ¬ IsExhaustive firing := by
  intro h
  exact Fin.zero_ne_one ((h 0).1 (by rfl))

theorem result : ¬ claim := by
  intro h
  apply non_exhaustive_verified
  exact h (3 / 20) (4 / 5) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) orbit firing duration initial_verified run_verified periodic_verified

end D5.S3.StatisticalMechanics.DegradeFireNonExhaustiveOrbitRefutation
