/- GID: D5/S1/Recurrence/MatveevaGlobalBoundedness
   generality: I
   mirror-B: D5/B/S1/Recurrence/MatveevaGlobalBoundedness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A rational linear sequence refutes the literal nonzero-parameter global-boundedness claim. -/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace D5.S1.Recurrence.MatveevaGlobalBoundedness

def integralScaling (s : ℕ → ℚ) : Prop :=
  ∃ C : ℤ, C ≠ 0 ∧ ∀ n : ℕ, 1 ≤ n →
    ∃ k : ℤ, (C : ℚ) ^ n * s n = (k : ℚ)

def positiveComplexRadius (s : ℕ → ℚ) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ z : ℂ, ‖z‖ < R →
    Summable (fun n : ℕ => (s n : ℂ) * z ^ n)

def globallyBounded (s : ℕ → ℚ) : Prop :=
  integralScaling s ∧ positiveComplexRadius s

def claim : Prop :=
  ∀ a1 a2 b0 b1 b2 : ℚ,
    a1 ≠ 0 → a2 ≠ 0 →
    (∀ n : ℕ, 2 ≤ n → b0 ≠ -(n : ℚ)) →
    ∀ s : ℕ → ℚ,
      (∀ n : ℕ, 2 ≤ n →
        ((n : ℚ) + b0) * s n +
          (a1 * (n : ℚ) + b1) * s (n - 1) +
          (a2 * (n : ℚ) + b2) * s (n - 2) = 0) →
      a1 * a2 * b0 + a1 * b2 - 2 * a2 * b1 ≠ 0 →
      ¬ globallyBounded s

def witness (n : ℕ) : ℚ := (n : ℚ) + 1

private theorem witness_data :
    witness 0 = 1 ∧ witness 1 = 2 ∧
    (∀ n : ℕ, 2 ≤ n →
      ((n : ℚ) + 1) * witness n +
        ((-3 : ℚ) * (n : ℚ) + (-1)) * witness (n - 1) +
        ((2 : ℚ) * (n : ℚ) + 1) * witness (n - 2) = 0) ∧
    globallyBounded witness := by
  refine ⟨by norm_num [witness], by norm_num [witness], ?_, ?_⟩
  · intro n hn
    have hn1 : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
    simp only [witness, Nat.cast_sub hn1, Nat.cast_sub hn]
    push_cast
    ring
  · constructor
    · refine ⟨1, by norm_num, ?_⟩
      intro n hn
      refine ⟨(n : ℤ) + 1, ?_⟩
      simp [witness]
    · refine ⟨1, by norm_num, ?_⟩
      intro z hz
      simpa [witness] using
        (summable_choose_mul_geometric_of_norm_lt_one (R := ℂ) 1 hz)

theorem result : ¬ claim := by
  intro h
  have hw := witness_data
  exact h (-3) 2 1 (-1) 1 (by norm_num) (by norm_num)
    (by
      intro n hn
      have hnonneg : (0 : ℚ) ≤ n := Nat.cast_nonneg n
      linarith)
    witness hw.2.2.1 (by norm_num) hw.2.2.2

end D5.S1.Recurrence.MatveevaGlobalBoundedness
