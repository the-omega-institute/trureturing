/- GID: D5/S3/Quantum/Rotors/ProductBranchLevels
   generality: G
   mirror-B: D5/B/S3/Quantum/Rotors/ProductBranchLevels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Order.Bounds.Basic]
   utility: none
   digest: First two positive product rotor levels and their parameter fibers. -/

module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The low-energy ordering of the specified product of two unit-three-sphere branch lists. -/

@[expose] public section
namespace D5.S3.Quantum.Rotors.ProductBranchLevels

/-- The value of the branch with angular degrees `l` and `k`. -/
def energy (a b : ℝ) (l k : ℕ) : ℝ :=
  a * (l * (l + 2) : ℕ) + b * (k * (k + 2) : ℕ)

/-- All distinct branch values strictly above a threshold. -/
def above (a b t : ℝ) : Set ℝ := {e | t < e ∧ ∃ l k : ℕ, energy a b l k = e}

/-- Candidate for the second distinct positive level with ordered coefficients. -/
noncomputable def secondLevel (a b : ℝ) : ℝ := if a = b then 6 * a else min (3 * b) (8 * a)

private theorem ladder_cases (n : ℕ) :
    (n * (n + 2) : ℕ) = 0 ∨ (n * (n + 2) : ℕ) = 3 ∨ 8 ≤ n * (n + 2) := by
  cases n with
  | zero => exact Or.inl rfl
  | succ n =>
    cases n with
    | zero => exact Or.inr (Or.inl rfl)
    | succ n =>
      right; right
      exact Nat.mul_le_mul (by omega : 2 ≤ n + 2) (by omega : 4 ≤ n + 2 + 2)

private theorem scaled_cases (a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    a * (n * (n + 2) : ℕ) = 0 ∨ a * (n * (n + 2) : ℕ) = 3 * a ∨
      8 * a ≤ a * (n * (n + 2) : ℕ) := by
  rcases ladder_cases n with h | h | h
  · simp [h]
  · simp [h, mul_comm]
  · right; right
    have bound : (8 : ℝ) ≤ (n * (n + 2) : ℕ) := by exact_mod_cast h
    linarith only [mul_le_mul_of_nonneg_left bound ha]

private theorem low_cases {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (l k : ℕ) :
    energy a b l k = 0 ∨ energy a b l k = 3 * a ∨ energy a b l k = 3 * b ∨
    energy a b l k = 3 * a + 3 * b ∨ 8 * a ≤ energy a b l k := by
  unfold energy
  have hb := ha.le.trans hab
  rcases scaled_cases a ha.le l with hl | hl | hl <;>
    rcases scaled_cases b hb k with hk | hk | hk <;> grind

/-- The minimum positive branch and the minimum branch strictly above that minimum. -/
theorem first_two_positive_levels {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IsLeast (above a b 0) (3 * a) ∧ IsLeast (above a b (3 * a)) (secondLevel a b) := by
  constructor
  · refine ⟨⟨by linarith, 1, 0, by norm_num [energy, mul_comm]⟩, ?_⟩
    rintro e ⟨he, l, k, rfl⟩
    rcases low_cases ha hab l k with h | h | h | h | h <;> linarith
  · constructor
    · unfold secondLevel
      split
      · rename_i h
        subst b
        exact ⟨by linarith, 1, 1, by norm_num [energy]; ring⟩
      · rename_i h
        have hlt := lt_of_le_of_ne hab h
        refine ⟨lt_min (by linarith) (by linarith), ?_⟩
        rcases le_total (3*b) (8*a) with h | h
        · exact ⟨0, 1, by rw [min_eq_left h]; norm_num [energy, mul_comm]⟩
        · exact ⟨2, 0, by rw [min_eq_right h]; norm_num [energy, mul_comm]⟩
    · rintro e ⟨he, l, k, rfl⟩
      unfold secondLevel
      split
      · rename_i h
        subst b
        rcases low_cases ha le_rfl l k with h | h | h | h | h <;> linarith
      · have h1 := min_le_left (3*b) (8*a)
        have h2 := min_le_right (3*b) (8*a)
        rcases low_cases ha hab l k with h | h | h | h | h <;> linarith

/-- Complete equality criterion for the second distinct level at a fixed smaller coefficient.
The two first levels therefore have the same fibers. -/
theorem second_level_fiber {a b c : ℝ} (ha : 0 < a) :
    secondLevel a b = secondLevel a c ↔
      b = c ∨ (b = a ∧ c = 2 * a) ∨ (c = a ∧ b = 2 * a) ∨
      (8 * a ≤ 3 * b ∧ 8 * a ≤ 3 * c) := by
  unfold secondLevel min
  split_ifs <;> grind

end D5.S3.Quantum.Rotors.ProductBranchLevels
