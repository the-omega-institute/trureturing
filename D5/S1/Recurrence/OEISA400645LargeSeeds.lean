import D5.S1.Recurrence.OEISA400645BoundedError
import D5.S1.Recurrence.RoundedNormBoundedError

set_option autoImplicit false

noncomputable section

namespace D5.S1.Recurrence.OEISA400645LargeSeeds

open Polynomial Asymptotics Filter
open D5.S1.Recurrence.OEISA400645 (radicand squaredLimit limitingRatio r_bounds)
open D5.S1.Recurrence.OEISA400645BoundedError (charPoly charPoly_sum rootMultiplicity_charPoly
  other_roots)

section

variable {a : ℕ → ℕ}

private theorem rad_cast (n : ℕ) (hn : 3 ≤ n) :
    (radicand a n : ℝ) = (a n : ℝ) ^ 2 + (a (n - 1) : ℝ) ^ 2 + (a (n - 2) : ℝ) ^ 2 -
      (a (n - 3) : ℝ) ^ 2 := by
  simp [radicand]

private theorem round_err (hrec : ∀ n, 4 ≤ n → (a (n + 1) : ℤ) = round (Real.sqrt (radicand a n : ℝ)))
    (n : ℕ) (hn : 4 ≤ n) :
    |(a (n + 1) : ℝ) - Real.sqrt (radicand a n : ℝ)| ≤ 1 / 2 := by
  have h := abs_sub_round (Real.sqrt (radicand a n : ℝ))
  rw [← hrec n hn, abs_sub_comm] at h
  exact_mod_cast h

/-- The sequence is nondecreasing from index one, and every radicand is at least `a n ^ 2`. -/
private theorem mono_rad (h12 : a 1 ≤ a 2) (h23 : a 2 ≤ a 3) (h34 : a 3 ≤ a 4)
    (hrec : ∀ n, 4 ≤ n → (a (n + 1) : ℤ) = round (Real.sqrt (radicand a n : ℝ))) :
    ∀ n, 1 ≤ n → a n ≤ a (n + 1) ∧ (4 ≤ n → (a n : ℝ) ^ 2 ≤ radicand a n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 4 with hlt | hge
    · refine ⟨?_, fun h => absurd h (by omega)⟩
      interval_cases n
      · exact h12
      · exact h23
      · exact h34
    · have hprev := (ih (n - 3) (by omega) (by omega)).1
      rw [show n - 3 + 1 = n - 2 by omega] at hprev
      have hprevR : (a (n - 3) : ℝ) ≤ a (n - 2) := by exact_mod_cast hprev
      have hrad : (a n : ℝ) ^ 2 ≤ radicand a n := by
        rw [rad_cast n (by omega)]
        nlinarith [sq_nonneg (a (n - 1) : ℝ), (Nat.cast_nonneg (a (n - 3)) : (0 : ℝ) ≤ _)]
      refine ⟨?_, fun _ => hrad⟩
      have h := (abs_le.mp (round_err hrec n hge)).1
      have hle : (a n : ℝ) ≤ Real.sqrt (radicand a n) :=
        Real.le_sqrt_of_sq_le hrad
      have : (a n : ℝ) < a (n + 1) + 1 := by linarith
      exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

end

end D5.S1.Recurrence.OEISA400645LargeSeeds
