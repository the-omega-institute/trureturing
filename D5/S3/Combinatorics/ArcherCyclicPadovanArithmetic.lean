/- GID: D5/S3/Combinatorics/ArcherCyclicPadovanArithmetic
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArcherCyclicPadovanArithmetic
   mirror-E: none(waiver:arithmetic-of-the-fixed-padovan-sequence)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Every third Padovan value satisfies the cyclic count recurrence. -/

import D5.S3.Combinatorics.ArcherCyclicDefs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArcherCyclicPadovanArithmetic

open ArcherCyclicDefs

end D5.S3.Combinatorics.ArcherCyclicPadovanArithmetic

namespace D5.S3.Combinatorics.ArcherCyclicPadovanRecurrenceUniqueness

open ArcherCyclicDefs ArcherCyclicPadovanArithmetic

theorem triple_recurrence_unique (b : ℕ → ℕ)
    (h₁ : b 1 = padovan 3)
    (h₂ : b 2 = padovan 6)
    (h₃ : b 3 = padovan 9)
    (hrec : ∀ n, 1 ≤ n →
      b (n + 3) + 2 * b (n + 1) = 3 * b (n + 2) + b n) :
    ∀ n, 1 ≤ n → b n = padovan (3 * n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hn1 : n = 1
    · subst n
      simpa using h₁
    by_cases hn2 : n = 2
    · subst n
      simpa using h₂
    by_cases hn3 : n = 3
    · subst n
      simpa using h₃
    let m := n - 3
    have hm : 1 ≤ m := by dsimp [m]; omega
    have hmn : m < n := by dsimp [m]; omega
    have hm1n : m + 1 < n := by dsimp [m]; omega
    have hm2n : m + 2 < n := by dsimp [m]; omega
    have hb0 := ih m hmn hm
    have hb1 := ih (m + 1) hm1n (by omega)
    have hb2 := ih (m + 2) hm2n (by omega)
    have hbr := hrec m hm
    have hpr : padovan (3 * (m + 3)) + 2 * padovan (3 * (m + 1)) =
        3 * padovan (3 * (m + 2)) + padovan (3 * m) := by
      have h (k : ℕ) : padovan (k + 3) = padovan (k + 1) + padovan k := by
        rfl
      have h₁ := h (3 * m)
      have h₂ := h (3 * m + 1)
      have h₃ := h (3 * m + 2)
      have h₄ := h (3 * m + 3)
      have h₅ := h (3 * m + 4)
      have h₆ := h (3 * m + 5)
      have h₇ := h (3 * m + 6)
      have h₈ := h (3 * m + 7)
      have h₉ := h (3 * m + 8)
      simp only [Nat.mul_add, mul_one, Nat.reduceMul, Nat.add_assoc, Nat.reduceAdd] at *
      omega
    have hnm : n = m + 3 := by dsimp [m]; omega
    rw [hnm]
    rw [hb0, hb1, hb2] at hbr
    omega

end D5.S3.Combinatorics.ArcherCyclicPadovanRecurrenceUniqueness
