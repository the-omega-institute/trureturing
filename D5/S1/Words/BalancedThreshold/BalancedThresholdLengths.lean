/- GID: D5/S1/Words/BalancedThreshold/BalancedThresholdLengths
   generality: G
   mirror-B: D5/B/S1/Words/BalancedThreshold/BalancedThresholdLengths
   mirror-E: none(waiver:infinite-continuant-length-growth)
   anchors: [mathlib/module/Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence]
   utility: none
   digest: Positive total continuant lengths grow strictly after their equal initial pair. -/

import Mathlib.Algebra.ContinuedFractions.ContinuantsRecurrence
import D5.S1.Words.BalancedThreshold.BalancedThresholdExpansion

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.BalancedThreshold

/-- Two-step induction propagates positive physical lengths. Strict growth starts at index
one: the auxiliary predecessor and the zeroth convergent both have total length one. -/
theorem uniform_continuant_length_growth (t : ℕ) (ht : 5 ≤ t) :
    let g := GenContFract.of (uniformSlope t / (1 - uniformSlope t))
    ∀ n, 0 < (g.contsAux n).a + (g.contsAux n).b ∧
      (1 ≤ n → (g.contsAux n).a + (g.contsAux n).b <
        (g.contsAux (n + 1)).a + (g.contsAux (n + 1)).b) := by
  let g := GenContFract.of (uniformSlope t / (1 - uniformSlope t))
  let L := fun n => (g.contsAux n).a + (g.contsAux n).b
  let digit := fun n : ℕ =>
    if n = 0 then t + 2 else if n = 1 then t
    else if n % 2 = 0 then t - 2 else t + 1
  have digits : ∀ n, g.s.get? n = some ⟨1, (digit n : ℝ)⟩ :=
    (uniform_ratio_expansion t ht).2
  have hhead : g.h = 0 := (uniform_ratio_expansion t ht).1
  have hcoeff : ∀ n, (1 : ℝ) ≤ digit n := by
    intro n
    have hd : 1 ≤ digit n := by dsimp [digit]; split_ifs <;> omega
    exact_mod_cast hd
  have recurrence : ∀ n, L (n + 2) = (digit n : ℝ) * L (n + 1) + L n := by
    intro n
    dsimp only [L]
    rw [GenContFract.contsAux_recurrence (digits n) rfl rfl]
    dsimp only
    ring
  have positive : ∀ n, 0 < L n := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => simp [L, GenContFract.contsAux]
    | one => simp [L, GenContFract.contsAux, hhead]
    | more n hn hn1 =>
      rw [recurrence]
      exact add_pos (mul_pos (lt_of_lt_of_le zero_lt_one (hcoeff n)) hn1) hn
  change ∀ n, 0 < L n ∧ (1 ≤ n → L n < L (n + 1))
  intro n
  refine ⟨positive n, ?_⟩
  intro hn
  cases n with
  | zero => omega
  | succ n =>
    rw [recurrence]
    have hmul := mul_le_mul_of_nonneg_right (hcoeff n) (positive (n + 1)).le
    linarith only [hmul, positive n]

end D5.S1.Words.BalancedThreshold
