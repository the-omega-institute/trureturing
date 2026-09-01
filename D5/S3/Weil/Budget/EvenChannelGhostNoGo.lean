/- GID: D5/S3/Weil/Budget/EvenChannelGhostNoGo
   generality: G
   mirror-B: D5/B/S3/Weil/Budget/EvenChannelGhostNoGo
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive square update preserves the even channel and defeats the odd. -/

import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * D5 searches for even/odd channels, ghost no-go statements, affine
     positivity updates, and square-margin criteria found no exact theorem.
     `ResolventParitySignatures` proves the analytic cosh/sinh sign identity,
     `OffLineOrbitParityDecomposition` packages even energy minus odd energy,
     and `OddTestBudgetUpperBound` bounds a negative rank-one pencil; none
     constructs a shared positive coefficient with the conclusion below.
   * Pinned Mathlib supplies `sq_nonneg`, `sq_pos_of_ne_zero`,
     `div_mul_cancel₀`, and the ordered-ring tactics used below. No Mathlib
     theorem packages the simultaneous even-preservation/odd-destruction
     statement.
   * Searches across the pinned third-party Lean dependency closure found no
     domain theorem with this statement. No new definition is introduced. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.Budget.EvenChannelGhostNoGo

/-- A nonnegative update coefficient preserves a nonnegative even channel. -/
theorem even_channel_update_nonnegative
    (qPlus c C : ℝ) (hqPlus : 0 ≤ qPlus) (hc : 0 ≤ c) :
    0 ≤ qPlus + c * C ^ 2 := by
  exact add_nonneg hqPlus (mul_nonneg hc (sq_nonneg C))

/-- A nonzero odd coefficient admits an explicit positive update that makes
the odd channel negative. The numerator `qMinus ^ 2 + 1` keeps the witness
positive for every real initial channel value. -/
theorem odd_channel_update_eventually_negative
    (qMinus S : ℝ) (hS : S ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ qMinus - c * S ^ 2 < 0 := by
  have hSquare : 0 < S ^ 2 := sq_pos_of_ne_zero hS
  let c : ℝ := (qMinus ^ 2 + 1) / S ^ 2
  have hNumerator : 0 < qMinus ^ 2 + 1 := by
    nlinarith [sq_nonneg qMinus]
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos hNumerator hSquare
  refine ⟨c, hc, ?_⟩
  have hCancel : c * S ^ 2 = qMinus ^ 2 + 1 := by
    dsimp [c]
    exact div_mul_cancel₀ _ hSquare.ne'
  rw [hCancel]
  nlinarith [sq_nonneg (qMinus - (1 / 2 : ℝ))]

/-- Even-channel positivity alone cannot force odd-channel positivity: one
positive coefficient simultaneously preserves the former and destroys the
latter whenever the odd coefficient is nonzero. -/
theorem even_channel_ghost_no_go
    (qPlus qMinus C S : ℝ) (hqPlus : 0 ≤ qPlus) (hS : S ≠ 0) :
    ∃ c : ℝ, 0 < c ∧
      0 ≤ qPlus + c * C ^ 2 ∧ qMinus - c * S ^ 2 < 0 := by
  obtain ⟨c, hc, hOdd⟩ := odd_channel_update_eventually_negative qMinus S hS
  exact ⟨c, hc, even_channel_update_nonnegative qPlus c C hqPlus hc.le, hOdd⟩

/-- The old odd-channel margin is exactly the condition that the update does
not destroy odd-channel nonnegativity. -/
theorem odd_channel_margin_iff_nonnegative (qMinus c S : ℝ) :
    c * S ^ 2 ≤ qMinus ↔ 0 ≤ qMinus - c * S ^ 2 := by
  constructor <;> intro h <;> linarith

/-- The same coefficient `c = 2` preserves the concrete even channel and
makes the concrete odd channel negative. -/
theorem concrete_same_coefficient_witness :
    0 < (2 : ℝ) ∧ (1 : ℝ) ≠ 0 ∧
      0 ≤ (1 : ℝ) + 2 * 1 ^ 2 ∧ (1 : ℝ) - 2 * 1 ^ 2 < 0 := by
  norm_num

/-- With `S = 0`, even a large positive update leaves a positive odd channel
unchanged, so the nonzero hypothesis in the no-go theorem is necessary. -/
theorem zero_odd_coefficient_counterexample :
    0 < (100 : ℝ) ∧ 0 ≤ (1 : ℝ) - 100 * 0 ^ 2 := by
  norm_num

#print axioms even_channel_update_nonnegative
#print axioms odd_channel_update_eventually_negative
#print axioms even_channel_ghost_no_go
#print axioms odd_channel_margin_iff_nonnegative
#print axioms concrete_same_coefficient_witness
#print axioms zero_odd_coefficient_counterexample

end D5.S3.Weil.Budget.EvenChannelGhostNoGo
