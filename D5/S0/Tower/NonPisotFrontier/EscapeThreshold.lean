/- GID: D5/S0/Tower/NonPisotFrontier/EscapeThreshold
   generality: I
   mirror-B: D5/B/S0/Tower/NonPisotFrontier/EscapeThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Past three plus root thirteen the conjugate step strictly expands. -/

import D5.S0.Tower.NonPisotFrontier.ConjugateBridge

/- Library-search audit trail (2026-08-18):
   * Repository search found the frontier base, its conjugate, the coordinate
     step and the conjugate bridge; nothing states an escape threshold.
   * Pinned Mathlib supplies `abs_sub_abs_le_abs_sub` and ordered-field lemmas;
     the threshold itself is elementary once the conjugate modulus is known. -/

namespace D5.S0.Tower.NonPisotFrontier.EscapeThreshold

open D5.S0.Tower.NonPisotFrontier.BetaThirteen

local notation "β'" => betaThirteenConjugate

/-- The conjugate modulus in closed form. -/
theorem abs_conjugate : |β'| = (Real.sqrt 13 - 1) / 2 := by
  have hneg := betaThirteenConjugate_neg
  rw [abs_of_neg hneg]
  simp only [betaThirteenConjugate]; ring

/-- The escape threshold, in closed form.  It is the point past which one step
of the conjugate map cannot be brought back by subtracting a digit. -/
noncomputable def escapeThreshold : Real := 3 + Real.sqrt 13

theorem escapeThreshold_pos : 0 < escapeThreshold := by
  have := sqrt_thirteen_nonneg
  simp only [escapeThreshold]; linarith

/-- The threshold is exactly two divided by the excess of the conjugate modulus
over one.  This is the inequality that makes it a threshold. -/
theorem escapeThreshold_spec : (|β'| - 1) * escapeThreshold = 2 := by
  have hsq := sqrt_thirteen_sq
  rw [abs_conjugate]
  simp only [escapeThreshold]
  nlinarith [hsq]

/-- Past the threshold, subtracting any digit between zero and two cannot undo
the expansion: the image is strictly farther from the origin than the source. -/
theorem escape_step {x d : Real} (hx : escapeThreshold < |x|)
    (hd0 : 0 ≤ d) (hd2 : d ≤ 2) : |x| < |β' * x - d| := by
  have hmod := abs_conjugate
  have hspec := escapeThreshold_spec
  have hbounds := sqrt_thirteen_bounds
  have hgt : 1 < |β'| := one_lt_abs_betaThirteenConjugate
  have hpos : 0 < |x| := lt_trans escapeThreshold_pos hx
  have hstep : |β'| * |x| - 2 ≤ |β' * x - d| := by
    have h1 : |β' * x| - |d| ≤ |β' * x - d| := by
      simpa using abs_sub_abs_le_abs_sub (β' * x) d
    have h2 : |β' * x| = |β'| * |x| := abs_mul _ _
    have h3 : |d| = d := abs_of_nonneg hd0
    rw [h2, h3] at h1
    linarith
  have hgrow : |x| < |β'| * |x| - 2 := by
    have hexcess : 2 < (|β'| - 1) * |x| := by
      have : (|β'| - 1) * escapeThreshold < (|β'| - 1) * |x| :=
        mul_lt_mul_of_pos_left hx (by linarith)
      linarith [hspec]
    nlinarith
  linarith

/-- The threshold statement, packaged: it is positive, it is exactly the ratio
that makes the step expanding, and past it every admissible digit leaves the
image strictly farther out. -/
theorem escape_threshold_is_a_threshold :
    0 < escapeThreshold ∧
      (|β'| - 1) * escapeThreshold = 2 ∧
        ∀ x d : Real, escapeThreshold < |x| → 0 ≤ d → d ≤ 2 →
          |x| < |β' * x - d| :=
  ⟨escapeThreshold_pos, escapeThreshold_spec,
    fun _ _ hx hd0 hd2 => escape_step hx hd0 hd2⟩

end D5.S0.Tower.NonPisotFrontier.EscapeThreshold
