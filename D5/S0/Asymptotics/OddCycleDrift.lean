/- GID: D5/S0/Asymptotics/OddCycleDrift
   generality: G
   mirror-B: D5/B/S0/Asymptotics/OddCycleDrift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An odd-length sign reversal forces a real drift value to vanish. -/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace D5.S0.Asymptotics.OddCycleDrift

/-- If wrapping around a cycle of odd length multiplies a real drift value by
`(-1) ^ ell`, then that drift value is zero. -/
theorem odd_cycle_drift_eq_zero (ell : ℕ) (s : ℝ) (hell : Odd ell)
    (hcycle : s = (-1 : ℝ) ^ ell * s) : s = 0 := by
  rw [hell.neg_one_pow, neg_one_mul] at hcycle
  linarith

example : Odd 1 ∧ (0 : ℝ) = (-1 : ℝ) ^ (1 : ℕ) * 0 := by
  norm_num [Odd]

end D5.S0.Asymptotics.OddCycleDrift
