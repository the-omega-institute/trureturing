/- GID: D5/S1/Recurrence/Sun/Sequences
   generality: G
   mirror-B: D5/B/S1/Recurrence/Sun/Sequences
   mirror-E: none(waiver:source-sequences-have-no-separate-evidence-artifact)
   anchors: []
   utility: none
   digest: Sun's lowercase g and v sequences with their literal real recurrences. -/

import Mathlib.Tactic

namespace D5.S1.Recurrence.Sun.Sequences

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The lowercase sequence `g` in Sun, arXiv:2608.13192v1, Conjecture 5.2. -/
noncomputable def g (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => (x + 1) / 2
  | n + 2 =>
      ((2 * (n + 1) * (n + 2) + (x + 1) / 2) * g x (n + 1) -
        (n + 1) ^ 2 * g x n) / (n + 2) ^ 2

/-- The lowercase sequence `v` in Sun, arXiv:2608.13192v1, Conjecture 5.2. -/
noncomputable def v (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => x
  | n + 2 =>
      ((2 * (n + 1) + 1) * ((n + 1) * (n + 2) + x) * v x (n + 1) -
        (n + 1) ^ 3 * v x n) / (n + 2) ^ 3

#print axioms g
#print axioms v

end D5.S1.Recurrence.Sun.Sequences
