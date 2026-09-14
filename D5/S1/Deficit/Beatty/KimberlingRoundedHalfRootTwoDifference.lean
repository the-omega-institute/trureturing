/- GID: D5/S1/Deficit/Beatty/KimberlingRoundedHalfRootTwoDifference
   generality: I
   mirror-B: D5/B/S1/Deficit/Beatty/KimberlingRoundedHalfRootTwoDifference
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Algebra.Order.Round, mathlib/module/Mathlib.NumberTheory.Real.Irrational, mathlib/module/Mathlib.Tactic]
   utility: none
   digest: The differences of round(n/sqrt 2) are zero or one at the two complementary shifted Beatty positions. -/

import Mathlib.Algebra.Order.Round
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Deficit.Beatty.KimberlingRoundedHalfRootTwoDifference

/-- OEIS A049473: the nearest integer to `n / sqrt 2`. -/
noncomputable def a (n : ℕ) : ℤ :=
  round ((n : ℝ) / Real.sqrt 2)

/-- OEIS A001953, the lower shifted Beatty sequence in the conjecture. -/
noncomputable def lower (k : ℕ) : ℤ :=
  ⌊((k : ℝ) + 1 / 2) * Real.sqrt 2⌋

/-- OEIS A001954, the upper shifted Beatty sequence in the conjecture. -/
noncomputable def upper (k : ℕ) : ℤ :=
  ⌊((k : ℝ) + 1 / 2) * (2 + Real.sqrt 2)⌋

end D5.S1.Deficit.Beatty.KimberlingRoundedHalfRootTwoDifference
