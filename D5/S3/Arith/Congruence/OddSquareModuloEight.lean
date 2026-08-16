/- GID: D5/S3/Arith/Congruence/OddSquareModuloEight
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/OddSquareModuloEight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every odd natural square is congruent to one modulo eight. -/

import Mathlib.NumberTheory.Multiplicity

namespace D5.S3.Arith.Congruence.OddSquareModuloEight

/-- The square of every odd natural number is congruent to one modulo eight. -/
theorem eight_dvd_odd_square_sub_one {T : ℕ} (hT : Odd T) :
    8 ∣ T ^ 2 - 1 :=
  Nat.eight_dvd_sq_sub_one_of_odd hT

end D5.S3.Arith.Congruence.OddSquareModuloEight
