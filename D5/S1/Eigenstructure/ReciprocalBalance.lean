/- GID: D5/S1/Eigenstructure/ReciprocalBalance
   generality: I
   mirror-B: D5/B/S1/Eigenstructure/ReciprocalBalance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reciprocal-antisymmetric periodic slopes vanish at metallic roots. -/

import Mathlib.Algebra.Ring.CharZero
import Mathlib.Algebra.Ring.Periodic
import D5.S0.Asymptotics.MetallicFamily

namespace D5.S1.Eigenstructure.ReciprocalBalance

open D5.S0.Asymptotics.MetallicFamily

/-- A unit-periodic reciprocal-antisymmetric slope vanishes at every metallic root. -/
theorem metallic_reciprocal_symmetry_forces_balance (n : ℕ) (s : ℝ → ℝ)
    (hperiodic : Function.Periodic s 1)
    (hreciprocal : s (1 / metallicValue n) = -s (metallicValue n)) :
    s (metallicValue n) = 0 := by
  have hshift : s (metallicValue n - n) = s (metallicValue n) := by
    simpa using hperiodic.sub_nat_mul_eq n (x := metallicValue n)
  rw [(metallic_family_value n).2, hshift] at hreciprocal
  exact CharZero.eq_neg_self_iff.mp hreciprocal

end D5.S1.Eigenstructure.ReciprocalBalance
