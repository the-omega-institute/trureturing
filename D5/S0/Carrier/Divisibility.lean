/- GID: D5/S0/Carrier/Divisibility
   generality: I
   mirror-B: D5/B/S0/Carrier/Divisibility
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Nonzero golden-integer divisibility bounds absolute norms. -/

import D5.S0.Carrier.Euclidean

namespace D5.S0.Carrier

/-- A divisor of a nonzero golden integer has absolute norm no larger than that element. -/
theorem norm_natAbs_le_of_dvd {x y : GoldenInt} (hy : y ≠ 0) (hxy : x ∣ y) :
    (norm x).natAbs ≤ (norm y).natAbs := by
  rcases hxy with ⟨z, rfl⟩
  have hz : z ≠ 0 := by
    intro hz
    apply hy
    simp [hz]
  rw [norm_mul, Int.natAbs_mul]
  apply Nat.le_mul_of_pos_right
  exact Int.natAbs_pos.mpr (mt (norm_eq_zero_iff z).mp hz)

end D5.S0.Carrier
