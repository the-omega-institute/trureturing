/- GID: D5/S1/Dynamics/Shadowing/PowersTwoReturnDistances
   generality: I
   mirror-B: D5/B/S1/Dynamics/Shadowing/PowersTwoReturnDistances
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Powers-of-two return distances separate neighborhood two-shadowing from exact-length QFT. -/

import D5.S1.Dynamics.Shadowing.ReturnDistanceShadowing

/-! The distance convention is 2^j, hence the intervening zero-run length is 2^j-1.
This includes distance one. The statement concerns Question 5.3 of
Meddaugh–Stephens, arXiv:2509.04312v1, with natural-time pseudo-orbits. -/

open scoped PiCountable

namespace D5.S1.Dynamics.Shadowing

/-- Positive return distances 1,2,4,8,... . -/
def powersTwoDistances : Set ℤ := {d | ∃ j : ℕ, d = (2 : ℤ) ^ j}

/-- The actual compact binary two-sided subshift has original neighborhood two-shadowing
and fails the original exact-length quasi-finite-type condition. -/
theorem powers_two_return_distance_example :
    CompactSpace (ReturnPoint powersTwoDistances) ∧
    Continuous (returnShift powersTwoDistances) ∧
    NeighborhoodTwoShadowing (returnShift powersTwoDistances) ∧
    ¬ ReturnQuasiFiniteType powersTwoDistances := by
  refine ⟨inferInstance, return_shift_continuous _, ?_, ?_⟩
  · apply unbounded_return_neighborhood_two
    · exact ⟨0, by simp⟩
    · intro N
      refine ⟨2 ^ (N + 1), ?_, ?_⟩
      · exact (Nat.lt_succ_self N).trans (Nat.lt_two_pow_self)
      · exact ⟨N + 1, by norm_cast⟩
  · apply forbidden_intervals_not_quasi_finite_type
    intro n
    let H : ℕ := 2 ^ (n + 2)
    have hnH : n + 1 < H := (Nat.lt_succ_self (n + 1)).trans Nat.lt_two_pow_self
    refine ⟨H, fun d hHd hdN => ?_⟩
    rintro ⟨j, hj⟩
    have hd : d = 2 ^ j := by exact_mod_cast hj
    by_cases hjn : j ≤ n + 2
    · have hp : (2 : ℕ) ^ j ≤ 2 ^ (n + 2) := by gcongr
      dsimp [H] at hHd
      omega
    · have hp : (2 : ℕ) ^ (n + 3) ≤ 2 ^ j := by gcongr; omega
      have he : (2 : ℕ) ^ (n + 3) = 2 * H := by dsimp [H]; ring
      rw [he] at hp
      omega

#print axioms powers_two_return_distance_example

end D5.S1.Dynamics.Shadowing
