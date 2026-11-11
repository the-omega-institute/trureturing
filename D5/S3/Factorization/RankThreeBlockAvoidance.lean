/- GID: D5/S3/Factorization/RankThreeBlockAvoidance
   generality: G
   mirror-B: D5/B/S3/Factorization/RankThreeBlockAvoidance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The c=1 incidence counts in the rank-three block argument are incompatible with at least two blocks. -/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! The c=1 incidence-count core of the rank-three block-avoidance argument. -/

namespace D5.S3.Factorization.RankThreeBlockAvoidance

/-- The two incidence counts used in the distinct-closure branch cannot hold
when there are at least two blocks and each original block has at least two
points. -/
theorem incidence_count_contradiction {b m d : ℕ}
    (hb : 2 ≤ b) (hm : 2 ≤ m)
    (hB : b * (d - 1) = m - 1)
    (hL : (b + m - 1) * (d - 1) = m - 1) :
    False := by
  have hd : 1 ≤ d := by
    by_contra h
    have : d = 0 := by omega
    subst d
    simp at hB
    omega
  have hbm : b + m - 1 = b + (m - 1) := by omega
  have hsum : b * (d - 1) + (m - 1) * (d - 1) = m - 1 := by
    calc
      b * (d - 1) + (m - 1) * (d - 1) =
          (b + (m - 1)) * (d - 1) := by rw [Nat.add_mul]
      _ = (b + m - 1) * (d - 1) := by rw [hbm]
      _ = m - 1 := hL
  have hzero : (m - 1) * (d - 1) = 0 := by omega
  have hm1 : m - 1 ≠ 0 := by omega
  have hdsubzero : d - 1 = 0 :=
    (Nat.mul_eq_zero.mp hzero).resolve_left hm1
  have hBzero : b * 0 = m - 1 := by simpa [hdsubzero] using hB
  omega

end D5.S3.Factorization.RankThreeBlockAvoidance
