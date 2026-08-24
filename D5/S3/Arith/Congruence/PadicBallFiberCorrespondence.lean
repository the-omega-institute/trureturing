/- GID: D5/S3/Arith/Congruence/PadicBallFiberCorrespondence
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/PadicBallFiberCorrespondence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Congruence modulo a prime power is exactly p-adic proximity, and its integer fiber is a closed ball intersected with the integer image. -/

import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.Padics.PadicNumbers

/- Library-search audit trail (2026-08-22):
   * `rg -n -F 'modeq_iff_padic_dist_le' D5 Golden/Frozen/accepted` returned no match.
   * Searches for `padicNorm`, `padicDist`, and p-adic closed balls in `D5` found no public
     or private version of either theorem; `PadicPrecisionBlindSpot.lean` is absent here.
   * The pinned mathlib provides `Padic.norm_int_le_pow_iff_dvd`, built from
     `padicNorm.dvd_iff_norm_le`; the proof reuses it, then proves the new fiber equality. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Congruence.PadicBallFiberCorrespondence

/-- The integer points congruent to `x` modulo `p ^ k`, embedded in the p-adic numbers. -/
def congruenceFiber (p k : ℕ) [Fact p.Prime] (x : ℤ) : Set ℚ_[p] :=
  {z | ∃ y : ℤ, z = y ∧ x ≡ y [ZMOD p ^ k]}

/-- Congruence modulo `p ^ k` is equivalent to lying within p-adic distance `p ^ (-k)`. -/
theorem modeq_iff_padic_dist_le (p k : ℕ) [Fact p.Prime] (x y : ℤ) :
    x ≡ y [ZMOD p ^ k] ↔
      dist (x : ℚ_[p]) (y : ℚ_[p]) ≤ (p : ℝ) ^ (-k : ℤ) := by
  rw [Int.modEq_comm, Int.modEq_iff_dvd,
    ← Padic.norm_int_le_pow_iff_dvd (p := p) (k := x - y) (n := k)]
  simp only [dist_eq_norm, ← Int.cast_sub]

/-- A congruence fiber is a p-adic closed ball intersected with the embedded integers. -/
theorem congruenceFiber_eq_closedBall_inter_range (p k : ℕ) [Fact p.Prime] (x : ℤ) :
    congruenceFiber p k x =
      Metric.closedBall (x : ℚ_[p]) ((p : ℝ) ^ (-k : ℤ)) ∩
        Set.range ((↑) : ℤ → ℚ_[p]) := by
  ext z
  simp only [congruenceFiber, Set.mem_setOf_eq, Set.mem_inter_iff,
    Metric.mem_closedBall, Set.mem_range]
  constructor
  · rintro ⟨y, rfl, hxy⟩
    refine ⟨?_, ⟨y, rfl⟩⟩
    simpa only [dist_comm] using (modeq_iff_padic_dist_le p k x y).mp hxy
  · rintro ⟨hy, ⟨y, rfl⟩⟩
    refine ⟨y, rfl, (modeq_iff_padic_dist_le p k x y).mpr ?_⟩
    simpa only [dist_comm] using hy

example :
    dist ((1 : ℤ) : ℚ_[2]) ((9 : ℤ) : ℚ_[2]) ≤ (2 : ℝ) ^ (-(3 : ℤ)) := by
  exact (modeq_iff_padic_dist_le 2 3 1 9).mp (by decide)

#print axioms modeq_iff_padic_dist_le

end D5.S3.Arith.Congruence.PadicBallFiberCorrespondence
