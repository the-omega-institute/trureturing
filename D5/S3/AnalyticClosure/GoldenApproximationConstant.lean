/- GID: D5/S3/AnalyticClosure/GoldenApproximationConstant
   generality: I
   mirror-B: D5/B/S3/AnalyticClosure/GoldenApproximationConstant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fibonacci approximation errors converge to the reciprocal square-root-five constant. -/

/- Library-search audit trail (2026-08-14):
   * Exact local hit: `golden_fibonacci_revival_score_tendsto` proves the
     equivalent scaled residual limit before division by the denominator.
   * Pinned-library hits behind that result are `Real.coe_fib_eq` and
     `tendsto_pow_atTop_nhds_zero_of_abs_lt_one`.
   * Searches for the quotient-form scaled approximation limit found no exact
     hit in the pinned library or the local formal modules.
-/

import D5.S3.ObserverMemory.GoldenRevivalScore

namespace D5.S3.AnalyticClosure.GoldenApproximationConstant

open Filter Topology

/-- The errors of the consecutive Fibonacci approximants to the golden ratio,
scaled by the squares of their denominators, converge to `1 / sqrt 5`. -/
theorem golden_fibonacci_approximation_constant_tendsto :
    Tendsto
      (fun n : Nat =>
        (Nat.fib n : Real) ^ 2 *
          |Real.goldenRatio -
            (Nat.fib (n + 1) : Real) / (Nat.fib n : Real)|)
      atTop (nhds (1 / Real.sqrt 5)) := by
  apply
    D5.S3.ObserverMemory.GoldenRevivalScore.golden_fibonacci_revival_score_tendsto.congr'
  filter_upwards [eventually_ge_atTop (1 : Nat)] with n hn
  have hposNat : 0 < Nat.fib n := Nat.fib_pos.mpr hn
  have hpos : (0 : Real) < Nat.fib n := by exact_mod_cast hposNat
  have hne : (Nat.fib n : Real) ≠ 0 := hpos.ne'
  have hquot :
      Real.goldenRatio - (Nat.fib (n + 1) : Real) / Nat.fib n =
        ((Nat.fib n : Real) * Real.goldenRatio - Nat.fib (n + 1)) / Nat.fib n := by
    field_simp
  rw [hquot, abs_div, abs_of_pos hpos, abs_sub_comm]
  field_simp [hne]

#print axioms golden_fibonacci_approximation_constant_tendsto

end D5.S3.AnalyticClosure.GoldenApproximationConstant
