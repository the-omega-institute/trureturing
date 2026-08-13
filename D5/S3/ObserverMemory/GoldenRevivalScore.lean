/- GID: D5/S3/ObserverMemory/GoldenRevivalScore
   generality: I
   mirror-B: D5/B/S3/ObserverMemory/GoldenRevivalScore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fibonacci golden revival scores converge to one over square root five. -/

/- Library-search audit trail (2026-08-13):
   * Exact local hit: `D5.S1.Scale.fibonacci_golden_residual` identifies the
     signed Fibonacci return error with a contracting golden power.
   * Exact pinned-mathlib hits: `Real.coe_fib_eq` supplies Binet's formula and
     `tendsto_pow_atTop_nhds_zero_of_abs_lt_one` supplies geometric decay.
   * Searches for the scaled score limit and a golden revival-score theorem
     found no exact hit in pinned Mathlib or D5.
   * This theorem closes only the Fibonacci return-time limit; no full
     Lagrange-Markov spectrum classification or global optimality is asserted.
-/

import D5.S1.Scale.FibonacciErrorRatio

namespace D5.S3.ObserverMemory.GoldenRevivalScore

open Filter Topology

private theorem fibonacci_revival_score_eq (n : Nat) :
    (Nat.fib n : Real) *
        |(Nat.fib n : Real) * Real.goldenRatio - Nat.fib (n + 1)| =
      (1 - (-Real.goldenConj ^ 2) ^ n) / Real.sqrt 5 := by
  rw [D5.S1.Scale.fibonacci_golden_residual, abs_neg, abs_pow]
  have hphi : 0 < Real.goldenRatio := Real.goldenRatio_pos
  rw [abs_div, abs_neg, abs_one, abs_of_pos hphi, one_div,
    Real.inv_goldenRatio, Real.coe_fib_eq]
  calc
    (Real.goldenRatio ^ n - Real.goldenConj ^ n) / Real.sqrt 5 *
          (-Real.goldenConj) ^ n =
        ((Real.goldenRatio * -Real.goldenConj) ^ n -
          (Real.goldenConj * -Real.goldenConj) ^ n) / Real.sqrt 5 := by
            rw [mul_pow, mul_pow]
            ring
    _ = (1 - (-Real.goldenConj ^ 2) ^ n) / Real.sqrt 5 := by
            rw [show Real.goldenRatio * -Real.goldenConj = 1 by
              rw [mul_neg, Real.goldenRatio_mul_goldenConj]
              norm_num]
            ring_nf

/-- Along Fibonacci return times, the scaled golden return error tends to the
sharp quadratic-irrational constant `1 / sqrt 5`. -/
theorem golden_fibonacci_revival_score_tendsto :
    Tendsto
      (fun n : Nat =>
        (Nat.fib n : Real) *
          |(Nat.fib n : Real) * Real.goldenRatio - Nat.fib (n + 1)|)
      atTop (nhds (1 / Real.sqrt 5)) := by
  have hpos : 0 < -Real.goldenConj := neg_pos.mpr Real.goldenConj_neg
  have hlt : -Real.goldenConj < 1 := by
    linarith [Real.neg_one_lt_goldenConj]
  have hbase : |-Real.goldenConj ^ 2| < 1 := by
    rw [abs_neg, abs_pow, abs_of_neg Real.goldenConj_neg]
    nlinarith
  have hpow := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hbase
  have hone : Tendsto (fun _ : Nat => (1 : Real)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hclosed :
      Tendsto (fun n : Nat =>
        (1 - (-Real.goldenConj ^ 2) ^ n) / Real.sqrt 5)
        atTop (nhds (1 / Real.sqrt 5)) := by
    simpa only [sub_zero] using (hone.sub hpow).div_const (Real.sqrt 5)
  exact hclosed.congr' (Filter.Eventually.of_forall fun n =>
    (fibonacci_revival_score_eq n).symm)

/-- The return-time index domain is inhabited. -/
example : Nonempty Nat := ⟨1⟩

end D5.S3.ObserverMemory.GoldenRevivalScore
