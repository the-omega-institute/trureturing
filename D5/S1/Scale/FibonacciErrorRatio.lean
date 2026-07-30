/- GID: D5/S1/Scale/FibonacciErrorRatio
   generality: I
   mirror-B: D5/B/S1/Scale/FibonacciErrorRatio
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   digest: Fibonacci convergent errors have an exact golden residual and asymptotic ratio. -/

import D5.S1.Scale.FibonacciEigen
import Mathlib.Analysis.SpecificLimits.Fibonacci

namespace D5.S1.Scale

open Filter Topology

/-- The signed error of the Fibonacci convergent with denominator `F_(n+1)`. -/
noncomputable def fibonacciConvergentError (n : ℕ) : ℝ :=
  Real.goldenRatio -
    (Nat.fib (n + 2) : ℝ) / Nat.fib (n + 1)

/-- The exact signed residual of consecutive Fibonacci numbers at the golden ratio. -/
theorem fibonacci_golden_residual (n : ℕ) :
    (Nat.fib n : ℝ) * Real.goldenRatio - Nat.fib (n + 1) =
      -((-1 / Real.goldenRatio) ^ n) := by
  have hcontract : -1 / Real.goldenRatio = contractingEigenvalue := by
    rw [contractingEigenvalue]
    ring
  rw [hcontract]
  exact (fibonacci_substitution_spec n).2.2.2.2

private theorem fibonacci_convergent_error_eq (n : ℕ) :
    fibonacciConvergentError n =
      -((-1 / Real.goldenRatio) ^ (n + 1)) / Nat.fib (n + 1) := by
  have hfib : (Nat.fib (n + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.fib_pos.2 (Nat.succ_pos n)))
  rw [fibonacciConvergentError]
  calc
    Real.goldenRatio - (Nat.fib (n + 2) : ℝ) / Nat.fib (n + 1) =
        ((Nat.fib (n + 1) : ℝ) * Real.goldenRatio - Nat.fib (n + 2)) /
          Nat.fib (n + 1) := by
            field_simp
    _ = -((-1 / Real.goldenRatio) ^ (n + 1)) / Nat.fib (n + 1) := by
      rw [fibonacci_golden_residual]

/-- The adjacent absolute-error ratio reduces to a shifted Fibonacci ratio and one golden factor. -/
theorem fibonacci_convergent_error_ratio (n : ℕ) :
    |fibonacciConvergentError (n + 1)| / |fibonacciConvergentError n| =
      ((Nat.fib (n + 1) : ℝ) / Nat.fib (n + 2)) / Real.goldenRatio := by
  rw [fibonacci_convergent_error_eq, fibonacci_convergent_error_eq]
  have hphi : 0 < Real.goldenRatio := Real.goldenRatio_pos
  have hfib1 : 0 < (Nat.fib (n + 1) : ℝ) := by
    exact_mod_cast (Nat.fib_pos.2 (Nat.succ_pos n))
  have hfib2 : 0 < (Nat.fib (n + 2) : ℝ) := by
    exact_mod_cast (Nat.fib_pos.2 (by omega : 0 < n + 2))
  rw [abs_div, abs_div, abs_neg, abs_neg, abs_pow, abs_pow,
    abs_of_pos hfib1, abs_of_pos hfib2]
  have hbase : |-1 / Real.goldenRatio| = 1 / Real.goldenRatio := by
    rw [abs_div, abs_neg, abs_one, abs_of_pos hphi]
  rw [hbase, pow_succ]
  field_simp [hphi.ne']

/-- Adjacent absolute errors of Fibonacci convergents have limiting ratio `1 / phi^2`. -/
theorem fibonacci_convergent_error_ratio_tendsto :
    Tendsto
      (fun n : ℕ =>
        |fibonacciConvergentError (n + 1)| / |fibonacciConvergentError n|)
      atTop
      (nhds (1 / Real.goldenRatio ^ 2)) := by
  have hratio :=
    tendsto_fib_div_fib_succ_atTop.comp (tendsto_add_atTop_nat 1)
  have hscaled := hratio.div_const Real.goldenRatio
  have hlimit :
      (-Real.goldenConj) / Real.goldenRatio = 1 / Real.goldenRatio ^ 2 := by
    rw [← Real.inv_goldenRatio]
    simp [div_eq_mul_inv, pow_two]
  rw [← hlimit]
  simpa only [fibonacci_convergent_error_ratio, Function.comp_apply, Nat.add_assoc]
    using hscaled

end D5.S1.Scale
