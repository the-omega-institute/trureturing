/- GID: D5/S3/Arith/FibonacciAtomic/MovingRootDisplacement
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/MovingRootDisplacement
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Uniform finite-product remainders and additive displacement of Fibonacci density roots. -/

import D5.S3.Arith.FibonacciAtomic.SourceDensityCrossing
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Arith.FibonacciAtomic.MovingRootDisplacement

open scoped BigOperators Topology
open Filter Set SourceDensityMonotonicity

/-- Cassini correction to the first moment. -/
noncomputable def kappa (k : ℕ) : ℝ := 1 / ((L k : ℝ) * A k * D k)

/-- Bounded part of the additive displacement. -/
noncomputable def sigma (k : ℕ) : ℝ :=
  (D k : ℝ) / L k + (E k : ℝ) / (2 * A k) + (A k : ℝ) / (2 * D k)

/-- First moment of the three normalized finite-product blocks. -/
noncomputable def B (k j : ℕ) : ℝ := sigma k + kappa k * ((j : ℝ) + 1 / 2)

private theorem log_error (x : ℝ) (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x) - x| ≤ x ^ 2 := by
  have hp : 0 < 1 + x := by have := (abs_le.mp hx).1; linarith
  have hc := Complex.norm_log_one_add_sub_self_le (z := (x : ℂ))
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hx.trans_lt (by norm_num))
  have he : Complex.log (1 + (x : ℂ)) - (x : ℂ) =
      ((Real.log (1 + x) - x : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub, Complex.ofReal_log hp.le]
    push_cast
    rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs,
    sq_abs] at hc
  have hi : (1 - |x|)⁻¹ ≤ (2 : ℝ) := by
    apply (inv_le_comm₀ (by linarith : 0 < 1 - |x|) (by norm_num)).mpr
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hi (sq_nonneg x)]

end D5.S3.Arith.FibonacciAtomic.MovingRootDisplacement
