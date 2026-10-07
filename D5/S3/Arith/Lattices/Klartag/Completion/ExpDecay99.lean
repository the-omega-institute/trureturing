/- GID: D5/S3/Arith/Lattices/Klartag/Completion/ExpDecay99
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/ExpDecay99
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import Mathlib

set_option linter.unusedSectionVars false

namespace D5.S3.Arith.Lattices.Klartag.Completion.ExpDecay99

/-- **`(x/20)^20 ≤ exp x`** for `x ≥ 0`.  `Real.add_one_le_exp` at `x/20`, then `pow_le_pow_left₀`;
`exp x = (exp (x/20))^20` is `Real.exp_nat_mul`. -/
theorem pow_div_le_exp {x : ℝ} (hx : 0 ≤ x) : (x / 20) ^ 20 ≤ Real.exp x := by
  have hstep : x / 20 ≤ Real.exp (x / 20) := by
    have h := Real.add_one_le_exp (x / 20)
    linarith
  have h20 : Real.exp x = Real.exp (x / 20) ^ 20 := by
    rw [← Real.exp_nat_mul]
    push_cast
    ring_nf
  rw [h20]
  exact pow_le_pow_left₀ (by positivity) hstep 20

/-- **`e^{-x} ≤ 20²⁰/x²⁰`** for `x > 0` — the decay `FailTotalBound99` consumes. -/
theorem exp_neg_le {x : ℝ} (hx : 0 < x) : Real.exp (-x) ≤ 20 ^ 20 / x ^ 20 := by
  have hxp : (0 : ℝ) < x ^ 20 := by positivity
  have hex : (0 : ℝ) < Real.exp x := Real.exp_pos x
  have hbase : x ^ 20 / 20 ^ 20 ≤ Real.exp x := by
    have h := pow_div_le_exp hx.le
    rwa [div_pow] at h
  have hkey : x ^ 20 ≤ 20 ^ 20 * Real.exp x := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 20 ^ 20)] at hbase
    linarith
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ hex hxp]
  linarith

/-- **The form the failure bound uses**: at a natural `n ≥ 1`. -/
theorem exp_neg_nat_le {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-(n : ℝ)) ≤ 20 ^ 20 / (n : ℝ) ^ 20 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact exp_neg_le hn0

end D5.S3.Arith.Lattices.Klartag.Completion.ExpDecay99
