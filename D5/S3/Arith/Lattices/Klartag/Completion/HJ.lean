/- GID: D5/S3/Arith/Lattices/Klartag/Completion/HJ
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Completion/HJ
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform constants and completion of lattice packing. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Contact.ProfileBound8

open D5.S3.Arith.Lattices.Klartag.Construction
open D5.S3.Arith.Lattices.Klartag.Walk

namespace D5.S3.Arith.Lattices.Klartag

open Real

/-- `Real.log_le_rpow_div` at `ε = 1/6`. -/
theorem log_le_six_rpow {n : ℕ} : Real.log n ≤ 6 * (n : ℝ) ^ ((1 : ℝ) / 6) := by
  have h := Real.log_le_rpow_div (x := (n : ℝ)) (Nat.cast_nonneg n) (by norm_num : (0:ℝ) < 1/6)
  calc Real.log n ≤ (n : ℝ) ^ ((1 : ℝ) / 6) / (1 / 6) := h
    _ = 6 * (n : ℝ) ^ ((1 : ℝ) / 6) := by ring

/-- `(log n)³ ≤ 216·√n`.  Cubing `log n ≤ 6·n^{1/6}` and `(n^{1/6})³ = n^{1/2} = √n`. -/
theorem log_cube_le {n : ℕ} (hn : 1 ≤ n) : (Real.log n) ^ 3 ≤ 216 * Real.sqrt n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog0 : (0 : ℝ) ≤ Real.log n := Real.log_nonneg hn1
  have hrp0 : (0 : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / 6) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hcube : ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 3 = Real.sqrt n := by
    rw [← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / 6)) 3, ← Real.rpow_mul (Nat.cast_nonneg n),
      Real.sqrt_eq_rpow]
    norm_num
  calc (Real.log n) ^ 3 ≤ (6 * (n : ℝ) ^ ((1 : ℝ) / 6)) ^ 3 :=
        pow_le_pow_left₀ hlog0 log_le_six_rpow 3
    _ = 216 * ((n : ℝ) ^ ((1 : ℝ) / 6)) ^ 3 := by ring
    _ = 216 * Real.sqrt n := by rw [hcube]

end D5.S3.Arith.Lattices.Klartag
