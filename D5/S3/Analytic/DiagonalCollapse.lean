/- GID: D5/S3/Analytic/DiagonalCollapse
   generality: I
   mirror-B: D5/B/S3/Analytic/DiagonalCollapse
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The two-face generating function collapses on the diagonal to a geometric series. -/

import D5.S0.Conventions.WDigits
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/- Provenance: pinned mathlib supplies the canonical-word equivalence
   (`Nat.zeckendorfEquiv`), Binet's formula (`Real.coe_fib_eq`), and the
   geometric-series sum (`tsum_geometric_of_lt_one`).  The proof composes
   these declarations for the diagonal two-face weight. -/

namespace D5.S3.Analytic.DiagonalCollapse

open D5.S0.Conventions

private theorem face_gap_eq_sqrt_five_mul_fib (k : ℕ) :
    Real.goldenRatio ^ k - Real.goldenConj ^ k =
      Real.sqrt 5 * (Nat.fib k : ℝ) := by
  rw [Real.coe_fib_eq]
  field_simp

private theorem word_face_gap (digits : List ℕ) :
    (digits.map fun k => Real.goldenRatio ^ k - Real.goldenConj ^ k).sum =
      Real.sqrt 5 * ((digits.map Nat.fib).sum : ℝ) := by
  induction digits with
  | nil => simp
  | cons k digits ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [face_gap_eq_sqrt_five_mul_fib, ih, Nat.cast_add]
      ring

/-- On a positive diagonal parameter, the generating function over canonical
nonadjacent Fibonacci words is the geometric series with ratio
`exp (-sqrt 5 * x)`. -/
theorem diagonal_partition_collapse (x : ℝ) (hx : 0 < x) :
    (∑' digits : WDigitString,
        Real.exp
          (-x *
            (digits.1.map fun k =>
              Real.goldenRatio ^ k - Real.goldenConj ^ k).sum)) =
      1 / (1 - Real.exp (-Real.sqrt 5 * x)) := by
  calc
    _ = ∑' digits : WDigitString,
        Real.exp
          (-Real.sqrt 5 * x * ((digits.1.map Nat.fib).sum : ℝ)) := by
      apply tsum_congr
      intro digits
      rw [word_face_gap]
      congr 1
      ring
    _ = ∑' n : ℕ, Real.exp (-Real.sqrt 5 * x * (n : ℝ)) := by
      rw [← wEncoding.tsum_eq]
      apply tsum_congr
      intro n
      change
        Real.exp
            (-Real.sqrt 5 * x * (((Nat.zeckendorf n).map Nat.fib).sum : ℝ)) =
          Real.exp (-Real.sqrt 5 * x * (n : ℝ))
      rw [Nat.sum_zeckendorf_fib]
    _ = ∑' n : ℕ, (Real.exp (-Real.sqrt 5 * x)) ^ n := by
      apply tsum_congr
      intro n
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ = (1 - Real.exp (-Real.sqrt 5 * x))⁻¹ := by
      apply tsum_geometric_of_lt_one (Real.exp_nonneg _)
      rw [Real.exp_lt_one_iff]
      have hsqrt : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
      nlinarith [mul_pos hsqrt hx]
    _ = 1 / (1 - Real.exp (-Real.sqrt 5 * x)) := by
      rw [one_div]

end D5.S3.Analytic.DiagonalCollapse
