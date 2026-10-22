/- GID: D5/S3/Analytic/MeijerZeroCount/Mellin
   generality: G
   mirror-B: D5/B/S3/Analytic/MeijerZeroCount/Mellin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Gamma.Beta, mathlib/module/Mathlib.Analysis.SpecialFunctions.ImproperIntegrals]
   utility: none
   digest: Mellin inversion identifies the Gamma quotient with its Rodrigues kernel. -/

import D5.S3.Analytic.MeijerZeroCount.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
open Complex MeasureTheory Set
open scoped BigOperators
namespace D5.S3.Analytic.MeijerZeroCount.Mellin
open Defs
set_option maxHeartbeats 800000

theorem gammaQuot_pochhammer (n d : ℕ) (c : ℝ) (s : ℂ)
    (hc : 0 < c) (hs : 0 < s.re) :
    gammaQuot ![(n : ℝ) + c, (n : ℝ) + c] ![c, (2 * n + d : ℕ) + c] s =
      (ascPochhammer ℂ n).eval (s + c) /
        (ascPochhammer ℂ (n + d)).eval (s + c + n) := by
  have hz : 0 < (s + (c : ℂ)).re := by simpa using add_pos hs hc
  have hzn : 0 < (s + (c : ℂ) + n).re := by
    simpa using add_pos_of_pos_of_nonneg hz (Nat.cast_nonneg n)
  have hg := Complex.Gamma_ne_zero_of_re_pos hz
  have hgn := Complex.Gamma_ne_zero_of_re_pos hzn
  have havoid (z : ℂ) (hz : 0 < z.re) : ∀ k : ℕ, z ≠ -k := by
    intro k hk
    have := congrArg Complex.re hk
    simp only [Complex.neg_re, Complex.natCast_re] at this
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  rw [← Complex.Gamma_add_nat_div_Gamma_eq _ (havoid _ hz),
    ← Complex.Gamma_add_nat_div_Gamma_eq _ (havoid _ hzn)]
  simp only [gammaQuot, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  push_cast
  have e₁ : (n : ℂ) + c + s = s + c + n := by ring
  have e₂ : 2 * (n : ℂ) + d + c + s = s + c + n + (n + d) := by ring
  rw [e₁, e₂, show (c : ℂ) + s = s + c by ring]
  field_simp

end D5.S3.Analytic.MeijerZeroCount.Mellin
