/- GID: D5/S3/Analytic/MeijerZeroCount/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/MeijerZeroCount/Result
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic.FinCases]
   utility: none
   digest: The two-component Meijer family refutes the interior zero-count comparison. -/

import D5.S3.Analytic.MeijerZeroCount.Mellin
import D5.S3.Analytic.MeijerZeroCount.Control
import Mathlib.Tactic.FinCases
open Set
namespace D5.S3.Analytic.MeijerZeroCount.Result
open Defs Rodrigues Mellin Control

/-- The two-parameter family has n zeros of G and one zero of the control function. -/
theorem family (n d : ℕ) (c : ℝ) (hn : 2 ≤ n) (hd : 2 ≤ d) (hc : 0 < c) :
    {x : ℝ | x ∈ Set.Ioo 0 1 ∧
      meijerG ![(n : ℝ)+c, (n : ℝ)+c] ![c, ((2*n+d : ℕ) : ℝ)+c] x = 0}.encard = n ∧
    {x : ℝ | x ∈ Set.Ioo 0 1 ∧
      control ![(n : ℝ)+c, (n : ℝ)+c] ![c, ((2*n+d : ℕ) : ℝ)+c] x = 0}.encard = 1 := by
  constructor
  · have he : {x : ℝ | x ∈ Set.Ioo 0 1 ∧
        meijerG ![(n : ℝ)+c, (n : ℝ)+c] ![c, ((2*n+d : ℕ) : ℝ)+c] x = 0} =
        {x : ℝ | x ∈ Set.Ioo 0 1 ∧ f n d c x = 0} := by
      ext x
      apply and_congr_right
      intro hx
      rw [meijerG_eq_f n d c hd hc hx]
    rw [he]
    exact zeros_f n d c (by omega)
  · exact zeros_control n d c (by omega) (by omega)

/-- The zero-count comparison fails already for a=(3,3) and b=(1,7). -/
theorem result : ¬ claim := by
  intro h
  have hz := family 2 2 1 (by norm_num) (by norm_num) (by norm_num)
  have hh := h 2 ![(2 : ℝ)+1, (2 : ℝ)+1] ![1, ((2*2+2 : ℕ) : ℝ)+1]
    (by intro i; fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_two])
  norm_num at hz hh
  rw [hz.1, hz.2] at hh
  norm_num at hh

end D5.S3.Analytic.MeijerZeroCount.Result
