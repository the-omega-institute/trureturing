/- GID: D5/S0/Asymptotics/GeneratingFunctions/KotesovecA092484
   generality: I
   mirror-B: D5/B/S0/Asymptotics/GeneratingFunctions/KotesovecA092484
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Weighted distinct-partition coefficients satisfy Kotesovec's logarithmic limit. -/

/-
admission_basis: open-problem-resolution (#21435; Proved).
proof_shape: result = bind-only; specialization of all_exponents.
escape_witness: none.
Direct frozen dependencies: none; A022629 is part of this delivery.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21754.
-/

import D5.S0.Asymptotics.GeneratingFunctions.KotesovecA022629

namespace D5.S0.Asymptotics.GeneratingFunctions.KotesovecA092484

open scoped BigOperators

/-- The degree-n coefficient of the source's locally finite product. -/
noncomputable def a (n : ℕ) : ℕ :=
  (∏ k ∈ Finset.Icc 1 n,
    (1 + Polynomial.C (k ^ 2) * Polynomial.X ^ k : Polynomial ℕ)).coeff n

/-- The OEIS conjecture; the limit is along all natural indices. -/
def claim : Prop :=
  Filter.Tendsto
    (fun n : ℕ => Real.log (a n : ℝ) / (Real.sqrt (2 * (n : ℝ)) * (Real.log (2 * (n : ℝ)) - 2)))
    Filter.atTop (nhds (1 : ℝ))

theorem result : claim := by
  have h := D5.S0.Asymptotics.GeneratingFunctions.KotesovecA022629.all_exponents 2 (by norm_num)
  have hs (n : ℕ) : (2 : ℝ) * Real.sqrt ((n : ℝ) / 2) = Real.sqrt (2 * (n : ℝ)) := by
    have h1 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2)
    have h2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * n)
    have h3 := Real.sqrt_nonneg ((n : ℝ) / 2)
    have h4 := Real.sqrt_nonneg (2 * (n : ℝ))
    nlinarith
  simpa only [claim, a, Nat.cast_ofNat, hs] using h


end D5.S0.Asymptotics.GeneratingFunctions.KotesovecA092484
