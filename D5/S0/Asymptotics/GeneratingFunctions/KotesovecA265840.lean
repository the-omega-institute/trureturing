/- GID: D5/S0/Asymptotics/GeneratingFunctions/KotesovecA265840
   generality: I
   mirror-B: D5/B/S0/Asymptotics/GeneratingFunctions/KotesovecA265840
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Weighted distinct-partition coefficients satisfy Kotesovec's logarithmic limit. -/

/-
admission_basis: open-problem-resolution (#21436; Proved).
proof_shape: result = bind-only; specialization of all_exponents.
escape_witness: none.
Direct frozen dependencies: none; A022629 is part of this delivery.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21754.
-/

import D5.S0.Asymptotics.GeneratingFunctions.KotesovecA022629

namespace D5.S0.Asymptotics.GeneratingFunctions.KotesovecA265840

open scoped BigOperators

/-- The degree-n coefficient of the source's locally finite product. -/
noncomputable def a (n : ℕ) : ℕ :=
  (∏ k ∈ Finset.Icc 1 n,
    (1 + Polynomial.C (k ^ 3) * Polynomial.X ^ k : Polynomial ℕ)).coeff n

/-- The OEIS conjecture; the limit is along all natural indices. -/
def claim : Prop :=
  Filter.Tendsto
    (fun n : ℕ => Real.log (a n : ℝ) / (3 * Real.sqrt ((n : ℝ) / 2) * (Real.log (2 * (n : ℝ)) - 2)))
    Filter.atTop (nhds (1 : ℝ))

theorem result : claim := by
  simpa only [claim, a, Nat.cast_ofNat] using
    D5.S0.Asymptotics.GeneratingFunctions.KotesovecA022629.all_exponents 3 (by norm_num)


end D5.S0.Asymptotics.GeneratingFunctions.KotesovecA265840
