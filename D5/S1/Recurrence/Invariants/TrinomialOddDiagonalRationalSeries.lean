/- GID: D5/S1/Recurrence/Invariants/TrinomialOddDiagonalRationalSeries
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/TrinomialOddDiagonalRationalSeries
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [Mathlib.Algebra.Polynomial.Coeff, Mathlib.RingTheory.PowerSeries.Inverse]
   utility: none
   digest: Odd trinomial diagonals have Schulte's rational generating series. -/

import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.RingTheory.PowerSeries.Inverse

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S1.Recurrence.Invariants.TrinomialOddDiagonalRationalSeries

open Finset

/-- The `r`-th coefficient in row `m` of OEIS A027907. -/
def trinomial (m r : Nat) : Rat :=
  Polynomial.coeff ((1 + Polynomial.X + Polynomial.X ^ 2) ^ m) r

/-- Werner Schulte's odd diagonal sum in the trinomial triangle. -/
def diagonal (n : Nat) : Rat :=
  ∑ j ∈ range (n / 2 + 1), trinomial (n + 1 - j) (2 * j + 1)

/-- The rational generating function defining OEIS A077864. -/
def generatingSeries : PowerSeries Rat :=
  ((1 - PowerSeries.X) *
    (1 - PowerSeries.X - 2 * PowerSeries.X ^ 2 - PowerSeries.X ^ 3))⁻¹

/-- The `n`-th coefficient of OEIS A077864. -/
def a (n : Nat) : Rat :=
  PowerSeries.coeff n generatingSeries

end D5.S1.Recurrence.Invariants.TrinomialOddDiagonalRationalSeries
