/- GID: D5/S3/ArithSums/BarryTriangleRowSumsOdd
   generality: I
   mirror-B: D5/B/S3/ArithSums/BarryTriangleRowSumsOdd
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Sum, mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Moebius]
   utility: none
   digest: OEIS A105595: every row sum of the A105594 triangle is odd. -/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ArithSums.BarryTriangleRowSumsOdd

/-- The entry `T(n, k)` from the formula in OEIS A105594. -/
def rowEntry (n k : ℕ) : ℕ :=
  (∑ j ∈ Finset.range (n + 1),
      Int.natAbs (ArithmeticFunction.moebius (Nat.choose n j)) *
        (Nat.choose j k % 2)) % 2

/-- The row sum `a(n)` from the formula in OEIS A105595. -/
def rowSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), rowEntry n k

end D5.S3.ArithSums.BarryTriangleRowSumsOdd
