/- GID: D5/S1/Recurrence/Invariants/DivisorPairProductPrimePreimages
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/DivisorPairProductPrimePreimages
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [Mathlib.NumberTheory.ArithmeticFunction.Misc, Mathlib.Data.Finset.NatDivisors, Mathlib.Data.Nat.Factorization.PrimePow, Mathlib.Data.Nat.Squarefree, Mathlib.RingTheory.MvPolynomial.Symmetric.Defs, Mathlib.Algebra.Ring.GeomSum]
   utility: none
   digest: A prime divisor-pair product sum of a composite has exactly its composite and prime preimages. -/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Squarefree
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Invariants.DivisorPairProductPrimePreimages

open scoped ArithmeticFunction.sigma

/-- The second elementary symmetric function of the positive divisors of `n` (OEIS A119616). -/
noncomputable def S2 (n : ℕ) : ℕ :=
  n.divisors.val.esymm 2

end D5.S1.Recurrence.Invariants.DivisorPairProductPrimePreimages
