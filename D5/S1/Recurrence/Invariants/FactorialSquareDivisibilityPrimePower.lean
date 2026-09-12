/- GID: D5/S1/Recurrence/Invariants/FactorialSquareDivisibilityPrimePower
   generality: G
   mirror-B: D5/B/S1/Recurrence/Invariants/FactorialSquareDivisibilityPrimePower
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [Mathlib.Data.Nat.Choose.Multinomial, Mathlib.Data.Nat.Factorization.PrimePow, Mathlib.NumberTheory.Padics.PadicVal.Basic]
   utility: none
   digest: Prime-power exactness for factorial-square divisibility via prime valuations and base-p digits. -/

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.NumberTheory.Padics.PadicVal.Basic

#check Nat.Prime.emultiplicity_factorial
#check padicValNat_factorial
#check Nat.Prime.multiplicity_factorial_pow
#check Nat.factorization_factorial
#check Nat.Prime.pow_dvd_iff_le_factorization
#check isPrimePow_nat_iff
#check Nat.not_isPrimePow_iff_nontrivial_of_two_le
#check Nat.prod_factorial_dvd_factorial_sum
