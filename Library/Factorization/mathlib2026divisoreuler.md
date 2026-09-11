---
bibkey: mathlib2026divisoreuler
authors: Mathlib contributors
year: 2026
title: Multiplicative arithmetic functions and finite divisor sums in Mathlib
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean
claim: Multiplicative arithmetic functions factor over prime powers, and arithmetic zeta convolution is summation over divisors.
strata_touched:
  - D5/S3/Arith/DivisorGibbs/FiniteDivisorEulerProduct
license: Apache-2.0
triage: anchor
---

# Multiplicative divisor sums

The pinned library supplies `ArithmeticFunction.IsMultiplicative.multiplicative_factorization`
and `ArithmeticFunction.IsMultiplicative.mul`. Its `ArithmeticFunction/Zeta.lean` supplies
`coe_zeta_mul_apply`, while `NumberTheory/Divisors.lean` supplies
`Nat.sum_divisors_prime_pow`. Together these identify the divisor sum with its finite
Euler product.

`Analysis/SpecialFunctions/Pow/Complex.lean` supplies
`Complex.natCast_mul_natCast_cpow` and `Complex.natCast_cpow_natCast_mul`, including
zero complex exponent. `Topology/Algebra/InfiniteSum/Basic.lean` supplies `tsum_eq_sum`
for functions vanishing outside a finite set.

## Verified locator

- URL: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/NumberTheory/ArithmeticFunction/Defs.lean
