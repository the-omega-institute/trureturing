---
bibkey: mathlib2026finitedivisorzeros
authors: Mathlib contributors
year: 2026
title: Finite geometric sums and complex exponential roots in Mathlib
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Algebra/Field/GeomSum.lean
claim: The finite geometric sum equals the quotient of the difference of powers by the difference of bases; complex exponential periodicity identifies its nontrivial roots.
strata_touched:
  - D5/S3/Arith/GoldenResource/FiniteDivisorPartitionZeros
license: Apache-2.0
triage: anchor
---

# Finite geometric factors

## Verified locator

- URL: https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Algebra/Field/GeomSum.lean

The pinned source supplies `geom_sum_eq` for a ratio different from one.
The same revision's `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean`
supplies `Complex.exp_eq_one_iff`, which describes the integer multiples
of two pi i. `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` supplies
`Complex.norm_natCast_cpow_of_pos` and `Real.rpow_right_inj`.

The repository combines these classical identities for a prime base and a
finite exponent range. It reuses the existing local exponential lattice
in `EulerProduct.finite_euler_denominator_eq_zero_iff`, identifies the
excluded integer multiples of the range length, and then proves
nonvanishing for the finite product. The cited upstream file does not
define the repository's finite divisor partition function.
