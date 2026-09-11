---
bibkey: cipollina2026growth
authors: Matteo Cipollina; Stefan Kebekus; Chris Hughes; Abhimanyu Pallavi Sudhir; Jean Lo; Calle Sönne
year: 2026
title: Real logarithmic and exponential growth comparisons and epsilon-family entire order
doi: null
url: https://github.com/or4nge19/mathlib4/tree/84f82618a724f6ba559475094a1184fb323c6346
claim: Real logarithmic and exponential norm growth bounds convert in both directions, quadratic factors are absorbed by positive real powers in an exponential, and entire order is expressed by an epsilon family of uniform bounds.
strata_touched:
  - D5/S3/Analytic/EntireGrowth/RealExponential
license: Apache-2.0
triage: anchor
---

# Real exponential growth

The source is a root mathlib fork at the immutable revision in the locator.
The selected statements are general real inequalities, norm estimates for arbitrary
seminormed groups and radius functions, and the epsilon-family entire-order predicate.
The predicate includes differentiability and a positive constant for every positive
epsilon, uniformly over all complex arguments. No equivalence with an infimum or
limsup definition of order is asserted here.

## Verified locator

https://github.com/or4nge19/mathlib4/tree/84f82618a724f6ba559475094a1184fb323c6346

The exact original paths, relative to that revision, are:

- `Mathlib/Analysis/SpecialFunctions/Log/PosLog.lean`
- `Mathlib/Analysis/SpecialFunctions/Exp.lean`
- `Mathlib/Analysis/SpecialFunctions/Log/ExpGrowth.lean`
- `Mathlib/Analysis/Complex/HadamardFactorization/Order.lean`

The source toolchain is Lean 4.29.0-rc8. The local extraction uses Lean 4.33.0
and mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`, without adding the fork
as a Lake dependency. Original-source declaration types and source-file SHA-256
identities are retained in `docs/reports/realexponential/source-record.json`.

## Attribution and modifications

PosLog carries copyright 2025 Stefan Kebekus and authorship Stefan Kebekus.
Exp carries copyright 2018 Chris Hughes and authorship Chris Hughes, Abhimanyu
Pallavi Sudhir, Jean Lo, and Calle Sönne. ExpGrowth and Order carry copyright
2026 Matteo Cipollina and authorship Matteo Cipollina. All these author chains
are preserved in the production source. The Apache 2.0 license text is retained
verbatim at `docs/reports/realexponential/LICENSE.txt`; the fixed fork root has
no NOTICE file.

This is a selected-source extraction. The namespace becomes
`D5.S3.Analytic.EntireGrowth.RealExponential`; imports target the local pinned
Mathlib, and ordinary repository source syntax replaces module/public syntax.
The quadratic estimate uses the pinned `Real.log_le_rpow_div` for the same
intermediate logarithmic bound. Other selected proof bodies retain the source
arguments, with namespace qualification adjusted. No mathematical novelty is claimed.

## Declaration correspondence

Each name below retains its original binders and conclusion, modulo the
namespace substitution. The full type echo is in the source record.

| Original source | Original declaration |
| --- | --- |
| PosLog | `Real.log_one_add_exp_le_add_log_two` |
| PosLog | `Real.log_one_add_le_add_log_two_of_le_exp` |
| PosLog | `Real.le_exp_of_log_one_add_le` |
| Exp | `Real.le_exp_self` |
| ExpGrowth | `Real.log_norm_le_log_one_add_norm` |
| ExpGrowth | `Real.log_nonneg_mul_inv_norm_of_norm_le` |
| ExpGrowth | `Real.log_two_le_log_two_mul_mul_inv_norm_of_norm_le` |
| ExpGrowth | `Real.norm_le_exp_mul_rpow_of_exponent_le` |
| ExpGrowth | `Real.norm_le_exp_mul_rpow_of_log_growth` |
| ExpGrowth | `Real.log_growth_of_norm_le_exp_mul_rpow` |
| ExpGrowth | `Real.exists_norm_le_exp_mul_pow_of_rpow_bound` |
| ExpGrowth | `Real.sq_le_exp_const_mul_rpow` |
| ExpGrowth | `Real.one_add_le_three_mul_one_add_of_le_two_mul_max` |
| ExpGrowth | `Real.exp_mul_rpow_le_exp_mul_rpow_of_le_mul` |
| ExpGrowth | `Real.exists_between_self_and_floor_add_one_same_floor` |
| ExpGrowth | `Real.log_norm_le_of_log_one_add_growth_on_sphere` |
| Order | `Complex.Hadamard.EntireOfOrderAtMost` |
| Order | `Complex.Hadamard.EntireOfOrderAtMost.differentiable` |
| Order | `Complex.Hadamard.EntireOfOrderAtMost.exists_bound` |

## Mathematical uses and replacement condition

Quadratic absorption supplies the polynomial factor estimate in the xi order-one
argument. The logarithmic conversion supplies finite-order zero counting and the
degree bound for an exponential of a polynomial. Radius comparisons and the
floor-preserving exponent supply the general Hadamard growth argument. The entire
order definition and its projections are companions to these estimates.

If this repository's own pinned Mathlib supplies equivalent declarations, consumers
must use those declarations directly. Any retirement of this extraction follows
the repository's frozen-source rules; it is not triggered by an unmerged upstream PR.
