---
bibkey: miyahara2026scalarcomposition
authors: Miyahara Kō
year: 2026
title: Scalar power series and formal multilinear composition
doi: null
url: https://github.com/Komyyy/ado/blob/acac59b08bfc356fdf5f3966ad95ad8edf7a3202/AdoArchive/Log.lean
claim: Scalar realization commutes with substitution into a series with nilpotent constant coefficient.
strata_touched:
  - D5/S3/Analytic/PowerSeries/ScalarComposition
license: Apache-2.0
triage: anchor
---

## Verified locator

https://github.com/Komyyy/ado/blob/acac59b08bfc356fdf5f3966ad95ad8edf7a3202/AdoArchive/Log.lean

The retained source declarations are `PowerSeries.toFMS`, `toFMS_apply`, and
`toFMS_subst`. The scalar field, possibly noncommutative target ring algebra,
topology, and topological-ring hypotheses are preserved. `subst P Q` denotes
the outer series Q evaluated at the inner series P; `HasSubst` is required of P.

## Attribution and license

Copyright (c) 2026 Miyahara Kō. All rights reserved.
Authors: Miyahara Kō. Released under Apache 2.0.
The complete upstream license is retained in
`docs/reports/licenses/ado-log-LICENSE.txt`.

Modification notice: the leaf retains only the three declarations above.
Its ordered-product step instantiates the host `List.foldr_hom₂` and
`mul_smul_mul_comm` inside the composition proof. The source's two list-product
declarations and the remaining logarithm development are omitted.

The source uses Lean v4.36.0-rc2 and mathlib
`df6966d0d900bebfbed7dff2a86a91e60eb8f3a9`.
The leaf uses this repository's toolchain and imports.
Retire it when this repository's own mathlib pin supplies an equivalent
correspondence and every consumer can directly use that supplier.

## Mathematical scope

The proof removes zero-sized blocks using the inner constant-coefficient
condition, reduces the coefficient sum to finitely many positive block
partitions, identifies these partitions with compositions of the degree,
and preserves the order of the target-ring product when flattening blocks.
It asserts a formal coefficient identity, without an analytic convergence
or inverse-branch assertion.
