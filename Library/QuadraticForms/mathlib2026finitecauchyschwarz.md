---
bibkey: mathlib2026finitecauchyschwarz
authors: Mathlib contributors
year: 2026
title: Finite Cauchy-Schwarz inequality in ordered commutative semirings
doi: null
url: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean
claim: For functions f and g over a finset s in a linearly ordered commutative semiring with IsStrictOrderedRing and ExistsAddOfLE, the finite Cauchy-Schwarz inequality $(\sum_{i \in s} f_i g_i)^2 \le (\sum_{i \in s} f_i^2)(\sum_{i \in s} g_i^2)$ holds.
strata_touched:
  - D5/S3/Combinatorics/Orthogonality/ThetaRepresentationNonconvex
license: Apache-2.0
triage: anchor
---

# Finite Cauchy-Schwarz inequality

The declaration `Finset.sum_mul_sq_le_sq_mul_sq` states the squared finite
Cauchy-Schwarz inequality. Its declaration and proof are quoted verbatim:

```lean
lemma sum_mul_sq_le_sq_mul_sq [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]
    [ExistsAddOfLE R] (s : Finset ι)
    (f g : ι → R) : (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2 :=
  sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun _ _ ↦ sq_nonneg _) (fun _ _ ↦ sq_nonneg _) (fun _ _ ↦ (mul_pow ..).le)
```

The declaration is in namespace `Finset`, with implicit type parameters
`{ι R : Type*}`. For real vectors on a finite type, take `s = Finset.univ`.
Expanding `dotProduct` and normalizing squares gives the statement of
`ThetaRepresentationNonconvex.dot_cauchy` directly.

## Verified locator

The upstream source is
https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean
at `Finset.sum_mul_sq_le_sq_mul_sq`, line 171 (declaration and proof on
lines 171–175), commit `56a005855ea17e0b0958f73ec801ae140b0a1679`.
The file is `Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean`.

The upstream file carries this license notice:

```text
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
```
