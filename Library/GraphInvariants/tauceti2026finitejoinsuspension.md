---
bibkey: tauceti2026finitejoinsuspension
authors: The Tau Ceti contributors
year: 2026
title: Finite barycentric polyhedra and precomplex joins in TauCeti
doi: null
url: https://github.com/TauCetiProject/TauCeti/tree/64bb4d871548995899dee90beda88b787fafe27d
claim: Standard simplex membership is nonnegative coordinates of total mass one with support in its vertex set; onFinsupp polyhedron membership requires the true support to be a face, and joins permit empty projections with nonempty total support.
strata_touched:
  - D5/S3/GraphInvariants/Simplicial/FiniteJoinSuspension
license: Apache-2.0
triage: anchor
---

# Finite polyhedron coordinates and joins

## Verified locator

https://github.com/TauCetiProject/TauCeti/tree/64bb4d871548995899dee90beda88b787fafe27d

The retained declarations are `PreAbstractSimplicialComplex.join` in
`TauCeti/AlgebraicTopology/SimplicialComplex/Join/Basic.lean`,
`AbstractSimplicialComplex.StandardSimplex.nonneg`, `.sum_eq_one`,
`.support_subset` and `AbstractSimplicialComplex.mem_standardSimplex_iff`
in `TauCeti/AlgebraicTopology/SimplicialComplex/Realization/Basic.lean`,
and `Geometry.SimplicialComplex.mem_space_onFinsupp_iff` in
`TauCeti/AlgebraicTopology/SimplicialComplex/Realization/Coordinates.lean`.
The private simplex abbreviation is their coordinate convex-hull domain.
No weak-realization topology or collapse declarations are imported.

The local realization is the literal union of closed face convex hulls in the
finite real product, with its Euclidean subspace topology. The native
`Finsupp.linearEquivFunOnFinite` and `LinearMap.image_convexHull` transport the
sourced support characterization to this union. Native `Finset.toLeft`,
`Finset.toRight` and finite sums supply the join projections. The donor finite-sum
wrappers, weak-topology comparison and full-simplex API are not needed.

The endpoint equivalence relation and the geometric suspension identification
are separate constructions. The sourced coordinate characterization alone does
not supply that identification. The join works for precomplexes with unused
vertices and for the empty precomplex; the Homeomorph requires a nonempty
geometric base, and the empty-base cylinder quotient is empty.

Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Authors: The Tau Ceti contributors.
The full Apache 2.0 license is retained at
[`tauceti-LICENSE.txt`](../../docs/reports/polarization-suppliers/tauceti-LICENSE.txt).

The donor pins Lean 4.35.0-rc3 and Mathlib
`0493595ecd5da8ef14742febab99728f98e948e8`;
the local pins are Lean 4.33.0 and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.
Retire each adapter when an equivalent declaration in the locally resolved
Mathlib substitutes directly and its actual consumers compile. Acceptance
elsewhere without that compiled substitution is insufficient.
