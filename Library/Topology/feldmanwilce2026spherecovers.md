---
bibkey: feldmanwilce2026spherecovers
authors: David V. Feldman and Alexander Wilce
year: 2026
title: A Note on Compactness and Clique Size, Question 3
doi: 10.48550/arXiv.2608.13320
url: https://arxiv.org/abs/2608.13320v1
claim: Question 3 asks for the least number of open orthogonality-free sets covering the two-sphere and, more generally, estimates in every dimension.
strata_touched:
  - D5/S3/Topology/SphereOrthogonalityCover
  - D5/S3/Topology/SphereBrouwerObstruction
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Topology/feldmanwilce2026spherecovers -->

# Relatively open orthogonality-free sphere covers

Feldman and Wilce, *A Note on Compactness and Clique Size*,
arXiv:2608.13320v1, Question 3, ask: "What is the least number of open
orthogonality-free sets covering S2? More generally, determine or estimate
the open chromatic number of literal orthogonality on S(n-1)."
The sphere has its relative topology, and literal orthogonality means zero
real inner product. The sets may overlap and need not be connected.

The general lower estimate considered here is k >= 2n-1 for n >= 2.
It leaves the exact open chromatic number undetermined and is a partial
answer to Question 3. No originality or priority claim is made.
For n=3, the bound k >= 5 already follows from Holmsen and Lee,
*Orthogonal colorings of the sphere*, arXiv:1505.02514v3, Theorem 1;
that special case is not new. The source's Remark 6 discusses this
classification and the proposed lower bound five.

The proof uses actual connected components of the open cover members,
with one component per original color and actual subset. Inner-product
sign constancy makes each component acute. Orthogonal-complement bases
bound original point multiplicity, and finite component refinement
preserves that bound. A subordinate partition of unity gives a normalized
sphere map homotopic to the identity. Low multiplicity confines the image
to finitely many proper linear subspaces, so it misses a sphere point.
Stereographic projection makes this map nullhomotopic. Noncontractibility
of the sphere is derived from the existing simplex Brouwer theorem by
descending a contraction along the compact cylinder-to-ball quotient and
constructing a fixed-point-free simplex self-map from a ball retraction.

## Reused formal sources

The simplex fixed point theorem is
`D5.S3.Geometry.FixedPoint.Brouwer.Brouwer`, with the Math_XMUM provenance
and MIT license retained in its source. Mathlib supplies the orthogonal
complement basis, open connected components, partitions of unity, finite
union of proper subspaces, stereographic projection, convex contractibility,
homotopy composition and compact quotient-map criterion.

The private `normalizeToSphere` definition is a source adaptation of
`TauCeti.normalizeToSphere` from
`TauCetiProject/TauCeti`, immutable revision
`5a01f5fe3621126cccf9ba22e700493cbc7b7156`, file
`TauCeti/Analysis/Normed/Module/Normalize.lean`.
Only this definition is reused: visibility, namespace and qualified names
are adapted; its proof is retained. The upstream pins Lean 4.35.0 and
Mathlib `ccbef15ebdb41c2addfac682131f83c75904c3c1`, whereas the receiving
pin is Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. The unequal
Mathlib pins exclude dependency-form reuse.

Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0. The complete license is retained at
[the Tau Ceti license](../../docs/reports/polarization-suppliers/tauceti-LICENSE.txt),
SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`.
The complete upstream Git tree at the stated revision has no NOTICE file.

Remove this selected definition when the project's own pinned Mathlib
contains an equivalent declaration at the full telescope and direct
replacement compiles all its live consumers. Upstream acceptance alone
does not satisfy that condition.

```json
{"declaration":"normalizeToSphere","source_revision":"5a01f5fe3621126cccf9ba22e700493cbc7b7156","retire_when":{"own_pinned_mathlib_has_equivalent_full_telescope":true,"all_live_consumers_compile_with_direct_replacement":true}}
```

## Verified locators

https://arxiv.org/abs/2608.13320v1

https://arxiv.org/abs/1505.02514v3

https://github.com/TauCetiProject/TauCeti/blob/5a01f5fe3621126cccf9ba22e700493cbc7b7156/TauCeti/Analysis/Normed/Module/Normalize.lean
