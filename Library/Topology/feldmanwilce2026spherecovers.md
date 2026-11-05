---
bibkey: feldmanwilce2026spherecovers
authors: David V. Feldman and Alexander Wilce
year: 2026
title: A Note on Compactness and Clique Size, Question 3
doi: null
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

The exact endpoint is the lower bound k >= 6 on S2. With an independently
verified six-set open cover this determines the value six. This is known
mathematics, with no worldwide originality or priority claim.

Ari Blondal, Hamed Hatami, Pooya Hatami, Chavdar Lalov and Sivan Tretiak,
*Tight list replicability bounds via a novel sphere covering theorem*,
arXiv:2606.06148v1, Theorem 2.1 (COLT 2026, PMLR 336, Theorem 2), prove
the open-hemisphere-cover multiplicity theorem. Their proof already uses
the normalized weighted sum, positive radial inner product and finite-span
image mechanism. The general estimate k >= 2n-1 is an antecedent, not a new
result here. The finite-union-of-proper-subspaces and punctured-sphere
homotopy finish is a formalization proof variant.

OpenAI, *A nine-dimensional counterexample to Borsuk's covering assertion*,
September 23, 2026, Definition 2.3 and Proposition 4.1, give the triangular
lower bound in the equivalent smooth antipodal partition formulation.
The primary Lean declaration is `OAI.BorsukNine.Admissible.label_bound` in
`lean/OAI/Geometry/Borsuk/Simplicial/OddSphereDimensionBoundFintype.lean`,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a` of `OpenAI/math`.
Its dimension-three case supplies the lower bound six. The manuscript and
Lean source establish a prior result; this delivery claims a cover proof
and exact formal construction, without a mathematical priority claim.

The cover proof uses actual connected components of the open cover members,
with one component per original color and actual subset. Inner-product
sign constancy makes each component acute. A finite component refinement
preserves original color multiplicities. A subordinate partition of unity
gives a normalized sphere map homotopic to the identity. If every point
lies in fewer components than the ambient dimension, the image lies in
finitely many proper subspaces and misses a sphere point. Stereographic
projection then makes the map nullhomotopic. The sphere obstruction is the
source-ported TauCeti reduced singular homology theorem: the sphere has
nonzero reduced singular homology with integer coefficients in its dimension,
whereas a contractible space has zero reduced homology in every degree.

For S2, restrict a cover to the perpendicular unit circle of any point x.
Every color containing x misses that circle by orthogonality-freeness.
Identify the perpendicular plane isometrically with real Euclidean two-space;
the dimension-two case of the general estimate requires at least three
remaining colors. If the total number is at most five, every x therefore
belongs to at most two original colors. The acute-refinement obstruction
then contradicts the sphere obstruction. This argument preserves relative
openness and allows overlapping, disconnected original cover members.

## Reused formal sources

The sphere obstruction endpoint is adopted from the exact declaration
`TauCeti.not_contractibleSpace_sphere` in
`TauCeti/AlgebraicTopology/Sphere/Contractible.lean`, TauCetiProject/TauCeti
revision `5a01f5fe3621126cccf9ba22e700493cbc7b7156`. Its source proof uses
the six transitive sphere-homology declarations needed by that endpoint, with
the actual source dependency closure retained under
`D5/S3/Topology/TauCeti/`. The receiving import paths are namespaced for this
repository; the proof content and declaration telescopes are ported from the
immutable source.

The supplier pins Lean 4.35.0 and Mathlib
`ccbef15ebdb41c2addfac682131f83c75904c3c1`, whereas this repository pins
Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, so dependency-form reuse
is unavailable. Every adapted source file retains the Tau Ceti copyright and
prominent modification notice. The complete Apache-2.0 license is retained at
[`docs/reports/licenses/tauceti-sphere-port-LICENSE.txt`](../../docs/reports/licenses/tauceti-sphere-port-LICENSE.txt),
SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`.
The complete upstream Git tree at the stated revision has no NOTICE file.

Remove this source port only when this project's own pinned Mathlib contains
an equivalent declaration at the full telescope and all live consumers compile
with direct replacement. Upstream acceptance alone does not satisfy that
condition.

```json
{"declaration":"TauCeti.not_contractibleSpace_sphere","source_revision":"5a01f5fe3621126cccf9ba22e700493cbc7b7156","source_path":"TauCeti/AlgebraicTopology/Sphere/Contractible.lean","transitive_source_modules":49,"transitive_source_lines":9630,"retire_when":{"own_pinned_mathlib_has_equivalent_full_telescope":true,"all_live_consumers_compile_with_direct_replacement":true}}
```

## Verified locator

https://arxiv.org/abs/2608.13320v1

https://arxiv.org/abs/1505.02514v3

https://github.com/TauCetiProject/TauCeti/blob/5a01f5fe3621126cccf9ba22e700493cbc7b7156/TauCeti/AlgebraicTopology/Sphere/Contractible.lean

https://arxiv.org/abs/2606.06148v1

https://github.com/OpenAI/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Borsuk/Simplicial/OddSphereDimensionBoundFintype.lean
