---
bibkey: axiommath2026polygoncatalan
authors: Ashvin A. Swaminathan and Alexey Sorokin
year: 2026
title: "ClusterAlgebras: interval and polygon triangulation enumeration"
doi: null
url: https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c
claim: "For m at least three, the extended cardinality of all maximal noncrossing internal-chord sets of the labelled cyclic m-gon is the Catalan number C(m-2)."
strata_touched: []
license: Apache-2.0
triage: anchor
---

# Exact polygon Catalan enumeration

The immutable [source tree](https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c)
supplies `ClusterAlgebras.TypeA.encard_setOf_isTriangulation` in
`ClusterAlgebras/TypeA/Flips.lean`, lines 535–548. For every natural
$m\ge3$ with the cyclic vertex type $\mathbb Z/m\mathbb Z$, it states

$$
\operatorname{encard}\{T:\ T\text{ is a maximal noncrossing internal-chord set}\}
=C_{m-2}.
$$

`IsTriangulation` requires every member to be an internal diagonal, no two
members to cross, and every omitted internal diagonal to cross a member.
There is no selected-completion restriction. The supporting interval
recursion is in `TypeA/Interval.lean`; cyclic-order linearization is in
`TypeA/Polygon.lean`; `TypeA/Catalan.lean` identifies the sequence with
Mathlib's `catalan`.

The exact count cone is transplanted into
`D5/S3/Geometry/Polygons/PolygonCatalanSupplier.lean`. Its consumers identify
the original project carrier with the supplier carrier by the identity on
entire chord sets. The source pins Lean 4.31.0; the receiver uses Lean 4.35.0
and its pinned Mathlib. Only module, import, visibility, documentation
attribute and namespace-boundary metadata are adapted; the retained proof
bodies are unchanged. Source spans, hashes, the complete Apache-2.0 license,
author notices and the receiver-pinned replacement condition are in
[the attribution](../../docs/reports/licenses/cluster-algebras-polygon-third-party.md).

The source result is reused enumeration. Actual ear contraction and the
conditioned original-carrier application belong to the receiver's
`PolygonEarContraction` and `PolygonConditionalCounts`; they are separate
from the imported enumeration theorem. No global originality claim is made.

## Verified locator

- Source: https://github.com/AxiomMath/ClusterAlgebras/tree/a9174706bce3bcb0fa342b4614f98ef2acb7f91c
- Theorem: [`ClusterAlgebras.TypeA.encard_setOf_isTriangulation`](https://github.com/AxiomMath/ClusterAlgebras/blob/a9174706bce3bcb0fa342b4614f98ef2acb7f91c/ClusterAlgebras/TypeA/Flips.lean#L535-L548), lines 535–548 at that pinned revision.
