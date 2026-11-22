---
bibkey: jafari2026forestpacking
authors: Mahdi Jafari
year: 2026
title: "Packing subtrees of a forest"
doi: null
url: https://github.com/mahdi-jfri/GraphMinor/blob/04a7046c000043c02c6a3351f4d7d9a4b24b2b34/GraphMinor/GM16/ForestPacking.lean
claim: "Every indexed family of nonempty connected vertex sets in a finite forest has a finite disjoint subfamily and an equal-size finite vertex transversal."
strata_touched:
  - D5/S3/Combinatorics/Graph/Walks/ForestPacking
license: Apache-2.0
triage: anchor
---

<!-- GID: D5/L/Combinatorics/jafari2026forestpacking -->

# Finite-forest subtree packing and covering

The original Lean source is `GraphMinor/GM16/ForestPacking.lean` at immutable
revision `04a7046c000043c02c6a3351f4d7d9a4b24b2b34` of Mahdi Jafari's
GraphMinor repository. Its source SHA-256 is
`1bf93b078138dd611a334f0d7c05da7bc6ad69d104b1455b2fb27a39ff39f6cf`.
The source identifies the packing theorem used in the proof of Graph Minors
XVI, (5.3), page 56. This adoption makes no claim of mathematical originality
or resolution of an external open problem.

## Verified locator

https://github.com/mahdi-jfri/GraphMinor/blob/04a7046c000043c02c6a3351f4d7d9a4b24b2b34/GraphMinor/GM16/ForestPacking.lean

## Source correspondence

The source definition `GraphMinor.GM16.IsSubtreeSet` and its six theorems
are preserved in `SimpleGraph.ForestPacking`: the five public theorems
`exists_leaf_of_finite_forest`, `IsSubtreeSet.remove_leaf`,
`IsSubtreeSet.exists_neighbor`, `disjoint_of_disjoint_remove_leaf`, and
`forest_packing_cover`, and the private `forest_packing_cover_aux`.
Their telescopes and proof bodies are unchanged. Repository metadata and
namespace packaging are adapted. Native module visibility and definition
exposure are preserved. The source
imports only Mathlib's SimpleGraph Acyclic, Connectivity.Connected,
Walk.Maps and Finset.Card modules. No GraphMinor package is imported.

The original toolchain is Lean 4.35.0-rc3 with Mathlib revision beginning
`b63f6e8`. The host pins Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. These unequal pins require
original-source transplantation rather than a Lake package dependency.
The transplanted source uses the host's native graph, set, walk and Finset
carriers, without a dependency upgrade.

## Scope

Only the host vertex type is finite. The index type has an independent
universe and may be empty or infinite. Every family member is nonempty
and internally connected by simple paths. The conclusion supplies one
finite selection of indices and one finite vertex transversal whose
cardinalities agree, with disjointness referring to the original sets.
No connectedness of the ambient forest, supplied leaf, root, ordering,
packing or transversal is a premise. Empty hosts wherever satisfiable,
repeated sets, disconnected forests and isolated vertices are included.
The removal, neighbor and disjointness helpers have no finite-host
assumption. There is no weighted-cost, infinite-host or complexity claim.

## License and retirement

The complete upstream Apache-2.0 license is preserved at
`docs/reports/licenses/graphminor-forest-packing/LICENSE.txt`; its SHA-256 is
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`.
The supplied source has no copyright header; source authorship is
attribution rather than an invented copyright notice. The transplanted
file prominently identifies its modifications. No additional NOTICE applies to this supplied source.

Retire this transplant when this repository's own pinned Mathlib contains
an equivalent theorem, replacing it by direct reuse. An upstream merge
alone does not satisfy that condition.
