---
bibkey: tauceti2026simplicialcollapse
authors: The Tau Ceti contributors
year: 2026
title: Deletion, free pairs and elementary simplicial collapses in TauCeti
doi: null
url: https://github.com/TauCetiProject/TauCeti/tree/64bb4d871548995899dee90beda88b787fafe27d
claim: Deletion removes faces containing a specified simplex, a free pair has exactly two cofaces of its lower face, and finite collapse is the reflexive transitive closure of elementary free-pair deletion.
strata_touched:
  - D5/S3/GraphInvariants/Simplicial/DominatedVertexCollapse
license: Apache-2.0
triage: anchor
---

# Simplicial collapse primitives

## Verified locator

https://github.com/TauCetiProject/TauCeti/tree/64bb4d871548995899dee90beda88b787fafe27d

The selected definitions are `PreAbstractSimplicialComplex.deletion` in
`TauCeti/AlgebraicTopology/SimplicialComplex/LinkStar.lean`,
`IsFreePair` and `ElementaryCollapsesTo` in
`TauCeti/AlgebraicTopology/SimplicialComplex/ElementaryCollapse.lean`, and
`CollapsesTo` in
`TauCeti/AlgebraicTopology/SimplicialComplex/Collapse/Basic.lean`.
Their underlying faces are nonempty finite sets, and the vertex type need not be finite.

The local adaptation retains only these four definition bodies, changes the
namespace, and uses the resolved Mathlib structures and relation API directly.
The relative dominated-vertex theorem constructs its free pairs and its finite
sequence separately. The definitions alone supply no geometric realization,
homotopy, suspension, classification or physical operation.

Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Authors: The Tau Ceti contributors.
The full Apache 2.0 license is retained at
[`tauceti-LICENSE.txt`](../../docs/reports/polarization-suppliers/tauceti-LICENSE.txt).
Its SHA-256 is
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`.
The donor tree has no NOTICE file.

The donor pins Lean 4.35.0-rc3 and Mathlib
`0493595ecd5da8ef14742febab99728f98e948e8`;
the local pins are Lean 4.33.0 and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`.
Retire these ports when the locally resolved Mathlib has equivalent primitive
declarations and direct substitutions compile, subject to reconciliation of
frozen content. Upstream acceptance alone does not meet that condition.
